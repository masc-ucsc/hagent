#!/usr/bin/env python3

import sys
import os
import unittest
from unittest.mock import patch, MagicMock

from hagent.tool.compile_slang import Compile_slang


def inline_verilog():
    # Minimal Verilog code to be compiled.
    verilog_code = r"""
module trivial(input [2:0] a, input [2:0] b, output [1:0] c);
wire tmp;  // Warning, undriven
assign c = a ^ tmp; // warning here about conversion
assign x = a[1] ^ b[0] // error here -- Semicolon
endmodule

module leaf5(input [29:0] ci, output [29:0] co);
  assign co = ~ci;
endmodule
"""
    verilog_code2 = r"""
module leaf1(input [14:0] ai, output [14:0] ao);
  assign ao = (~ai == 15'h0) ? 15'h5 : 15'h0;
endmodule

module leaf2(input [14:0] ai, output [14:0] ao, input [24:0] bi, output [24:0] bo);
  // longer temp expression to get some variability in the area of the leaves
  assign ao = bi ^ ~{bi[15:0], bi[24:16]} / ai;
  assign bo = bi * 7;
endmodule

module leaf3(input [29:0] ci, output [29:0] co);
  assign co = ~ci;
endmodule

module leaf4(input[29:0] tempi, output[29:0] tempo);
  assign tempo = tempi - 2;
endmodule

module leaf5(input [29:0] ci, output [29:0] co);
  assign co = ~ci;
endmodule

module leaf6(input tempi, output tempo);
  assign tempo = ~tempi;
endmodule

module leaf7(input [24:0] bi, output [24:0] bo);
  assign bo = bi + bi;
endmodule

module leaf8(input [1:0] i, output [1:0] o);
  assign o = i * 2;
endmodule

module leafout(input oi, output oo);
  assign oo = ~oi;
endmodule

module mid1(input [59:0] di, output [59:0] dout);
  wire [14:0] w_1_to_2;
  wire [14:0] w_2_to_1;

  wire [24:0] w_2_to_7;
  wire [24:0] w_7_to_2;

  leaf1 l1(.ai(w_2_to_1), .ao(w_1_to_2));
  leaf1 ltest(.ai(w_2_to_1), .ao(dout[15:1]));
  leafout lout(.oi(1'b1), .oo(dout[0]));
  leaf2 l2(.ai(w_1_to_2), .ao(w_2_to_1), .bi(w_7_to_2), .bo(w_2_to_7));
  leaf7 l7(.bi(w_2_to_7), .bo(w_7_to_2));

  assign dout = ~{w_7_to_2[19:0], w_1_to_2, w_2_to_7};
endmodule

module mid2(input [59:0] di, output [59:0] dout, input [9:0] ei, output [9:0] eo);
  wire [29:0] w_3_to_5;
  wire [29:0] w_5_to_3;

  leaf3 l3(.ci(di[29:0]), .co(w_3_to_5));
  leaf4 l4(.tempi(w_3_to_5), .tempo(w_3_to_5));
  leaf5 l5(.ci(w_3_to_5), .co(w_5_to_3));

  assign dout = ~{di[59:30], w_3_to_5};
  assign eo = ~{ei[9:1], w_5_to_3[0]};
endmodule

module mid4(input [9:0] ei, output [9:0] eo, input [4:0] fi, output [4:0] fo);
  assign eo = ~ei;
  assign fo = ~fi;
endmodule

module mid3(input [4:0] fi, output [4:0] fo);
  wire w_o_6;
  leaf6 l6(.tempi(fi[3]), .tempo(w_o_6));
  assign fo = ~{fi[4:1], w_o_6};
endmodule

module mid5(input [59:0] gi, output [890:0] gout, input [9:0] hi, output [9:0] ho);
  wire [29:0] w_3_to_5;
  wire [29:0] w_5_to_3;

  wire [899:0] w_1_up_5;

  mid1 m1s(.di(gi), .dout(w_1_up_5));

  leaf3 l3d(.ci(gi[58:28]), .co(w_3_to_5));
  leaf4 l4d(.tempi(w_3_to_5[12]), .tempo(w_3_to_5[13]));
  leaf5 l5d(.ci(w_3_to_5), .co(w_5_to_3));

  assign gout = ~{gi[59:30] & w_1_up_5[890:30], w_3_to_5};
  assign ho = ~{hi[9:1], w_5_to_3[0]};
endmodule

module hier_test(input [59:0] testi, output [59:0] testo);
  wire [59:0] w_1_to_2;
  wire [59:0] w_2_to_1;

  wire [9:0] w_2_to_4;
  wire [9:0] w_4_to_2;

  wire [4:0] w_4_to_3;
  wire [4:0] w_3_to_4;

  wire [59:0] m5out;
  wire [59:0] m6out;

  mid1 m1(.di(w_2_to_1), .dout(w_1_to_2));
  mid2 m2(.di(w_1_to_2), .dout(w_2_to_1), .ei(w_2_to_4), .eo(w_4_to_2));
  mid3 m3(.fi(w_4_to_3), .fo(w_3_to_4));
  mid4 m4(.ei(w_4_to_2), .eo(w_2_to_4), .fi(w_3_to_4), .fo(w_4_to_3));

  // higher-level duplicate instantiation, for regularity discovery
  mid5 m5(.gi(w_1_to_2), .gout(m5out), .hi(w_2_to_4), .ho(m5out[9:0]));
  mid5 m6(.gi(w_1_to_2), .gout(m6out), .hi(w_2_to_4), .ho(m6out[9:0]));

  leaf8 l8(.i(testi[1:0]), .o(testo[1:0]));

  assign testo = ~{testi[0], w_2_to_1[49:2], m5out[1], m6out[0], w_2_to_4, w_3_to_4};

endmodule
"""

    # Create an instance of the Compile_slang tool.
    compiler = Compile_slang()

    # Validate setup: Ensure the pyslang package is present.
    if not compiler.setup():
        print('Setup failed:', compiler.error_message, file=sys.stderr)
        sys.exit(1)

    compiler.add_inline(verilog_code)

    if compiler.set_top('potato'):
        print('Potato should not be a valid top', file=sys.stderr)
        sys.exit(1)

    hierarchy = compiler.get_top_list()
    assert len(hierarchy) == 2
    sum('trivial' in s for s in hierarchy)
    sum('leaf5' in s for s in hierarchy)

    # Not needed to set trivial if there is a single module
    if not compiler.set_top('trivial'):
        print('Failed to set trivial as top module.', file=sys.stderr)
        sys.exit(1)

    hierarchy = compiler.get_top_list()
    assert len(hierarchy) == 1
    assert hierarchy[0] == 'trivial'

    # Retrieve input/output definitions from the top module.
    ios = compiler.get_ios()
    assert len(ios) == 3
    assert ios[0].name == 'a'
    assert ios[1].name == 'b'
    assert ios[2].name == 'c'

    assert ios[0].input == True
    assert ios[1].input == True
    assert ios[2].input == False

    assert ios[0].output == False
    assert ios[1].output == False
    assert ios[2].output == True

    assert ios[0].bits == 3
    assert ios[1].bits == 3
    assert ios[2].bits == 2

    # Retrieve compilation warnings and errors.
    warnings = compiler.get_warnings()
    errors = compiler.get_errors()
    assert len(warnings) > 2
    assert len(errors) == 1
    print(f'err:{errors[0].to_str()}')
    assert errors[0].loc > 0

    compiler2 = Compile_slang()
    compiler2.setup()  # clears the list of tops
    compiler2.add_inline(verilog_code2)
    hier2 = compiler2.get_top_list()
    assert len(hier2) == 1
    for a in hier2:
        print(f'hier:{a}')


def from_fileverilog(args):
    compiler = Compile_slang()

    use_command_line_args = False

    if use_command_line_args:
        compiler.setup(f'-f {args[0]}')
    else:
        compiler.setup()

        for a in args:
            ok = compiler.add_file(file=a)
            if not ok:
                print(f'OOPS {compiler.error_message}')

    hier = compiler.get_top_list()
    for a in hier:
        print(f'top level module options:{a}')

    err = compiler.get_errors()
    for a in err:
        print(f'ERR: File {a.file} Line {a.loc} msg:{a.msg}')

    err = compiler.get_warnings()
    for a in err:
        print(f'WARN: File {a.file} Line {a.loc} msg:{a.msg}')

from hagent.core.step import Step
from typing import Dict

# Trivial example of extending the Pass class
class Step_compile_slang(Step):
    def setup(self):
        super().setup()  # superclass

    def run(self, data: Dict):
        ret = data.copy()

        code = data.get('code',"")
        files = data.get('files',"")

        compiler = Compile_slang()

        if files:
            compiler.setup(f'-f {files}')
        else:
            compiler.setup()

        if code:
            ok = compiler.add_inline(text=code)
            if not ok:
                print(f'ERROR, could not compile {compiler.error_message}')
                sys.exit(3)

        hier = compiler.get_top_list()
        for a in hier:
            print(f'top level module options:{a}')

        err = compiler.get_errors()
        if err:
            err_list = []
            for a in err:
                print(f'ERR: File {a.file} Line {a.loc} msg:{a.msg}')
                err_list.append(a.to_str())

            if err_list:
                ret['err'] = err_list


        err = compiler.get_warnings()
        if err:
            err_list = []
            for a in err:
                print(f'WARN: File {a.file} Line {a.loc} msg:{a.msg}')
                err_list.append(a.to_str())

            if err_list:
                ret['warn'] = err_list

        return ret

def from_fileyaml(args):

    for arg in args:
        st = Step_compile_slang()
        filename = os.path.basename(arg)
        st.set_io(inp_file=arg, out_file=f"out_{filename}")

        st.setup()
        st.step()


class TestCompileSlang(unittest.TestCase):
    """Unit tests for the Compile_slang class to increase code coverage."""

    def test_init(self):
        """Test initialization."""
        compiler = Compile_slang()
        self.assertEqual(compiler.error_message, '')
        self.assertIsNone(compiler._compiler)
        self.assertIsNone(compiler._top_module)

    def test_setup_no_pyslang(self):
        """Test setup when pyslang is not available."""
        compiler = Compile_slang()
        
        # Save original pyslang
        import hagent.tool.compile_slang
        original_pyslang = hagent.tool.compile_slang.pyslang
        
        try:
            # Set pyslang to None
            hagent.tool.compile_slang.pyslang = None
            
            # Test setup
            result = compiler.setup()
            self.assertFalse(result)
        finally:
            # Restore original pyslang
            hagent.tool.compile_slang.pyslang = original_pyslang

    def test_setup_with_invalid_args(self):
        """Test setup with invalid arguments."""
        compiler = Compile_slang()
        
        # Test with invalid command line arguments
        with patch('hagent.tool.compile_slang.pyslang.Driver') as MockDriver:
            mock_driver = MagicMock()
            MockDriver.return_value = mock_driver
            
            # Configure the mock to simulate failure in processOptions
            mock_driver.parseCommandLine.return_value = True
            mock_driver.processOptions.return_value = False
            
            result = compiler.setup("--invalid-option")
            self.assertFalse(result)
            self.assertTrue(compiler.error_message.startswith('could not process slang options'))

    def test_setup_with_invalid_source_files(self):
        """Test setup with invalid source files."""
        compiler = Compile_slang()
        
        # Test with non-existent source file
        with patch('hagent.tool.compile_slang.pyslang.Driver') as MockDriver:
            mock_driver = MagicMock()
            MockDriver.return_value = mock_driver
            
            # Configure the mock to simulate failure in parseAllSources
            mock_driver.parseCommandLine.return_value = True
            mock_driver.processOptions.return_value = True
            mock_driver.parseAllSources.return_value = False
            
            result = compiler.setup("nonexistent_file.v")
            self.assertFalse(result)
            self.assertTrue(compiler.error_message.startswith('count not process slang source files'))

    def test_setup_exception(self):
        """Test setup when an exception occurs."""
        compiler = Compile_slang()
        
        with patch('hagent.tool.compile_slang.pyslang.Driver', side_effect=Exception("Test exception")):
            result = compiler.setup()
            self.assertFalse(result)
            self.assertIn("Test exception", compiler.error_message)

    def test_add_inline_no_pyslang(self):
        """Test add_inline when pyslang is not available."""
        compiler = Compile_slang()
        
        # Temporarily mock pyslang as None
        import hagent.tool.compile_slang
        original_pyslang = hagent.tool.compile_slang.pyslang
        hagent.tool.compile_slang.pyslang = None
        
        try:
            result = compiler.add_inline("module test; endmodule")
            self.assertFalse(result)
        finally:
            # Restore pyslang
            hagent.tool.compile_slang.pyslang = original_pyslang

    def test_add_inline_no_compiler(self):
        """Test add_inline when compiler is not initialized."""
        compiler = Compile_slang()
        compiler._compiler = None
        
        result = compiler.add_inline("module test; endmodule")
        self.assertFalse(result)

    def test_add_inline_exception(self):
        """Test add_inline when an exception occurs."""
        compiler = Compile_slang()
        compiler.setup()
        
        # Mock SyntaxTree.fromText to raise an exception
        import hagent.tool.compile_slang
        if hagent.tool.compile_slang.pyslang:
            original_from_text = hagent.tool.compile_slang.pyslang.SyntaxTree.fromText
            
            def mock_from_text(*args, **kwargs):
                raise Exception("Test exception")
            
            hagent.tool.compile_slang.pyslang.SyntaxTree.fromText = mock_from_text
            
            try:
                result = compiler.add_inline("module test; endmodule")
                self.assertFalse(result)
                self.assertEqual(compiler.error_message, 'Error adding source: Test exception')
            finally:
                # Restore original fromText
                hagent.tool.compile_slang.pyslang.SyntaxTree.fromText = original_from_text

    def test_add_file_no_pyslang(self):
        """Test add_file when pyslang is not available."""
        compiler = Compile_slang()
        
        # Temporarily mock pyslang as None
        import hagent.tool.compile_slang
        original_pyslang = hagent.tool.compile_slang.pyslang
        hagent.tool.compile_slang.pyslang = None
        
        try:
            result = compiler.add_file("test.v")
            self.assertFalse(result)
        finally:
            # Restore pyslang
            hagent.tool.compile_slang.pyslang = original_pyslang

    def test_add_file_no_compiler(self):
        """Test add_file when compiler is not initialized."""
        compiler = Compile_slang()
        compiler._compiler = None
        
        result = compiler.add_file("test.v")
        self.assertFalse(result)

    def test_add_file_file_not_found(self):
        """Test add_file with a non-existent file."""
        compiler = Compile_slang()
        compiler.setup()
        
        result = compiler.add_file("nonexistent_file.v")
        self.assertFalse(result)
        self.assertEqual(compiler.error_message, 'File not found: nonexistent_file.v')

    def test_add_file_exception(self):
        """Test add_file when an exception occurs."""
        compiler = Compile_slang()
        compiler.setup()
        
        # Mock SyntaxTree.fromFile to raise a generic exception
        import hagent.tool.compile_slang
        if hagent.tool.compile_slang.pyslang:
            original_from_file = hagent.tool.compile_slang.pyslang.SyntaxTree.fromFile
            
            def mock_from_file(*args, **kwargs):
                raise Exception("Test exception")
            
            hagent.tool.compile_slang.pyslang.SyntaxTree.fromFile = mock_from_file
            
            try:
                result = compiler.add_file("test.v")
                self.assertFalse(result)
                self.assertEqual(compiler.error_message, 'Error adding source: Test exception')
            finally:
                # Restore original fromFile
                hagent.tool.compile_slang.pyslang.SyntaxTree.fromFile = original_from_file

    def test_set_top_no_compiler(self):
        """Test set_top when compiler is not initialized."""
        compiler = Compile_slang()
        compiler._compiler = None
        
        result = compiler.set_top("test")
        self.assertFalse(result)

    def test_get_top_no_compiler(self):
        """Test get_top when compiler is not initialized."""
        compiler = Compile_slang()
        compiler._compiler = None
        
        result = compiler.get_top()
        self.assertEqual(result, '')

    def test_get_top_no_top_module_multiple_instances(self):
        """Test get_top when no top module is set and there are multiple instances."""
        compiler = Compile_slang()
        
        # Mock setup and add_inline
        with patch('hagent.tool.compile_slang.pyslang') as mock_pyslang:
            # Create mock objects
            mock_compilation = MagicMock()
            mock_root = MagicMock()
            
            # Configure mocks
            mock_pyslang.Driver.return_value.createCompilation.return_value = mock_compilation
            mock_compilation.getRoot.return_value = mock_root
            
            # Setup the compiler
            compiler.setup()
            
            # Configure mock_root to return multiple instances
            mock_instance1 = MagicMock()
            mock_instance1.name = "top1"
            mock_instance2 = MagicMock()
            mock_instance2.name = "top2"
            mock_root.topInstances = [mock_instance1, mock_instance2]
            
            # Test get_top
            result = compiler.get_top()
            self.assertEqual(result, '')
            self.assertIn("uname to find a single top module", compiler.error_message)

    def test_get_top_list_no_compiler(self):
        """Test get_top_list when compiler is not initialized."""
        compiler = Compile_slang()
        compiler._compiler = None
        
        result = compiler.get_top_list()
        self.assertEqual(result, [])

    def test_get_top_list_with_top_module_match(self):
        """Test get_top_list with a matching top module."""
        compiler = Compile_slang()
        compiler.setup()
        compiler._top_module = "test_module"
        
        result = compiler.get_top_list("test_module")
        self.assertEqual(result, ["test_module"])

    def test_get_top_list_with_top_module_no_match(self):
        """Test get_top_list with a non-matching top module."""
        compiler = Compile_slang()
        compiler.setup()
        compiler._top_module = "test_module"
        
        result = compiler.get_top_list("other_module")
        self.assertEqual(result, [])

    def test_get_ios_no_compiler(self):
        """Test get_ios when compiler is not initialized."""
        compiler = Compile_slang()
        compiler._compiler = None
        
        result = compiler.get_ios()
        self.assertEqual(result, [])

    def test_get_ios_module_not_found(self):
        """Test get_ios when the module is not found."""
        compiler = Compile_slang()
        compiler.setup()
        
        result = compiler.get_ios("nonexistent_module")
        self.assertEqual(result, [])

    def test_get_ios_attribute_error(self):
        """Test get_ios when an AttributeError occurs."""
        compiler = Compile_slang()
    
        # Mock setup and add_inline
        with patch('hagent.tool.compile_slang.pyslang') as mock_pyslang:
            # Create mock objects
            mock_compilation = MagicMock()
            mock_root = MagicMock()
            mock_definition = MagicMock()
    
            # Configure mocks
            mock_pyslang.Driver.return_value.createCompilation.return_value = mock_compilation
            mock_compilation.getRoot.return_value = mock_root
            mock_root.lookupName.return_value = mock_definition
    
            # Setup the compiler
            compiler.setup()
            
            # Configure mock_definition to raise AttributeError when accessing body
            # Use a property that raises an exception when accessed
            mock_definition.body.side_effect = AttributeError("No body attribute")
            
            # Test get_ios
            result = compiler.get_ios("test_module")
            self.assertEqual(result, [])

    def test_get_warnings_no_pyslang(self):
        """Test get_warnings when pyslang is not available."""
        compiler = Compile_slang()
        
        # Temporarily mock pyslang as None
        import hagent.tool.compile_slang
        original_pyslang = hagent.tool.compile_slang.pyslang
        hagent.tool.compile_slang.pyslang = None
        
        try:
            result = compiler.get_warnings()
            self.assertEqual(result, [])
        finally:
            # Restore pyslang
            hagent.tool.compile_slang.pyslang = original_pyslang

    def test_get_errors_no_pyslang(self):
        """Test get_errors when pyslang is not available."""
        compiler = Compile_slang()
        
        # Temporarily mock pyslang as None
        import hagent.tool.compile_slang
        original_pyslang = hagent.tool.compile_slang.pyslang
        hagent.tool.compile_slang.pyslang = None
        
        try:
            result = compiler.get_errors()
            self.assertEqual(result, [])
        finally:
            # Restore pyslang
            hagent.tool.compile_slang.pyslang = original_pyslang

    def test_get_diagnostics_no_compiler(self):
        """Test _get_diagnostics when compiler is not initialized."""
        compiler = Compile_slang()
        compiler._compiler = None
        
        result = compiler._get_diagnostics(errors=True)
        self.assertEqual(result, [])
        
    def test_setup_parse_all_sources_failure(self):
        """Test setup when parseAllSources fails."""
        compiler = Compile_slang()
        
        # Mock pyslang.Driver to have parseAllSources return False
        import hagent.tool.compile_slang
        if hagent.tool.compile_slang.pyslang:
            original_driver_class = hagent.tool.compile_slang.pyslang.Driver
            
            class MockDriver:
                def __init__(self):
                    pass
                
                def addStandardArgs(self):
                    pass
                
                def parseCommandLine(self, *args, **kwargs):
                    return True
                
                def processOptions(self):
                    return True
                
                def parseAllSources(self):
                    return False
                
                def createCompilation(self):
                    pass
                
                @property
                def sourceManager(self):
                    pass
            
            hagent.tool.compile_slang.pyslang.Driver = MockDriver
            
            try:
                result = compiler.setup("some_file.v")
                self.assertFalse(result)
                self.assertTrue(compiler.error_message.startswith('count not process slang source files'))
            finally:
                # Restore original Driver
                hagent.tool.compile_slang.pyslang.Driver = original_driver_class
    
    def test_add_file_with_no_source_manager(self):
        """Test add_file when _sm is not initialized."""
        compiler = Compile_slang()
        
        # Mock setup to create a compiler but with _sm set to None
        with patch('hagent.tool.compile_slang.pyslang') as mock_pyslang:
            # Create mock objects
            mock_compilation = MagicMock()
            mock_source_manager = MagicMock()
            mock_tree = MagicMock()
            
            # Configure mock_pyslang
            mock_pyslang.Driver.return_value.createCompilation.return_value = mock_compilation
            mock_pyslang.Driver.return_value.sourceManager = mock_source_manager
            mock_pyslang.SyntaxTree.fromFile.return_value = mock_tree
            
            # Setup the compiler
            compiler.setup()
            
            # Set _sm to None to test the branch where it gets initialized
            compiler._sm = None
            
            # Create a temporary file for testing
            import tempfile
            with tempfile.NamedTemporaryFile(suffix='.v', delete=False) as tmp:
                tmp_name = tmp.name
                tmp.write(b"module test; endmodule")
            
            try:
                # Test add_file
                result = compiler.add_file(tmp_name)
                self.assertTrue(result)
                
                # Verify that _sm was set from _compiler.sourceManager
                self.assertEqual(compiler._sm, mock_compilation.sourceManager)
                
                # Verify that SyntaxTree.fromFile was called with the correct arguments
                mock_pyslang.SyntaxTree.fromFile.assert_called_once_with(tmp_name, sourceManager=mock_compilation.sourceManager)
                
                # Verify that addSyntaxTree was called with the mock tree
                mock_compilation.addSyntaxTree.assert_called_once_with(mock_tree)
            finally:
                # Clean up
                if os.path.exists(tmp_name):
                    os.remove(tmp_name)
    
    def test_set_top_with_valid_module(self):
        """Test set_top with a valid module name."""
        compiler = Compile_slang()
        
        # Mock setup and add_inline
        with patch('hagent.tool.compile_slang.pyslang') as mock_pyslang:
            # Create mock objects
            mock_compilation = MagicMock()
            mock_root = MagicMock()
            mock_definition = MagicMock()
            
            # Configure mocks
            mock_pyslang.Driver.return_value.createCompilation.return_value = mock_compilation
            mock_compilation.getRoot.return_value = mock_root
            mock_root.lookupName.return_value = mock_definition
            
            # Setup the compiler
            compiler.setup()
            
            # Test set_top
            result = compiler.set_top("test_module")
            self.assertTrue(result)
            self.assertEqual(compiler._top_module, "test_module")
            
            # Verify lookupName was called with the correct module name
            mock_root.lookupName.assert_called_once_with("test_module")
    
    def test_get_top_with_single_instance(self):
        """Test get_top when there's a single top instance."""
        compiler = Compile_slang()
        
        # Mock setup and add_inline
        with patch('hagent.tool.compile_slang.pyslang') as mock_pyslang:
            # Create mock objects
            mock_compilation = MagicMock()
            mock_root = MagicMock()
            
            # Configure mocks
            mock_pyslang.Driver.return_value.createCompilation.return_value = mock_compilation
            mock_compilation.getRoot.return_value = mock_root
            
            # Setup the compiler
            compiler.setup()
            
            # Configure mock_root to return a single instance
            mock_instance = MagicMock()
            mock_instance.name = "test_module"
            mock_root.topInstances = [mock_instance]
            
            # Test get_top
            result = compiler.get_top()
            self.assertEqual(result, "test_module")
    
    def test_get_top_list_with_modname(self):
        """Test get_top_list with a specific module name."""
        compiler = Compile_slang()
        
        # Mock setup and add_inline
        with patch('hagent.tool.compile_slang.pyslang') as mock_pyslang:
            # Create mock objects
            mock_compilation = MagicMock()
            mock_root = MagicMock()
            mock_definition = MagicMock()
            
            # Configure mocks
            mock_pyslang.Driver.return_value.createCompilation.return_value = mock_compilation
            mock_compilation.getRoot.return_value = mock_root
            mock_root.lookupName.return_value = mock_definition
            
            # Setup the compiler
            compiler.setup()
            
            # Test get_top_list with a specific module name
            result = compiler.get_top_list("test_module")
            self.assertEqual(result, ["test_module"])
            
            # Verify lookupName was called with the correct module name
            mock_root.lookupName.assert_called_once_with("test_module")
    
    def test_get_ios_with_port_types(self):
        """Test get_ios with different port types."""
        compiler = Compile_slang()
        
        # Mock setup and add_inline
        with patch('hagent.tool.compile_slang.pyslang') as mock_pyslang:
            # Create mock objects
            mock_compilation = MagicMock()
            mock_root = MagicMock()
            mock_definition = MagicMock()
            
            # Configure mocks
            mock_pyslang.Driver.return_value.createCompilation.return_value = mock_compilation
            mock_compilation.getRoot.return_value = mock_root
            mock_root.lookupName.return_value = mock_definition
            
            # Setup the compiler
            compiler.setup()
            
            # Create mock port objects with different directions
            mock_in_port = MagicMock()
            mock_in_port.name = "in_port"
            mock_in_port.direction = mock_pyslang.ArgumentDirection.In
            mock_in_port.kind = mock_pyslang.SymbolKind.Port
            mock_in_port.type.bitWidth = 8
            
            mock_out_port = MagicMock()
            mock_out_port.name = "out_port"
            mock_out_port.direction = mock_pyslang.ArgumentDirection.Out
            mock_out_port.kind = mock_pyslang.SymbolKind.Port
            mock_out_port.type.bitWidth = 8
            
            mock_inout_port = MagicMock()
            mock_inout_port.name = "inout_port"
            mock_inout_port.direction = mock_pyslang.ArgumentDirection.InOut
            mock_inout_port.kind = mock_pyslang.SymbolKind.Port
            mock_inout_port.type.bitWidth = 8
            
            # Configure mock_definition.body to contain the mock ports
            mock_definition.body = [mock_in_port, mock_out_port, mock_inout_port]
            
            # Test get_ios
            result = compiler.get_ios("test_module")
            self.assertEqual(len(result), 3)
            
            # Verify the input port
            self.assertEqual(result[0].name, "in_port")
            self.assertTrue(result[0].input)
            self.assertFalse(result[0].output)
            self.assertEqual(result[0].bits, 8)
            
            # Verify the output port
            self.assertEqual(result[1].name, "out_port")
            self.assertFalse(result[1].input)
            self.assertTrue(result[1].output)
            self.assertEqual(result[1].bits, 8)
            
            # Verify the inout port
            self.assertEqual(result[2].name, "inout_port")
            self.assertTrue(result[2].input)
            self.assertTrue(result[2].output)
            self.assertEqual(result[2].bits, 8)

    def test_get_diagnostics_with_errors_and_warnings(self):
        """Test _get_diagnostics with both errors and warnings."""
        compiler = Compile_slang()
        
        # Mock setup and add_inline
        with patch('hagent.tool.compile_slang.pyslang') as mock_pyslang:
            # Create mock objects
            mock_compilation = MagicMock()
            mock_source_manager = MagicMock()
            mock_diag_engine = MagicMock()
            
            # Create mock diagnostics
            mock_error = MagicMock()
            mock_error.isError.return_value = True
            
            mock_warning = MagicMock()
            mock_warning.isError.return_value = False
            
            # Configure mocks
            mock_pyslang.Driver.return_value.createCompilation.return_value = mock_compilation
            mock_pyslang.Driver.return_value.sourceManager = mock_source_manager
            mock_pyslang.DiagnosticEngine.return_value = mock_diag_engine
            mock_compilation.getAllDiagnostics.return_value = [mock_error, mock_warning]
            mock_diag_engine.reportAll.return_value = "Error message"
            
            # Setup the compiler
            compiler.setup()
            
            # Test get_errors
            errors = compiler.get_errors()
            self.assertEqual(len(errors), 1)
            
            # Test get_warnings
            warnings = compiler.get_warnings()
            self.assertEqual(len(warnings), 1)

    def test_setup_parse_command_line_failure(self):
        """Test setup when parseCommandLine returns False."""
        compiler = Compile_slang()
        
        with patch('hagent.tool.compile_slang.pyslang.Driver') as MockDriver:
            mock_driver = MagicMock()
            MockDriver.return_value = mock_driver
            
            # Configure the mock to simulate failure in parseCommandLine
            mock_driver.parseCommandLine.return_value = False
            
            result = compiler.setup("some_args")
            self.assertFalse(result)
    
    def test_add_inline_success(self):
        """Test successful add_inline operation."""
        compiler = Compile_slang()
        
        # Mock setup and pyslang
        with patch('hagent.tool.compile_slang.pyslang') as mock_pyslang:
            # Create mock objects
            mock_compilation = MagicMock()
            mock_tree = MagicMock()
            mock_sm = MagicMock()
            
            # Configure mocks
            mock_pyslang.SyntaxTree.fromText.return_value = mock_tree
            
            # Set up compiler attributes
            compiler._compiler = mock_compilation
            compiler._sm = mock_sm
            
            # Call add_inline
            result = compiler.add_inline("module test; endmodule")
            
            # Verify the result and method calls
            self.assertTrue(result)
            mock_pyslang.SyntaxTree.fromText.assert_called_once()
            mock_compilation.addSyntaxTree.assert_called_once_with(mock_tree)
    
    def test_get_top_with_top_module_set(self):
        """Test get_top when _top_module is already set."""
        compiler = Compile_slang()
        
        # Set up compiler attributes
        compiler._compiler = MagicMock()
        compiler._top_module = "TestModule"
        
        # Call get_top
        result = compiler.get_top()
        
        # Verify the result
        self.assertEqual(result, "TestModule")
    
    def test_get_top_list_no_modname(self):
        """Test get_top_list when no modname is provided."""
        compiler = Compile_slang()
        
        # Mock setup and compiler
        with patch('hagent.tool.compile_slang.pyslang') as mock_pyslang:
            # Create mock objects
            mock_compilation = MagicMock()
            mock_root = MagicMock()
            mock_instance1 = MagicMock()
            mock_instance2 = MagicMock()
            
            # Configure mocks
            mock_compilation.getRoot.return_value = mock_root
            mock_instance1.name = "Module1"
            mock_instance2.name = "Module2"
            mock_root.topInstances = [mock_instance1, mock_instance2]
            
            # Set up compiler attributes
            compiler._compiler = mock_compilation
            compiler._top_module = None
            
            # Call get_top_list with no modname
            result = compiler.get_top_list()
            
            # Verify the result
            self.assertEqual(result, ["Module1", "Module2"])
    
    def test_get_ios_no_modname(self):
        """Test get_ios when no modname is provided."""
        compiler = Compile_slang()
        
        # Mock setup and compiler
        with patch.object(compiler, 'get_top', return_value="DefaultTop") as mock_get_top:
            with patch('hagent.tool.compile_slang.pyslang') as mock_pyslang:
                # Create mock objects
                mock_compilation = MagicMock()
                mock_root = MagicMock()
                mock_definition = MagicMock()
                mock_stmt = MagicMock()
                
                # Configure mocks
                mock_compilation.getRoot.return_value = mock_root
                mock_root.lookupName.return_value = mock_definition
                mock_definition.body = [mock_stmt]
                
                # Configure mock_stmt to simulate a port
                mock_stmt.kind = mock_pyslang.SymbolKind.Port
                mock_stmt.direction = mock_pyslang.ArgumentDirection.In
                mock_stmt.name = "test_port"
                mock_stmt.type.bitWidth = 8
                
                # Set up compiler attributes
                compiler._compiler = mock_compilation
                
                # Call get_ios with no modname
                result = compiler.get_ios()
                
                # Verify the result
                self.assertEqual(len(result), 1)
                self.assertEqual(result[0].name, "test_port")
                self.assertEqual(result[0].bits, 8)
                self.assertTrue(result[0].input)
                self.assertFalse(result[0].output)
                
                # Verify get_top was called
                mock_get_top.assert_called_once()
                # Verify lookupName was called with the correct module name
                mock_root.lookupName.assert_called_once_with("DefaultTop")

    def test_set_top_with_nonexistent_module(self):
        """Test set_top with a module name that doesn't exist."""
        compiler = Compile_slang()
        
        # Mock setup and add_inline
        with patch('hagent.tool.compile_slang.pyslang') as mock_pyslang:
            # Create mock objects
            mock_compilation = MagicMock()
            mock_root = MagicMock()
            
            # Configure mocks
            mock_pyslang.Driver.return_value.createCompilation.return_value = mock_compilation
            mock_compilation.getRoot.return_value = mock_root
            # Return None to simulate a module that doesn't exist
            mock_root.lookupName.return_value = None
            
            # Setup the compiler
            compiler.setup()
            
            # Test set_top with a nonexistent module
            result = compiler.set_top("nonexistent_module")
            self.assertFalse(result)
            self.assertIsNone(compiler._top_module)  # _top_module should not be set
            
            # Verify lookupName was called with the correct module name
            mock_root.lookupName.assert_called_once_with("nonexistent_module")


def main(args):
    # Ensure args is a list
    if isinstance(args, str):
        args = [args]

    # If no arguments, run all tests
    if len(args) <= 1:
        unittest.main()
        return 0

    # Run specific test
    if args[1] == 'inline':
        inline_verilog()
    elif args[1].endswith('.v'):
        from_fileverilog(args[1:])
    elif args[1].endswith('.yaml'):
        from_fileyaml(args[1:])
    else:
        print(f'Unknown option {args[1]}')
        return 1
    return 0


if __name__ == '__main__':  # pragma: no cover
    sys.exit(main(sys.argv))
