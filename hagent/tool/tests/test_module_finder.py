import unittest
import tempfile
import os
from hagent.tool.module_finder import Module_finder


class TestModuleFinder(unittest.TestCase):
    def setUp(self):
        self.finder = Module_finder()

    def test_extract_modules_from_diff(self):
        """Test extraction of module names from Verilog diff"""
        diff_content = """
--- a/test.v
+++ b/test.v
@@ -1,10 +1,12 @@ module ALU(
+module ALU(
     input wire clk,
     input wire reset,
-    output reg result
+    output wire result
 );
+  // New logic here
 endmodule
 
 module Control(
"""
        modules = self.finder._extract_modules_from_diff(diff_content)
        self.assertIn('ALU', modules)
        self.assertIn('Control', modules)

    def test_extract_modules_from_diff_context_line(self):
        """Test extraction from @@ context lines"""
        diff_content = """
@@ -15,7 +15,8 @@ module CPU_Core(
     input wire clk,
-    output reg done
+    output wire done,
+    output wire ready
"""
        modules = self.finder._extract_modules_from_diff(diff_content)
        self.assertIn('CPU_Core', modules)

    def test_calculate_match_confidence_exact(self):
        """Test exact module name matching"""
        confidence = self.finder._calculate_match_confidence('ALU', 'ALU')
        self.assertEqual(confidence, 1.0)

    def test_calculate_match_confidence_case_insensitive(self):
        """Test case insensitive matching"""
        confidence = self.finder._calculate_match_confidence('alu', 'ALU')
        self.assertEqual(confidence, 1.0)

    def test_calculate_match_confidence_normalized(self):
        """Test normalized name matching"""
        confidence = self.finder._calculate_match_confidence('CPU_Core', 'CPUCore')
        self.assertGreaterEqual(confidence, 0.8)

    def test_calculate_match_confidence_substring(self):
        """Test substring matching"""
        confidence = self.finder._calculate_match_confidence('ALU', 'ALUControl')
        self.assertGreater(confidence, 0.7)

    def test_normalize_module_name(self):
        """Test module name normalization"""
        self.assertEqual(self.finder._normalize_module_name('CPU_Core_Module'), 'cpucore')
        self.assertEqual(self.finder._normalize_module_name('Top_ALU'), 'alu')
        self.assertEqual(self.finder._normalize_module_name('Control_Unit'), 'control')

    def test_string_similarity(self):
        """Test string similarity calculation"""
        self.assertEqual(self.finder._string_similarity('abc', 'abc'), 1.0)
        self.assertGreater(self.finder._string_similarity('abc', 'abd'), 0.5)
        self.assertEqual(self.finder._string_similarity('', ''), 1.0)
        self.assertEqual(self.finder._string_similarity('abc', ''), 0.0)

    def test_extract_scala_modules(self):
        """Test extraction of Scala class/object definitions"""
        scala_content = """
package test

class ALU extends Module {
  val io = IO(new Bundle {
    val input1 = Input(UInt(32.W))
    val output = Output(UInt(32.W))
  })
  
  io.output := io.input1 + 1.U
}

object ControlUnit {
  def apply() = new ControlUnit
}

class ControlUnit extends Module {
  // implementation
}
"""
        lines = scala_content.split('\n')
        modules = self.finder._extract_scala_modules(scala_content, lines)

        self.assertEqual(len(modules), 3)  # ALU, ControlUnit object, ControlUnit class

        # Check ALU class
        alu_modules = [m for m in modules if m['name'] == 'ALU']
        self.assertEqual(len(alu_modules), 1)
        self.assertEqual(alu_modules[0]['type'], 'class')

        # Check ControlUnit object and class
        control_modules = [m for m in modules if m['name'] == 'ControlUnit']
        self.assertEqual(len(control_modules), 2)

    def test_find_modules_in_file_with_temp_file(self):
        """Test finding modules in a temporary Scala file"""
        scala_content = """
package dinocpu.components

import chisel3._

class ALU extends Module {
  val io = IO(new Bundle {
    val operation = Input(UInt(5.W))
    val inputx = Input(UInt(64.W))
    val inputy = Input(UInt(64.W))
    val result = Output(UInt(64.W))
  })
  
  // ALU implementation
  io.result := io.inputx + io.inputy
}
"""

        with tempfile.NamedTemporaryFile(mode='w', suffix='.scala', delete=False) as f:
            f.write(scala_content)
            temp_file = f.name

        try:
            hits = self.finder._find_modules_in_file(temp_file, ['ALU', 'Control'])

            # Should find ALU with high confidence
            alu_hits = [h for h in hits if h.module_name == 'ALU']
            self.assertEqual(len(alu_hits), 1)
            self.assertEqual(alu_hits[0].confidence, 1.0)

            # Should not find Control
            control_hits = [h for h in hits if h.module_name == 'Control']
            self.assertEqual(len(control_hits), 0)

        finally:
            os.unlink(temp_file)

    def test_find_class_end_line(self):
        """Test finding the end line of a class definition"""
        lines = [
            'class ALU extends Module {',  # line 0
            '  val io = IO(new Bundle {',  # line 1
            '    val input = Input(UInt(32.W))',  # line 2
            '  })',  # line 3
            '  ',  # line 4
            '  io.result := io.input + 1.U',  # line 5
            '}',  # line 6
            '',  # line 7
            'class Other extends Module {',  # line 8
        ]

        end_line = self.finder._find_class_end_line(lines, 0)
        self.assertEqual(end_line, 7)  # Should be line 7 (1-based)

    def test_full_integration(self):
        """Test the complete workflow with temporary files"""
        # Create temporary Scala files
        alu_content = """
package dinocpu.components

import chisel3._

class ALU extends Module {
  val io = IO(new Bundle {
    val operation = Input(UInt(5.W))
    val result = Output(UInt(64.W))
  })
}
"""

        control_content = """
package dinocpu.components

import chisel3._

class Control extends Module {
  val io = IO(new Bundle {
    val instruction = Input(UInt(32.W))
    val control_signals = Output(UInt(16.W))
  })
}
"""

        # Verilog diff targeting ALU
        verilog_diff = """
--- a/alu.v
+++ b/alu.v
@@ -1,5 +1,6 @@ module ALU(
 module ALU(
     input wire [4:0] operation,
+    input wire clk,
     output reg [63:0] result
 );
"""

        temp_files = []
        try:
            # Create temporary files
            with tempfile.NamedTemporaryFile(mode='w', suffix='.scala', delete=False) as f:
                f.write(alu_content)
                temp_files.append(f.name)

            with tempfile.NamedTemporaryFile(mode='w', suffix='.scala', delete=False) as f:
                f.write(control_content)
                temp_files.append(f.name)

            # Test the complete workflow
            hits = self.finder.find_modules(temp_files, 'ALU', verilog_diff)

            # Should find ALU with high confidence
            self.assertGreater(len(hits), 0)

            alu_hits = [h for h in hits if h.module_name == 'ALU']
            self.assertEqual(len(alu_hits), 1)
            self.assertEqual(alu_hits[0].confidence, 1.0)

            # Verify file information
            self.assertIn('.scala', alu_hits[0].file_name)
            self.assertGreater(alu_hits[0].start_line, 0)
            self.assertGreater(alu_hits[0].end_line, alu_hits[0].start_line)

        finally:
            # Clean up temporary files
            for temp_file in temp_files:
                try:
                    os.unlink(temp_file)
                except OSError:
                    pass

    def test_multiple_modules_in_diff(self):
        """Test handling multiple modules in a single diff"""
        multi_module_diff = """
--- a/cpu.v
+++ b/cpu.v
@@ -10,5 +10,6 @@ module CPU_Core(
 module CPU_Core(
     input wire clk,
+    input wire reset,
     output wire done
 );
 endmodule
 
 module ALU(
     input wire [63:0] a,
     input wire [63:0] b,
+    output wire [63:0] result
 );
"""

        modules = self.finder._extract_modules_from_diff(multi_module_diff)
        self.assertIn('CPU_Core', modules)
        self.assertIn('ALU', modules)

    def test_empty_inputs(self):
        """Test handling of empty or invalid inputs"""
        # Empty diff
        hits = self.finder.find_modules(['nonexistent.scala'], 'ALU', '')
        self.assertEqual(len(hits), 0)

        # Empty file list
        hits = self.finder.find_modules([], 'ALU', 'some diff')
        self.assertEqual(len(hits), 0)

        # Nonexistent files (should be handled gracefully)
        hits = self.finder.find_modules(['nonexistent.scala'], 'ALU', 'module ALU();')
        self.assertEqual(len(hits), 0)


if __name__ == '__main__':
    unittest.main()
