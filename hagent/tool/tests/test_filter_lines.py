#!/usr/bin/env python3
"""
Tests for the FilterLines class.
"""

import os
import tempfile
from hagent.tool.filter_lines import FilterLines


class TestFilterLines:
    """Test class for FilterLines."""

    @classmethod
    def setup_class(cls):
        """Set up the test class."""
        cls.filter_tool = FilterLines()

    def test_split_methods(self):
        """Test token splitting methods."""
        # Test split_on_underscore with various inputs
        underscore_tests = [
            # input, expected found tokens, expected missing tokens
            ('hello_world_test', ['hello', 'world', 'test'], []),
            ('a_b_long_c', ['long'], ['a', 'b', 'c']),  # Short tokens should be filtered
        ]
        for input_str, expected_in, expected_not_in in underscore_tests:
            parts = self.filter_tool._split_on_underscore(input_str)
            for token in expected_in:
                assert token in parts, f"Token '{token}' should be in {parts}"
            for token in expected_not_in:
                assert token not in parts, f"Token '{token}' should not be in {parts}"

        # Test split_camel with various inputs
        camel_tests = [('HelloWorldTest', ['Hello', 'World', 'Test']), ('AbcDefGhi', ['Abc', 'Def', 'Ghi'])]
        for input_str, expected in camel_tests:
            parts = self.filter_tool._split_camel(input_str)
            for token in expected:
                assert token in parts, f"Token '{token}' should be in {parts}"

    def test_token_extraction(self):
        """Test extracting and normalizing tokens from diff code lines."""
        # Test various token extraction scenarios
        test_cases = [
            # description, input, expected tokens, excluded tokens
            ('Basic tokens', 'val counter = counter + 1', ['counter', 'val'], []),
            ('Special prefixes', 'io_dataOut = in_dataValue', ['dataOut', 'data', 'Out', 'dataValue'], []),
            ('Out suffix', 'signalOut = value', ['signalOut', 'signal'], []),
            ('Numeric tokens', 'reg[7:0] = 42', ['42'], ['7', '0']),
            ('Operators', 'a && b || c', ['&&', '||'], []),
            ('io_ prefix handling', 'io_data = 123', ['data'], []),
            ('in_ prefix handling', 'in_value = 456', ['value'], []),
        ]

        for desc, input_str, expected_tokens, excluded_tokens in test_cases:
            tokens = self.filter_tool._extract_tokens(input_str)
            for token in expected_tokens:
                assert token in tokens, f"Failed in '{desc}': {token} not found in {tokens}"
            for token in excluded_tokens:
                assert token not in tokens, f"Failed in '{desc}': {token} should not be in {tokens}"

    def test_extract_hint_lines(self):
        """Test extracting line numbers from comments."""
        test_cases = [
            # Input comment, expected line numbers
            ('Found in src/main/scala/Test.scala:42', [42]),
            ('Check src/main/scala/Module.scala:10 and src/test/scala/ModuleTest.scala:20', [10, 20]),
            ('No line numbers here', []),
        ]

        for comment, expected_lines in test_cases:
            hints = self.filter_tool._extract_hint_lines(comment)
            assert set(hints) == set(expected_lines)

    def create_test_files(self, diff_text, chisel_text):
        """Create temporary test files and return their paths."""
        diff_file = tempfile.NamedTemporaryFile(mode='w', delete=False, suffix='.diff')
        chisel_file = tempfile.NamedTemporaryFile(mode='w', delete=False, suffix='.scala')

        diff_file.write(diff_text)
        chisel_file.write(chisel_text)
        diff_file.close()
        chisel_file.close()

        self.test_files = [diff_file.name, chisel_file.name]
        return diff_file.name, chisel_file.name

    def teardown_method(self):
        """Clean up any created test files."""
        if hasattr(self, 'test_files'):
            for file_path in self.test_files:
                if os.path.exists(file_path):
                    os.unlink(file_path)
            self.test_files = []

    def test_filter_with_basic_and_context(self):
        """Test both basic filtering and context-based filtering."""
        # Create test files
        diff_text = """--- verilog_original.v
+++ verilog_fixed.v
@@ -1,5 +1,5 @@
 module test;
-  reg [7:0] counterReg;
-  always @(posedge clk)
-    counterReg <= counterReg + 1;
+  reg [7:0] counterReg;
+  always @(posedge clk)
+    counterReg <= counterReg + 2;
 endmodule"""

        chisel_text = """
class Test extends Module {
  val counterReg = RegInit(0.U(8.W))
  counterReg := counterReg + 1.U
}
"""

        diff_file, chisel_file = self.create_test_files(diff_text, chisel_text)

        # Test basic filtering
        result = self.filter_tool.filter_lines(diff_file, chisel_file)
        assert 'counterReg' in result

        # Test with context
        result_with_context = self.filter_tool.filter_lines(diff_file, chisel_file, context=1)
        assert len(result_with_context.splitlines()) >= len(result.splitlines())

        # Check that context lines are included
        context_lines = [line for line in result_with_context.splitlines() if not line.startswith('->')]
        assert len(context_lines) > 0, 'No context lines found with context=1'

    def test_filter_with_hints(self):
        """Test filtering with line hints in comments."""
        diff_text = """--- verilog_original.v
+++ verilog_fixed.v
@@ -1,5 +1,5 @@
 module test;
  wire signal;
-  assign signal = value; // src/main/scala/Test.scala:3
+  assign signal = newValue;
 endmodule"""

        chisel_text = """
class Test {
  val signal = Wire(Bool())
  signal := value
}
"""

        diff_file, chisel_file = self.create_test_files(diff_text, chisel_text)
        result = self.filter_tool.filter_lines(diff_file, chisel_file)
        assert 'signal' in result

    def test_filter_with_comments_and_imports(self):
        """Test filtering with comments, imports, and context."""
        diff_text = """--- verilog_original.v
+++ verilog_fixed.v
@@ -1,5 +1,5 @@
 module test;
-  reg [7:0] counterValue counter_reg;
-  always @(posedge clk) counter_reg <= counter_reg + 1;
+  reg [7:0] counterValue counter_reg;
+  always @(posedge clk) counter_reg <= counter_reg + 2;
 endmodule"""

        chisel_text = """// File header comment
import chisel3._
import chisel3.util._

class Test extends Module {
  // Comment line
  val counterValue = RegInit(0.U(8.W))
  val counter_reg = Wire(UInt(8.W))
  counter_reg := counterValue + 1.U
  // Another comment
}
"""

        diff_file, chisel_file = self.create_test_files(diff_text, chisel_text)
        result = self.filter_tool.filter_lines(diff_file, chisel_file, context=2)

        # Core assertions
        assert 'counter' in result
        assert '->' in result
        assert 'import chisel3._' not in result
        assert '// Comment line' not in result

        # Context line check
        context_lines = [line for line in result.splitlines() if not line.startswith('->')]
        assert len(context_lines) > 0

    def test_file_error_handling(self):
        """Test error handling for missing or invalid files."""
        # Test with non-existent diff file
        with self.assert_raises_with_message(RuntimeError, 'Failed to read diff file', 'non_existent_diff.txt'):
            self.filter_tool.filter_lines('non_existent_diff.txt', 'dummy.scala')

        # Test with non-existent chisel file but valid diff file
        diff_file = tempfile.NamedTemporaryFile(mode='w', delete=False, suffix='.diff')
        diff_file.write('some content')
        diff_file.close()
        self.test_files = [diff_file.name]

        with self.assert_raises_with_message(RuntimeError, 'Failed to read Chisel file', 'non_existent_chisel.scala'):
            self.filter_tool.filter_lines(diff_file.name, 'non_existent_chisel.scala')

    def assert_raises_with_message(self, exception_type, message_part, file_part=None):
        """Helper method to check exceptions with specific message content."""

        class MessageChecker:
            def __enter__(self):
                return self

            def __exit__(self, exc_type, exc_val, exc_tb):
                assert exc_type is exception_type, f'Expected {exception_type}, got {exc_type}'
                assert message_part in str(exc_val), f"Expected '{message_part}' in '{exc_val}'"
                if file_part:
                    assert file_part in str(exc_val), f"Expected '{file_part}' in '{exc_val}'"
                return True  # Exception has been handled

        return MessageChecker()


if __name__ == '__main__':
    tester = TestFilterLines()
    tester.setup_class()
    tester.test_split_methods()
    tester.test_token_extraction()
    tester.test_extract_hint_lines()
    tester.test_filter_with_basic_and_context()
    tester.teardown_method()
    tester.test_filter_with_hints()
    tester.teardown_method()
    tester.test_filter_with_comments_and_imports()
    tester.teardown_method()
    tester.test_file_error_handling()
    tester.teardown_method()
    print('All tests passed!')
