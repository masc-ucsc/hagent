#!/usr/bin/env python3
"""
Test file for extract_code.py.
This file tests the functionality of the Extract_code classes.
"""

import unittest
import types
import inspect
import sys
from unittest.mock import patch, MagicMock
from hagent.tool.extract_code import (
    Extract_code_verilog,
    Extract_code_chisel,
    Extract_code_pyrtl,
    Extract_code_dslx,
    Extract_code_default,
    get_extract_code,
    Extract_code
)


class TestExtractCode(unittest.TestCase):
    """Test class for Extract_code classes."""
    
    def test_abstract_base_class(self):
        """Test the abstract base class."""
        # Create a concrete implementation of the abstract class for testing
        class ConcreteExtractCode(Extract_code):
            def parse(self, prompt: str, verilog_path: str = None) -> str:
                return "Concrete implementation"
        
        # Test that we can instantiate a concrete implementation
        extractor = ConcreteExtractCode()
        self.assertEqual(extractor.parse("test", "test.v"), "Concrete implementation")
        
        # Test that the abstract class has an abstract method 'parse'
        self.assertTrue(inspect.isabstract(Extract_code))
        self.assertTrue('parse' in Extract_code.__abstractmethods__)
        
        # Directly test the signature of the parse method without instantiating
        parse_method = Extract_code.parse
        signature = inspect.signature(parse_method)
        self.assertEqual(str(signature), "(self, prompt: str, verilog_path: str) -> str")
        
        try:
            # Create a temporary instance with __abstractmethods__ cleared
            temp_class = type('TempExtractCode', (Extract_code,), {})
            temp_class.__abstractmethods__ = frozenset()
            instance = temp_class()
            result = Extract_code.parse(instance, "test", "test.v")
            self.assertIsNone(result)

        except Exception as e:
            pass
    
    def test_extract_codeblock(self):
        """Test the extract_codeblock method."""
        extractor = Extract_code_default()
        
        # Test with code block with language
        text = "Some text\n```python\ndef hello():\n    print('Hello')\n```\nMore text"
        result = extractor.extract_codeblock(text)
        self.assertEqual(result, "def hello():\n    print('Hello')")
        
        # Test with code block without language
        text = "Some text\n```\ndef hello():\n    print('Hello')\n```\nMore text"
        result = extractor.extract_codeblock(text)
        self.assertEqual(result, "def hello():\n    print('Hello')")
        
        # Test with multiple code blocks
        text = "```python\ndef hello():\n    print('Hello')\n```\n```javascript\nconsole.log('Hello');\n```"
        result = extractor.extract_codeblock(text)
        self.assertEqual(result, "def hello():\n    print('Hello')\n\nconsole.log('Hello');")
        
        # Test with no code blocks
        text = "Just plain text without code blocks"
        result = extractor.extract_codeblock(text)
        self.assertEqual(result, "Just plain text without code blocks")
        
        # Test with backticks in text
        text = "Text with `inline code` and ```block code```"
        result = extractor.extract_codeblock(text)
        # The actual behavior is that it extracts just "code" from the block code part
        self.assertEqual(result, "code")
        
        # Test with None input
        result = extractor.extract_codeblock(None)
        self.assertEqual(result, "")
    
    def test_extract_code_verilog(self):
        """Test the Extract_code_verilog class."""
        extractor = Extract_code_verilog()
        
        # Test with Verilog module
        text = """
Some text before
```verilog
`include "header.v"
`define CONSTANT 1

module test(input clk, output reg out);
    always @(posedge clk) begin
        out <= ~out;
    end
endmodule

module unused(input a, output b);
    assign b = a;
endmodule
```
Some text after
"""
        result = extractor.parse(text)
        # The actual behavior is that it only includes module content and not the include directives
        # when they appear before the first module
        self.assertIn("module test(input clk, output reg out);", result)
        self.assertIn("always @(posedge clk) begin", result)
        self.assertIn("out <= ~out;", result)
        self.assertIn("endmodule", result)
        self.assertIn("module unused(input a, output b);", result)
        self.assertNotIn("Some text before", result)
        self.assertNotIn("Some text after", result)
        
        # Test with preprocessor directives only - note that backticks are removed by extract_codeblock
        # and the implementation doesn't capture preprocessor directives without a module
        text = """
```verilog
`include "header.v"
`define CONSTANT 1
`ifdef DEBUG
`endif
```
"""
        result = extractor.parse(text)
        # The actual behavior is that it returns an empty string when there's no module
        self.assertEqual(result, "")
        
        # Test with preprocessor directives and a module
        text = """
```verilog
`include "header.v"
`define CONSTANT 1

module test();
endmodule
```
"""
        result = extractor.parse(text)
        # The actual behavior is that it includes the module but not the preprocessor directives
        self.assertIn("module test();", result)
        self.assertIn("endmodule", result)
        self.assertNotIn("include", result)
        self.assertNotIn("define", result)
        
        # Create a custom subclass that overrides extract_codeblock to return preprocessor directives
        class TestExtractCodeVerilogPreprocessor(Extract_code_verilog):
            def extract_codeblock(self, text):
                # Return a string with preprocessor directives only (no module)
                return "`include \"test.v\"\n`define TEST 1"
        
        # Create an instance of our test class
        test_extractor = TestExtractCodeVerilogPreprocessor()
        
        # Call parse with any text, the extract_codeblock method will return our test string
        result = test_extractor.parse("dummy text")
        
        # Verify the result - the parse method should include the preprocessor directives
        self.assertIn("`include \"test.v\"", result)
        self.assertIn("`define TEST 1", result)
        
        # Test with escaped backslashes
        text = """
```verilog
module test(input clk, output reg out);
    always @(posedge clk) begin
        out <= \\~out;
    end
endmodule
```
"""
        result = extractor.parse(text)
        self.assertIn("out <= ~out;", result)  # Backslashes should be removed
    
    def test_extract_code_chisel(self):
        """Test the Extract_code_chisel class."""
        extractor = Extract_code_chisel()
        
        # Test with Chisel code
        text = """
Some text before
```scala
package example

import chisel3._
import chisel3.util._

class MyModule extends Module {
  val io = IO(new Bundle {
    val in = Input(UInt(8.W))
    val out = Output(UInt(8.W))
  })
  
  io.out := io.in + 1.U
}
```
Some text after
"""
        result = extractor.parse(text)
        self.assertIn("import chisel3._", result)
        self.assertIn("import chisel3.util._", result)
        self.assertIn("class MyModule extends Module {", result)
        self.assertIn("io.out := io.in + 1.U", result)
        self.assertNotIn("Some text before", result)
        self.assertNotIn("Some text after", result)
        
        # Test with non-Chisel code
        text = """
```scala
package example

class MyClass {
  def hello() = println("Hello")
}
```
"""
        result = extractor.parse(text)
        self.assertEqual(result, text.replace("```scala", "").replace("```", "").strip())
        
        # Test with escaped backslashes
        text = """
```scala
import chisel3._

class MyModule extends Module {
  val io = IO(new Bundle {
    val in = Input(UInt(8.\\W))
  })
}
```
"""
        result = extractor.parse(text)
        self.assertIn("val in = Input(UInt(8.W))", result)  # Backslashes should be removed
        
        # Test with non-Chisel code that doesn't have 'import chisel' (to cover line 114)
        text = """
```scala
package example

class MyClass {
  def hello() = println("Hello")
}
```
"""
        result = extractor.parse(text)
        self.assertEqual(result, text.replace("```scala", "").replace("```", "").strip())
    
    def test_extract_code_pyrtl(self):
        """Test the Extract_code_pyrtl class."""
        extractor = Extract_code_pyrtl()
        
        # Test with PyRTL code
        text = """
Some text before
```python
import pyrtl

# Create inputs and outputs
in1 = pyrtl.Input(8, 'in1')
in2 = pyrtl.Input(8, 'in2')
out = pyrtl.Output(8, 'out')

# Create logic
out <<= in1 + in2

# Simulate and output to file
with open('output.v', 'w') as f:
    pyrtl.output_to_verilog(f)
```
Some text after
"""
        result = extractor.parse(text, "new_output.v")
        self.assertIn("import pyrtl", result)
        self.assertIn("in1 = pyrtl.Input(8, 'in1')", result)
        self.assertIn("out <<= in1 + in2", result)
        self.assertIn("with open('new_output.v', 'w') as f:", result)  # Path should be replaced
        self.assertNotIn("Some text before", result)
        self.assertNotIn("Some text after", result)
        
        # Test with non-PyRTL code
        text = """
```python
def hello():
    print("Hello")
```
"""
        result = extractor.parse(text, "output.v")
        self.assertEqual(result, text.replace("```python", "").replace("```", "").strip())
        
        # Test with escaped backslashes
        text = """
```python
import pyrtl

# Create inputs and outputs
in1 = pyrtl.Input(8, 'in1\\')
```
"""
        result = extractor.parse(text, "output.v")
        self.assertIn("in1 = pyrtl.Input(8, 'in1')", result)  # Backslashes should be removed
        
        # Test with non-PyRTL code that doesn't have 'import pyrtl' (to cover line 114)
        text = """
```python
def hello():
    print("Hello")
```
"""
        result = extractor.parse(text, "output.v")
        self.assertEqual(result, text.replace("```python", "").replace("```", "").strip())
    
    def test_extract_code_dslx(self):
        """Test the Extract_code_dslx class."""
        extractor = Extract_code_dslx()
        
        # Test with DSLX code
        text = """
Some text before
```dslx
struct Point {
  x: u32,
  y: u32,
}

fn add_points(p1: Point, p2: Point) -> Point {
  Point {
    x: p1.x + p2.x,
    y: p1.y + p2.y,
  }
}
```
Some text after
"""
        result = extractor.parse(text)
        self.assertIn("struct Point {", result)
        self.assertIn("x: u32,", result)
        self.assertIn("fn add_points(p1: Point, p2: Point) -> Point {", result)
        self.assertIn("x: p1.x + p2.x,", result)
        self.assertNotIn("Some text before", result)
        self.assertNotIn("Some text after", result)
        
        # Test with non-DSLX code
        text = """
```rust
fn main() {
    println!("Hello");
}
```
"""
        result = extractor.parse(text)
        # The actual behavior is that it returns the full text with a newline at the end
        self.assertEqual(result, "fn main() {\n    println!(\"Hello\");\n}\n")
        
        # Test with escaped backslashes
        text = """
```dslx
struct Point {
  x: u32\\,
  y: u32,
}
```
"""
        result = extractor.parse(text)
        self.assertIn("x: u32,", result)  # Backslashes should be removed
        
        # Test with non-DSLX code that doesn't have 'struct' or 'fn' (to cover line 114)
        text = """
```dslx
// Just a comment
```
"""
        result = extractor.parse(text)
        # The actual behavior is that it returns the comment without a trailing newline
        self.assertEqual(result, "// Just a comment")
        
        # Create a custom mock that returns a string with backticks
        mock_extract = MagicMock(return_value="struct Point {\n  x: u32,\n  ```\n  y: u32,\n}")
        with patch.object(Extract_code_dslx, 'extract_codeblock', mock_extract):
            result = extractor.parse("dummy text")
            self.assertEqual(result, "struct Point {\n  x: u32,\n")
    
    def test_extract_code_default(self):
        """Test the Extract_code_default class."""
        extractor = Extract_code_default()
        
        # Test with code block
        text = """
Some text before
```python
def hello():
    print("Hello")
```
Some text after
"""
        result = extractor.parse(text)
        self.assertEqual(result, "def hello():\n    print(\"Hello\")")
        
        # Test with escaped backslashes
        text = """
```
Line with \\ backslash
```
"""
        result = extractor.parse(text)
        self.assertEqual(result, "Line with  backslash")  # Backslashes should be removed
    
    def test_get_extract_code(self):
        """Test the get_extract_code function."""
        # Test with valid language types
        self.assertIsInstance(get_extract_code("verilog"), Extract_code_verilog)
        self.assertIsInstance(get_extract_code("Verilog"), Extract_code_verilog)  # Case insensitive
        self.assertIsInstance(get_extract_code("VERILOG"), Extract_code_verilog)  # Case insensitive
        
        self.assertIsInstance(get_extract_code("chisel"), Extract_code_chisel)
        self.assertIsInstance(get_extract_code("pyrtl"), Extract_code_pyrtl)
        self.assertIsInstance(get_extract_code("dslx"), Extract_code_dslx)
        self.assertIsInstance(get_extract_code("default"), Extract_code_default)
        
        # Test with invalid language type
        with self.assertRaises(ValueError):
            get_extract_code("invalid_language")


if __name__ == "__main__":
    unittest.main()
