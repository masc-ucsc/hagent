#!/usr/bin/env python3
"""
Interactive Hints Generator Test Tool

This tool allows you to input a verilog_diff (directly or from file) and get Chisel hints output.
Perfect for testing and demonstrating how hint generation works with your own data.

Usage:
    # Interactive mode - enter diff directly
    uv run python hagent/step/v2chisel_batch/tests/interactive_hints_test.py

    # File mode - read diff from file
    uv run python hagent/step/v2chisel_batch/tests/interactive_hints_test.py --file path/to/diff.txt

    # Example with inline diff
    uv run python hagent/step/v2chisel_batch/tests/interactive_hints_test.py --diff "--- a/Control.sv
+++ b/Control.sv
@@ -27,1 +27,1 @@
-  wire _signals_T_132 = io_opcode == 7'h3B;
+  wire _signals_T_132 = io_opcode == 7'h3F;"
"""

import os
import sys
import argparse
import tempfile
from pathlib import Path
from unittest.mock import Mock
from types import SimpleNamespace

# Set environment before importing
os.environ['HAGENT_EXECUTION_MODE'] = 'docker'

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent.parent))

from hagent.step.v2chisel_batch.components.hints_generator import HintsGenerator
from hagent.step.v2chisel_batch.components.bug_info import BugInfo
from hagent.tool.module_finder import Module_finder


def create_mock_chisel_files():
    """Create realistic Chisel files for testing"""
    
    # Control module with BitPat definitions
    control_content = '''package dinocpu.components

import chisel3._
import chisel3.util.{BitPat, ListLookup}

class Control extends Module {
  val io = IO(new Bundle {
    val opcode = Input(UInt(7.W))
    val itype        = Output(Bool())
    val aluop        = Output(Bool())
    val regwrite     = Output(Bool())
    val validinst    = Output(Bool())
    val wordinst     = Output(Bool())
  })

  val signals = ListLookup(io.opcode,
    /*default*/           List(false.B, false.B, false.B, false.B, false.B),
    Array(              /*       itype,   aluop, regwrite, validinst, wordinst */
      // R-format
      BitPat("b0110011") -> List(false.B,  true.B,   true.B,    true.B,  false.B),
      // I-format
      BitPat("b0010011") -> List( true.B,  true.B,   true.B,    true.B,  false.B),
      // load
      BitPat("b0000011") -> List(false.B, false.B,   true.B,    true.B,  false.B),
      // R-format 32-bit operands (LIKELY NEEDS TO CHANGE!)
      BitPat("b0111011") -> List(false.B,  true.B,   true.B,    true.B,   true.B),
      ) // Array
    ) // ListLookup

  io.itype        := signals(0)
  io.aluop        := signals(1)
  io.regwrite     := signals(2)
  io.validinst    := signals(3)
  io.wordinst     := signals(4)
}'''
    
    # ALU module with different patterns
    alu_content = '''package dinocpu.components

import chisel3._
import chisel3.util._

class ALU extends Module {
  val io = IO(new Bundle {
    val operation   = Input(UInt(4.W))
    val inputx      = Input(UInt(64.W))
    val inputy      = Input(UInt(64.W))
    val result      = Output(UInt(64.W))
  })

  switch (io.operation) {
    is (0.U) { io.result := io.inputx & io.inputy }        // AND
    is (1.U) { io.result := io.inputx | io.inputy }        // OR
    is (2.U) { io.result := io.inputx + io.inputy }        // ADD
    is (6.U) { io.result := io.inputx - io.inputy }        // SUB
    is (7.U) { io.result := io.inputx < io.inputy }        // SLT
    is (12.U) { io.result := ~(io.inputx | io.inputy) }    // NOR
  }
}'''
    
    # Create temp files
    temp_files = []
    
    for name, content in [('Control.scala', control_content), ('ALU.scala', alu_content)]:
        temp_fd, temp_path = tempfile.mkstemp(suffix='.scala', prefix=f'{name[:-6]}_')
        with os.fdopen(temp_fd, 'w') as f:
            f.write(content)
        temp_files.append(temp_path)
    
    return temp_files


def create_mock_module_finder_with_hits(chisel_files, verilog_module):
    """Create a mock module_finder that returns hits for our test files"""
    mock_module_finder = Mock()
    
    # Create hits that point to our test files
    mock_hits = []
    
    for i, file_path in enumerate(chisel_files):
        if 'Control' in file_path and verilog_module.lower() in ['control', 'ctrl']:
            # High confidence hit for Control module
            mock_hit = SimpleNamespace()
            mock_hit.file_name = file_path
            mock_hit.module_name = 'Control'
            mock_hit.start_line = 18  # Around the BitPat section
            mock_hit.end_line = 28    # Cover the relevant BitPat lines
            mock_hit.confidence = 0.95
            mock_hits.append(mock_hit)
            
        elif 'ALU' in file_path and verilog_module.lower() in ['alu', 'arithmetic']:
            # Medium confidence hit for ALU module
            mock_hit = SimpleNamespace()
            mock_hit.file_name = file_path
            mock_hit.module_name = 'ALU'
            mock_hit.start_line = 12  # Around the switch statement
            mock_hit.end_line = 22    # Cover the operations
            mock_hit.confidence = 0.80
            mock_hits.append(mock_hit)
    
    # If no specific matches, create a generic hit
    if not mock_hits and chisel_files:
        mock_hit = SimpleNamespace()
        mock_hit.file_name = chisel_files[0]
        mock_hit.module_name = verilog_module
        mock_hit.start_line = 5
        mock_hit.end_line = 15
        mock_hit.confidence = 0.60
        mock_hits.append(mock_hit)
    
    mock_module_finder.find_modules.return_value = mock_hits
    return mock_module_finder


def parse_verilog_diff(diff_text):
    """Parse verilog diff to extract file name and create BugInfo"""
    lines = diff_text.strip().split('\n')
    
    # Find the file name from diff header
    file_name = 'Unknown.sv'
    for line in lines:
        if line.startswith('--- a/') or line.startswith('+++ b/'):
            potential_file = line.split('/')[-1]
            if potential_file.endswith('.sv') or potential_file.endswith('.v'):
                file_name = potential_file
                break
    
    # Create bug data
    bug_data = {
        'file': file_name,
        'unified_diff': diff_text
    }
    
    return BugInfo(bug_data, 0)


def run_hints_generation(verilog_diff, use_real_module_finder=False):
    """Run hints generation with the given verilog diff"""
    
    print("🔬 INTERACTIVE HINTS GENERATOR TEST")
    print("=" * 80)
    
    # Step 1: Parse the verilog diff
    print("\n📋 STEP 1: Parsing Verilog Diff")
    print("-" * 40)
    
    bug_info = parse_verilog_diff(verilog_diff)
    print(f"✅ File: {bug_info.file_name}")
    print(f"✅ Module: {bug_info.module_name}")
    print(f"✅ Has diff: {bug_info.has_verilog_diff()}")
    
    print(f"\nVerilog diff preview:")
    print(verilog_diff[:200] + ("..." if len(verilog_diff) > 200 else ""))
    
    # Step 2: Create test files and module_finder
    print(f"\n📋 STEP 2: Setting up HintsGenerator")
    print("-" * 40)
    
    chisel_files = []
    temp_files = []
    
    try:
        if use_real_module_finder:
            print("Using real Module_finder (requires actual Chisel files)")
            try:
                real_module_finder = Module_finder()
                hints_gen = HintsGenerator(real_module_finder, debug=True)
            except Exception as e:
                print(f"❌ Failed to create real Module_finder: {e}")
                print("🔄 Falling back to mock module_finder...")
                use_real_module_finder = False
        
        if not use_real_module_finder:
            # Create mock Chisel files
            temp_files = create_mock_chisel_files()
            chisel_files = temp_files
            
            # Create mock module_finder with hits
            mock_module_finder = create_mock_module_finder_with_hits(chisel_files, bug_info.module_name or 'Unknown')
            hints_gen = HintsGenerator(mock_module_finder, debug=True)
            
            print(f"✅ Created {len(chisel_files)} mock Chisel files")
            print(f"✅ Created mock module_finder with targeted hits")
        
        # Step 3: Generate hints
        print(f"\n📋 STEP 3: Generating Hints")
        print("-" * 40)
        
        print(f"🚀 Running HintsGenerator.find_hints()...")
        print(f"   Module: {bug_info.module_name}")
        print(f"   Files: {len(chisel_files)} files")
        
        result = hints_gen.find_hints(bug_info, chisel_files, 'test_container')
        
        # Step 4: Show results
        print(f"\n🎯 STEP 4: Results")
        print("=" * 80)
        
        print(f"Success: {result['success']}")
        print(f"Source: {result['source']}")
        print(f"Number of hits: {len(result['hits'])}")
        
        if result['hits']:
            for i, hit in enumerate(result['hits']):
                print(f"  Hit {i+1}: {hit.module_name} (confidence: {hit.confidence:.2f})")
        
        print(f"\n📝 GENERATED CHISEL HINTS:")
        print("=" * 80)
        print(result['hints'])
        print("=" * 80)
        
        # Step 5: Interpretation
        print(f"\n💡 STEP 5: What These Hints Mean")
        print("-" * 40)
        
        if result['success']:
            print("✅ Success! The hints show:")
            print("   🎯 Which Chisel files contain relevant code")
            print("   📍 Which lines in those files might need modification")
            print("   🔍 The actual Chisel code that corresponds to the Verilog")
            print("   💭 Context around the code for better understanding")
        else:
            print("❌ No hints found. This might mean:")
            print("   📁 No relevant Chisel files were found")
            print("   🔍 The module_finder couldn't match the Verilog to Chisel code")
            print("   ⚙️  The diff might be in generated code without clear Chisel mapping")
        
        return result
        
    finally:
        # Cleanup temp files
        for temp_file in temp_files:
            try:
                os.unlink(temp_file)
            except:
                pass


def interactive_mode():
    """Interactive mode - let user enter diff directly"""
    print("🎯 INTERACTIVE HINTS GENERATOR")
    print("=" * 50)
    print("Enter your Verilog diff below.")
    print("You can paste multiple lines, then type 'END' on a new line when done.")
    print()
    print("Example format:")
    print("--- a/Control.sv")
    print("+++ b/Control.sv")
    print("@@ -27,1 +27,1 @@")
    print("-  wire _signals_T_132 = io_opcode == 7'h3B;")
    print("+  wire _signals_T_132 = io_opcode == 7'h3F;")
    print("END")
    print()
    print("Your diff (type 'END' when finished):")
    
    # Read multiple lines until user types END
    diff_lines = []
    while True:
        try:
            line = input()
            if line.strip() == 'END':
                break
            diff_lines.append(line)
        except EOFError:
            # Handle Ctrl+D as well
            break
        except KeyboardInterrupt:
            print("\n❌ Cancelled by user")
            return False
    
    if not diff_lines:
        print("❌ No diff provided!")
        return False
    
    verilog_diff = '\n'.join(diff_lines)
    return run_hints_generation(verilog_diff)


def main():
    parser = argparse.ArgumentParser(
        description="Interactive Hints Generator Test Tool",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Interactive mode
  uv run python hagent/step/v2chisel_batch/tests/interactive_hints_test.py

  # From file
  uv run python hagent/step/v2chisel_batch/tests/interactive_hints_test.py --file my_diff.txt

  # Direct diff
  uv run python hagent/step/v2chisel_batch/tests/interactive_hints_test.py --diff "--- a/Control.sv
+++ b/Control.sv
@@ -1,1 +1,1 @@
-wire test = 1'b0;
+wire test = 1'b1;"

  # Use real module_finder (requires actual Chisel files)
  uv run python hagent/step/v2chisel_batch/tests/interactive_hints_test.py --real
        """
    )
    
    parser.add_argument('--file', '-f', help='Read verilog diff from file')
    parser.add_argument('--diff', '-d', help='Provide verilog diff directly as argument')
    parser.add_argument('--real', action='store_true', help='Use real Module_finder instead of mock')
    
    args = parser.parse_args()
    
    try:
        if args.diff:
            # Direct diff argument
            return run_hints_generation(args.diff, args.real)
        elif args.file:
            # Read from file
            if not os.path.exists(args.file):
                print(f"❌ File not found: {args.file}")
                return False
            
            with open(args.file, 'r') as f:
                verilog_diff = f.read()
            
            if not verilog_diff.strip():
                print(f"❌ File is empty: {args.file}")
                return False
            
            print(f"📁 Reading diff from: {args.file}")
            return run_hints_generation(verilog_diff, args.real)
        else:
            # Interactive mode
            return interactive_mode()
            
    except KeyboardInterrupt:
        print("\n👋 Interrupted by user")
        return False
    except Exception as e:
        print(f"❌ Error: {e}")
        return False


if __name__ == '__main__':
    success = main()
    if success:
        print(f"\n🎉 HINTS GENERATION COMPLETE!")
        print(f"You can now see how your Verilog diff maps to Chisel hints!")
    else:
        print(f"\n❌ HINTS GENERATION FAILED")
        sys.exit(1)