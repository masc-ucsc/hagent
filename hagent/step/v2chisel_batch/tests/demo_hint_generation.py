#!/usr/bin/env python3
"""
Demo test showing how HintsGenerator works with real Verilog diff.

This test demonstrates the complete hint generation workflow:
1. Input: Verilog diff (what changed in the Verilog)
2. Process: HintsGenerator finds relevant Chisel code
3. Output: Chisel hints (what Chisel code needs to be modified)

Usage:
    uv run python hagent/step/v2chisel_batch/tests/demo_hint_generation.py
"""

import os
import sys
import tempfile
from pathlib import Path
from unittest.mock import Mock

# Set environment before importing
# Docker mode enabled via HAGENT_DOCKER

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent.parent))

from hagent.step.v2chisel_batch.components.hints_generator import HintsGenerator
from hagent.step.v2chisel_batch.components.bug_info import BugInfo
from hagent.tool.module_finder import Module_finder


def demo_hint_generation():
    """
    Demonstrate the complete hint generation workflow with a real example.
    """
    print('🔬 DEMO: HintsGenerator Workflow')
    print('=' * 80)

    # Step 1: Real Verilog Diff (what changed in the generated Verilog)
    print('\n📋 STEP 1: Input Verilog Diff')
    print('-' * 40)

    verilog_diff = """--- a/Control.sv
+++ b/Control.sv
@@ -27,1 +27,1 @@
-  wire _signals_T_132 = io_opcode == 7'h3B;
+  wire _signals_T_132 = io_opcode == 7'h3F;"""

    print('Verilog diff shows a change in Control.sv:')
    print(verilog_diff)
    print("\n💡 This means: OpCode 7'h3B was changed to 7'h3F")

    # Step 2: Create BugInfo
    print('\n📋 STEP 2: Create Bug Information')
    print('-' * 40)

    bug_data = {'file': 'Control.sv', 'unified_diff': verilog_diff}

    bug_info = BugInfo(bug_data, 0)
    print(f'Bug file: {bug_info.file_name}')
    print(f'Module name: {bug_info.module_name}')
    print(f'Has diff: {bug_info.has_verilog_diff()}')

    # Step 3: Create realistic Chisel source files
    print('\n📋 STEP 3: Mock Chisel Source Files')
    print('-' * 40)

    # Create temporary Chisel file with realistic Control module
    chisel_content = """package dinocpu.components

import chisel3._
import chisel3.util.{BitPat, ListLookup}

/**
 * Control logic for the processor
 *
 * Input: opcode:        Opcode from instruction
 * Output: itype         True if we're working on an itype instruction
 * Output: aluop         True if inst is of R-type or I-type
 * Output: regwrite      True if writing to the register file
 * Output: validinst     True if the instruction we're decoding is valid
 * Output: wordinst      True if instruction only operates on 32-bit operands
 */
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
      // R-format 32-bit operands (THIS IS WHAT NEEDS TO CHANGE!)
      BitPat("b0111011") -> List(false.B,  true.B,   true.B,    true.B,   true.B),
      ) // Array
    ) // ListLookup

  io.itype        := signals(0)
  io.aluop        := signals(1)
  io.regwrite     := signals(2)
  io.validinst    := signals(3)
  io.wordinst     := signals(4)
}"""

    # Create temporary file
    with tempfile.NamedTemporaryFile(mode='w', suffix='.scala', delete=False) as f:
        f.write(chisel_content)
        chisel_file = f.name

    print(f'Created temporary Chisel file: {chisel_file}')
    print('File contains Control module with BitPat definitions')

    try:
        # Step 4: Set up HintsGenerator with mock module_finder that finds our code
        print('\n📋 STEP 4: Configure HintsGenerator')
        print('-' * 40)

        # Create mock module_finder that returns a hit pointing to our realistic code
        mock_module_finder = Mock()

        # Create a mock hit that points to our temporary file
        from types import SimpleNamespace

        mock_hit = SimpleNamespace()
        mock_hit.file_name = chisel_file
        mock_hit.module_name = 'Control'
        mock_hit.start_line = 35  # Around the BitPat section
        mock_hit.end_line = 42  # Cover the relevant BitPat lines
        mock_hit.confidence = 0.9

        mock_module_finder.find_modules.return_value = [mock_hit]

        # Create HintsGenerator
        hints_gen = HintsGenerator(mock_module_finder, debug=True)

        print('✅ HintsGenerator created with mock module_finder')
        print(f'✅ Mock hit will return lines {mock_hit.start_line}-{mock_hit.end_line} from Control module')

        # Step 5: Generate hints!
        print('\n📋 STEP 5: Generate Hints')
        print('-' * 40)

        print('🚀 Running HintsGenerator.find_hints()...')
        print('   Input: verilog_diff =', repr(verilog_diff[:50] + '...'))
        print('   Input: chisel_files =', [chisel_file])
        print('   Input: module_name =', bug_info.module_name)

        result = hints_gen.find_hints(bug_info, [chisel_file], 'demo_container')

        # Step 6: Show the results!
        print('\n🎯 STEP 6: Hint Generation Results')
        print('=' * 80)

        print(f'✅ Success: {result["success"]}')
        print(f'✅ Source: {result["source"]}')
        print(f'✅ Number of hits: {len(result["hits"])}')

        if result['hits']:
            hit = result['hits'][0]
            print(f'✅ Hit confidence: {hit.confidence}')
            print(f'✅ Hit file: {hit.file_name}')
            print(f'✅ Hit lines: {hit.start_line}-{hit.end_line}')

        print('\n📝 GENERATED CHISEL HINTS:')
        print('=' * 80)
        print(result['hints'])
        print('=' * 80)

        # Step 7: Explain what the hints mean
        print('\n💡 STEP 7: What These Hints Mean')
        print('-' * 40)

        print('The hints show you:')
        print('1. 🎯 Which Chisel file contains the relevant code')
        print('2. 📍 Which lines in that file need to be modified')
        print('3. 🔍 The actual Chisel code that generates the Verilog')
        print('4. 💭 Context around the code to understand the structure')

        print('\nIn this example:')
        print("- Verilog change: 7'h3B → 7'h3F")
        print('- Chisel location: BitPat definitions in Control module')
        print('- Likely fix: Change BitPat("b0111011") to BitPat("b0111111")')
        print("  (because 7'h3B = 59 = b0111011, 7'h3F = 63 = b0111111)")

        print('\n🎉 DEMO COMPLETE!')
        print('This shows how HintsGenerator takes a Verilog diff and finds')
        print('the corresponding Chisel code that needs to be modified.')

        return True

    finally:
        # Cleanup
        try:
            os.unlink(chisel_file)
        except OSError:
            pass


def demo_with_real_module_finder():
    """
    Demo with the actual Module_finder (requires more setup but shows real behavior).
    """
    print('\n\n🔬 BONUS DEMO: With Real Module_finder')
    print('=' * 80)

    try:
        # Create real Module_finder
        real_module_finder = Module_finder()

        # Create HintsGenerator with real module_finder
        hints_gen = HintsGenerator(real_module_finder, debug=True)

        print('✅ Created HintsGenerator with real Module_finder')

        # Create simple test case
        verilog_diff = """--- a/SimpleModule.sv
+++ b/SimpleModule.sv
@@ -1,3 +1,3 @@
 module SimpleModule();
-  wire test = 1'b0;
+  wire test = 1'b1;
 endmodule"""

        bug_data = {'file': 'SimpleModule.sv', 'unified_diff': verilog_diff}
        bug_info = BugInfo(bug_data, 0)

        # This would normally find real Scala files, but we'll use empty list for demo
        result = hints_gen.find_hints(bug_info, [], 'demo_container')

        print('✅ Real module_finder result:')
        print(f'   Success: {result["success"]}')
        print(f'   Source: {result["source"]}')
        print(f'   Hits: {len(result["hits"])}')

        if result['source'] == 'none':
            print('💡 No hits found (expected - no real Scala files provided)')

    except Exception as e:
        print(f'⚠️  Real module_finder demo failed (expected): {e}')
        print('💡 This is normal - real module_finder needs actual Chisel files')


if __name__ == '__main__':
    print('🎯 HintsGenerator Demo - See How Hint Generation Works!')
    print('=' * 80)
    print('This demo shows the complete workflow:')
    print('  Verilog Diff → HintsGenerator → Chisel Hints')
    print()

    success = demo_hint_generation()

    if success:
        demo_with_real_module_finder()
        print('\n' + '=' * 80)
        print('✅ Demo completed successfully!')
        print("🎓 You've seen how HintsGenerator transforms Verilog changes")
        print('   into actionable Chisel code hints!')
    else:
        print('❌ Demo failed')
        sys.exit(1)
