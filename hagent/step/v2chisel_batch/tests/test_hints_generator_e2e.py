#!/usr/bin/env python3
"""
End-to-end integration tests for HintsGenerator with V2chisel_batch.
Tests the full pipeline without requiring actual Docker containers.
"""

import os
import sys
import tempfile
import yaml
from pathlib import Path
from unittest.mock import Mock, patch

# Set environment before importing
os.environ['HAGENT_EXECUTION_MODE'] = 'docker'

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent.parent))

from hagent.step.v2chisel_batch.v2chisel_batch import V2chisel_batch
from hagent.step.v2chisel_batch.components.hints_generator import HintsGenerator
from hagent.step.v2chisel_batch.components.bug_info import BugInfo


class MockModuleFinder:
    """Mock module_finder for testing."""

    def __init__(self, return_hits=True):
        self.return_hits = return_hits

    def find_modules(self, scala_files, verilog_module, verilog_diff):
        if self.return_hits:
            # Return a mock hit with good confidence
            from types import SimpleNamespace

            hit = SimpleNamespace()
            hit.file_name = f'test_{verilog_module.lower()}.scala'
            hit.module_name = verilog_module
            hit.start_line = 10
            hit.end_line = 25
            hit.confidence = 0.85
            return [hit]
        else:
            return []


def test_hints_generator_integration_with_v2chisel_batch():
    """Test HintsGenerator integration with full V2chisel_batch setup."""
    print('🔬 Testing HintsGenerator E2E Integration...')

    # Create realistic test data
    test_bugs = [
        {
            'file': 'Control.sv',
            'unified_diff': """--- a/Control.sv
+++ b/Control.sv
@@ -27,1 +27,1 @@
-  wire _signals_T_132 = io_opcode == 7'h3B;
+  wire _signals_T_132 = io_opcode == 7'h3F;""",
        },
        {
            'file': 'ALU.sv',
            'unified_diff': """--- a/ALU.sv
+++ b/ALU.sv
@@ -15,2 +15,2 @@
-  wire [31:0] result = a + b;
+  wire [31:0] result = a - b;""",
        },
    ]

    input_data = {
        'bugs': test_bugs,
        'docker_container': 'test_container',
        'docker_patterns': ['/code/workspace/repo'],
        'chisel_patterns': ['./src/*.scala'],
    }

    # Create temporary files
    with tempfile.NamedTemporaryFile(mode='w', suffix='.yaml', delete=False) as f:
        yaml.dump(input_data, f)
        input_file = f.name

    output_file = tempfile.mktemp(suffix='.yaml')

    try:
        # Test 1: Initialize V2chisel_batch with HintsGenerator
        processor = V2chisel_batch()
        processor.input_file = input_file
        processor.output_file = output_file

        # Mock the module_finder to avoid external dependencies
        mock_module_finder = MockModuleFinder(return_hits=True)

        # Setup processor
        processor.setup()

        # Replace the module_finder with our mock
        processor.module_finder = mock_module_finder
        processor.hints_generator = HintsGenerator(mock_module_finder, debug=True)

        print('✅ V2chisel_batch setup with mocked module_finder')

        # Test 2: Process the first bug using HintsGenerator
        bug_entry = test_bugs[0]
        bug_info = BugInfo(bug_entry, 0)

        # Mock the file finding methods to return test files
        test_files = ['control.scala', 'docker:test_container:/code/workspace/repo/components/control.scala']

        # Mock Docker operations
        with patch.object(processor.hints_generator, '_read_docker_file') as mock_read_docker:
            mock_read_docker.return_value = """
package dinocpu.components

import chisel3._
import chisel3.util.{BitPat, ListLookup}

class Control extends Module {
  val io = IO(new Bundle {
    val opcode = Input(UInt(7.W))
    // ... rest of Control module
  })
  
  val signals = ListLookup(io.opcode,
    /*default*/ List(false.B, false.B, false.B),
    Array(
      BitPat("b0111011") -> List(false.B, true.B, false.B)
    ))
}"""

            # Test hints generation
            hints_result = processor.hints_generator.find_hints(bug_info, test_files, 'test_container')

            print(f'✅ Hints generated - Source: {hints_result["source"]}')
            print(f'✅ Hints success: {hints_result["success"]}')

            assert hints_result['success']
            assert hints_result['source'] == 'module_finder'
            assert 'Control' in hints_result['hints']
            assert len(hints_result['hits']) > 0
            assert hints_result['hits'][0].confidence >= 0.5

        print('✅ HintsGenerator successfully processed Control module')

        # Test 3: Test with second bug (ALU)
        bug_entry_2 = test_bugs[1]
        bug_info_2 = BugInfo(bug_entry_2, 1)

        alu_files = ['alu.scala', 'docker:test_container:/code/workspace/repo/components/alu.scala']

        with patch.object(processor.hints_generator, '_read_docker_file') as mock_read_docker:
            mock_read_docker.return_value = """
package dinocpu.components

import chisel3._

class ALU extends Module {
  val io = IO(new Bundle {
    val a = Input(UInt(32.W))
    val b = Input(UInt(32.W))
    val result = Output(UInt(32.W))
  })
  
  io.result := io.a + io.b  // This line should be identified
}"""

            hints_result_2 = processor.hints_generator.find_hints(bug_info_2, alu_files, 'test_container')

            print(f'✅ ALU Hints generated - Source: {hints_result_2["source"]}')

            assert hints_result_2['success']
            assert hints_result_2['source'] == 'module_finder'
            assert 'ALU' in hints_result_2['hints']

        print('✅ HintsGenerator successfully processed ALU module')

        # Test 4: Test fallback mechanism
        mock_module_finder_no_hits = MockModuleFinder(return_hits=False)
        processor.hints_generator.module_finder = mock_module_finder_no_hits

        # Mock metadata fallback
        with patch.object(processor.hints_generator, '_get_metadata_fallback_hints') as mock_fallback:
            mock_fallback.return_value = '// Fallback hints from metadata analysis\\nclass Control extends Module'

            hints_result_fallback = processor.hints_generator.find_hints(bug_info, test_files, 'test_container')

            print(f'✅ Fallback test - Source: {hints_result_fallback["source"]}')

            assert hints_result_fallback['success']
            assert hints_result_fallback['source'] == 'metadata_fallback'
            assert 'Fallback hints' in hints_result_fallback['hints']

        print('✅ HintsGenerator metadata fallback working')

        # Test 5: Test no hints scenario
        with patch.object(processor.hints_generator, '_get_metadata_fallback_hints') as mock_fallback:
            mock_fallback.return_value = ''

            hints_result_none = processor.hints_generator.find_hints(bug_info, test_files, 'test_container')

            print(f'✅ No hints test - Source: {hints_result_none["source"]}')

            assert hints_result_none['success'] is False
            assert hints_result_none['source'] == 'none'
            assert 'No hints found' in hints_result_none['hints']

        print('✅ HintsGenerator no-hints scenario working')

        print('\\n🎉 All E2E integration tests passed!')
        print('✅ HintsGenerator is fully integrated with V2chisel_batch')
        print('✅ All code paths tested: module_finder success, fallback, and failure')

        return True

    except Exception as e:
        print(f'❌ E2E integration test failed: {e}')
        import traceback

        traceback.print_exc()
        return False

    finally:
        # Cleanup
        try:
            os.unlink(input_file)
            os.unlink(output_file)
        except OSError:
            pass


def test_hints_generator_with_real_file_operations():
    """Test HintsGenerator with actual file operations (no Docker)."""
    print('\\n🔬 Testing HintsGenerator with Real File Operations...')

    # Create temporary Scala file
    scala_content = """
package dinocpu.components

import chisel3._
import chisel3.util.{BitPat, ListLookup}

class Control extends Module {
  val io = IO(new Bundle {
    val opcode = Input(UInt(7.W))
    val itype = Output(Bool())
    val aluop = Output(Bool())
  })

  val signals = ListLookup(io.opcode,
    /*default*/ List(false.B, false.B),
    Array(
      BitPat("b0110011") -> List(false.B, true.B),   // R-format
      BitPat("b0010011") -> List(true.B, true.B),    // I-format  
      BitPat("b0111011") -> List(false.B, true.B),   // R-format 32-bit
    ))
    
  io.itype := signals(0)
  io.aluop := signals(1)
}
"""

    with tempfile.NamedTemporaryFile(mode='w', suffix='.scala', delete=False) as f:
        f.write(scala_content)
        scala_file = f.name

    try:
        # Create bug info
        bug_data = {
            'file': 'Control.sv',
            'unified_diff': """--- a/Control.sv
+++ b/Control.sv
@@ -27,1 +27,1 @@
-  wire _signals_T_132 = io_opcode == 7'h3B;
+  wire _signals_T_132 = io_opcode == 7'h3F;""",
        }
        bug_info = BugInfo(bug_data, 0)

        # Mock module_finder to return a hit pointing to our real file
        mock_module_finder = Mock()

        from types import SimpleNamespace

        hit = SimpleNamespace()
        hit.file_name = scala_file
        hit.module_name = 'Control'
        hit.start_line = 14
        hit.end_line = 25
        hit.confidence = 0.9
        mock_module_finder.find_modules.return_value = [hit]

        # Create HintsGenerator
        hints_gen = HintsGenerator(mock_module_finder, debug=True)

        # Test with real file
        result = hints_gen.find_hints(bug_info, [scala_file], 'dummy_container')

        print(f'✅ Real file test - Source: {result["source"]}')
        print(f'✅ Real file test - Success: {result["success"]}')

        assert result['success']
        assert result['source'] == 'module_finder'
        assert 'Control (confidence: 0.90)' in result['hints']
        assert 'ListLookup' in result['hints']  # Should contain actual file content
        assert 'BitPat' in result['hints']

        print('✅ HintsGenerator successfully extracted real file content')

    finally:
        os.unlink(scala_file)

    return True


if __name__ == '__main__':
    success1 = test_hints_generator_integration_with_v2chisel_batch()
    success2 = test_hints_generator_with_real_file_operations()

    if success1 and success2:
        print('\\n🎉 ALL E2E TESTS PASSED!')
        sys.exit(0)
    else:
        print('\\n❌ SOME E2E TESTS FAILED!')
        sys.exit(1)
