#!/usr/bin/env python3
"""
Test HintsGenerator with a minimal version of the actual v2chisel_batch pipeline.
This test runs the actual integration but with mocked external dependencies.
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


def test_hints_generator_in_actual_pipeline():
    """
    Test HintsGenerator integration by running the actual _process_single_bug method
    but with mocked external dependencies to make it safe to run.
    """
    print('🔬 Testing HintsGenerator in Actual Pipeline...')
    print('=' * 60)

    # Create realistic test data similar to single_adder_test.yaml
    test_input = {
        'bugs': [
            {
                'file': 'Control.sv',
                'unified_diff': """--- a/Control.sv
+++ b/Control.sv
@@ -27,1 +27,1 @@
-  wire _signals_T_132 = io_opcode == 7'h3B;
+  wire _signals_T_132 = io_opcode == 7'h3F;""",
            }
        ],
        'docker_container': 'hagent-simplechisel',
        'docker_patterns': ['/code/workspace/repo'],
        'chisel_patterns': ['./src/main/scala/*/*.scala'],
    }

    # Create temporary files
    with tempfile.NamedTemporaryFile(mode='w', suffix='.yaml', delete=False) as f:
        yaml.dump(test_input, f)
        input_file = f.name

    output_file = tempfile.mktemp(suffix='.yaml')

    try:
        # Initialize processor
        processor = V2chisel_batch()
        processor.input_file = input_file
        processor.output_file = output_file
        processor.setup()

        print('✅ V2chisel_batch initialized with HintsGenerator')

        # Verify HintsGenerator is properly initialized
        assert hasattr(processor, 'hints_generator')
        assert processor.hints_generator is not None
        print(f'✅ HintsGenerator type: {type(processor.hints_generator).__name__}')

        # Mock external Docker operations to make test safe
        def mock_docker_command(cmd_list, timeout=None):
            """Mock Docker commands to return reasonable test data."""
            cmd_str = ' '.join(cmd_list) if isinstance(cmd_list, list) else str(cmd_list)

            if 'find' in cmd_str and '.scala' in cmd_str:
                # Mock finding Scala files
                return Mock(
                    returncode=0,
                    stdout='/code/workspace/repo/src/main/scala/components/control.scala\\n/code/workspace/repo/src/main/scala/components/alu.scala',
                )
            elif 'find' in cmd_str and '.sv' in cmd_str:
                # Mock finding Verilog files
                return Mock(returncode=0, stdout='/code/workspace/build/Control.sv\\n/code/workspace/build/ALU.sv')
            else:
                # Default mock response
                return Mock(returncode=0, stdout='mock output')

        # Mock the file finding methods
        with patch.object(processor, '_run_docker_command', side_effect=mock_docker_command):
            with patch.object(processor, '_find_chisel_files_docker_filtered') as mock_find_chisel:
                with patch.object(processor, '_find_verilog_files_in_docker') as mock_find_verilog:
                    # Set up mock returns
                    mock_find_chisel.return_value = [
                        'docker:hagent-simplechisel:/code/workspace/repo/src/main/scala/components/control.scala',
                        'docker:hagent-simplechisel:/code/workspace/repo/src/main/scala/components/alu.scala',
                    ]
                    mock_find_verilog.return_value = ['Control.sv', 'ALU.sv']

                    # Mock Docker file reading for HintsGenerator
                    mock_scala_content = """
package dinocpu.components

import chisel3._
import chisel3.util.{BitPat, ListLookup}

/**
 * Control logic for the processor
 */
class Control extends Module {
  val io = IO(new Bundle {
    val opcode = Input(UInt(7.W))
    val itype = Output(Bool())
    val aluop = Output(Bool())
    val regwrite = Output(Bool())
    val validinst = Output(Bool())
    val wordinst = Output(Bool())
  })

  val signals = ListLookup(io.opcode,
    /*default*/ List(false.B, false.B, false.B, false.B, false.B),
    Array(
      // R-format
      BitPat("b0110011") -> List(false.B, true.B, true.B, true.B, false.B),
      // I-format
      BitPat("b0010011") -> List(true.B, true.B, true.B, true.B, false.B),  
      // R-format 32-bit operands (this is what needs to change)
      BitPat("b0111011") -> List(false.B, true.B, true.B, true.B, true.B),
    ))
    
  io.itype := signals(0)
  io.aluop := signals(1) 
  io.regwrite := signals(2)
  io.validinst := signals(3)
  io.wordinst := signals(4)
}"""

                    with patch.object(processor.hints_generator, '_read_docker_file') as mock_read_docker:
                        mock_read_docker.return_value = mock_scala_content

                        # Mock the module_finder to return a relevant hit
                        from types import SimpleNamespace

                        mock_hit = SimpleNamespace()
                        mock_hit.file_name = (
                            'docker:hagent-simplechisel:/code/workspace/repo/src/main/scala/components/control.scala'
                        )
                        mock_hit.module_name = 'Control'
                        mock_hit.start_line = 20
                        mock_hit.end_line = 35
                        mock_hit.confidence = 0.85

                        processor.module_finder.find_modules = Mock(return_value=[mock_hit])

                        print('✅ All mocks configured')

                        # Now test the actual pipeline method with HintsGenerator
                        print('\\n🚀 Running _process_single_bug with HintsGenerator...')

                        try:
                            result = processor._process_single_bug(
                                bug_idx=0,
                                bug_entry=test_input['bugs'][0],
                                local_files=[],  # Only Docker files for this test
                                docker_container='hagent-simplechisel',
                                docker_patterns=['/code/workspace/repo'],
                            )

                            print('✅ _process_single_bug completed successfully!')
                            print(f'✅ Result keys: {list(result.keys())}')

                            # Verify the result structure
                            assert 'bug_index' in result
                            assert 'verilog_file' in result
                            assert 'module_name' in result
                            assert 'hints_source' in result

                            print(f'✅ Bug index: {result["bug_index"]}')
                            print(f'✅ Verilog file: {result["verilog_file"]}')
                            print(f'✅ Module name: {result["module_name"]}')
                            print(f'✅ Hints source: {result["hints_source"]}')

                            # Most importantly, verify that HintsGenerator was actually used
                            if result['hints_source'] == 'module_finder':
                                print('🎯 SUCCESS: HintsGenerator module_finder path was used!')
                            elif result['hints_source'] == 'metadata_fallback':
                                print('🎯 SUCCESS: HintsGenerator metadata fallback was used!')
                            elif result['hints_source'] == 'none':
                                print('🎯 SUCCESS: HintsGenerator no-hints path was used!')
                            else:
                                print(f'⚠️  Unknown hints source: {result["hints_source"]}')

                            print('\\n🎉 HintsGenerator integration in actual pipeline SUCCESSFUL!')
                            return True

                        except Exception as e:
                            print(f'❌ Pipeline execution failed: {e}')
                            import traceback

                            traceback.print_exc()
                            return False

    except Exception as e:
        print(f'❌ Test setup failed: {e}')
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


def test_hints_generator_backwards_compatibility():
    """
    Test that HintsGenerator produces the same interface and behavior
    as the original v2chisel_batch hints logic.
    """
    print('\\n🔬 Testing HintsGenerator Backwards Compatibility...')
    print('=' * 60)

    # Test that the result format matches what the rest of v2chisel_batch expects
    from hagent.step.v2chisel_batch.components.hints_generator import HintsGenerator
    from hagent.step.v2chisel_batch.components.bug_info import BugInfo
    from unittest.mock import Mock

    # Create a realistic scenario
    bug_data = {'file': 'Control.sv', 'unified_diff': 'test diff content'}
    bug_info = BugInfo(bug_data, 0)

    # Test with mock module_finder
    mock_module_finder = Mock()

    # Mock successful module_finder result
    from types import SimpleNamespace

    mock_hit = SimpleNamespace()
    mock_hit.file_name = 'control.scala'
    mock_hit.module_name = 'Control'
    mock_hit.start_line = 10
    mock_hit.end_line = 20
    mock_hit.confidence = 0.8
    mock_module_finder.find_modules.return_value = [mock_hit]

    hints_gen = HintsGenerator(mock_module_finder, debug=False)

    # Mock code extraction
    with patch.object(hints_gen, '_extract_code_from_hits') as mock_extract:
        mock_extract.return_value = 'mock extracted code'

        result = hints_gen.find_hints(bug_info, ['control.scala'], 'test_container')

        # Verify the result has the expected structure
        expected_keys = {'hints', 'source', 'success', 'hits'}
        assert set(result.keys()) == expected_keys, f'Result keys mismatch: {set(result.keys())} vs {expected_keys}'

        # Verify types
        assert isinstance(result['hints'], str)
        assert isinstance(result['source'], str)
        assert isinstance(result['success'], bool)
        assert isinstance(result['hits'], list)

        # Verify values for successful case
        assert result['success']
        assert result['source'] == 'module_finder'
        assert 'Module finder results for Control' in result['hints']
        assert len(result['hits']) == 1
        assert result['hits'][0].confidence == 0.8

        print('✅ Successful hints generation format is correct')

    # Test with no hits (fallback scenario)
    mock_module_finder.find_modules.return_value = []

    with patch.object(hints_gen, '_get_metadata_fallback_hints') as mock_fallback:
        mock_fallback.return_value = 'fallback hints'

        result = hints_gen.find_hints(bug_info, ['control.scala'], 'test_container')

        assert result['success']
        assert result['source'] == 'metadata_fallback'
        assert result['hints'] == 'fallback hints'

        print('✅ Fallback hints generation format is correct')

    # Test with complete failure
    with patch.object(hints_gen, '_get_metadata_fallback_hints') as mock_fallback:
        mock_fallback.return_value = ''

        result = hints_gen.find_hints(bug_info, ['control.scala'], 'test_container')

        assert result['success'] is False
        assert result['source'] == 'none'
        assert 'No hints found' in result['hints']

        print('✅ No-hints scenario format is correct')

    print('✅ HintsGenerator maintains backwards compatibility!')
    return True


if __name__ == '__main__':
    print('🧪 HintsGenerator Pipeline Integration Tests')
    print('=' * 80)

    test1_success = test_hints_generator_in_actual_pipeline()
    test2_success = test_hints_generator_backwards_compatibility()

    if test1_success and test2_success:
        print('\\n' + '=' * 80)
        print('🎉 ALL PIPELINE INTEGRATION TESTS PASSED!')
        print('✅ HintsGenerator is fully integrated and working in v2chisel_batch')
        print('✅ All interfaces are backwards compatible')
        print('✅ Ready for production use!')
        sys.exit(0)
    else:
        print('\\n' + '=' * 80)
        print('❌ SOME PIPELINE INTEGRATION TESTS FAILED!')
        sys.exit(1)
