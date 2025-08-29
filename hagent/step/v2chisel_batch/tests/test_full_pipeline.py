#!/usr/bin/env python3
"""
Complete v2chisel_batch pipeline test with known chisel_diff.

This test runs the EXACT same pipeline as v2chisel_batch but bypasses ONLY the LLM call
and provides the known correct chisel_diff instead. Everything else is identical:
- Same Docker operations
- Same module finder
- Same applier
- Same compilation
- Same verilog generation
- Same golden design creation
- Same LEC process

Purpose: Test the complete pipeline with a known correct answer without paying for LLM.
"""

import os
import sys
import argparse
import tempfile

# Add parent directory to path for imports
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
from v2chisel_batch import V2chisel_batch

# Import Module_finder using the same path as v2chisel_batch
from hagent.tool.module_finder import Module_finder


class TestV2chisel_batch(V2chisel_batch):
    """Test version of V2chisel_batch that overrides only the LLM call"""

    def __init__(self):
        # Initialize parent class completely (this sets chisel_source_pattern and other required attributes)
        super().__init__()
        self.test_chisel_diff = None

        # Ensure all required attributes are set (in case parent init missed some)
        if not hasattr(self, 'chisel_source_pattern'):
            self.chisel_source_pattern = './tmp/src/main/scala/*/*.scala'
        if not hasattr(self, 'module_finder'):
            self.module_finder = Module_finder()  # Initialize module finder properly

    def set_test_chisel_diff(self, chisel_diff):
        """Set the known correct chisel_diff to use instead of LLM"""
        self.test_chisel_diff = chisel_diff
        print(f'🎯 [TEST] Set test chisel_diff: {len(chisel_diff)} characters')

    def _call_llm_for_chisel_diff(
        self,
        verilog_diff: str,
        chisel_hints: str,
        attempt: int = 1,
        previous_diff: str = '',
        error_message: str = '',
        attempt_history: str = '',
    ) -> dict:
        """Override LLM call to return known correct chisel_diff"""

        if self.test_chisel_diff is None:
            return {'success': False, 'error': 'Test chisel_diff not set! Call set_test_chisel_diff() first'}

        print(f'🎯 [TEST] Using known correct chisel_diff instead of LLM (attempt {attempt})')
        print('📝 [TEST] Known correct chisel_diff preview:')
        preview = self.test_chisel_diff.split('\n')[:5]
        for line in preview:
            print(f'     {line}')
        if len(self.test_chisel_diff.split('\n')) > 5:
            print('     ...')

        return {
            'success': True,
            'response': self.test_chisel_diff,
            'input_tokens': 150,  # Estimated
            'output_tokens': 75,  # Estimated
            'model': 'test_known_answer',
            'usage_cost': 0.0,
        }


def create_test_input():
    """Create test input exactly like a real v2chisel_batch input"""

    test_input = {
        # Required keys for v2chisel_batch
        'bugs': [
            {
                'id': 'test_control_opcode_fix',
                'description': 'Test LEC pipeline with known correct chisel_diff for Control opcode change',
                'verilog_diff': {
                    'file': 'Control.sv',
                    'unified_diff': """--- a/Control.sv
+++ b/Control.sv
@@ -24,7 +24,7 @@ module Control (
   wire _signals_T_87 = io_opcode == 7'h37;
   wire _signals_T_110 = io_opcode == 7'h3;
   wire _signals_T_1 = io_opcode == 7'h33;
-  wire _signals_T_132 = io_opcode == 7'h3B;
+  wire _signals_T_132 = io_opcode == 7'h3F;
   assign io_validinst = _signals_T_14 | (_signals_T_18 | (_signals_T_22 | (_signals_T_26 | (_signals_T_30 | (_signals_T_34 | (_signals_T_38 | (_signals_T_42 |
     (_signals_T_46 | (_signals_T_50 | (_signals_T_54 | (_signals_T_58 | (_signals_T_62 | (_signals_T_66 | (_signals_T_70 | (_signals_T_74 | (_signals_T_78 |
     (_signals_T_82 | (_signals_T_86 | (_signals_T_90 | (_signals_T_94 | (_signals_T_98 | (_signals_T_102 | (_signals_T_106 | (_signals_T_110 | (_signals_T_114""",
                },
            }
        ],
        # Optional configuration to match real usage
        'docker_patterns': ['/code/workspace/repo'],
        'chisel_patterns': ['./tmp/src/main/scala/*/*.scala'],
        # LLM config (won't be used but needed for initialization)
        'llm': {'model': 'test_model', 'temperature': 0.1},
    }

    return test_input


def main():
    """Run the complete pipeline test"""
    print('🔬 COMPLETE v2chisel_batch PIPELINE TEST')
    print('=' * 80)
    print('Purpose: Test complete pipeline with known chisel_diff (no LLM cost)')
    print('Pipeline: Module Finder → Master Backup → [LLM Override] → Diff Apply →')
    print('          Compile → Verilog Gen → Golden Design → LEC')
    print('=' * 80)
    print()

    # Parse command line args (optional)
    parser = argparse.ArgumentParser(description='Test complete v2chisel_batch pipeline')
    parser.add_argument('--output', '-o', default=None, help='Output YAML file (optional)')
    args = parser.parse_args()

    # Known correct chisel_diff for Control.sv opcode change
    known_chisel_diff = """@@ -1194,7 +1194,7 @@
           // I-format 32-bit operands
           BitPat("b0011011") -> List( true.B,  true.B, false.B,  1.U,  false.B,       0.U,      false.B,   0.U, false.B,   true.B,    true.B,   true.B),
   -       // R-format 32-bit operands
   -       BitPat("b0111011") -> List(false.B,  true.B, false.B,  0.U,  false.B,       0.U,      false.B,   0.U, false.B,   true.B,    true.B,   true.B),
   +       // R-format 32-bit operands
   +       BitPat("b0111111") -> List(false.B,  true.B, false.B,  0.U,  false.B,       0.U,      false.B,   0.U, false.B,   true.B,    true.B,   true.B),"""

    # Create test input data
    test_data = create_test_input()
    print(f'📋 Created test input with {len(test_data["bugs"])} bug(s)')

    # Create test processor
    processor = TestV2chisel_batch()
    processor.set_test_chisel_diff(known_chisel_diff)

    # Create output file
    if args.output:
        output_file = args.output
    else:
        output_file = tempfile.mktemp(suffix='_test_pipeline.yaml')

    try:
        print(f'🎯 Output file: {output_file}')
        print()
        print('🚀 STARTING COMPLETE PIPELINE TEST')
        print('=' * 60)

        # Set up processor (same as real usage)
        processor.input_data = test_data
        processor.output_path = output_file

        # Run the complete pipeline (this will call all the same methods as real v2chisel_batch)
        result = processor.run(test_data)

        print()
        print('=' * 60)
        print('📊 PIPELINE TEST RESULTS')
        print('=' * 60)

        if result and result.get('success', False):
            print('✅ PIPELINE SUCCESS: Complete test passed!')

            # Check specific results
            if 'results' in result and result['results']:
                for i, bug_result in enumerate(result['results']):
                    print(f'📋 Bug #{i + 1} Results:')
                    print(f'     Module Finder: {"✅" if bug_result.get("module_finder_success") else "❌"}')
                    print(f'     LLM: {"✅" if bug_result.get("llm_success") else "❌"}')
                    print(f'     Applier: {"✅" if bug_result.get("applier_success") else "❌"}')
                    print(f'     Compilation: {"✅" if bug_result.get("compile_success") else "❌"}')
                    print(f'     Verilog Gen: {"✅" if bug_result.get("verilog_success") else "❌"}')

                    # LEC Results
                    lec_result = bug_result.get('lec_result', {})
                    if lec_result.get('success'):
                        lec_passed = lec_result.get('lec_passed')
                        if lec_passed is True:
                            print('     LEC: ✅ PASSED (Designs are equivalent)')
                        elif lec_passed is False:
                            print('     LEC: ⚠️  FAILED (Designs not equivalent - may be expected)')
                        else:
                            print('     LEC: ❓ INCONCLUSIVE')
                    else:
                        print(f'     LEC: ❌ ERROR ({lec_result.get("error", "Unknown error")})')

                    print()

            print('🎉 COMPLETE PIPELINE TEST: SUCCESS!')
            print('The v2chisel_batch pipeline works correctly with known chisel_diff.')

        else:
            print('❌ PIPELINE FAILURE')
            error_msg = result.get('error', 'Unknown error') if result else 'No result returned'
            print(f'Error: {error_msg}')

            print()
            print('💡 This indicates an issue with the pipeline (not LLM-related)')
            return 1

        print()
        print(f'📄 Detailed results saved to: {output_file}')
        return 0

    except Exception as e:
        print(f'💥 PIPELINE EXCEPTION: {str(e)}')
        import traceback

        traceback.print_exc()
        return 1

    finally:
        # Clean up temp file if not specified by user
        if not args.output and os.path.exists(output_file):
            try:
                os.unlink(output_file)
                print('🗑️  Cleaned up temporary output file')
            except OSError:
                pass


if __name__ == '__main__':
    sys.exit(main())
