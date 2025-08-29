#!/usr/bin/env python3
"""
Test LEC functionality in isolation using known correct chisel_diff.

This test bypasses the LLM and applies a known correct chisel_diff to test
the full LEC pipeline: diff application → compilation → verilog generation → LEC.

Test case:
- Input verilog_diff: Changes Control.sv line from 7'h3B to 7'h3F
- Known correct chisel_diff: Changes Control.scala line from "b0111011" to "b0111111"
- Expected result: LEC should pass with equivalent designs
"""

import os
import sys
import tempfile

# Add parent directories to path for imports
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
from v2chisel_batch import V2chisel_batch


def create_test_input():
    """Create test input with known verilog_diff and correct chisel_diff"""
    return {
        'id': 'test_lec_isolated',
        'description': 'LEC isolation test with known correct chisel_diff',
        'verilog_diff': {
            'file': 'Control.sv',
            'unified_diff': """--- a/Control.sv
+++ b/Control.sv
@@ -1,1 +1,1 @@
-wire _signals_T_132 = io_opcode == 7'h3B;
+wire _signals_T_132 = io_opcode == 7'h3F;""",
        },
        # This is the KNOWN CORRECT answer - bypass LLM
        'expected_chisel_diff': """@@ -1194,7 +1194,7 @@
           // I-format 32-bit operands
           BitPat("b0011011") -> List( true.B,  true.B, false.B,  1.U,  false.B,       0.U,      false.B,   0.U, false.B,   true.B,    true.B,   true.B),
   -       // R-format 32-bit operands
   -       BitPat("b0111011") -> List(false.B,  true.B, false.B,  0.U,  false.B,       0.U,      false.B,   0.U, false.B,   true.B,    true.B,   true.B),
   +       // R-format 32-bit operands
   +       BitPat("b0111111") -> List(false.B,  true.B, false.B,  0.U,  false.B,       0.U,      false.B,   0.U, false.B,   true.B,    true.B,   true.B),""",
    }


class MockV2chisel_batch(V2chisel_batch):
    """Mock processor that bypasses LLM and uses known correct answer"""

    def __init__(self):
        super().__init__()
        self.test_chisel_diff = None
        # Initialize ALL required attributes to prevent AttributeError
        self.chisel_source_pattern = './tmp/src/main/scala/*/*.scala'

        # Create mock template_config with required structure
        class MockTemplateConfig:
            def __init__(self):
                self.template_dict = {'v2chisel_batch': {'llm': {'model': 'test', 'temperature': 0.1}}}

        self.template_config = MockTemplateConfig()
        self.debug = True
        self.module_finder = None  # Will be set if needed

    def set_test_chisel_diff(self, chisel_diff):
        """Set the known correct chisel_diff to use instead of LLM"""
        self.test_chisel_diff = chisel_diff

    def _call_llm(self, docker_container, system_prompt, user_prompt, history=None):
        """Override LLM call to return known correct chisel_diff"""
        if self.test_chisel_diff is None:
            raise ValueError('Test chisel_diff not set! Call set_test_chisel_diff() first')

        print('🎯 [TEST] Using known correct chisel_diff instead of LLM')
        print('📝 [TEST] Chisel diff to apply:')
        print(self.test_chisel_diff[:200] + '...' if len(self.test_chisel_diff) > 200 else self.test_chisel_diff)

        return {
            'success': True,
            'response': self.test_chisel_diff,
            'input_tokens': 100,
            'output_tokens': 50,
            'model': 'test_known_answer',
        }


def test_lec_isolated():
    """Test LEC functionality with known correct chisel_diff"""
    print('🧪 TESTING LEC IN ISOLATION')
    print('=' * 50)

    # Create test input
    test_bug = create_test_input()
    print(f'📋 Test case: {test_bug["description"]}')
    print(f'🎯 Verilog diff: {test_bug["verilog_diff"]["file"]}')
    print("🔍 Expected to change: 7'h3B → 7'h3F")

    # Create mock processor
    processor = MockV2chisel_batch()
    processor.set_test_chisel_diff(test_bug['expected_chisel_diff'])

    # Create temporary output file
    with tempfile.NamedTemporaryFile(mode='w', suffix='.yaml', delete=False) as tmp_output:
        output_file = tmp_output.name

    try:
        print('\n🚀 STARTING LEC TEST PIPELINE')
        print('=' * 50)

        # Create test input data in the expected format
        test_data = {
            'bugs': [test_bug]  # Use 'bugs' instead of 'bug_lists'
        }

        # Set input data and output path
        processor.input_data = test_data
        processor.output_path = output_file

        # Process the test case (this will run the full pipeline)
        result = processor.run(test_data)

        print('\n📊 TEST RESULTS')
        print('=' * 30)

        if result.get('success', False):
            print('✅ Overall pipeline: SUCCESS')

            # Check specific LEC results
            lec_result = result.get('lec_result', {})
            if lec_result.get('success', False):
                if lec_result.get('lec_passed', False):
                    print('✅ LEC test: PASSED - Designs are equivalent!')
                    print('🎉 SUCCESS: LEC functionality works correctly with known correct chisel_diff')
                    return True
                else:
                    print('❌ LEC test: FAILED - Designs are not equivalent')
                    print(f'⚠️  LEC error: {lec_result.get("lec_error", "Unknown error")}')
                    print(f'📝 LEC output: {lec_result.get("lec_output", "No output")}')
                    return False
            else:
                print(f'❌ LEC setup failed: {lec_result.get("error", "Unknown error")}')
                return False
        else:
            print(f'❌ Pipeline failed: {result.get("error", "Unknown error")}')
            return False

    except Exception as e:
        print(f'💥 Test exception: {str(e)}')
        import traceback

        traceback.print_exc()
        return False
    finally:
        # Clean up temporary file
        try:
            os.unlink(output_file)
        except OSError:
            pass


def main():
    """Run the isolated LEC test"""
    print('🔬 LEC ISOLATION TEST')
    print('=' * 60)
    print('Purpose: Test LEC functionality with known correct chisel_diff')
    print('Expected: LEC should pass with equivalent designs')
    print('=' * 60)

    success = test_lec_isolated()

    print('\n' + '=' * 60)
    if success:
        print('🎉 TEST RESULT: SUCCESS - LEC works correctly!')
        sys.exit(0)
    else:
        print('💥 TEST RESULT: FAILURE - LEC has issues')
        sys.exit(1)


if __name__ == '__main__':
    main()
