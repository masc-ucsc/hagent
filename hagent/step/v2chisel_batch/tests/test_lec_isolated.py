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
import pytest

# Add parent directories to path for imports
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
# ruff: noqa: E402
from v2chisel_batch import V2chisel_batch
from hagent.inou.builder import Builder


@pytest.fixture(autouse=True)
def setup_test_env():
    """Pytest fixture to ensure proper environment setup for every test in this module"""
    # Store original environment
    original_env = {
        'HAGENT_REPO_DIR': os.environ.get('HAGENT_REPO_DIR'),
        'HAGENT_BUILD_DIR': os.environ.get('HAGENT_BUILD_DIR'),
        'HAGENT_CACHE_DIR': os.environ.get('HAGENT_CACHE_DIR'),
    }

    # Set up environment for this test
    setup_test_environment()

    yield  # Run the test

    # Restore original environment (cleanup)
    for key, value in original_env.items():
        if value is None:
            os.environ.pop(key, None)
        else:
            os.environ[key] = value


def setup_test_environment():
    """Set up environment variables for testing - called before each test"""
    # Force set environment variables (don't use setdefault)
    # Docker mode enabled via HAGENT_DOCKER

    # Use current directory for CI compatibility
    current_dir = os.path.dirname(os.path.abspath(__file__))
    os.environ['HAGENT_REPO_DIR'] = current_dir
    os.environ['HAGENT_BUILD_DIR'] = os.path.join(current_dir, 'build')
    os.environ['HAGENT_CACHE_DIR'] = os.path.join(current_dir, 'cache')

    # Create directories if they don't exist
    os.makedirs(os.environ['HAGENT_REPO_DIR'], exist_ok=True)
    os.makedirs(os.environ['HAGENT_BUILD_DIR'], exist_ok=True)
    os.makedirs(os.environ['HAGENT_CACHE_DIR'], exist_ok=True)

    # Environment successfully set up


def create_test_input():
    """Create test input with known verilog_diff and correct chisel_diff"""
    return {
        'id': 'test_lec_isolated',
        'description': 'LEC isolation test with known correct chisel_diff',
        'verilog_diff': """--- a/Control.sv
+++ b/Control.sv
@@ -27,1 +27,1 @@
-  wire _signals_T_132 = io_opcode == 7'h3B;
+  wire _signals_T_132 = io_opcode == 7'h3F;""",
        # This is the KNOWN CORRECT answer - bypass LLM
        'expected_chisel_diff': """--- a/src/main/scala/components/control.scala
+++ b/src/main/scala/components/control.scala
@@ -1194,7 +1194,7 @@
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

        # Create mock template_config with required structure including prompts
        class MockTemplateConfig:
            def __init__(self):
                self.template_dict = {
                    'v2chisel_batch': {
                        'llm': {'model': 'test', 'temperature': 0.1},
                        'prompt_initial': 'test prompt',
                        'prompt_retry': 'test retry prompt',
                        'prompt_compile_error': 'test compile error prompt',
                        'prompt_applier_error': 'test applier error prompt',
                    }
                }

        self.template_config = MockTemplateConfig()
        self.debug = True
        self.module_finder = None  # Will be set if needed

        # Initialize Builder for automated Docker management
        self.runner = Builder()

        # Setup runner and get container name
        self.runner.setup()

        # Create mock input_data with proper container name
        if hasattr(self, 'runner') and self.runner and hasattr(self.runner, 'container_manager'):
            container_mgr = self.runner.container_manager
            if hasattr(container_mgr, 'container') and container_mgr.container:
                actual_container_name = container_mgr.container.name
            else:
                actual_container_name = 'test_container'
        else:
            actual_container_name = 'test_container'

        # Set input_data with proper structure
        self.input_data = {'docker_container': actual_container_name, 'docker_patterns': ['/code/workspace/repo']}

        # Create mock LLM wrapper
        class MockLLMWrapper:
            def __init__(self):
                self.last_error = None

        self.lw = MockLLMWrapper()

    def set_test_chisel_diff(self, chisel_diff):
        """Set the known correct chisel_diff to use instead of LLM"""
        self.test_chisel_diff = chisel_diff

    def _run_docker_command(self, cmd_list, timeout=None):
        """Override parent method to use our Builder instead of subprocess"""
        if timeout:
            print(f'⚠️  Warning: timeout={timeout}s requested but not supported by Builder')

        # Convert Docker exec command list to Builder command
        if len(cmd_list) >= 4 and cmd_list[0] == 'docker' and cmd_list[1] == 'exec':
            # Find where the actual command starts (skip docker, exec, optional -u user, container)
            command_start = 2  # Start after 'docker exec'

            # Skip optional user specification
            if command_start < len(cmd_list) and cmd_list[command_start] == '-u':
                command_start += 2  # Skip '-u' and 'user'

            # Skip container name
            command_start += 1

            if (
                command_start < len(cmd_list)
                and len(cmd_list) >= command_start + 3
                and cmd_list[command_start : command_start + 3] == ['bash', '-l', '-c']
            ):
                # Extract bash command
                command = cmd_list[command_start + 3]
            else:
                # Join remaining command parts
                command = ' '.join(cmd_list[command_start:])

            return self.runner.run(command)
        else:
            # Fallback: join all parts
            return self.runner.run(' '.join(cmd_list))

    def _call_llm_for_chisel_diff(
        self, verilog_diff, chisel_hints, attempt=1, previous_diff='', error_message='', attempt_history=''
    ):
        """Override LLM call to return known correct chisel_diff"""
        if self.test_chisel_diff is None:
            raise ValueError('Test chisel_diff not set! Call set_test_chisel_diff() first')

        print('🎯 [TEST] Using known correct chisel_diff instead of LLM')
        print('📝 [TEST] Chisel diff to apply:')
        print(self.test_chisel_diff[:200] + '...' if len(self.test_chisel_diff) > 200 else self.test_chisel_diff)

        return {
            'success': True,
            'chisel_diff': self.test_chisel_diff,
            'prompt_used': 'test_prompt',
            'attempt': attempt,
        }


def test_lec_isolated():
    """Test LEC functionality with known correct chisel_diff"""
    print('🧪 TESTING LEC IN ISOLATION')
    print('=' * 50)

    # Create test input
    test_bug = create_test_input()
    print(f'📋 Test case: {test_bug["description"]}')
    print('🎯 Verilog diff: Control.sv')
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
        processor.output_file = output_file

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
