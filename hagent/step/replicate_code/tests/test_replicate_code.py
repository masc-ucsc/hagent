# See LICENSE for details

import os
import pytest
import tempfile
import yaml

from hagent.step.replicate_code.replicate_code import Replicate_code
from hagent.inou.path_manager import PathManager


def test_replicate_missing_llm():
    test_dir = os.path.dirname(os.path.abspath(__file__))

    inp_file = os.path.join(test_dir, 'bad_input.yaml')

    trivial_step = Replicate_code()
    trivial_step.set_io(inp_file=inp_file, out_file=PathManager().get_cache_path('test_replicate_code_output.yaml'))

    with pytest.raises(ValueError):
        trivial_step.setup()
        trivial_step.step()


def test_replicate_code():
    # Set up environment for Docker mode (needed for yosys in equiv_check)
    original_env = os.environ.copy()
    test_env = {
        'HAGENT_REPO_DIR': os.path.abspath('./output/test_replicate_code/repo'),
        'HAGENT_BUILD_DIR': os.path.abspath('./output/test_replicate_code/build'),
        'HAGENT_CACHE_DIR': os.path.abspath('./output/test_replicate_code/cache'),
    }

    # Create directories
    for dir_path in [test_env['HAGENT_REPO_DIR'], test_env['HAGENT_BUILD_DIR'], test_env['HAGENT_CACHE_DIR']]:
        os.makedirs(dir_path, exist_ok=True)

    # Update environment
    os.environ.update(test_env)

    try:
        # Create a lightweight test input for faster testing
        test_input = {
            'description': 'Fast test case',
            'code_content': 'module simple_and(output Y, input A, input B); assign Y = A & B; endmodule',
            'top_name': 'simple_and',
            'threshold': 50,
            'llm': {'model': 'bedrock/us.meta.llama3-3-70b-instruct-v1:0', 'aws_region_name': 'us-east-1'},
            'cost': 10,
        }

        # Let test run even without credentials to test error handling

        # Create a temporary input file for faster testing
        with tempfile.NamedTemporaryFile(mode='w', suffix='.yaml', delete=False) as f:
            yaml.dump(test_input, f)
            temp_input_file = f.name

        try:
            trivial_step = Replicate_code()
            trivial_step.set_io(
                inp_file=temp_input_file, out_file=PathManager().get_cache_path('test_replicate_code_output.yaml')
            )

            trivial_step.setup()

            # Run the actual test and check for LLM errors
            try:
                res = trivial_step.step()

                # If we get here, the test completed successfully
                xx = res['optimized_equivalent']
                print(f'optimized_equivalent:{xx}')

                # The test should complete successfully
                assert isinstance(xx, list)  # Should return a list (even if empty)
                assert 'optimized_equivalent' in res  # Should have the key in results

            except Exception as e:
                # Check if the error is due to missing LLM credentials
                error_msg = str(e).lower()
                llm_error_indicators = [
                    'environment variable',
                    'aws_access_key_id',
                    'aws_secret_access_key',
                    'openai_api_key',
                    'anthropic_api_key',
                    'not set',
                    'authentication',
                    'api key',
                ]

                # Check if this is an LLM credential error
                is_llm_error = any(indicator in error_msg for indicator in llm_error_indicators)

                if is_llm_error:
                    pytest.skip(f'Test disabled due to missing LLM credentials: {str(e)}')
                else:
                    # Re-raise if it's a different kind of error
                    raise

        finally:
            # Clean up temp file
            if os.path.exists(temp_input_file):
                os.unlink(temp_input_file)
    finally:
        # Restore original environment
        os.environ.clear()
        os.environ.update(original_env)


if __name__ == '__main__':  # pragma: no cover
    test_replicate_missing_llm()
    test_replicate_code()
