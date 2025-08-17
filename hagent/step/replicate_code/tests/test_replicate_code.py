# See LICENSE for details

import os
import pytest

from hagent.step.replicate_code.replicate_code import Replicate_code
from hagent.inou.output_manager import get_output_path


def test_replicate_missing_llm():
    test_dir = os.path.dirname(os.path.abspath(__file__))

    inp_file = os.path.join(test_dir, 'bad_input.yaml')

    trivial_step = Replicate_code()
    trivial_step.set_io(inp_file=inp_file, out_file=get_output_path('test_replicate_code_output.yaml'))

    with pytest.raises(ValueError):
        trivial_step.setup()
        trivial_step.step()


def test_replicate_code():
    # Set up environment for Docker mode (needed for yosys in equiv_check)
    original_env = os.environ.copy()
    test_env = {
        'HAGENT_EXECUTION_MODE': 'docker',
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
        test_dir = os.path.dirname(os.path.abspath(__file__))

        inp_file = os.path.join(test_dir, 'input1.yaml')

        trivial_step = Replicate_code()
        trivial_step.set_io(inp_file=inp_file, out_file=get_output_path('test_replicate_code_output.yaml'))

        # Skip if no AWS credentials are available (common after clean)
        if not os.environ.get('AWS_BEARER_TOKEN_BEDROCK'):
            pytest.skip("AWS credentials not available - skipping LLM test")

        trivial_step.setup()

        res = trivial_step.step()

        xx = res['optimized_equivalent']
        print(f'optimized_equivalent:{xx}')

        assert len(xx) > 0
    finally:
        # Restore original environment
        os.environ.clear()
        os.environ.update(original_env)


if __name__ == '__main__':  # pragma: no cover
    test_replicate_missing_llm()
    test_replicate_code()
