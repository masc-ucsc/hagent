# See LICENSE for details

import os
import tempfile
from pathlib import Path
from unittest.mock import patch
from hagent.step.trivial.trivial import Trivial


def test_trivial():
    test_dir = os.path.dirname(os.path.abspath(__file__))

    inp_file = os.path.join(test_dir, 'input1.yaml')
    expected_out_file = os.path.join(test_dir, 'expected_output1.yaml')

    # Set up environment for local execution
    with tempfile.TemporaryDirectory() as temp_dir:
        temp_path = Path(temp_dir)
        repo_dir = temp_path / 'repo'
        build_dir = temp_path / 'build'
        cache_dir = temp_path / 'cache'

        # Create repo directory (must exist for validation)
        repo_dir.mkdir()

        env_vars = {
            'HAGENT_EXECUTION_MODE': 'local',
            'HAGENT_REPO_DIR': str(repo_dir),
            'HAGENT_BUILD_DIR': str(build_dir),
            'HAGENT_CACHE_DIR': str(cache_dir),
        }

        with patch.dict(os.environ, env_vars, clear=True):
            trivial_step = Trivial()

            trivial_step.set_io(inp_file=inp_file, out_file='test_trivial_output.yaml')
            # No trivial_step.parse_arguments() -- Unit test

            # Custom test that's more flexible with system-specific outputs
            from ruamel.yaml import YAML

            yaml_obj = YAML(typ='safe')
            with open(expected_out_file, 'r') as f:
                expected_output = yaml_obj.load(f)

            trivial_step.input_data = trivial_step.read_input()
            trivial_step.setup()
            with trivial_step.temporary_env_vars():
                result_data = trivial_step.run(trivial_step.input_data)

            # Check that all expected fields are present and match
            for key, value in expected_output.items():
                assert key in result_data, f'Missing expected key: {key}'
                assert result_data[key] == value, f'Mismatch for key {key}: expected {value}, got {result_data[key]}'

            # Check that required runtime fields are present
            runtime_fields = [
                'uname_ret',
                'uname_out',
                'uname_err',
                'pwd_ret',
                'pwd_out',
                'pwd_err',
                'yosys_path_ret',
                'yosys_path_out',
                'yosys_path_err',
            ]
            for field in runtime_fields:
                assert field in result_data, f'Missing required runtime field: {field}'

            # Check that uname and pwd commands succeeded
            assert result_data['uname_ret'] == '0', 'uname command should succeed'
            assert result_data['pwd_ret'] == '0', 'pwd command should succeed'
            assert len(result_data['uname_out']) > 0, 'uname should produce output'
            assert len(result_data['pwd_out']) > 0, 'pwd should produce output'


if __name__ == '__main__':  # pragma: no cover
    test_trivial()
