"""
Integration Test 4: Docker Tool Validation

Tests that required tools are installed and working in Docker images.
"""

from pathlib import Path

import pytest
import yaml

from tests.integration.utils.docker_helper import get_docker_args, run_docker_command


@pytest.mark.integration
@pytest.mark.cva6
def test_cva6_docker_tools(cva6_setup, test_config):
    """
    Test that required tools are available and working in CVA6 Docker image.

    Steps:
    1. Use docker_args.sh to generate Docker command
    2. Run tool version checks in Docker
    3. Validate tool availability and versions
    """
    env = cva6_setup['env_vars']

    # Get Docker args from docker_args.sh
    docker_args = get_docker_args(env)

    # Load tool requirements
    tools_file = Path(__file__).parent / 'data' / 'tool_requirements' / 'cva6_tools.yaml'

    if not tools_file.exists():
        pytest.skip(f'Tool requirements file not found: {tools_file}')

    with open(tools_file) as f:
        tool_reqs = yaml.safe_load(f)

    # Test each required tool
    for tool in tool_reqs.get('required_tools', []):
        tool_name = tool['name']
        version_flag = tool.get('version_flag', '--version')

        print(f'\\nTesting tool: {tool_name}')

        # Run tool version command in Docker
        result = run_docker_command(docker_args, f'{tool_name} {version_flag}', timeout=test_config['docker_timeout'])

        # Check tool is available
        assert result.returncode == 0, f'{tool_name} not found or failed:\\nstderr: {result.stderr}\\nstdout: {result.stdout}'

        combined_output = result.stdout + result.stderr

        # Check version if specified
        if 'min_version' in tool:
            assert tool['min_version'] in combined_output, (
                f'{tool_name} version {tool["min_version"]} not found in output:\\n{combined_output}'
            )

        # Check expected output if specified
        if 'expected_output' in tool:
            assert tool['expected_output'] in combined_output, (
                f"{tool_name} expected output '{tool['expected_output']}' not found in:\\n{combined_output}"
            )

        print(f'✓ {tool_name} available')


@pytest.mark.integration
@pytest.mark.simplechisel
def test_simplechisel_docker_tools(simplechisel_setup, test_config):
    """
    Test that required tools are available and working in SimpleChisel Docker image.

    Similar to CVA6 test but for SimpleChisel.
    """
    env = simplechisel_setup['env_vars']

    # Get Docker args
    docker_args = get_docker_args(env)

    # Load tool requirements
    tools_file = Path(__file__).parent / 'data' / 'tool_requirements' / 'simplechisel_tools.yaml'

    if not tools_file.exists():
        pytest.skip(f'Tool requirements file not found: {tools_file}')

    with open(tools_file) as f:
        tool_reqs = yaml.safe_load(f)

    # Test each tool
    for tool in tool_reqs.get('required_tools', []):
        tool_name = tool['name']
        version_flag = tool.get('version_flag', '--version')

        print(f'\\nTesting tool: {tool_name}')

        result = run_docker_command(docker_args, f'{tool_name} {version_flag}', timeout=test_config['docker_timeout'])

        assert result.returncode == 0, f'{tool_name} not found or failed: {result.stderr}'

        combined_output = result.stdout + result.stderr

        if 'min_version' in tool:
            assert tool['min_version'] in combined_output

        if 'expected_output' in tool:
            assert tool['expected_output'] in combined_output

        print(f'✓ {tool_name} available')
