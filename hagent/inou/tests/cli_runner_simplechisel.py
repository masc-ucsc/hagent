#!/usr/bin/env python3
"""
Simple test example using Runner for SimpleChisel functionality.
Demonstrates simplified command execution with unified API.
Converted to use Runner instead of direct Executor/ContainerManager/PathManager usage.

Can be run as:
1. CLI tool: uv run python hagent/inou/tests/cli_runner_simplechisel.py
2. Slow test: uv run pytest -m slow hagent/inou/tests/cli_runner_simplechisel.py
"""

import pytest

# Set up environment for testing - only set execution mode
# Let Runner handle all Docker paths internally
# Docker mode enabled via HAGENT_DOCKER

from hagent.inou.runner import Runner


def _run_simplechisel_test():
    """Core SimpleChisel test logic - shared between CLI and pytest."""

    # 1. Initialize Runner with Docker image
    runner = Runner(docker_image='mascucsc/hagent-simplechisel:2025.12')

    # 2. Setup runner (creates and configures container)
    assert runner.setup(), f'Setup failed: {runner.get_error()}'
    print('✅ Container setup successful')

    # 4. Check if SimpleChisel project exists in the container
    print('Checking for SimpleChisel project...')

    # Try multiple possible locations
    possible_locations = ['/code/workspace/repo']
    project_location = None

    for location in possible_locations:
        exit_code, stdout, stderr = runner.run_cmd(f'ls -la {location}/', cwd='/')
        if exit_code == 0:
            project_location = location
            print(f'✅ Found SimpleChisel project at: {location}')
            break

    if project_location is None:
        # List what's actually available
        print('Exploring container structure...')
        runner.run_cmd('ls -la /code/', cwd='/code')
        runner.run_cmd('find /code -name "build.sbt" -o -name "*.scala" | head -10', cwd='/code')

        print('⚠️  SimpleChisel project not found in expected locations')
        print('This test requires the mascucsc/hagent-simplechisel:2025.12 image with SimpleChisel project')
        print('✅ Test completed - container setup verified (SimpleChisel project not available)')
        runner.cleanup()
        return

    # 4. Execute SBT compile command in the found project directory
    runner.run_cmd('ls -la /code/workspace/repo', cwd='/')
    print('Running SBT compile...')
    exit_code, stdout, stderr = runner.run_cmd('sbt compile', cwd=project_location)
    assert exit_code == 0, f'sbt compile failed: code:{exit_code}\nstderr: {stderr}'
    print('✅ SBT compile successful')

    # 5. Execute SBT runMain command
    print('Running SBT runMain...')
    exit_code, stdout, stderr = runner.run_cmd(
        'sbt "runMain dinocpu.pipelined.PipelinedDualIssueDebug"',
        # No need to say cwd because /code/workspace/repo is supposed to be the default
    )
    assert exit_code == 0, f'sbt runMain failed: code:{exit_code}\nstderr: {stderr}'
    print('✅ SBT runMain successful')

    # 6. Cleanup
    print('Cleaning up...')
    runner.cleanup()
    print('✅ Test completed successfully - SimpleChisel execution verified')


@pytest.mark.slow
def test_simplechisel_execution():
    """Pytest slow test for SimpleChisel execution via Runner API."""
    _run_simplechisel_test()


def main():
    """CLI entry point - calls the core test logic."""
    _run_simplechisel_test()


if __name__ == '__main__':
    main()
