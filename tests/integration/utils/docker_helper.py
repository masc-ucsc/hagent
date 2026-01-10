"""
Docker Helper for Integration Tests

Provides utilities for working with docker_args.sh and running Docker commands.
"""

import subprocess
from pathlib import Path
from typing import Dict, List


def get_docker_args(env: Dict[str, str]) -> List[str]:
    """
    Run docker_args.sh to get Docker command arguments.

    Args:
        env: Environment variables (including HAGENT_DOCKER, etc.)

    Returns:
        List of Docker command arguments

    Raises:
        RuntimeError: If docker_args.sh fails
    """
    # Get project root
    project_root = Path(__file__).parent.parent.parent.parent

    docker_args_script = project_root / 'scripts' / 'docker_args.sh'
    assert docker_args_script.exists(), f'docker_args.sh not found at {docker_args_script}'

    result = subprocess.run([str(docker_args_script)], env=env, capture_output=True, text=True, cwd=str(project_root))

    if result.returncode != 0:
        raise RuntimeError(f'docker_args.sh failed:\\nstdout: {result.stdout}\\nstderr: {result.stderr}')

    # Parse output into list (docker_args.sh returns single string)
    # Output format: "docker run --rm -it -v ... image:tag"
    return result.stdout.strip().split()


def run_docker_command(docker_args: List[str], command: str, timeout: int = 60) -> subprocess.CompletedProcess:
    """
    Run a command inside Docker using docker_args.

    Args:
        docker_args: Docker arguments from get_docker_args()
        command: Command to run inside Docker
        timeout: Timeout in seconds

    Returns:
        subprocess.CompletedProcess result
    """
    # docker_args is like: ['docker', 'run', '--rm', '-it', '-v', '...', 'image:tag']
    # We need to remove '-it' for non-interactive and add command
    docker_cmd = [arg for arg in docker_args if arg != '-it']

    # Add bash -c wrapper for the command
    docker_cmd.extend(['bash', '-c', command])

    return subprocess.run(docker_cmd, capture_output=True, text=True, timeout=timeout)
