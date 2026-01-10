"""
Setup Helper for Integration Tests

Provides Python wrapper for setup_mcp.sh to extract projects from Docker images.
"""

import os
import re
import subprocess
from pathlib import Path
from typing import Dict


def setup_project(project_name: str, base_dir: Path, docker_mode: bool = True) -> Dict[str, any]:
    """
    Run setup_mcp.sh to extract project from Docker image.

    Args:
        project_name: Project name ('cva6', 'simplechisel', etc.)
        base_dir: Target directory for extraction
        docker_mode: Use Docker mode if True, local mode if False

    Returns:
        Dict with keys:
        - repo_dir: Path to extracted repo
        - build_dir: Path to build directory
        - cache_dir: Path to cache directory
        - logs_dir: Path to logs directory
        - env_vars: Dict of environment variables from hagent_server.sh
    """
    base_dir = Path(base_dir)
    base_dir.mkdir(parents=True, exist_ok=True)

    # Get project root (hagent directory)
    project_root = Path(__file__).parent.parent.parent.parent

    # Build setup_mcp.sh command
    setup_script = project_root / 'scripts' / 'setup_mcp.sh'
    assert setup_script.exists(), f'setup_mcp.sh not found at {setup_script}'

    cmd = [str(setup_script), project_name, str(base_dir)]
    if not docker_mode:
        cmd.insert(1, '--local')

    # Run setup_mcp.sh
    result = subprocess.run(cmd, capture_output=True, text=True, cwd=str(project_root))

    if result.returncode != 0:
        raise RuntimeError(f'setup_mcp.sh failed for {project_name}:\nstdout: {result.stdout}\nstderr: {result.stderr}')

    # Parse hagent_server.sh for environment variables
    server_sh = base_dir / 'hagent_server.sh'
    if not server_sh.exists():
        raise FileNotFoundError(f'hagent_server.sh not found at {server_sh}')

    env_vars = parse_env_vars(server_sh)

    # Validate that extraction was successful
    repo_dir = base_dir / 'repo'
    build_dir = base_dir / 'build'

    if not repo_dir.exists() or not build_dir.exists():
        raise RuntimeError(
            f'setup_mcp.sh completed but directories not created.\n'
            f'repo_dir exists: {repo_dir.exists()}\n'
            f'build_dir exists: {build_dir.exists()}\n'
            f'This might indicate a cache consistency issue. Try clearing: '
            f'rm -rf {project_root}/.cache/setup_{project_name}_mcp_*'
        )

    # Check that repo or build has some content
    repo_contents = list(repo_dir.iterdir()) if repo_dir.exists() else []
    build_contents = list(build_dir.iterdir()) if build_dir.exists() else []

    if not repo_contents and not build_contents:
        raise RuntimeError(
            f'setup_mcp.sh extracted directories but they are empty.\n'
            f'This indicates cache corruption or Docker image issue.\n'
            f'Try: rm -rf {project_root}/.cache/setup_{project_name}_mcp_*'
        )

    return {
        'repo_dir': repo_dir,
        'build_dir': build_dir,
        'cache_dir': base_dir / 'cache',
        'logs_dir': base_dir / 'logs',
        'env_vars': env_vars,
    }


def parse_env_vars(server_sh: Path) -> Dict[str, str]:
    """
    Parse environment variables from hagent_server.sh.

    Args:
        server_sh: Path to hagent_server.sh file

    Returns:
        Dict of environment variable name -> value
    """
    env_vars = os.environ.copy()

    with open(server_sh) as f:
        content = f.read()

    # Parse export statements
    # Pattern: export VAR_NAME="value" or export VAR_NAME=value
    export_pattern = r'export\s+([A-Z_]+)=[\"]?([^\"\n]+)[\"]?'

    for match in re.finditer(export_pattern, content):
        var_name = match.group(1)
        var_value = match.group(2).strip('"').strip("'")
        env_vars[var_name] = var_value

    return env_vars
