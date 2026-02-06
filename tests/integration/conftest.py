"""
Conftest for Integration Tests

Provides shared fixtures and pytest configuration for integration tests.
"""

import re
import subprocess
import uuid
from pathlib import Path

import pytest

from tests.integration.utils.setup_helper import setup_project


# ============================================================================
# Pytest Configuration
# ============================================================================


def pytest_configure(config):
    """Register custom markers for integration tests."""
    config.addinivalue_line('markers', 'integration: mark test as integration test (requires external repos/Docker)')
    config.addinivalue_line('markers', 'cva6: mark test as using CVA6 Docker image')
    config.addinivalue_line('markers', 'simplechisel: mark test as using SimpleChisel Docker image')


def pytest_sessionfinish(session, exitstatus):
    """
    After all tests complete, collect coverage files from cache directories.

    Integration tests write coverage data to HAGENT_CACHE_DIR (which persists
    after Docker containers exit). This hook copies those files to the repo root
    so 'coverage combine' can find them.
    """
    import os
    import shutil

    repo_root = Path(__file__).resolve().parent.parent.parent

    # Find all .coverage.* files in output/integration_tests/*/cache/
    integration_output = repo_root / 'output' / 'integration_tests'
    if not integration_output.exists():
        return

    coverage_files_found = []
    for cache_dir in integration_output.rglob('cache'):
        if cache_dir.is_dir():
            # Find all coverage files (.coverage and .coverage.*)
            for pattern in ['.coverage', '.coverage.*']:
                for cov_file in cache_dir.glob(pattern):
                    if not cov_file.is_file():
                        continue
                    # Copy to repo root with unique name
                    if cov_file.name == '.coverage':
                        # Rename .coverage to .coverage.<random> to avoid conflicts
                        import uuid

                        dest = repo_root / f'.coverage.{uuid.uuid4().hex[:8]}'
                    else:
                        dest = repo_root / cov_file.name
                        # If file already exists, append random suffix
                        if dest.exists():
                            import uuid

                            dest = repo_root / f'{cov_file.name}.{uuid.uuid4().hex[:8]}'
                    shutil.copy2(cov_file, dest)
                    coverage_files_found.append(dest.name)

    if coverage_files_found:
        print(f'\n✓ Collected {len(coverage_files_found)} coverage file(s) from cache directories')
        print(f'  Run: uv run coverage combine && uv run coverage xml -o coverage.xml')


def _sanitize_node_id(node_id: str) -> str:
    """Normalize a pytest node id for filesystem use."""
    return re.sub(r'[^A-Za-z0-9_.-]+', '_', node_id).strip('_')


@pytest.fixture(autouse=True)
def test_output_dir(request, monkeypatch):
    """
    Create a per-test output directory and route temp files there.

    Keeps all test artifacts under <repo>/output/tests/<nodeid>_<uuid>.
    """
    repo_root = Path(__file__).resolve().parent.parent.parent
    safe_node_id = _sanitize_node_id(request.node.nodeid)
    test_id = uuid.uuid4().hex[:8]
    output_dir = (repo_root / 'output' / 'tests' / f'{safe_node_id}_{test_id}').resolve()
    output_dir.mkdir(parents=True, exist_ok=True)

    monkeypatch.setenv('TMPDIR', str(output_dir))
    monkeypatch.setenv('TEMP', str(output_dir))
    monkeypatch.setenv('TMP', str(output_dir))

    return output_dir


@pytest.fixture(autouse=True)
def enable_subprocess_coverage(monkeypatch):
    """
    Automatically wrap subprocess.run calls to enable coverage tracking.

    This fixture monkeypatches subprocess.run to inject 'coverage run -p'
    for Python commands, enabling coverage tracking in integration test subprocesses.

    For Docker-based tests, coverage data is written to HAGENT_CACHE_DIR so it
    persists after the container exits.
    """
    original_run = subprocess.run
    repo_root = Path(__file__).resolve().parent.parent.parent

    def coverage_aware_run(cmd, *args, **kwargs):
        """Wrapper that injects coverage tracking for Python subprocess calls."""
        # Check if this is a Python command via uv run
        if isinstance(cmd, list) and len(cmd) >= 3 and cmd[0:3] == ['uv', 'run', 'python']:
            # Ensure env has coverage config
            if 'env' in kwargs:
                env = kwargs['env'].copy()
            else:
                import os

                env = os.environ.copy()

            # Determine if running in Docker mode
            is_docker = 'HAGENT_DOCKER' in env and env.get('HAGENT_DOCKER')

            # Set coverage paths based on Docker vs local mode
            if is_docker:
                # Inside Docker:
                # - pyproject.toml is at /code/hagent/pyproject.toml
                # - cache is mounted at /code/workspace/cache
                coverage_rc = '/code/hagent/pyproject.toml'
                coverage_file = '/code/workspace/cache/.coverage'
            else:
                # Local mode
                coverage_rc = str(repo_root / 'pyproject.toml')
                if 'HAGENT_CACHE_DIR' in env:
                    coverage_file = f"{env['HAGENT_CACHE_DIR']}/.coverage"
                else:
                    coverage_file = str(repo_root / '.coverage')

            # Inject coverage with explicit config file
            # ['uv', 'run', 'python', ...] -> ['uv', 'run', 'coverage', 'run', '-p', '--rcfile=...', 'python', ...]
            modified_cmd = cmd[0:2] + ['coverage', 'run', '-p', f'--rcfile={coverage_rc}'] + cmd[2:]

            # Set COVERAGE_FILE to write to cache directory (persists after Docker exit)
            env['COVERAGE_FILE'] = coverage_file

            kwargs['env'] = env
            return original_run(modified_cmd, *args, **kwargs)
        else:
            # Not a Python command, run as-is
            return original_run(cmd, *args, **kwargs)

    monkeypatch.setattr(subprocess, 'run', coverage_aware_run)


# ============================================================================
# Test-Level Fixtures
# ============================================================================


@pytest.fixture
def cva6_setup(request):
    """
    Extract CVA6 from Docker using setup_mcp.sh.

    Returns:
        Dict with repo_dir, build_dir, cache_dir, logs_dir, env_vars
    """
    # Create test directory under project output/ directory (not /tmp)
    project_root = Path(__file__).parent.parent.parent
    safe_node_id = _sanitize_node_id(request.node.nodeid)
    test_id = uuid.uuid4().hex[:8]
    base_dir = project_root / 'output' / 'integration_tests' / 'cva6' / f'{safe_node_id}_{test_id}'
    base_dir.mkdir(parents=True, exist_ok=True)

    setup_info = setup_project('cva6', base_dir, docker_mode=True)

    yield setup_info

    # Keep artifacts for debugging - don't delete


@pytest.fixture
def simplechisel_setup(request):
    """
    Extract SimpleChisel from Docker using setup_mcp.sh.

    Returns:
        Dict with repo_dir, build_dir, cache_dir, logs_dir, env_vars
    """
    # Create test directory under project output/ directory (not /tmp)
    project_root = Path(__file__).parent.parent.parent
    safe_node_id = _sanitize_node_id(request.node.nodeid)
    test_id = uuid.uuid4().hex[:8]
    base_dir = project_root / 'output' / 'integration_tests' / 'simplechisel' / f'{safe_node_id}_{test_id}'
    base_dir.mkdir(parents=True, exist_ok=True)

    setup_info = setup_project('simplechisel', base_dir, docker_mode=True)

    yield setup_info

    # Keep artifacts for debugging - don't delete


@pytest.fixture
def test_config():
    """
    Load test configuration with timeouts and expected value ranges.

    Returns:
        Dict with configuration values
    """
    # Load STA ranges from file if it exists
    sta_ranges_file = Path(__file__).parent / 'data' / 'expected' / 'cva6_sta_ranges.yaml'
    if sta_ranges_file.exists():
        import yaml

        with open(sta_ranges_file) as f:
            sta_ranges = yaml.safe_load(f)
    else:
        # Default ranges if file doesn't exist yet
        sta_ranges = {
            'timing': {
                'min_slack': -100.0,
                'max_slack': 1000.0,
                'min_delay': 0.0,
                'max_delay': 10000.0,
            },
            'power': {
                'min_total_power': 0.0,
                'max_total_power': 1.0,
                'min_leakage': 0.0,
                'max_leakage': 0.1,
            },
        }

    return {
        'timeout': 600,  # 10 minutes default
        'synth_timeout': 300,  # 5 minutes for synthesis
        'lec_timeout': 600,  # 10 minutes for LEC
        'docker_timeout': 30,  # 30 seconds for Docker commands
        'sta_ranges': sta_ranges,
    }
