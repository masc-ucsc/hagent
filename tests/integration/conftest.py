"""
Conftest for Integration Tests

Provides shared fixtures and pytest configuration for integration tests.
"""

import re
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
