"""
Global pytest configuration for hagent tests.

Provides automatic cleanup of Docker containers created during testing
to prevent container accumulation from test runs.
"""

import os
import re
import sys
import uuid
from pathlib import Path

import docker
import pytest


def pytest_sessionstart(session):
    """Called after the Session object has been created."""
    # Store containers that existed before tests started
    try:
        client = docker.from_env()
        hagent_pattern = re.compile(r'^mascucsc/hagent-.*$')
        existing_containers = {
            container.id
            for container in client.containers.list(all=True)
            if hagent_pattern.match(container.attrs['Config']['Image'])
        }
        session.config._initial_test_containers = existing_containers
    except Exception:
        # If Docker isn't available, just set empty set
        session.config._initial_test_containers = set()


def pytest_sessionfinish(session, exitstatus):
    """Called after whole test run finished."""
    try:
        client = docker.from_env()
        hagent_pattern = re.compile(r'^mascucsc/hagent-.*$')
        current_containers = {
            container.id
            for container in client.containers.list(all=True)
            if hagent_pattern.match(container.attrs['Config']['Image'])
        }

        # Find containers created during this test session
        initial_containers = getattr(session.config, '_initial_test_containers', set())
        new_containers = current_containers - initial_containers

        if new_containers:
            print(f'\n⚠️  Cleaning up {len(new_containers)} hagent Docker containers created during tests...')

            for container_id in new_containers:
                try:
                    container = client.containers.get(container_id)
                    image_name = container.attrs['Config']['Image']
                    print(f'  Stopping and removing container {container_id[:12]} ({image_name})...')
                    if container.status == 'running':
                        container.kill()
                    container.remove()
                except docker.errors.NotFound:
                    pass  # Container was already removed
                except Exception as e:
                    print(f'  Warning: Failed to cleanup container {container_id[:12]}: {e}')

            print('✅ Container cleanup completed.')

    except Exception as e:
        # Only show warning if we actually had containers to cleanup
        initial_containers = getattr(session.config, '_initial_test_containers', set())
        if initial_containers:
            print(f'Warning: Failed to cleanup test containers: {e}', file=sys.stderr)


def _sanitize_node_id(node_id: str) -> str:
    """Normalize a pytest node id for filesystem use."""
    return re.sub(r'[^A-Za-z0-9_.-]+', '_', node_id).strip('_')


@pytest.fixture(autouse=True)
def test_output_dir(request, monkeypatch):
    """
    Create a per-test output directory and route temp files there.

    Keeps all test artifacts under <repo>/output/tests/<nodeid>_<uuid>.
    """
    repo_root = Path(__file__).resolve().parent.parent
    safe_node_id = _sanitize_node_id(request.node.nodeid)
    test_id = uuid.uuid4().hex[:8]
    output_dir = (repo_root / 'output' / 'tests' / f'{safe_node_id}_{test_id}').resolve()
    output_dir.mkdir(parents=True, exist_ok=True)

    monkeypatch.setenv('TMPDIR', str(output_dir))
    monkeypatch.setenv('TEMP', str(output_dir))
    monkeypatch.setenv('TMP', str(output_dir))

    return output_dir


@pytest.fixture(autouse=True)
def setup_test_environment():
    """
    Auto-use fixture that sets up required environment variables for all tests.

    This ensures that tests have the necessary environment variables set
    even when running the full test suite.

    Note: Execution mode is determined by HAGENT_DOCKER:
    - If HAGENT_DOCKER is set → docker mode
    - If HAGENT_DOCKER is not set → local mode (default for tests)
    """
    # Store original values to restore later
    original_tokenizers = os.environ.get('TOKENIZERS_PARALLELISM')
    original_no_proxy = os.environ.get('no_proxy')

    # Set required environment variables if not already set
    os.environ['TOKENIZERS_PARALLELISM'] = 'false'

    # Disable proxy detection to avoid Python 3.13 + macOS + fork segfault
    # See: https://github.com/python/cpython/issues/124448
    os.environ['no_proxy'] = '*'

    yield

    # Restore original values
    if original_tokenizers is None:
        os.environ.pop('TOKENIZERS_PARALLELISM', None)
    else:
        os.environ['TOKENIZERS_PARALLELISM'] = original_tokenizers

    if original_no_proxy is None:
        os.environ.pop('no_proxy', None)
    else:
        os.environ['no_proxy'] = original_no_proxy


@pytest.fixture(autouse=True, scope='function')
def ensure_container_cleanup(request):
    """
    Auto-use fixture that ensures containers are cleaned up even if tests fail.

    This fixture runs before and after each test to track container creation
    and ensure cleanup happens even when tests are interrupted.

    Note: This fixture is disabled when running with pytest-xdist (-n auto)
    to avoid parallel Docker client initialization issues. The session-level
    cleanup (pytest_sessionfinish) handles cleanup in that case.
    """
    # Skip this fixture if running in parallel mode (pytest-xdist worker)
    # The session cleanup will handle container cleanup instead
    if hasattr(request.config, 'workerinput'):
        # Running in xdist worker, skip per-test cleanup
        yield
        return

    # Before test: record current containers
    containers_before = set()
    try:
        client = docker.from_env()
        hagent_pattern = re.compile(r'^mascucsc/hagent-.*$')
        containers_before = {
            container.id
            for container in client.containers.list(all=True)
            if hagent_pattern.match(container.attrs['Config']['Image'])
        }
    except Exception:
        pass  # Docker not available or other error

    yield

    # After test: cleanup any new containers
    try:
        client = docker.from_env()
        hagent_pattern = re.compile(r'^mascucsc/hagent-.*$')
        containers_after = {
            container.id
            for container in client.containers.list(all=True)
            if hagent_pattern.match(container.attrs['Config']['Image'])
        }

        new_containers = containers_after - containers_before
        for container_id in new_containers:
            try:
                container = client.containers.get(container_id)
                # Only cleanup containers that are still running the default "keep alive" command
                if container.attrs['Config']['Cmd'] == ['tail', '-f', '/dev/null']:
                    if container.status == 'running':
                        container.kill()
                    container.remove()
            except Exception:
                pass  # Ignore cleanup errors
    except Exception:
        pass  # Ignore Docker connection errors
