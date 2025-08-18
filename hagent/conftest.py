"""
Global pytest configuration for hagent tests.

Provides automatic cleanup of Docker containers created during testing
to prevent container accumulation from test runs.
"""

import pytest
import docker
import sys
import re


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
        print(f'Warning: Failed to cleanup test containers: {e}', file=sys.stderr)


@pytest.fixture(autouse=True)
def ensure_container_cleanup():
    """
    Auto-use fixture that ensures containers are cleaned up even if tests fail.

    This fixture runs before and after each test to track container creation
    and ensure cleanup happens even when tests are interrupted.
    """
    # Before test: record current containers
    try:
        client = docker.from_env()
        hagent_pattern = re.compile(r'^mascucsc/hagent-.*$')
        containers_before = {
            container.id
            for container in client.containers.list(all=True)
            if hagent_pattern.match(container.attrs['Config']['Image'])
        }
    except Exception:
        containers_before = set()

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
