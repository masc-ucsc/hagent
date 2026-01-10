"""Tests for Builder execution mode selection and overrides."""

import os

import pytest

from hagent.inou.builder import Builder
from hagent.inou.path_manager import PathManager


@pytest.fixture(autouse=True)
def reset_path_manager_state():
    """Reset PathManager state before and after each test.

    These tests check Builder behavior with different environment configurations,
    so we need to reset PathManager directly to allow tests to control the env.
    """
    # Save original state
    old_instance = PathManager._instance
    old_initialized = PathManager._initialized

    # Reset before test
    PathManager._instance = None
    PathManager._initialized = False

    yield

    # Reset after test
    PathManager._instance = old_instance
    PathManager._initialized = old_initialized


def test_builder_uses_environment_mode_by_default(monkeypatch):
    """Builder should respect HAGENT_DOCKER when no docker override is provided."""
    monkeypatch.setenv('HAGENT_DOCKER', 'mascucsc/hagent-simplechisel:2026.01')

    builder = Builder()
    try:
        assert builder.runner.is_docker_mode()
        assert os.environ['HAGENT_DOCKER'] == 'mascucsc/hagent-simplechisel:2026.01'
    finally:
        builder.cleanup()


def test_builder_local_mode(monkeypatch, tmp_path):
    """Builder should stay in local mode when HAGENT_DOCKER is not set."""
    repo_dir = tmp_path / 'repo'
    build_dir = tmp_path / 'build'
    cache_dir = tmp_path / 'cache'
    repo_dir.mkdir()
    build_dir.mkdir()
    cache_dir.mkdir()

    # Ensure HAGENT_DOCKER is not set (local mode)
    monkeypatch.delenv('HAGENT_DOCKER', raising=False)
    monkeypatch.setenv('HAGENT_REPO_DIR', str(repo_dir))
    monkeypatch.setenv('HAGENT_BUILD_DIR', str(build_dir))
    monkeypatch.setenv('HAGENT_CACHE_DIR', str(cache_dir))

    builder = Builder()
    try:
        assert builder.runner.is_local_mode()
        assert 'HAGENT_DOCKER' not in os.environ
    finally:
        builder.cleanup()
