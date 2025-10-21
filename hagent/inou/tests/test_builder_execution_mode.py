"""Tests for Builder execution mode selection and overrides."""

import os

import pytest

from hagent.inou.builder import Builder
from hagent.inou.path_manager import PathManager


@pytest.fixture(autouse=True)
def reset_path_manager():
    """Ensure PathManager starts clean for each test."""
    PathManager.reset()
    yield
    PathManager.reset()


def test_builder_uses_environment_mode_by_default(monkeypatch):
    """Builder should respect HAGENT_EXECUTION_MODE when no docker override is provided."""
    monkeypatch.setenv('HAGENT_EXECUTION_MODE', 'docker')
    monkeypatch.setenv('HAGENT_DOCKER', 'mascucsc/hagent-builder:2025.09')

    builder = Builder()
    try:
        assert builder.runner.path_manager.is_docker_mode()
    finally:
        builder.cleanup()


def test_builder_explicit_docker_override(monkeypatch, tmp_path):
    """Providing docker_image should force docker mode even if environment is local."""
    repo_dir = tmp_path / 'repo'
    build_dir = tmp_path / 'build'
    cache_dir = tmp_path / 'cache'
    repo_dir.mkdir()
    build_dir.mkdir()
    cache_dir.mkdir()

    monkeypatch.setenv('HAGENT_EXECUTION_MODE', 'local')
    monkeypatch.setenv('HAGENT_REPO_DIR', str(repo_dir))
    monkeypatch.setenv('HAGENT_BUILD_DIR', str(build_dir))
    monkeypatch.setenv('HAGENT_CACHE_DIR', str(cache_dir))

    builder = Builder(docker_image='mascucsc/hagent-builder:2025.09')
    try:
        assert builder.runner.path_manager.is_docker_mode()
        assert os.environ['HAGENT_EXECUTION_MODE'] == 'docker'
    finally:
        builder.cleanup()

    assert os.environ['HAGENT_EXECUTION_MODE'] == 'local'


def test_builder_overrides_docker_image(monkeypatch):
    """Builder should temporarily override HAGENT_DOCKER when a custom image is provided."""
    monkeypatch.setenv('HAGENT_EXECUTION_MODE', 'docker')
    monkeypatch.setenv('HAGENT_DOCKER', 'mascucsc/hagent-simplechisel:2025.10')

    builder = Builder(docker_image='mascucsc/hagent-builder:2025.09')
    try:
        assert os.environ['HAGENT_DOCKER'] == 'mascucsc/hagent-builder:2025.09'
    finally:
        builder.cleanup()

    assert os.environ['HAGENT_DOCKER'] == 'mascucsc/hagent-simplechisel:2025.10'
