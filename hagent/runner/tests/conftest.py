"""Shared fixtures for runner tests."""

import pytest


@pytest.fixture(autouse=True)
def _clean_hagent_env(monkeypatch):
    """Remove HAGENT_* variables that may leak from the user's shell.

    Individual tests set only the vars they need via monkeypatch.setenv().
    Without this, a stray HAGENT_DOCKER in the terminal can cause Builder
    to attempt Docker execution when tests expect local mode.
    """
    for var in ('HAGENT_DOCKER', 'HAGENT_CACHE_DIR', 'HAGENT_REPO_DIR', 'HAGENT_BUILD_DIR'):
        monkeypatch.delenv(var, raising=False)
