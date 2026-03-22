"""Tests for hagent.runner.commands."""

import os

import pytest

from hagent.runner.commands import run_command
from hagent.runner.tag import setup_tag


@pytest.fixture
def runner_toml(tmp_path):
    """Create a runner.toml with simple echo-based commands."""
    content = """\
[meta]
schema_version = 2

[default]
memory = 4

[echo]
description = "Echo profile"
[echo.api.hello]
description = "Say hello"
command = "echo hello"
cwd = "."
[echo.api.greet_tag]
description = "Greet with tag"
command = "echo hello {tag}"
cwd = "."
[echo.api.show_build]
description = "Show build dir"
command = "echo $HAGENT_BUILD_DIR"
cwd = "."
[echo.api.fail_cmd]
description = "A failing command"
command = "false"
cwd = "."
"""
    p = tmp_path / 'runner.toml'
    p.write_text(content)
    return str(p)


@pytest.fixture
def tag_setup(runner_toml, tmp_path, monkeypatch):
    """Setup a tag and return (tag_name, cache_dir)."""
    cache_dir = str(tmp_path / 'cache')
    os.makedirs(cache_dir, exist_ok=True)

    # Set env vars needed by Builder/PathManager
    monkeypatch.setenv('HAGENT_CACHE_DIR', cache_dir)
    monkeypatch.setenv('HAGENT_REPO_DIR', str(tmp_path))
    monkeypatch.setenv('HAGENT_BUILD_DIR', str(tmp_path / 'build'))
    os.makedirs(str(tmp_path / 'build'), exist_ok=True)

    setup_tag(runner_toml, 'tst1', 'echo', cache_dir=cache_dir)
    return 'tst1', cache_dir


class TestRunCommand:
    def test_echo(self, tag_setup):
        tag_name, cache_dir = tag_setup
        rc = run_command('hello', tag_name, cache_dir=cache_dir)
        assert rc == 0

    def test_fail(self, tag_setup):
        tag_name, cache_dir = tag_setup
        rc = run_command('fail_cmd', tag_name, cache_dir=cache_dir)
        assert rc != 0

    def test_log_written(self, tag_setup):
        tag_name, cache_dir = tag_setup
        run_command('hello', tag_name, cache_dir=cache_dir)
        log_path = os.path.join(cache_dir, 'tags', tag_name, 'logs', 'hello.log')
        assert os.path.exists(log_path)
        content = open(log_path).read()
        assert 'echo hello' in content

    def test_placeholder_expansion(self, tag_setup):
        tag_name, cache_dir = tag_setup
        rc = run_command('greet_tag', tag_name, cache_dir=cache_dir)
        assert rc == 0
        log_path = os.path.join(cache_dir, 'tags', tag_name, 'logs', 'greet_tag.log')
        content = open(log_path).read()
        assert 'tst1' in content

    def test_unknown_api(self, tag_setup):
        tag_name, cache_dir = tag_setup
        rc = run_command('nonexistent', tag_name, cache_dir=cache_dir)
        assert rc == 1

    def test_missing_tag(self, tmp_path):
        cache_dir = str(tmp_path / 'cache')
        os.makedirs(cache_dir, exist_ok=True)
        from hagent.runner.tag import TagError

        with pytest.raises(TagError):
            run_command('hello', 'nope', cache_dir=cache_dir)

    def test_path_style_tag(self, runner_toml, tmp_path, monkeypatch):
        """Use a path instead of a tag name to run a command."""
        cache_dir = str(tmp_path / 'cache')
        os.makedirs(cache_dir, exist_ok=True)
        monkeypatch.setenv('HAGENT_CACHE_DIR', cache_dir)
        monkeypatch.setenv('HAGENT_REPO_DIR', str(tmp_path))
        monkeypatch.setenv('HAGENT_BUILD_DIR', str(tmp_path / 'build'))
        os.makedirs(str(tmp_path / 'build'), exist_ok=True)

        tag_path = str(tmp_path / 'my_tag')
        setup_tag(runner_toml, tag_path, 'echo', cache_dir=cache_dir)
        # Run using the path directly
        rc = run_command('hello', tag_path)
        assert rc == 0
        assert os.path.exists(os.path.join(tag_path, 'logs', 'hello.log'))
