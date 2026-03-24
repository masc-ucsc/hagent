"""Tests for hagent.runner.__main__ CLI dispatch."""

import os

import pytest

from hagent.runner.__main__ import main


@pytest.fixture
def runner_toml(tmp_path):
    """Create a minimal runner.toml."""
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
"""
    p = tmp_path / 'runner.toml'
    p.write_text(content)
    return str(p)


@pytest.fixture
def env_setup(tmp_path, monkeypatch):
    """Set up environment for CLI tests."""
    cache_dir = str(tmp_path / 'cache')
    os.makedirs(cache_dir, exist_ok=True)
    monkeypatch.setenv('HAGENT_CACHE_DIR', cache_dir)
    monkeypatch.setenv('HAGENT_REPO_DIR', str(tmp_path))
    monkeypatch.setenv('HAGENT_BUILD_DIR', str(tmp_path / 'build'))
    os.makedirs(str(tmp_path / 'build'), exist_ok=True)
    return cache_dir


class TestHelp:
    def test_no_args(self):
        assert main([]) == 0

    def test_help_flag(self):
        assert main(['--help']) == 0

    def test_help_command(self):
        assert main(['help']) == 0


class TestSetup:
    def test_setup_help(self):
        assert main(['setup', '--help']) == 0

    def test_setup_missing_name(self, runner_toml, env_setup, capsys):
        rc = main(['setup', 'tst1', '--config', runner_toml, '--cache-dir', env_setup])
        assert rc == 1

    def test_setup_basic(self, runner_toml, env_setup, capsys):
        rc = main(['setup', 'tst1', '--name', 'echo', '--config', runner_toml, '--cache-dir', env_setup])
        assert rc == 0
        captured = capsys.readouterr()
        assert 'setup tst1' in captured.out

    def test_setup_and_run(self, runner_toml, env_setup):
        rc = main(['setup', 'tst1', '--name', 'echo', '--config', runner_toml, '--cache-dir', env_setup])
        assert rc == 0
        rc = main(['run', 'hello', 'tst1', '--cache-dir', env_setup])
        assert rc == 0

    def test_setup_force(self, runner_toml, env_setup):
        main(['setup', 'tst1', '--name', 'echo', '--config', runner_toml, '--cache-dir', env_setup])
        rc = main(['setup', 'tst1', '--name', 'echo', '--config', runner_toml, '--cache-dir', env_setup, '--force'])
        assert rc == 0


class TestConfig:
    def test_config_help(self):
        assert main(['config', '--help']) == 0

    def test_config_list_profiles(self, runner_toml, capsys):
        rc = main(['config', runner_toml, '--list'])
        assert rc == 0
        captured = capsys.readouterr()
        assert 'echo' in captured.out
        assert 'Echo profile' in captured.out

    def test_config_list_apis(self, runner_toml, capsys):
        rc = main(['config', runner_toml, '--name', 'echo', '--list'])
        assert rc == 0
        captured = capsys.readouterr()
        assert 'hello' in captured.out
        assert 'Say hello' in captured.out

    def test_config_missing_profile(self, runner_toml, capsys):
        rc = main(['config', runner_toml, '--name', 'nope', '--list'])
        assert rc == 1

    def test_config_missing_file(self, capsys):
        rc = main(['config', '/nonexistent.toml', '--list'])
        assert rc == 1

    def test_config_no_list_flag(self, runner_toml, capsys):
        rc = main(['config', runner_toml])
        assert rc == 1

    def test_config_yaml(self, tmp_path, capsys):
        yaml_content = """\
profiles:
  - name: adder
    title: "4-bit Adder"
    apis:
      - name: compile
        description: "Compile Verilog"
        command: "iverilog adder.v"
"""
        p = tmp_path / 'hagent.yaml'
        p.write_text(yaml_content)
        rc = main(['config', str(p), '--list'])
        assert rc == 0
        captured = capsys.readouterr()
        assert 'adder' in captured.out

    def test_config_yaml_apis(self, tmp_path, capsys):
        yaml_content = """\
profiles:
  - name: adder
    title: "4-bit Adder"
    apis:
      - name: compile
        description: "Compile Verilog"
        command: "iverilog adder.v"
      - name: sim
        description: "Run simulation"
        command: "vvp out"
"""
        p = tmp_path / 'hagent.yaml'
        p.write_text(yaml_content)
        rc = main(['config', str(p), '--name', 'adder', '--list'])
        assert rc == 0
        captured = capsys.readouterr()
        assert 'compile' in captured.out
        assert 'sim' in captured.out


class TestStatus:
    def test_status_help(self):
        assert main(['status', '--help']) == 0

    def test_status_tag(self, runner_toml, env_setup, capsys):
        main(['setup', 'tst1', '--name', 'echo', '--config', runner_toml, '--cache-dir', env_setup])
        rc = main(['status', 'tst1', '--cache-dir', env_setup])
        assert rc == 0
        captured = capsys.readouterr()
        assert 'hello' in captured.out
        assert 'Say hello' in captured.out

    def test_status_missing_tag(self, env_setup, capsys):
        rc = main(['status', 'nope', '--cache-dir', env_setup])
        assert rc == 1


class TestRun:
    def test_run_help(self):
        assert main(['run', '--help']) == 0

    def test_run_missing_tag(self, env_setup, capsys):
        rc = main(['run', 'hello', 'nope', '--cache-dir', env_setup])
        assert rc == 1
