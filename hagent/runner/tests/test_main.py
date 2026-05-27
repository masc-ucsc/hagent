"""Tests for hagent.runner.__main__ CLI dispatch."""

import json
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

    def test_setup_at_tag(self, runner_toml, env_setup, capsys):
        """runner setup @tst1 --name echo"""
        rc = main(['setup', '@tst1', '--name', 'echo', '--config', runner_toml, '--cache-dir', env_setup])
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
        rc = main(['config', runner_toml])
        assert rc == 0
        captured = capsys.readouterr()
        data = json.loads(captured.out)
        names = [p['name'] for p in data]
        assert 'echo' in names

    def test_config_list_apis(self, runner_toml, capsys):
        rc = main(['config', runner_toml, '--name', 'echo'])
        assert rc == 0
        captured = capsys.readouterr()
        data = json.loads(captured.out)
        names = [a['name'] for a in data]
        assert 'hello' in names

    def test_config_missing_profile(self, runner_toml, capsys):
        rc = main(['config', runner_toml, '--name', 'nope'])
        assert rc == 1

    def test_config_missing_file(self, capsys):
        rc = main(['config', '/nonexistent.toml'])
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
        rc = main(['config', str(p)])
        assert rc == 0
        captured = capsys.readouterr()
        data = json.loads(captured.out)
        names = [p['name'] for p in data]
        assert 'adder' in names

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
        rc = main(['config', str(p), '--name', 'adder'])
        assert rc == 0
        captured = capsys.readouterr()
        data = json.loads(captured.out)
        names = [a['name'] for a in data]
        assert 'compile' in names
        assert 'sim' in names


class TestStatus:
    def test_status_help(self):
        assert main(['status', '--help']) == 0

    def test_status_tag(self, runner_toml, env_setup, capsys):
        main(['setup', 'tst1', '--name', 'echo', '--config', runner_toml, '--cache-dir', env_setup])
        capsys.readouterr()  # clear setup output
        rc = main(['status', 'tst1', '--cache-dir', env_setup])
        assert rc == 0
        captured = capsys.readouterr()
        data = json.loads(captured.out)
        assert data['tag'] == 'tst1'
        api_names = [a['name'] for a in data['apis']]
        assert 'hello' in api_names

    def test_status_at_tag(self, runner_toml, env_setup, capsys):
        main(['setup', 'tst1', '--name', 'echo', '--config', runner_toml, '--cache-dir', env_setup])
        rc = main(['status', '@tst1', '--cache-dir', env_setup])
        assert rc == 0

    def test_status_missing_tag(self, env_setup, capsys):
        rc = main(['status', 'nope', '--cache-dir', env_setup])
        assert rc == 1


class TestList:
    def test_list_help(self):
        assert main(['list', '--help']) == 0

    def test_list_tag(self, runner_toml, env_setup, capsys):
        main(['setup', 'tst1', '--name', 'echo', '--config', runner_toml, '--cache-dir', env_setup])
        capsys.readouterr()  # clear setup output
        rc = main(['list', 'tst1', '--cache-dir', env_setup])
        assert rc == 0
        captured = capsys.readouterr()
        data = json.loads(captured.out)
        names = [a['name'] for a in data]
        assert 'hello' in names

    def test_list_at_tag(self, runner_toml, env_setup, capsys):
        main(['setup', 'tst1', '--name', 'echo', '--config', runner_toml, '--cache-dir', env_setup])
        rc = main(['list', '@tst1', '--cache-dir', env_setup])
        assert rc == 0

    def test_list_missing_tag(self, env_setup):
        rc = main(['list', 'nope', '--cache-dir', env_setup])
        assert rc == 1


class TestDescribe:
    def test_describe_help(self):
        assert main(['describe', '--help']) == 0

    def test_describe_api(self, runner_toml, env_setup, capsys):
        main(['setup', 'tst1', '--name', 'echo', '--config', runner_toml, '--cache-dir', env_setup])
        capsys.readouterr()  # clear setup output
        rc = main(['describe', 'hello', 'tst1', '--cache-dir', env_setup])
        assert rc == 0
        captured = capsys.readouterr()
        data = json.loads(captured.out)
        assert data['name'] == 'hello'
        assert data['description'] == 'Say hello'
        assert data['command'] == 'echo hello'

    def test_describe_at_tag(self, runner_toml, env_setup, capsys):
        main(['setup', 'tst1', '--name', 'echo', '--config', runner_toml, '--cache-dir', env_setup])
        rc = main(['describe', 'hello', '@tst1', '--cache-dir', env_setup])
        assert rc == 0

    def test_describe_missing_api(self, runner_toml, env_setup):
        main(['setup', 'tst1', '--name', 'echo', '--config', runner_toml, '--cache-dir', env_setup])
        rc = main(['describe', 'nonexistent', 'tst1', '--cache-dir', env_setup])
        assert rc == 1


class TestRun:
    def test_run_help(self):
        assert main(['run', '--help']) == 0

    def test_run_missing_tag(self, env_setup, capsys):
        rc = main(['run', 'hello', 'nope', '--cache-dir', env_setup])
        assert rc == 1

    def test_run_shorthand_rejected(self, runner_toml, env_setup, capsys):
        main(['setup', 'tst1', '--name', 'echo', '--config', runner_toml, '--cache-dir', env_setup])
        rc = main(['run', 'tst1', '--cache-dir', env_setup])
        assert rc == 1

    def test_run_at_tag(self, runner_toml, env_setup):
        main(['setup', 'tst1', '--name', 'echo', '--config', runner_toml, '--cache-dir', env_setup])
        rc = main(['run', 'hello', '@tst1', '--cache-dir', env_setup])
        assert rc == 0
