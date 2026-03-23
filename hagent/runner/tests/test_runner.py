"""Integration tests for the runner CLI using demo_runner.toml.

These tests exercise the full runner workflow end-to-end through the
CLI entry point (main()), mirroring the sample commands a user would
type.  They serve as both a demo and a regression test.
"""

import os
from pathlib import Path

import pytest
import tomlkit

from hagent.runner.__main__ import main

# Path to demo_runner.toml in the same directory as this test
DEMO_TOML = str(Path(__file__).resolve().parent / 'demo_runner.toml')


@pytest.fixture
def runner_env(tmp_path, monkeypatch):
    """Set up a clean environment for runner integration tests.

    Creates temp dirs for cache, repo, and build, sets HAGENT_* env vars,
    and returns (cache_dir, repo_dir, build_dir) paths.
    """
    cache_dir = str(tmp_path / 'cache')
    repo_dir = str(tmp_path / 'repo')
    build_dir = str(tmp_path / 'build')
    os.makedirs(cache_dir)
    os.makedirs(repo_dir)
    os.makedirs(build_dir)

    # Put some files in repo_dir so ls_repo has something to list
    (tmp_path / 'repo' / 'README.md').write_text('hello')
    (tmp_path / 'repo' / 'src').mkdir()
    (tmp_path / 'repo' / 'src' / 'main.py').write_text('pass')

    monkeypatch.setenv('HAGENT_CACHE_DIR', cache_dir)
    monkeypatch.setenv('HAGENT_REPO_DIR', repo_dir)
    monkeypatch.setenv('HAGENT_BUILD_DIR', build_dir)

    return cache_dir, repo_dir, build_dir


# ── runner config ────────────────────────────────────────────────

class TestConfig:
    def test_list_profiles(self, runner_env, capsys):
        """runner config demo_runner.toml --list"""
        rc = main(['config', DEMO_TOML, '--list'])
        assert rc == 0
        out = capsys.readouterr().out
        assert 'demo_local' in out
        assert 'demo' in out
        assert 'demo_docker' in out

    def test_list_apis_demo_local(self, runner_env, capsys):
        """runner config demo_runner.toml --name demo_local --list"""
        rc = main(['config', DEMO_TOML, '--name', 'demo_local', '--list'])
        assert rc == 0
        out = capsys.readouterr().out
        for api in ['hello', 'touch', 'check', 'ls_repo', 'env', 'write_result']:
            assert api in out

    def test_list_apis_demo(self, runner_env, capsys):
        """runner config demo_runner.toml --name demo --list"""
        rc = main(['config', DEMO_TOML, '--name', 'demo', '--list'])
        assert rc == 0
        out = capsys.readouterr().out
        assert 'hello' in out

    def test_list_apis_demo_docker(self, runner_env, capsys):
        """runner config demo_runner.toml --name demo_docker --list"""
        rc = main(['config', DEMO_TOML, '--name', 'demo_docker', '--list'])
        assert rc == 0
        out = capsys.readouterr().out
        # demo_docker inherits all default APIs
        for api in ['hello', 'touch', 'check', 'ls_repo', 'env', 'write_result']:
            assert api in out

    def test_bad_profile(self, runner_env):
        """runner config demo_runner.toml --name nonexistent --list"""
        rc = main(['config', DEMO_TOML, '--name', 'nonexistent', '--list'])
        assert rc == 1


# ── runner setup ─────────────────────────────────────────────────

class TestSetup:
    def test_setup_demo_local(self, runner_env, capsys):
        """runner setup d1 --name demo_local --config demo_runner.toml"""
        cache_dir, _, _ = runner_env
        rc = main(['setup', 'd1', '--name', 'demo_local', '--config', DEMO_TOML])
        assert rc == 0
        out = capsys.readouterr().out
        assert 'd1' in out
        assert os.path.exists(os.path.join(cache_dir, 'tags', 'd1', 'config.toml'))

    def test_setup_demo(self, runner_env, capsys):
        """runner setup d2 --name demo --config demo_runner.toml"""
        cache_dir, _, _ = runner_env
        rc = main(['setup', 'd2', '--name', 'demo', '--config', DEMO_TOML])
        assert rc == 0
        assert os.path.exists(os.path.join(cache_dir, 'tags', 'd2', 'config.toml'))

    def test_setup_duplicate_fails(self, runner_env):
        """Setup same tag twice without --force or --reuse fails."""
        main(['setup', 'd1', '--name', 'demo_local', '--config', DEMO_TOML])
        rc = main(['setup', 'd1', '--name', 'demo_local', '--config', DEMO_TOML])
        assert rc == 1

    def test_setup_reuse(self, runner_env):
        """runner setup d1 --name demo_local --config ... --reuse"""
        main(['setup', 'd1', '--name', 'demo_local', '--config', DEMO_TOML])
        rc = main(['setup', 'd1', '--name', 'demo_local', '--config', DEMO_TOML, '--reuse'])
        assert rc == 0

    def test_setup_reuse_mismatch(self, runner_env):
        """--reuse with different profile fails."""
        main(['setup', 'd1', '--name', 'demo_local', '--config', DEMO_TOML])
        rc = main(['setup', 'd1', '--name', 'demo', '--config', DEMO_TOML, '--reuse'])
        assert rc == 1

    def test_setup_force(self, runner_env):
        """runner setup d1 --name demo --config ... --force"""
        main(['setup', 'd1', '--name', 'demo_local', '--config', DEMO_TOML])
        rc = main(['setup', 'd1', '--name', 'demo', '--config', DEMO_TOML, '--force'])
        assert rc == 0

    def test_setup_demo_docker(self, runner_env):
        """runner setup d3 --name demo_docker --config demo_runner.toml"""
        cache_dir, _, _ = runner_env
        rc = main(['setup', 'd3', '--name', 'demo_docker', '--config', DEMO_TOML])
        assert rc == 0
        cfg_path = os.path.join(cache_dir, 'tags', 'd3', 'config.toml')
        assert os.path.exists(cfg_path)
        with open(cfg_path) as f:
            cfg = tomlkit.parse(f.read())
        assert cfg['docker'] == 'mascucsc/hagent-builder:2026.02'

    def test_setup_local_has_empty_docker(self, runner_env):
        """demo_local tag config should have docker = '' (force local)."""
        cache_dir, _, _ = runner_env
        main(['setup', 'd1', '--name', 'demo_local', '--config', DEMO_TOML])
        cfg_path = os.path.join(cache_dir, 'tags', 'd1', 'config.toml')
        with open(cfg_path) as f:
            cfg = tomlkit.parse(f.read())
        assert cfg['docker'] == ''

    def test_setup_demo_no_docker_section(self, runner_env):
        """demo tag config should have no docker section (inherits env)."""
        cache_dir, _, _ = runner_env
        main(['setup', 'd2', '--name', 'demo', '--config', DEMO_TOML])
        cfg_path = os.path.join(cache_dir, 'tags', 'd2', 'config.toml')
        with open(cfg_path) as f:
            cfg = tomlkit.parse(f.read())
        assert 'docker' not in cfg

    def test_setup_path_tag(self, runner_env, tmp_path):
        """runner setup ./my_tag --name demo_local --config ..."""
        tag_path = str(tmp_path / 'my_tag')
        rc = main(['setup', tag_path, '--name', 'demo_local', '--config', DEMO_TOML])
        assert rc == 0
        assert os.path.exists(os.path.join(tag_path, 'config.toml'))
        assert os.path.isdir(os.path.join(tag_path, 'logs'))


# ── runner list ──────────────────────────────────────────────────

class TestList:
    def test_list_tag_apis(self, runner_env, capsys):
        """runner list d1"""
        main(['setup', 'd1', '--name', 'demo_local', '--config', DEMO_TOML])
        rc = main(['list', 'd1'])
        assert rc == 0
        out = capsys.readouterr().out
        for api in ['hello', 'touch', 'check', 'ls_repo', 'env', 'write_result']:
            assert api in out

    def test_list_missing_tag(self, runner_env):
        """runner list nonexistent"""
        rc = main(['list', 'nonexistent'])
        assert rc == 1


# ── runner <api> (command execution) ─────────────────────────────

class TestRunAPIs:
    @pytest.fixture(autouse=True)
    def _setup_tag(self, runner_env):
        """Create the d1 tag before each test in this class."""
        self.cache_dir, self.repo_dir, self.build_dir = runner_env
        main(['setup', 'd1', '--name', 'demo_local', '--config', DEMO_TOML])

    def test_hello(self):
        """runner hello d1"""
        rc = main(['hello', 'd1'])
        assert rc == 0

    def test_hello_log(self):
        """hello command writes a log file."""
        main(['hello', 'd1'])
        log = os.path.join(self.cache_dir, 'tags', 'd1', 'logs', 'hello.log')
        assert os.path.exists(log)
        content = open(log).read()
        assert 'hello from d1' in content

    def test_touch_and_check(self):
        """runner touch d1 && runner check d1"""
        rc = main(['touch', 'd1'])
        assert rc == 0
        marker = os.path.join(self.cache_dir, 'tags', 'd1', 'marker.txt')
        assert os.path.exists(marker)

        rc = main(['check', 'd1'])
        assert rc == 0

    def test_ls_repo(self):
        """runner ls_repo d1"""
        rc = main(['ls_repo', 'd1'])
        assert rc == 0
        log = os.path.join(self.cache_dir, 'tags', 'd1', 'logs', 'ls_repo.log')
        content = open(log).read()
        assert 'README.md' in content

    def test_env(self):
        """runner env d1 — checks HAGENT_* vars are present."""
        rc = main(['env', 'd1'])
        assert rc == 0
        log = os.path.join(self.cache_dir, 'tags', 'd1', 'logs', 'env.log')
        content = open(log).read()
        assert 'REPO=' in content
        assert 'BUILD=' in content
        assert 'CACHE=' in content

    def test_write_result(self):
        """runner write_result d1"""
        rc = main(['write_result', 'd1'])
        assert rc == 0
        output = os.path.join(self.cache_dir, 'tags', 'd1', 'output.txt')
        assert os.path.exists(output)
        assert 'result from d1' in open(output).read()

    def test_unknown_api(self):
        """runner nonexistent d1 — should fail gracefully."""
        rc = main(['nonexistent', 'd1'])
        assert rc == 1

    def test_verbose(self):
        """runner hello d1 --verbose"""
        rc = main(['hello', 'd1', '--verbose'])
        assert rc == 0


# ── runner test ──────────────────────────────────────────────────

class TestRunTests:
    @pytest.fixture(autouse=True)
    def _setup_tag(self, runner_env):
        self.cache_dir, self.repo_dir, self.build_dir = runner_env
        main(['setup', 'd1', '--name', 'demo_local', '--config', DEMO_TOML])

    def test_list_tests(self, capsys):
        """runner test d1 --list"""
        rc = main(['test', 'd1', '--list'])
        assert rc == 0
        out = capsys.readouterr().out
        assert 'test_fast' in out
        assert 'test_medium' in out
        assert 'test_slow' in out

    def test_run_all(self):
        """runner test d1"""
        rc = main(['test', 'd1'])
        assert rc == 0
        # History should be written
        history_path = os.path.join(self.cache_dir, 'tags', 'd1', 'tests.toml')
        assert os.path.exists(history_path)

    def test_run_parallel(self):
        """runner test d1 --jobs 3"""
        rc = main(['test', 'd1', '--jobs', '3'])
        assert rc == 0

    def test_run_sequential(self):
        """runner test d1 --jobs 1"""
        rc = main(['test', 'd1', '--jobs', '1'])
        assert rc == 0

    def test_filter(self):
        """runner test d1 --filter test_fast"""
        rc = main(['test', 'd1', '--filter', 'test_fast'])
        assert rc == 0
        # Only test_fast log should exist
        logs_dir = os.path.join(self.cache_dir, 'tags', 'd1', 'logs')
        assert os.path.exists(os.path.join(logs_dir, 'test_test_fast.log'))

    def test_filter_glob(self):
        """runner test d1 --filter 'test_*ow'"""
        rc = main(['test', 'd1', '--filter', 'test_*ow'])
        assert rc == 0

    def test_filter_no_match(self):
        """runner test d1 --filter xyz"""
        rc = main(['test', 'd1', '--filter', 'xyz'])
        assert rc == 1

    def test_quiet(self):
        """runner test d1 --quiet"""
        rc = main(['test', 'd1', '--quiet'])
        assert rc == 0


# ── path-style tags ──────────────────────────────────────────────

class TestPathTag:
    def test_full_workflow(self, runner_env, tmp_path):
        """Setup, run, and test using a path-style tag."""
        tag_path = str(tmp_path / 'my_build')

        rc = main(['setup', tag_path, '--name', 'demo_local', '--config', DEMO_TOML])
        assert rc == 0

        rc = main(['hello', tag_path])
        assert rc == 0
        assert os.path.exists(os.path.join(tag_path, 'logs', 'hello.log'))

        rc = main(['touch', tag_path])
        assert rc == 0
        assert os.path.exists(os.path.join(tag_path, 'marker.txt'))

        rc = main(['test', tag_path, '--list'])
        assert rc == 0


# ── help ─────────────────────────────────────────────────────────

class TestHelp:
    def test_help(self, capsys):
        """runner --help"""
        rc = main(['--help'])
        assert rc == 0
        out = capsys.readouterr().out
        assert 'setup' in out
        assert 'test' in out

    def test_setup_help(self, capsys):
        """runner setup --help"""
        rc = main(['setup', '--help'])
        assert rc == 0

    def test_test_help(self, capsys):
        """runner test --help"""
        rc = main(['test', '--help'])
        assert rc == 0

    def test_config_help(self, capsys):
        """runner config --help"""
        rc = main(['config', '--help'])
        assert rc == 0
