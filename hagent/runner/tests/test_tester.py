"""Tests for hagent.runner.tester."""

import os

import pytest

from hagent.runner.tag import get_tag_dir, setup_tag, validate_tag
from hagent.runner.tester import (
    TestResult,
    discover_tests,
    filter_tests,
    load_test_history,
    order_tests,
    run_tests,
    save_test_history,
)


@pytest.fixture
def runner_toml_with_tests(tmp_path):
    """Create a runner.toml with a tests section."""
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
[echo.tests]
run = "echo test_{test_name}"
list = ["test_a", "test_b", "test_c"]
"""
    p = tmp_path / 'runner.toml'
    p.write_text(content)
    return str(p)


@pytest.fixture
def runner_toml_with_build(tmp_path):
    """Create a runner.toml with build + tests."""
    content = """\
[meta]
schema_version = 2

[default]
memory = 4

[echo]
description = "Echo profile"
[echo.api.hello]
command = "echo hello"
cwd = "."
[echo.tests]
build = "echo building"
run = "echo test_{test_name}"
list = ["test_x", "test_y"]
"""
    p = tmp_path / 'runner.toml'
    p.write_text(content)
    return str(p)


@pytest.fixture
def runner_toml_with_list_cmd(tmp_path):
    """Create a runner.toml with dynamic test discovery."""
    content = """\
[meta]
schema_version = 2

[default]
memory = 4

[echo]
description = "Echo profile"
[echo.api.hello]
command = "echo hello"
cwd = "."
[echo.tests]
run = "echo test_{test_name}"
list_cmd = "echo test_dyn1; echo test_dyn2"
"""
    p = tmp_path / 'runner.toml'
    p.write_text(content)
    return str(p)


@pytest.fixture
def runner_toml_no_tests(tmp_path):
    """Create a runner.toml without tests."""
    content = """\
[meta]
schema_version = 2

[default]
memory = 4

[echo]
description = "Echo profile"
[echo.api.hello]
command = "echo hello"
cwd = "."
"""
    p = tmp_path / 'runner.toml'
    p.write_text(content)
    return str(p)


@pytest.fixture
def cache_dir(tmp_path):
    d = tmp_path / 'cache'
    d.mkdir()
    return str(d)


@pytest.fixture
def env_setup(tmp_path, monkeypatch, cache_dir):
    """Set HAGENT_* env vars needed by Builder/PathManager."""
    monkeypatch.setenv('HAGENT_CACHE_DIR', cache_dir)
    monkeypatch.setenv('HAGENT_REPO_DIR', str(tmp_path))
    monkeypatch.setenv('HAGENT_BUILD_DIR', str(tmp_path / 'build'))
    os.makedirs(str(tmp_path / 'build'), exist_ok=True)
    return cache_dir


class TestFilterTests:
    def test_no_pattern(self):
        assert filter_tests(['a', 'b', 'c'], None) == ['a', 'b', 'c']

    def test_glob_pattern(self):
        assert filter_tests(['test_a', 'test_b', 'foo_c'], 'test_*') == ['test_a', 'test_b']

    def test_no_match(self):
        assert filter_tests(['a', 'b'], 'xyz*') == []


class TestOrderTests:
    def test_failed_first(self):
        history = {
            'test_a': {'status': 'PASS'},
            'test_b': {'status': 'FAIL'},
            'test_c': {'status': 'PASS'},
        }
        ordered = order_tests(['test_a', 'test_b', 'test_c'], history)
        assert ordered[0] == 'test_b'

    def test_no_history(self):
        ordered = order_tests(['test_a', 'test_b'], {})
        assert ordered == ['test_a', 'test_b']


class TestTestHistory:
    def test_save_and_load(self, tmp_path):
        tag_dir = str(tmp_path / 'tag1')
        os.makedirs(tag_dir)
        history = {
            'test_a': {'status': 'PASS', 'duration': 1.5},
            'test_b': {'status': 'FAIL', 'duration': 3.2},
        }
        save_test_history(tag_dir, history)
        loaded = load_test_history(tag_dir)
        assert loaded['test_a']['status'] == 'PASS'
        assert loaded['test_b']['status'] == 'FAIL'

    def test_load_missing(self, tmp_path):
        assert load_test_history(str(tmp_path / 'nodir')) == {}


class TestDiscoverTests:
    def test_static_list(self, runner_toml_with_tests, cache_dir):
        setup_tag(runner_toml_with_tests, 'tst1', 'echo', cache_dir=cache_dir)
        tag_dir = get_tag_dir('tst1', cache_dir)
        tag_config = validate_tag(tag_dir)
        env = os.environ.copy()
        tests = discover_tests(tag_config, tag_dir, env)
        assert tests == ['test_a', 'test_b', 'test_c']

    def test_list_cmd(self, runner_toml_with_list_cmd, cache_dir):
        setup_tag(runner_toml_with_list_cmd, 'tst1', 'echo', cache_dir=cache_dir)
        tag_dir = get_tag_dir('tst1', cache_dir)
        tag_config = validate_tag(tag_dir)
        env = os.environ.copy()
        tests = discover_tests(tag_config, tag_dir, env)
        assert tests == ['test_dyn1', 'test_dyn2']

    def test_static_list_wins_over_list_cmd(self, tmp_path, cache_dir):
        content = """\
[meta]
schema_version = 2

[default]
memory = 4

[echo]
description = "Echo"
[echo.api.hello]
command = "echo hi"
cwd = "."
[echo.tests]
run = "echo {test_name}"
list = ["static_test"]
list_cmd = "echo dynamic_test"
"""
        rt = str(tmp_path / 'runner.toml')
        (tmp_path / 'runner.toml').write_text(content)
        setup_tag(rt, 'tst1', 'echo', cache_dir=cache_dir)
        tag_dir = get_tag_dir('tst1', cache_dir)
        tag_config = validate_tag(tag_dir)
        env = os.environ.copy()
        tests = discover_tests(tag_config, tag_dir, env)
        assert tests == ['static_test']

    def test_no_tests_section(self, runner_toml_no_tests, cache_dir):
        setup_tag(runner_toml_no_tests, 'tst1', 'echo', cache_dir=cache_dir)
        tag_dir = get_tag_dir('tst1', cache_dir)
        tag_config = validate_tag(tag_dir)
        env = os.environ.copy()
        tests = discover_tests(tag_config, tag_dir, env)
        assert tests == []


class TestRunTests:
    def test_list_only(self, runner_toml_with_tests, cache_dir, capsys):
        setup_tag(runner_toml_with_tests, 'tst1', 'echo', cache_dir=cache_dir)
        rc = run_tests('tst1', cache_dir=cache_dir, list_only=True)
        assert rc == 0
        out = capsys.readouterr().out
        assert 'test_a' in out
        assert 'test_b' in out
        assert 'test_c' in out

    def test_no_tests_section(self, runner_toml_no_tests, cache_dir):
        setup_tag(runner_toml_no_tests, 'tst1', 'echo', cache_dir=cache_dir)
        rc = run_tests('tst1', cache_dir=cache_dir)
        assert rc == 1

    def test_filter_no_match(self, runner_toml_with_tests, cache_dir):
        setup_tag(runner_toml_with_tests, 'tst1', 'echo', cache_dir=cache_dir)
        rc = run_tests('tst1', cache_dir=cache_dir, filter_pattern='xyz*')
        assert rc == 1

    def test_run_all_pass(self, runner_toml_with_tests, env_setup):
        cache_dir = env_setup
        setup_tag(runner_toml_with_tests, 'tst1', 'echo', cache_dir=cache_dir)
        rc = run_tests('tst1', cache_dir=cache_dir, jobs=1, quiet=True)
        assert rc == 0
        tag_dir = get_tag_dir('tst1', cache_dir)
        history = load_test_history(tag_dir)
        assert 'test_a' in history
        assert history['test_a']['status'] == 'PASS'

    def test_run_with_build(self, runner_toml_with_build, env_setup):
        cache_dir = env_setup
        setup_tag(runner_toml_with_build, 'tst1', 'echo', cache_dir=cache_dir)
        rc = run_tests('tst1', cache_dir=cache_dir, jobs=1, quiet=True)
        assert rc == 0
        tag_dir = get_tag_dir('tst1', cache_dir)
        assert os.path.exists(os.path.join(tag_dir, 'logs', 'test_build.log'))

    def test_run_parallel(self, runner_toml_with_tests, env_setup):
        cache_dir = env_setup
        setup_tag(runner_toml_with_tests, 'tst1', 'echo', cache_dir=cache_dir)
        rc = run_tests('tst1', cache_dir=cache_dir, jobs=3, quiet=True)
        assert rc == 0

    def test_filter(self, runner_toml_with_tests, env_setup):
        cache_dir = env_setup
        setup_tag(runner_toml_with_tests, 'tst1', 'echo', cache_dir=cache_dir)
        rc = run_tests('tst1', cache_dir=cache_dir, filter_pattern='test_a', jobs=1, quiet=True)
        assert rc == 0
        tag_dir = get_tag_dir('tst1', cache_dir)
        history = load_test_history(tag_dir)
        assert 'test_a' in history
        assert 'test_b' not in history

    def test_fail_fast(self, tmp_path, env_setup):
        """Test --fail-fast stops after first failure."""
        cache_dir = env_setup
        content = """\
[meta]
schema_version = 2

[default]
memory = 4

[fail]
description = "Failing profile"
[fail.api.hello]
command = "echo hi"
cwd = "."
[fail.tests]
run = "false"
list = ["test_1", "test_2", "test_3"]
"""
        rt = str(tmp_path / 'runner.toml')
        (tmp_path / 'runner.toml').write_text(content)
        setup_tag(rt, 'tst1', 'fail', cache_dir=cache_dir)
        rc = run_tests('tst1', cache_dir=cache_dir, fail_fast=True, jobs=1, quiet=True)
        assert rc == 1
        tag_dir = get_tag_dir('tst1', cache_dir)
        history = load_test_history(tag_dir)
        assert len(history) == 1

    def test_failed_first_ordering(self, runner_toml_with_tests, env_setup):
        """Verify previously failed tests run first."""
        cache_dir = env_setup
        setup_tag(runner_toml_with_tests, 'tst1', 'echo', cache_dir=cache_dir)
        tag_dir = get_tag_dir('tst1', cache_dir)
        save_test_history(tag_dir, {
            'test_c': {'status': 'FAIL', 'duration': 1.0},
            'test_a': {'status': 'PASS', 'duration': 0.5},
        })
        rc = run_tests('tst1', cache_dir=cache_dir, jobs=1, quiet=True)
        assert rc == 0
        history = load_test_history(tag_dir)
        assert history['test_c']['status'] == 'PASS'
