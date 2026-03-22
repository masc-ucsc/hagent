"""Tests for hagent.runner.tag."""

import os
from pathlib import Path

import pytest

from hagent.runner.tag import TagError, get_tag_dir, resolve_input_dirs, setup_tag, tag_matches, validate_tag


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

[gcd]
description = "GCD profile"
[gcd.api.compile]
description = "Compile"
command = "echo compile"
cwd = "."
"""
    p = tmp_path / 'runner.toml'
    p.write_text(content)
    return str(p)


@pytest.fixture
def cache_dir(tmp_path):
    """Provide a cache directory."""
    d = tmp_path / 'cache'
    d.mkdir()
    return str(d)


class TestGetTagDir:
    def test_explicit_cache(self):
        assert get_tag_dir('tst1', '/tmp/cache') == '/tmp/cache/tags/tst1'

    def test_env_cache(self, monkeypatch):
        monkeypatch.setenv('HAGENT_CACHE_DIR', '/env/cache')
        assert get_tag_dir('tst1') == '/env/cache/tags/tst1'

    def test_no_cache(self, monkeypatch):
        monkeypatch.delenv('HAGENT_CACHE_DIR', raising=False)
        with pytest.raises(TagError, match='HAGENT_CACHE_DIR'):
            get_tag_dir('tst1')

    def test_path_with_slash(self, tmp_path):
        d = tmp_path / 'my_tag'
        d.mkdir()
        assert get_tag_dir(str(d)) == str(d.resolve())

    def test_relative_path(self, tmp_path, monkeypatch):
        monkeypatch.chdir(tmp_path)
        d = tmp_path / 'sub' / 'tag'
        d.mkdir(parents=True)
        assert get_tag_dir('./sub/tag') == str(d.resolve())

    def test_dot_path(self, tmp_path, monkeypatch):
        monkeypatch.chdir(tmp_path)
        assert get_tag_dir('.') == str(tmp_path.resolve())


class TestSetupTag:
    def test_basic_setup(self, runner_toml, cache_dir):
        toml_path = setup_tag(runner_toml, 'tst1', 'echo', cache_dir=cache_dir)
        assert os.path.exists(toml_path)
        assert 'config.toml' in toml_path
        # logs dir should exist
        tag_dir = os.path.dirname(toml_path)
        assert os.path.isdir(os.path.join(tag_dir, 'logs'))

    def test_already_exists_error(self, runner_toml, cache_dir):
        setup_tag(runner_toml, 'tst1', 'echo', cache_dir=cache_dir)
        with pytest.raises(TagError, match='already exists'):
            setup_tag(runner_toml, 'tst1', 'echo', cache_dir=cache_dir)

    def test_force_overwrites(self, runner_toml, cache_dir):
        setup_tag(runner_toml, 'tst1', 'echo', cache_dir=cache_dir)
        toml_path = setup_tag(runner_toml, 'tst1', 'gcd', cache_dir=cache_dir, force=True)
        config = validate_tag(os.path.dirname(toml_path))
        assert config['meta']['profile_name'] == 'gcd'

    def test_reuse_matching(self, runner_toml, cache_dir):
        setup_tag(runner_toml, 'tst1', 'echo', cache_dir=cache_dir)
        toml_path = setup_tag(runner_toml, 'tst1', 'echo', cache_dir=cache_dir, reuse=True)
        assert os.path.exists(toml_path)

    def test_reuse_mismatch(self, runner_toml, cache_dir):
        setup_tag(runner_toml, 'tst1', 'echo', cache_dir=cache_dir)
        with pytest.raises(TagError, match='different config'):
            setup_tag(runner_toml, 'tst1', 'gcd', cache_dir=cache_dir, reuse=True)

    def test_with_inputs(self, runner_toml, cache_dir):
        # First create the input tag
        setup_tag(runner_toml, 'src_tag', 'echo', cache_dir=cache_dir)
        # Now create a tag referencing it
        toml_path = setup_tag(
            runner_toml, 'tst1', 'gcd', cache_dir=cache_dir, inputs={'orig': 'src_tag'}
        )
        config = validate_tag(os.path.dirname(toml_path))
        assert config['inputs']['orig'] == 'src_tag'

    def test_with_overrides(self, runner_toml, cache_dir):
        toml_path = setup_tag(
            runner_toml, 'tst1', 'echo', cache_dir=cache_dir, overrides={'memory': '8'}
        )
        config = validate_tag(os.path.dirname(toml_path))
        assert config['memory'] == '8'

    def test_path_as_tag(self, runner_toml, cache_dir, tmp_path):
        custom = str(tmp_path / 'my_tag')
        toml_path = setup_tag(runner_toml, custom, 'echo', cache_dir=cache_dir)
        # config.toml should be in the custom dir, not in cache/tags/
        assert toml_path == os.path.join(custom, 'config.toml')
        assert os.path.exists(toml_path)
        assert os.path.isdir(os.path.join(custom, 'logs'))

    def test_path_tag_dir_in_config(self, runner_toml, cache_dir, tmp_path):
        custom = str(tmp_path / 'my_tag')
        setup_tag(runner_toml, custom, 'echo', cache_dir=cache_dir)
        config = validate_tag(custom)
        assert config['tag']['dir'] == custom

    def test_path_tag_get_resolves(self, runner_toml, cache_dir, tmp_path):
        custom = str(tmp_path / 'my_tag')
        setup_tag(runner_toml, custom, 'echo', cache_dir=cache_dir)
        # get_tag_dir with path returns resolved path
        resolved = get_tag_dir(custom)
        assert resolved == str(Path(custom).resolve())

    def test_path_tag_force(self, runner_toml, cache_dir, tmp_path):
        custom = str(tmp_path / 'my_tag')
        setup_tag(runner_toml, custom, 'echo', cache_dir=cache_dir)
        # Force should work and keep non-tag files
        (tmp_path / 'my_tag' / 'artifact.v').write_text('module x; endmodule')
        setup_tag(runner_toml, custom, 'gcd', cache_dir=cache_dir, force=True)
        config = validate_tag(custom)
        assert config['meta']['profile_name'] == 'gcd'
        # Artifact should survive --force
        assert (tmp_path / 'my_tag' / 'artifact.v').exists()

    def test_name_rejects_dots(self, runner_toml, cache_dir):
        with pytest.raises(TagError, match='must not contain'):
            setup_tag(runner_toml, 'bad.name', 'echo', cache_dir=cache_dir)

    def test_missing_profile(self, runner_toml, cache_dir):
        with pytest.raises(ValueError, match='no profile'):
            setup_tag(runner_toml, 'tst1', 'nonexistent', cache_dir=cache_dir)


class TestValidateTag:
    def test_valid(self, runner_toml, cache_dir):
        setup_tag(runner_toml, 'tst1', 'echo', cache_dir=cache_dir)
        tag_dir = get_tag_dir('tst1', cache_dir)
        config = validate_tag(tag_dir)
        assert 'meta' in config

    def test_missing_dir(self, cache_dir):
        with pytest.raises(TagError, match='does not exist'):
            validate_tag(os.path.join(cache_dir, 'tags', 'nope'))

    def test_missing_config(self, cache_dir):
        tag_dir = os.path.join(cache_dir, 'tags', 'empty')
        os.makedirs(tag_dir)
        with pytest.raises(TagError, match='no config.toml'):
            validate_tag(tag_dir)


class TestResolveInputDirs:
    def test_valid_input(self, runner_toml, cache_dir):
        setup_tag(runner_toml, 'src', 'echo', cache_dir=cache_dir)
        dirs = resolve_input_dirs({'orig': 'src'}, cache_dir)
        assert 'orig' in dirs
        assert dirs['orig'].endswith('tags/src')

    def test_missing_input(self, cache_dir):
        with pytest.raises(TagError, match='does not exist'):
            resolve_input_dirs({'orig': 'nope'}, cache_dir)


class TestTagMatches:
    def test_match(self):
        config = {'meta': {'profile_name': 'echo'}, 'inputs': {}}
        assert tag_matches(config, 'echo', None)

    def test_mismatch_profile(self):
        config = {'meta': {'profile_name': 'echo'}}
        assert not tag_matches(config, 'gcd', None)

    def test_mismatch_inputs(self):
        config = {'meta': {'profile_name': 'echo'}, 'inputs': {'a': 'b'}}
        assert not tag_matches(config, 'echo', {'a': 'c'})
