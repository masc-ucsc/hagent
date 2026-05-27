"""Tests for hagent.runner.config."""

import pytest

from hagent.runner.config import (
    apply_overrides,
    build_context,
    build_env,
    get_api_config,
    get_docker_image,
    list_api_names,
    load_runner_toml,
    load_tag_config,
    merge_default_and_profile,
    resolve_options,
    resolve_placeholders,
)


@pytest.fixture
def sample_runner_toml(tmp_path):
    """Create a minimal runner.toml for testing."""
    content = """\
[meta]
schema_version = 2

[default]
memory = 4
[default.environment]
PATH = "$PATH:/usr/local/bin"
[default.api.lint]
description = "Run linting"
command = "echo lint"
cwd = "$HAGENT_REPO_DIR"

[echo]
description = "Echo profile"
[echo.api.build_dir]
description = "Echo build dir"
command = "echo $HAGENT_BUILD_DIR"
cwd = "$HAGENT_REPO_DIR"

[gcd]
description = "GCD profile"
[gcd.api.compile]
description = "Compile GCD"
command = 'sbt "runMain gcd.GCD"'
cwd = "$HAGENT_REPO_DIR"
[gcd.api.synth_asic]
description = "Synth GCD"
command = "/scripts/synth.py --tag {tag} --top {top}"
cwd = "$HAGENT_BUILD_DIR"
[[gcd.api.synth_asic.options]]
name = "top"
description = "Top module"
format = "{value}"
default = "GCD"
"""
    p = tmp_path / 'runner.toml'
    p.write_text(content)
    return str(p)


@pytest.fixture
def sample_tag_dir(tmp_path):
    """Create a minimal tag directory with runner.toml."""
    tag_dir = tmp_path / 'tags' / 'tst1'
    tag_dir.mkdir(parents=True)
    content = """\
[meta]
schema_version = 1
profile_name = "echo"

[tag]
dir = "/tmp/out"

[environment]
FOO = "bar"

[api.build_dir]
description = "Echo build dir"
command = "echo $HAGENT_BUILD_DIR"
cwd = "$HAGENT_REPO_DIR"

[api.greet]
description = "Greet"
command = "echo hello {tag}"
"""
    (tag_dir / 'runner.toml').write_text(content)
    return str(tag_dir)


class TestLoadRunnerToml:
    def test_load_valid(self, sample_runner_toml):
        data = load_runner_toml(sample_runner_toml)
        assert 'meta' in data
        assert 'echo' in data
        assert 'gcd' in data

    def test_load_missing(self, tmp_path):
        with pytest.raises(FileNotFoundError):
            load_runner_toml(str(tmp_path / 'nonexistent.toml'))


class TestLoadTagConfig:
    def test_load_valid(self, sample_tag_dir):
        data = load_tag_config(sample_tag_dir)
        assert data['meta']['profile_name'] == 'echo'

    def test_load_missing(self, tmp_path):
        with pytest.raises(FileNotFoundError):
            load_tag_config(str(tmp_path / 'no_such_dir'))


class TestMergeDefaultAndProfile:
    def test_basic_merge(self, sample_runner_toml):
        data = load_runner_toml(sample_runner_toml)
        merged = merge_default_and_profile(data, 'echo')
        assert merged['memory'] == 4
        assert 'build_dir' in merged.get('api', {})
        # default lint should be inherited
        assert 'lint' in merged.get('api', {})

    def test_profile_override(self, sample_runner_toml):
        data = load_runner_toml(sample_runner_toml)
        merged = merge_default_and_profile(data, 'gcd')
        # gcd has its own compile, should not be overridden by default
        assert merged['api']['compile']['command'] == 'sbt "runMain gcd.GCD"'

    def test_missing_profile(self, sample_runner_toml):
        data = load_runner_toml(sample_runner_toml)
        with pytest.raises(ValueError, match='no profile'):
            merge_default_and_profile(data, 'nonexistent')

    def test_reserved_name(self, sample_runner_toml):
        data = load_runner_toml(sample_runner_toml)
        with pytest.raises(ValueError, match='reserved'):
            merge_default_and_profile(data, 'meta')


class TestApplyOverrides:
    def test_flat_key(self):
        config = {'memory': 4}
        result = apply_overrides(config, {'memory': '8'})
        assert result['memory'] == '8'

    def test_dotted_key(self):
        config = {'api': {'compile': {'cwd': '/old'}}}
        result = apply_overrides(config, {'api.compile.cwd': '/new'})
        assert result['api']['compile']['cwd'] == '/new'

    def test_creates_missing_keys(self):
        config = {}
        result = apply_overrides(config, {'a.b.c': 'val'})
        assert result['a']['b']['c'] == 'val'


class TestGetApiConfig:
    def test_existing_api(self, sample_tag_dir):
        data = load_tag_config(sample_tag_dir)
        api = get_api_config(data, 'build_dir')
        assert api is not None
        assert 'command' in api

    def test_missing_api(self, sample_tag_dir):
        data = load_tag_config(sample_tag_dir)
        assert get_api_config(data, 'nonexistent') is None


class TestListApiNames:
    def test_list(self, sample_tag_dir):
        data = load_tag_config(sample_tag_dir)
        names = list_api_names(data)
        assert 'build_dir' in names
        assert 'greet' in names


class TestResolvePlaceholders:
    def test_tag(self):
        assert resolve_placeholders('hello {tag}', {'tag': 'tst1'}) == 'hello tst1'

    def test_tag_dir(self):
        assert resolve_placeholders('{tag_dir}/out', {'tag_dir': '/cache/tags/x'}) == '/cache/tags/x/out'

    def test_input_dir(self):
        ctx = {'input': {'orig': {'dir': '/cache/tags/other'}}}
        assert resolve_placeholders('{input.orig.dir}/f', ctx) == '/cache/tags/other/f'

    def test_unknown_passthrough(self):
        assert resolve_placeholders('{unknown}', {}) == '{unknown}'


class TestBuildContext:
    def test_basic(self):
        ctx = build_context('tst1', '/cache/tags/tst1')
        assert ctx['tag'] == 'tst1'
        assert ctx['tag_dir'] == '/cache/tags/tst1'

    def test_with_inputs(self):
        ctx = build_context('tst1', '/d', input_dirs={'orig': '/cache/tags/src'})
        assert ctx['input']['orig']['dir'] == '/cache/tags/src'

    def test_with_api_options(self):
        api = {'options': [{'name': 'top', 'default': 'GCD'}]}
        ctx = build_context('tst1', '/d', api_config=api)
        assert ctx['top'] == 'GCD'


class TestBuildEnv:
    def test_sets_build_dir(self, sample_tag_dir):
        data = load_tag_config(sample_tag_dir)
        env = build_env(data, sample_tag_dir)
        assert env['HAGENT_BUILD_DIR'] == '/tmp/out'

    def test_layers_config_env(self, sample_tag_dir):
        data = load_tag_config(sample_tag_dir)
        env = build_env(data, sample_tag_dir)
        assert env['FOO'] == 'bar'


class TestGetDockerImage:
    def test_absent(self):
        assert get_docker_image({}) is None

    def test_with_image(self):
        assert get_docker_image({'docker': 'myimg:v1'}) == 'myimg:v1'

    def test_empty_string_forces_local(self):
        assert get_docker_image({'docker': ''}) == ''

    def test_not_a_string(self):
        assert get_docker_image({'docker': 42}) is None


class TestResolveOptions:
    def test_default_value(self):
        api = {'options': [{'name': 'top', 'format': '--top {value}', 'default': 'GCD'}]}
        result = resolve_options('synth {top}', api)
        assert result == 'synth --top GCD'

    def test_override_value(self):
        api = {'options': [{'name': 'top', 'format': '--top {value}', 'default': 'GCD'}]}
        result = resolve_options('synth {top}', api, {'top': 'ALU'})
        assert result == 'synth --top ALU'

    def test_empty_default(self):
        api = {'options': [{'name': 'top_synth', 'format': '--top-synthesis {value}', 'default': ''}]}
        result = resolve_options('synth {top_synth} done', api)
        assert result == 'synth  done'
