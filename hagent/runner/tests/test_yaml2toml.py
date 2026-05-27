"""Tests for hagent.runner.yaml2toml."""

from pathlib import Path

import pytest
import tomlkit
import yaml

from hagent.runner.yaml2toml import (
    find_profile,
    list_profiles,
    load_yaml,
    profile_to_toml_dict,
    setup_tag,
    yaml_to_runner_toml,
    yaml_to_tag_toml,
)

# --------------- fixtures ---------------

SIMPLE_YAML = {
    'profiles': [
        {
            'name': 'echo',
            'description': 'Just print HAGENT_ environment variables',
            'apis': [
                {
                    'name': 'build_dir',
                    'description': 'Echo HAGENT_BUILD_DIR',
                    'command': 'echo $HAGENT_BUILD_DIR',
                    'cwd': '$HAGENT_REPO_DIR',
                },
            ],
        },
        {
            'name': 'gcd',
            'description': 'Profile for building GCD module from Chisel/Scala sources',
            'memory': 4,
            'configuration': {
                'source': "track_repo_dir('src/main/scala', ext='.scala')",
                'output': "track_build_dir('build_gcd', ext='.sv')",
                'environment': {
                    'SCALA_HOME': '/usr/local/scala',
                    'SBT_OPTS': '-Xmx2G -XX:+UseG1GC',
                    'PATH': '$PATH:/usr/local/scala/bin',
                },
            },
            'apis': [
                {
                    'name': 'compile',
                    'description': 'Compile GCD module and generate Verilog',
                    'command': 'sbt "runMain gcd.GCD"',
                    'cwd': '$HAGENT_REPO_DIR',
                },
                {
                    'name': 'synth_asic',
                    'description': 'ASIC synthesis GCD using Yosys',
                    'command': '/code/hagent/scripts/synth.py --run-sta',
                    'cwd': '$HAGENT_BUILD_DIR',
                    'options': [
                        {
                            'name': 'tag',
                            'description': 'Tag for elaboration',
                            'format': '--tag {value}',
                            'default': '--tag reference',
                        },
                    ],
                },
            ],
        },
    ]
}

# YAML with shared env + shared api cwd to test [default] extraction
SHARED_YAML = {
    'profiles': [
        {
            'name': 'alpha',
            'description': 'Alpha profile',
            'configuration': {
                'environment': {
                    'SCALA_HOME': '/usr/local/scala',
                    'SBT_OPTS': '-Xmx2G',
                    'ALPHA_ONLY': 'yes',
                },
            },
            'apis': [
                {'name': 'compile', 'description': 'compile alpha', 'command': 'make alpha', 'cwd': '$HAGENT_REPO_DIR'},
                {'name': 'lint', 'description': 'lint alpha', 'command': 'lint alpha', 'cwd': '$HAGENT_REPO_DIR'},
            ],
        },
        {
            'name': 'beta',
            'description': 'Beta profile',
            'configuration': {
                'environment': {
                    'SCALA_HOME': '/usr/local/scala',
                    'SBT_OPTS': '-Xmx2G',
                    'BETA_ONLY': 'yes',
                },
            },
            'apis': [
                {'name': 'compile', 'description': 'compile beta', 'command': 'make beta', 'cwd': '$HAGENT_REPO_DIR'},
                {'name': 'lint', 'description': 'lint beta', 'command': 'lint beta', 'cwd': '$HAGENT_REPO_DIR'},
            ],
        },
    ]
}


@pytest.fixture
def yaml_file(tmp_path):
    """Write SIMPLE_YAML to a temporary file and return its path."""
    p = tmp_path / 'hagent.yaml'
    with open(p, 'w') as f:
        yaml.dump(SIMPLE_YAML, f)
    return str(p)


@pytest.fixture
def shared_yaml_file(tmp_path):
    """Write SHARED_YAML to a temporary file and return its path."""
    p = tmp_path / 'hagent_shared.yaml'
    with open(p, 'w') as f:
        yaml.dump(SHARED_YAML, f)
    return str(p)


# --------------- load_yaml ---------------


def test_load_yaml(yaml_file):
    data = load_yaml(yaml_file)
    assert 'profiles' in data
    assert len(data['profiles']) == 2


def test_load_yaml_missing():
    with pytest.raises(FileNotFoundError):
        load_yaml('/nonexistent/hagent.yaml')


def test_load_yaml_bad_structure(tmp_path):
    p = tmp_path / 'bad.yaml'
    p.write_text('just_a_string')
    with pytest.raises(ValueError, match='top-level YAML must be a mapping'):
        load_yaml(str(p))


# --------------- find_profile / list_profiles ---------------


def test_find_profile(yaml_file):
    data = load_yaml(yaml_file)
    prof = find_profile(data, 'gcd')
    assert prof['name'] == 'gcd'
    assert prof['memory'] == 4


def test_find_profile_case_insensitive(yaml_file):
    data = load_yaml(yaml_file)
    prof = find_profile(data, 'GCD')
    assert prof['name'] == 'gcd'


def test_find_profile_missing(yaml_file):
    data = load_yaml(yaml_file)
    with pytest.raises(ValueError, match='no profile named'):
        find_profile(data, 'nonexistent')


def test_list_profiles(yaml_file):
    data = load_yaml(yaml_file)
    names = list_profiles(data)
    assert names == ['echo', 'gcd']


# --------------- profile_to_toml_dict (tag config) ---------------


def test_toml_dict_meta(yaml_file):
    data = load_yaml(yaml_file)
    prof = find_profile(data, 'gcd')
    doc = profile_to_toml_dict(prof, yaml_file)
    assert doc['meta']['schema_version'] == 1
    assert 'created' in doc['meta']


def test_toml_dict_profile_fields(yaml_file):
    data = load_yaml(yaml_file)
    prof = find_profile(data, 'gcd')
    doc = profile_to_toml_dict(prof, yaml_file)
    assert doc['profile']['name'] == 'gcd'
    assert doc['profile']['memory'] == 4
    assert 'description' in doc['profile']


def test_toml_dict_configuration(yaml_file):
    data = load_yaml(yaml_file)
    prof = find_profile(data, 'gcd')
    doc = profile_to_toml_dict(prof, yaml_file)
    assert doc['configuration']['environment']['SCALA_HOME'] == '/usr/local/scala'
    assert 'source' in doc['configuration']['tracking']
    assert 'output' in doc['configuration']['tracking']


def test_toml_dict_named_apis(yaml_file):
    """APIs should be named tables: [api.compile], [api.synth_asic]."""
    data = load_yaml(yaml_file)
    prof = find_profile(data, 'gcd')
    doc = profile_to_toml_dict(prof, yaml_file)
    assert 'compile' in doc['api']
    assert 'synth_asic' in doc['api']
    assert doc['api']['compile']['command'] == 'sbt "runMain gcd.GCD"'


def test_toml_dict_api_options(yaml_file):
    data = load_yaml(yaml_file)
    prof = find_profile(data, 'gcd')
    doc = profile_to_toml_dict(prof, yaml_file)
    opts = doc['api']['synth_asic']['options']
    assert len(opts) == 1
    assert opts[0]['name'] == 'tag'
    assert opts[0]['format'] == '--tag {value}'
    assert opts[0]['default'] == '--tag reference'


def test_toml_dict_inputs(yaml_file):
    data = load_yaml(yaml_file)
    prof = find_profile(data, 'gcd')
    doc = profile_to_toml_dict(prof, yaml_file, inputs={'orig_verilog': 'tag_v', 'orig_chisel': 'tag_c'})
    assert doc['inputs']['orig_verilog'] == 'tag_v'
    assert doc['inputs']['orig_chisel'] == 'tag_c'


def test_toml_dict_overrides(yaml_file):
    data = load_yaml(yaml_file)
    prof = find_profile(data, 'gcd')
    doc = profile_to_toml_dict(prof, yaml_file, overrides={'tool.tech': 'sky130'})
    assert doc['overrides']['tool.tech'] == 'sky130'


def test_toml_dict_output_dir(yaml_file):
    data = load_yaml(yaml_file)
    prof = find_profile(data, 'gcd')
    doc = profile_to_toml_dict(prof, yaml_file, output_dir='/some/build/dir')
    assert doc['tag']['output_dir'] == '/some/build/dir'


def test_toml_dict_no_configuration(yaml_file):
    """Profile without configuration section should not have [configuration]."""
    data = load_yaml(yaml_file)
    prof = find_profile(data, 'echo')
    doc = profile_to_toml_dict(prof, yaml_file)
    assert 'configuration' not in doc


# --------------- yaml_to_tag_toml (round-trip) ---------------


def test_roundtrip_toml_parse(yaml_file):
    """Verify the TOML string can be parsed back with named APIs."""
    toml_str = yaml_to_tag_toml(yaml_file, 'gcd')
    parsed = tomlkit.parse(toml_str)
    assert parsed['profile']['name'] == 'gcd'
    assert 'compile' in parsed['api']
    assert 'synth_asic' in parsed['api']


def test_roundtrip_simple_profile(yaml_file):
    """Simple profile without configuration."""
    toml_str = yaml_to_tag_toml(yaml_file, 'echo')
    parsed = tomlkit.parse(toml_str)
    assert parsed['profile']['name'] == 'echo'
    assert 'build_dir' in parsed['api']


# --------------- setup_tag ---------------


def test_setup_tag(yaml_file, tmp_path):
    cache = tmp_path / 'cache'
    cache.mkdir()
    path = setup_tag(
        yaml_path=yaml_file,
        tag_name='tst1',
        profile_name='gcd',
        cache_dir=str(cache),
    )
    assert Path(path).exists()
    assert Path(path).name == 'config.toml'
    tag_dir = Path(path).parent
    assert (tag_dir / 'logs').is_dir()

    parsed = tomlkit.parse(Path(path).read_text())
    assert parsed['profile']['name'] == 'gcd'
    assert 'compile' in parsed['api']


def test_setup_tag_already_exists(yaml_file, tmp_path):
    cache = tmp_path / 'cache'
    cache.mkdir()
    setup_tag(yaml_path=yaml_file, tag_name='tst1', profile_name='gcd', cache_dir=str(cache))

    with pytest.raises(ValueError, match='already exists'):
        setup_tag(yaml_path=yaml_file, tag_name='tst1', profile_name='gcd', cache_dir=str(cache))


def test_setup_tag_force(yaml_file, tmp_path):
    cache = tmp_path / 'cache'
    cache.mkdir()
    setup_tag(yaml_path=yaml_file, tag_name='tst1', profile_name='gcd', cache_dir=str(cache))
    path = setup_tag(yaml_path=yaml_file, tag_name='tst1', profile_name='gcd', cache_dir=str(cache), force=True)
    assert Path(path).exists()


def test_setup_tag_with_inputs(yaml_file, tmp_path):
    cache = tmp_path / 'cache'
    cache.mkdir()
    path = setup_tag(
        yaml_path=yaml_file,
        tag_name='tst2',
        profile_name='gcd',
        cache_dir=str(cache),
        inputs={'orig_verilog': 'other_tag'},
    )
    parsed = tomlkit.parse(Path(path).read_text())
    assert parsed['inputs']['orig_verilog'] == 'other_tag'


def test_setup_tag_env_fallback(yaml_file, tmp_path, monkeypatch):
    cache = tmp_path / 'cache_env'
    cache.mkdir()
    monkeypatch.setenv('HAGENT_CACHE_DIR', str(cache))
    path = setup_tag(yaml_path=yaml_file, tag_name='tst_env', profile_name='echo')
    assert Path(path).exists()
    assert str(cache) in path


def test_setup_tag_no_cache_dir(yaml_file, monkeypatch):
    monkeypatch.delenv('HAGENT_CACHE_DIR', raising=False)
    with pytest.raises(EnvironmentError, match='HAGENT_CACHE_DIR'):
        setup_tag(yaml_path=yaml_file, tag_name='tst_fail', profile_name='echo')


# --------------- all-profiles conversion (runner.toml) ---------------


def test_yaml_to_runner_toml(yaml_file):
    """All profiles should appear as top-level keys."""
    toml_str = yaml_to_runner_toml(yaml_file)
    parsed = tomlkit.parse(toml_str)
    assert parsed['meta']['schema_version'] == 1
    assert 'echo' in parsed
    assert 'gcd' in parsed


def test_runner_toml_named_apis(yaml_file):
    """APIs should be named tables: [gcd.api.compile]."""
    toml_str = yaml_to_runner_toml(yaml_file)
    parsed = tomlkit.parse(toml_str)
    assert 'compile' in parsed['gcd']['api']
    assert 'synth_asic' in parsed['gcd']['api']
    assert parsed['gcd']['api']['synth_asic']['options'][0]['name'] == 'tag'


def test_runner_toml_environment(yaml_file):
    """Environment should be direct child of profile."""
    toml_str = yaml_to_runner_toml(yaml_file)
    parsed = tomlkit.parse(toml_str)
    assert parsed['gcd']['environment']['SCALA_HOME'] == '/usr/local/scala'
    assert 'source' in parsed['gcd']['tracking']


def test_runner_toml_simple_profile(yaml_file):
    toml_str = yaml_to_runner_toml(yaml_file)
    parsed = tomlkit.parse(toml_str)
    assert parsed['echo']['description'] == 'Just print HAGENT_ environment variables'
    assert 'build_dir' in parsed['echo']['api']


# --------------- [default] extraction ---------------


def test_default_common_env(shared_yaml_file):
    """Common env vars should be extracted into [default.environment]."""
    toml_str = yaml_to_runner_toml(shared_yaml_file)
    parsed = tomlkit.parse(toml_str)
    assert 'default' in parsed
    assert parsed['default']['environment']['SCALA_HOME'] == '/usr/local/scala'
    assert parsed['default']['environment']['SBT_OPTS'] == '-Xmx2G'


def test_default_unique_env_not_in_default(shared_yaml_file):
    """Profile-unique env vars should NOT appear in [default]."""
    toml_str = yaml_to_runner_toml(shared_yaml_file)
    parsed = tomlkit.parse(toml_str)
    assert 'ALPHA_ONLY' not in parsed['default']['environment']
    assert 'BETA_ONLY' not in parsed['default']['environment']


def test_default_unique_env_stays_in_profile(shared_yaml_file):
    """Profile-unique env vars should remain in the profile."""
    toml_str = yaml_to_runner_toml(shared_yaml_file)
    parsed = tomlkit.parse(toml_str)
    assert parsed['alpha']['environment']['ALPHA_ONLY'] == 'yes'
    assert parsed['beta']['environment']['BETA_ONLY'] == 'yes'


def test_default_common_env_removed_from_profile(shared_yaml_file):
    """Common env vars should be removed from per-profile sections."""
    toml_str = yaml_to_runner_toml(shared_yaml_file)
    parsed = tomlkit.parse(toml_str)
    # SCALA_HOME is in default, so should not be in alpha/beta
    alpha_env = parsed['alpha'].get('environment', {})
    assert 'SCALA_HOME' not in alpha_env
    assert 'SBT_OPTS' not in alpha_env


def test_default_common_api_cwd(shared_yaml_file):
    """Common API cwd should be extracted into [default.api.compile]."""
    toml_str = yaml_to_runner_toml(shared_yaml_file)
    parsed = tomlkit.parse(toml_str)
    assert parsed['default']['api']['compile']['cwd'] == '$HAGENT_REPO_DIR'
    assert parsed['default']['api']['lint']['cwd'] == '$HAGENT_REPO_DIR'


def test_default_api_cwd_removed_from_profile(shared_yaml_file):
    """When cwd is in [default.api.compile], profiles should omit it."""
    toml_str = yaml_to_runner_toml(shared_yaml_file)
    parsed = tomlkit.parse(toml_str)
    assert 'cwd' not in parsed['alpha']['api']['compile']
    assert 'cwd' not in parsed['beta']['api']['lint']


def test_no_default_when_nothing_shared(yaml_file):
    """SIMPLE_YAML has only one profile with env — no [default] should appear."""
    toml_str = yaml_to_runner_toml(yaml_file)
    parsed = tomlkit.parse(toml_str)
    # echo has no env, gcd has env — nothing to share
    assert 'default' not in parsed


# --------------- CLI (main) ---------------


def test_cli_list(yaml_file, capsys):
    from hagent.runner.yaml2toml import main

    rc = main([yaml_file, '--list'])
    assert rc == 0
    out = capsys.readouterr().out
    assert 'echo' in out
    assert 'gcd' in out


def test_cli_convert_stdout(yaml_file, capsys):
    from hagent.runner.yaml2toml import main

    rc = main([yaml_file, '--name', 'gcd'])
    assert rc == 0
    out = capsys.readouterr().out
    parsed = tomlkit.parse(out)
    assert parsed['profile']['name'] == 'gcd'
    assert 'compile' in parsed['api']


def test_cli_convert_to_file(yaml_file, tmp_path):
    from hagent.runner.yaml2toml import main

    out_file = tmp_path / 'out.toml'
    rc = main([yaml_file, '--name', 'gcd', '-o', str(out_file)])
    assert rc == 0
    parsed = tomlkit.parse(out_file.read_text())
    assert parsed['profile']['name'] == 'gcd'


def test_cli_tag_create(yaml_file, tmp_path):
    from hagent.runner.yaml2toml import main

    cache = tmp_path / 'cache'
    cache.mkdir()
    rc = main([yaml_file, '--name', 'gcd', '--tag', 'tst1', '--cache-dir', str(cache)])
    assert rc == 0
    assert (cache / 'tags' / 'tst1' / 'config.toml').exists()


def test_cli_tag_requires_name(yaml_file, capsys):
    from hagent.runner.yaml2toml import main

    rc = main([yaml_file, '--tag', 'tst1'])
    assert rc == 1
    err = capsys.readouterr().err
    assert '--tag requires --name' in err


def test_cli_all_profiles_stdout(yaml_file, capsys):
    from hagent.runner.yaml2toml import main

    rc = main([yaml_file])
    assert rc == 0
    out = capsys.readouterr().out
    parsed = tomlkit.parse(out)
    assert 'echo' in parsed
    assert 'gcd' in parsed


def test_cli_all_profiles_to_file(yaml_file, tmp_path):
    from hagent.runner.yaml2toml import main

    out_file = tmp_path / 'runner.toml'
    rc = main([yaml_file, '-o', str(out_file)])
    assert rc == 0
    parsed = tomlkit.parse(out_file.read_text())
    assert 'echo' in parsed
    assert 'gcd' in parsed


def test_cli_bad_profile(yaml_file, capsys):
    from hagent.runner.yaml2toml import main

    rc = main([yaml_file, '--name', 'nonexistent'])
    assert rc == 1
    err = capsys.readouterr().err
    assert 'no profile named' in err
