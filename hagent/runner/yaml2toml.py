"""Translate hagent.yaml profiles into runner TOML config files.

This module converts the existing YAML-based profile configuration into
TOML format.  Two modes:

- **Single profile** (``--name``): snapshot one profile into a tag-local
  ``config.toml`` for the runner's tag model.
- **All profiles** (default, no ``--name``): convert the entire
  ``hagent.yaml`` into a single ``runner.toml`` — the migration path
  from YAML to the future TOML-only config.

When converting all profiles, common values across profiles are extracted
into a ``[default]`` section so that per-profile tables only contain what
is unique.

Usage as a library:

    from hagent.runner.yaml2toml import yaml_to_tag_toml, yaml_to_runner_toml
    toml_str = yaml_to_tag_toml(yaml_path, profile_name)
    full_toml = yaml_to_runner_toml(yaml_path)

Usage from the command line:

    python -m hagent.runner.yaml2toml hagent.yaml                       # all profiles → stdout
    python -m hagent.runner.yaml2toml hagent.yaml -o runner.toml        # all profiles → file
    python -m hagent.runner.yaml2toml hagent.yaml --name gcd            # single profile
    python -m hagent.runner.yaml2toml hagent.yaml --name gcd -o config.toml
    python -m hagent.runner.yaml2toml hagent.yaml --list
"""

import os
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Optional

import tomlkit
import yaml

SCHEMA_VERSION = 1

RESERVED_KEYS = {'meta', 'default', 'overrides', 'inputs', 'tag'}


def load_yaml(yaml_path: str) -> dict:
    """Load and validate a hagent.yaml file.

    Returns the parsed dict.  Raises ValueError on structural problems.
    """
    with open(yaml_path, 'r') as f:
        data = yaml.safe_load(f)

    if not isinstance(data, dict):
        raise ValueError(f'{yaml_path}: top-level YAML must be a mapping')
    if 'profiles' not in data:
        raise ValueError(f'{yaml_path}: missing "profiles" key')
    if not isinstance(data['profiles'], list):
        raise ValueError(f'{yaml_path}: "profiles" must be a list')
    return data


def find_profile(data: dict, name: str) -> dict:
    """Find a profile by exact name (case-insensitive).

    Raises ValueError when zero or multiple matches are found.
    """
    hits = [p for p in data.get('profiles', []) if (p.get('name') or '').lower() == name.lower()]
    if not hits:
        avail = ', '.join(p.get('name', '<unnamed>') for p in data.get('profiles', []))
        raise ValueError(f"no profile named '{name}'; available: {avail}")
    if len(hits) > 1:
        raise ValueError(f"multiple profiles named '{name}'")
    return hits[0]


def list_profiles(data: dict) -> List[str]:
    """Return the list of profile names."""
    return [p.get('name', '<unnamed>') for p in data.get('profiles', [])]


# --------------- internal helpers ---------------


def _convert_options(options_list: List[dict]) -> List[dict]:
    """Convert a YAML options list into a list of plain dicts for TOML."""
    result = []
    for opt in options_list:
        entry: Dict[str, str] = {}
        for key in ('name', 'description', 'format', 'default'):
            if key in opt:
                entry[key] = opt[key]
        result.append(entry)
    return result


def _api_to_toml_table(api: dict) -> tomlkit.items.Table:
    """Convert a single YAML API entry to a tomlkit Table."""
    tbl = tomlkit.table()
    for key in ('description', 'command', 'cwd'):
        if key in api:
            tbl[key] = api[key]
    if 'options' in api and api['options']:
        opts_aot = tomlkit.aot()
        for opt in _convert_options(api['options']):
            opt_item = tomlkit.table()
            for ok, ov in opt.items():
                opt_item[ok] = ov
            opts_aot.append(opt_item)
        tbl.append('options', opts_aot)
    return tbl


def _strip_defaults(api_tbl: tomlkit.items.Table, defaults: dict) -> tomlkit.items.Table:
    """Return a copy of *api_tbl* with entries that match *defaults* removed."""
    out = tomlkit.table()
    for k, v in api_tbl.items():
        if k in defaults and defaults[k] == v:
            continue
        out[k] = v
    return out


# --------------- default extraction ---------------


def _extract_common_env(profiles: List[dict]) -> Dict[str, str]:
    """Find environment variables common to every profile that has a configuration."""
    profiles_with_env = []
    for p in profiles:
        cfg = p.get('configuration', {})
        if isinstance(cfg, dict):
            env = cfg.get('environment')
            if isinstance(env, dict) and env:
                profiles_with_env.append(env)

    if len(profiles_with_env) < 2:
        return {}

    common = {}
    # Start with keys from the first profile's environment
    for k, v in profiles_with_env[0].items():
        if all(pe.get(k) == v for pe in profiles_with_env[1:]):
            common[k] = v
    return common


def _extract_common_api_fields(profiles: List[dict]) -> Dict[str, dict]:
    """Find API-level fields common across all profiles that define that API name.

    Returns {api_name: {field: value, ...}} for fields shared by every profile
    that contains that API name (minimum 2 profiles).
    """
    # Collect per-api-name field values across profiles
    api_fields: Dict[str, List[dict]] = {}
    for p in profiles:
        for api in p.get('apis', []):
            name = api.get('name')
            if not name:
                continue
            fields = {}
            for key in ('cwd',):  # Only extract fields that commonly repeat
                if key in api:
                    fields[key] = api[key]
            if fields:
                api_fields.setdefault(name, []).append(fields)

    common = {}
    for api_name, field_list in api_fields.items():
        if len(field_list) < 2:
            continue
        shared = {}
        for k, v in field_list[0].items():
            if all(f.get(k) == v for f in field_list[1:]):
                shared[k] = v
        if shared:
            common[api_name] = shared
    return common


# --------------- tag config (single profile, --name) ---------------


def profile_to_toml_dict(
    profile: dict,
    yaml_path: str,
    inputs: Optional[Dict[str, str]] = None,
    overrides: Optional[Dict[str, str]] = None,
    output_dir: Optional[str] = None,
) -> dict:
    """Build the TOML document dict for a tag config from a YAML profile.

    The tag config uses named API tables: ``[api.compile]``, ``[api.lint]``, etc.
    """
    doc = tomlkit.document()

    doc.add(tomlkit.comment('Runner tag config — auto-generated from hagent.yaml'))
    doc.add(tomlkit.comment('Do not edit manually unless you know what you are doing.'))
    doc.add(tomlkit.nl())

    # --- [meta] ---
    meta = tomlkit.table()
    meta['schema_version'] = SCHEMA_VERSION
    meta['created'] = datetime.now(timezone.utc).isoformat()
    meta['source_yaml'] = str(Path(yaml_path).resolve())
    doc['meta'] = meta

    # --- [profile] ---
    prof = tomlkit.table()
    prof['name'] = profile.get('name', '')
    if profile.get('title'):
        prof['title'] = profile['title']
    if profile.get('description'):
        prof['description'] = profile['description']
    if profile.get('memory'):
        prof['memory'] = profile['memory']
    doc['profile'] = prof

    # --- [configuration] ---
    cfg_yaml = profile.get('configuration', {})
    if isinstance(cfg_yaml, dict) and cfg_yaml:
        cfg = tomlkit.table()

        env_yaml = cfg_yaml.get('environment')
        if isinstance(env_yaml, dict) and env_yaml:
            env_tbl = tomlkit.table()
            for k, v in env_yaml.items():
                env_tbl[k] = v
            cfg['environment'] = env_tbl

        tracking = tomlkit.table()
        if 'source' in cfg_yaml:
            tracking['source'] = cfg_yaml['source']
        if 'output' in cfg_yaml:
            tracking['output'] = cfg_yaml['output']
        if tracking:
            cfg['tracking'] = tracking

        doc['configuration'] = cfg

    # --- [inputs] ---
    if inputs:
        inputs_tbl = tomlkit.table()
        for k, v in inputs.items():
            inputs_tbl[k] = v
        doc['inputs'] = inputs_tbl

    # --- [tag] ---
    if output_dir:
        tag_tbl = tomlkit.table()
        tag_tbl['output_dir'] = output_dir
        doc['tag'] = tag_tbl

    # --- [api.*] (named tables) ---
    if profile.get('apis'):
        api_super = tomlkit.table(is_super_table=True)
        for api in profile['apis']:
            api_name = api.get('name')
            if not api_name:
                continue
            api_super[api_name] = _api_to_toml_table(api)
        doc['api'] = api_super

    # --- [overrides] ---
    if overrides:
        ov_tbl = tomlkit.table()
        for k, v in overrides.items():
            ov_tbl[k] = v
        doc['overrides'] = ov_tbl

    return doc


# --------------- runner.toml (all profiles) ---------------


def _add_profile_to_doc(
    doc: tomlkit.TOMLDocument,
    profile: dict,
    common_env: Dict[str, str],
    common_api_fields: Dict[str, dict],
) -> None:
    """Add one YAML profile as a top-level ``[name]`` table in *doc*.

    Values already present in ``[default]`` are omitted.
    """
    name = profile.get('name', '')
    if not name:
        raise ValueError('profile is missing a "name" field')
    if name in RESERVED_KEYS:
        raise ValueError(f"profile name '{name}' conflicts with reserved key")

    tbl = tomlkit.table()
    if profile.get('title'):
        tbl['title'] = profile['title']
    if profile.get('description'):
        tbl['description'] = profile['description']
    if profile.get('memory'):
        tbl['memory'] = profile['memory']

    # environment (minus common entries)
    cfg_yaml = profile.get('configuration', {})
    if isinstance(cfg_yaml, dict) and cfg_yaml:
        env_yaml = cfg_yaml.get('environment')
        if isinstance(env_yaml, dict) and env_yaml:
            unique_env = {k: v for k, v in env_yaml.items() if common_env.get(k) != v}
            if unique_env:
                env_tbl = tomlkit.table()
                for k, v in unique_env.items():
                    env_tbl[k] = v
                tbl['environment'] = env_tbl

        tracking = tomlkit.table()
        if 'source' in cfg_yaml:
            tracking['source'] = cfg_yaml['source']
        if 'output' in cfg_yaml:
            tracking['output'] = cfg_yaml['output']
        if tracking:
            tbl['tracking'] = tracking

    # [name.api.*] (named tables, minus default fields)
    if profile.get('apis'):
        api_super = tomlkit.table(is_super_table=True)
        for api in profile['apis']:
            api_name = api.get('name')
            if not api_name:
                continue
            api_tbl = _api_to_toml_table(api)
            defaults_for_api = common_api_fields.get(api_name, {})
            if defaults_for_api:
                api_tbl = _strip_defaults(api_tbl, defaults_for_api)
            api_super[api_name] = api_tbl
        if api_super:
            tbl['api'] = api_super

    doc.add(name, tbl)


def yaml_to_runner_toml(yaml_path: str) -> str:
    """Convert an entire hagent.yaml (all profiles) into a single TOML string.

    Each profile becomes a top-level ``[name]`` table.  Common values are
    extracted into ``[default]``.  This is the migration path:
    ``hagent.yaml`` → ``runner.toml``.
    """
    data = load_yaml(yaml_path)
    profiles = data.get('profiles', [])

    doc = tomlkit.document()

    doc.add(tomlkit.comment('runner.toml — auto-generated from hagent.yaml'))
    doc.add(tomlkit.comment(f'source: {Path(yaml_path).resolve()}'))
    doc.add(tomlkit.nl())

    meta = tomlkit.table()
    meta['schema_version'] = SCHEMA_VERSION
    meta['created'] = datetime.now(timezone.utc).isoformat()
    meta['source_yaml'] = str(Path(yaml_path).resolve())
    doc['meta'] = meta

    # Extract defaults
    common_env = _extract_common_env(profiles)
    common_api_fields = _extract_common_api_fields(profiles)

    if common_env or common_api_fields:
        default_tbl = tomlkit.table()

        if common_env:
            env_tbl = tomlkit.table()
            for k, v in common_env.items():
                env_tbl[k] = v
            default_tbl['environment'] = env_tbl

        if common_api_fields:
            api_super = tomlkit.table(is_super_table=True)
            for api_name, fields in common_api_fields.items():
                api_tbl = tomlkit.table()
                for k, v in fields.items():
                    api_tbl[k] = v
                api_super[api_name] = api_tbl
            default_tbl['api'] = api_super

        doc['default'] = default_tbl

    for profile in profiles:
        _add_profile_to_doc(doc, profile, common_env, common_api_fields)

    return tomlkit.dumps(doc)


# --------------- single-profile convenience ---------------


def yaml_to_tag_toml(
    yaml_path: str,
    profile_name: str,
    inputs: Optional[Dict[str, str]] = None,
    overrides: Optional[Dict[str, str]] = None,
    output_dir: Optional[str] = None,
) -> str:
    """High-level: load YAML, select profile, return TOML string."""
    data = load_yaml(yaml_path)
    profile = find_profile(data, profile_name)
    doc = profile_to_toml_dict(profile, yaml_path, inputs, overrides, output_dir)
    return tomlkit.dumps(doc)


def yaml_to_tag_toml_file(
    yaml_path: str,
    profile_name: str,
    toml_path: str,
    inputs: Optional[Dict[str, str]] = None,
    overrides: Optional[Dict[str, str]] = None,
    output_dir: Optional[str] = None,
) -> None:
    """High-level: load YAML, select profile, write config.toml."""
    content = yaml_to_tag_toml(yaml_path, profile_name, inputs, overrides, output_dir)
    Path(toml_path).parent.mkdir(parents=True, exist_ok=True)
    with open(toml_path, 'w') as f:
        f.write(content)


def setup_tag(
    yaml_path: str,
    tag_name: str,
    profile_name: str,
    cache_dir: Optional[str] = None,
    inputs: Optional[Dict[str, str]] = None,
    overrides: Optional[Dict[str, str]] = None,
    output_dir: Optional[str] = None,
    force: bool = False,
) -> str:
    """Create a tag directory under <cache>/tags/<tag>/ with a config.toml snapshot.

    Uses HAGENT_CACHE_DIR from the environment if cache_dir is not provided.
    """
    if cache_dir is None:
        cache_dir = os.environ.get('HAGENT_CACHE_DIR')
        if not cache_dir:
            raise EnvironmentError('HAGENT_CACHE_DIR not set and --cache-dir not provided')

    tag_dir = Path(cache_dir) / 'tags' / tag_name
    toml_path = tag_dir / 'config.toml'

    if tag_dir.exists() and not force:
        raise ValueError(f"tag '{tag_name}' already exists at {tag_dir}; use --force to overwrite")

    tag_dir.mkdir(parents=True, exist_ok=True)
    (tag_dir / 'logs').mkdir(exist_ok=True)

    yaml_to_tag_toml_file(yaml_path, profile_name, str(toml_path), inputs, overrides, output_dir)
    return str(toml_path)


# --------------- CLI ---------------


def _parse_key_value(arg: str) -> tuple:
    """Parse 'KEY=VALUE' into (key, value). Raises ValueError on bad format."""
    if '=' not in arg:
        raise ValueError(f'expected KEY=VALUE, got: {arg}')
    k, v = arg.split('=', 1)
    return k.strip(), v.strip()


def main(argv: Optional[List[str]] = None) -> int:
    import argparse

    parser = argparse.ArgumentParser(
        description='Convert hagent.yaml to runner TOML config',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""examples:
  %(prog)s hagent.yaml                                    # all profiles → stdout
  %(prog)s hagent.yaml -o runner.toml                     # all profiles → file
  %(prog)s hagent.yaml --list                             # list profile names
  %(prog)s hagent.yaml --name gcd                         # single profile → stdout
  %(prog)s hagent.yaml --name gcd -o config.toml          # single profile → file
  %(prog)s hagent.yaml --name gcd --tag tst1              # create tag directory
  %(prog)s hagent.yaml --name gcd --tag tst1 --input orig_verilog=other_tag
  %(prog)s hagent.yaml --name gcd --tag tst1 --set tool.tech=sky130
""",
    )
    parser.add_argument('yaml_path', help='path to hagent.yaml')
    parser.add_argument('--name', help='profile name to snapshot')
    parser.add_argument('--list', action='store_true', help='list available profiles')
    parser.add_argument('-o', '--output', help='write TOML to file instead of stdout')
    parser.add_argument('--tag', help='create a full tag under HAGENT_CACHE_DIR/tags/<tag>/')
    parser.add_argument('--cache-dir', help='override HAGENT_CACHE_DIR')
    parser.add_argument('--dir', help='explicit output directory for the tag')
    parser.add_argument('--input', action='append', default=[], help='named input: NAME=TAG (repeatable)')
    parser.add_argument('--set', action='append', default=[], dest='overrides', help='KEY=VALUE override (repeatable)')
    parser.add_argument('--force', action='store_true', help='overwrite existing tag')

    args = parser.parse_args(argv)

    try:
        data = load_yaml(args.yaml_path)
    except (FileNotFoundError, ValueError) as e:
        print(f'error: {e}', file=sys.stderr)
        return 1

    if args.list:
        for name in list_profiles(data):
            print(name)
        return 0

    # No --name: convert all profiles into a single runner.toml
    if not args.name:
        if args.tag:
            print('error: --tag requires --name to select a profile', file=sys.stderr)
            return 1

        try:
            toml_str = yaml_to_runner_toml(args.yaml_path)
        except (ValueError, EnvironmentError) as e:
            print(f'error: {e}', file=sys.stderr)
            return 1

        if args.output:
            Path(args.output).parent.mkdir(parents=True, exist_ok=True)
            with open(args.output, 'w') as f:
                f.write(toml_str)
            print(f'wrote {args.output}', file=sys.stderr)
        else:
            print(toml_str)
        return 0

    # Parse inputs
    inputs = {}
    for inp in args.input:
        try:
            k, v = _parse_key_value(inp)
            inputs[k] = v
        except ValueError as e:
            print(f'error: --input {e}', file=sys.stderr)
            return 1

    # Parse overrides
    overrides = {}
    for ov in args.overrides:
        try:
            k, v = _parse_key_value(ov)
            overrides[k] = v
        except ValueError as e:
            print(f'error: --set {e}', file=sys.stderr)
            return 1

    try:
        if args.tag:
            path = setup_tag(
                yaml_path=args.yaml_path,
                tag_name=args.tag,
                profile_name=args.name,
                cache_dir=args.cache_dir,
                inputs=inputs or None,
                overrides=overrides or None,
                output_dir=args.dir,
                force=args.force,
            )
            print(f'tag created: {path}')
            return 0

        toml_str = yaml_to_tag_toml(
            yaml_path=args.yaml_path,
            profile_name=args.name,
            inputs=inputs or None,
            overrides=overrides or None,
            output_dir=args.dir,
        )

        if args.output:
            Path(args.output).parent.mkdir(parents=True, exist_ok=True)
            with open(args.output, 'w') as f:
                f.write(toml_str)
            print(f'wrote {args.output}', file=sys.stderr)
        else:
            print(toml_str)

        return 0

    except (ValueError, EnvironmentError) as e:
        print(f'error: {e}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
