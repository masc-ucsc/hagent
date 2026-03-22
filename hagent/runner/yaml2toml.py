"""Translate hagent.yaml profiles into runner TOML config files.

This module converts the existing YAML-based profile configuration into
TOML format.  Two modes:

- **Single profile** (``--name``): snapshot one profile into a tag-local
  ``config.toml`` for the runner's tag model.
- **All profiles** (default, no ``--name``): convert the entire
  ``hagent.yaml`` into a single ``runner.toml`` — the migration path
  from YAML to the future TOML-only config.

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


def _convert_options(options_list: List[dict]) -> List[dict]:
    """Convert a YAML options list into a list of plain dicts for TOML."""
    result = []
    for opt in options_list:
        entry: Dict[str, str] = {}
        if 'name' in opt:
            entry['name'] = opt['name']
        if 'description' in opt:
            entry['description'] = opt['description']
        if 'format' in opt:
            entry['format'] = opt['format']
        if 'default' in opt:
            entry['default'] = opt['default']
        result.append(entry)
    return result


def _convert_api(api: dict) -> dict:
    """Convert a single YAML API entry to a TOML-friendly dict."""
    entry: Dict = {}
    for key in ('name', 'description', 'command', 'cwd'):
        if key in api:
            entry[key] = api[key]
    if 'options' in api and api['options']:
        entry['options'] = _convert_options(api['options'])
    return entry


def profile_to_toml_dict(
    profile: dict,
    yaml_path: str,
    inputs: Optional[Dict[str, str]] = None,
    overrides: Optional[Dict[str, str]] = None,
    output_dir: Optional[str] = None,
) -> dict:
    """Build the TOML document dict for a tag config from a YAML profile.

    Args:
        profile: The selected profile dict from hagent.yaml.
        yaml_path: Path to the source hagent.yaml (recorded in metadata).
        inputs: Optional dict of named input tags (e.g. {"orig_verilog": "tag1"}).
        overrides: Optional dict of --set KEY=VALUE overrides to persist.
        output_dir: Optional explicit output directory for the tag.

    Returns:
        An ordered dict suitable for tomlkit serialization.
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

        # environment
        env_yaml = cfg_yaml.get('environment')
        if isinstance(env_yaml, dict) and env_yaml:
            env_tbl = tomlkit.table()
            for k, v in env_yaml.items():
                env_tbl[k] = v
            cfg['environment'] = env_tbl

        # tracking directives (source/output kept as strings for now)
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

    # --- [[apis]] ---
    if profile.get('apis'):
        apis_aot = tomlkit.aot()
        for api in profile['apis']:
            item = tomlkit.table()
            converted = _convert_api(api)
            for k, v in converted.items():
                if k == 'options':
                    opts_aot = tomlkit.aot()
                    for opt_dict in v:
                        opt_item = tomlkit.table()
                        for ok, ov in opt_dict.items():
                            opt_item[ok] = ov
                        opts_aot.append(opt_item)
                    item.append('options', opts_aot)
                else:
                    item[k] = v
            apis_aot.append(item)
        doc.append('apis', apis_aot)

    # --- [overrides] ---
    if overrides:
        ov_tbl = tomlkit.table()
        for k, v in overrides.items():
            ov_tbl[k] = v
        doc['overrides'] = ov_tbl

    return doc


RESERVED_KEYS = {'meta', 'overrides', 'inputs', 'tag'}


def _add_profile_to_doc(doc: tomlkit.TOMLDocument, profile: dict) -> None:
    """Add one YAML profile as a top-level ``[name]`` table in *doc*.

    The profile name becomes the TOML key.  Sub-tables:
    - ``[name.environment]``  — env vars
    - ``[name.tracking]``     — source/output directives
    - ``[[name.api]]``        — array of API entries
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

    # environment + tracking (flattened — no intermediate "configuration")
    cfg_yaml = profile.get('configuration', {})
    if isinstance(cfg_yaml, dict) and cfg_yaml:
        env_yaml = cfg_yaml.get('environment')
        if isinstance(env_yaml, dict) and env_yaml:
            env_tbl = tomlkit.table()
            for k, v in env_yaml.items():
                env_tbl[k] = v
            tbl['environment'] = env_tbl

        tracking = tomlkit.table()
        if 'source' in cfg_yaml:
            tracking['source'] = cfg_yaml['source']
        if 'output' in cfg_yaml:
            tracking['output'] = cfg_yaml['output']
        if tracking:
            tbl['tracking'] = tracking

    # [[name.api]]
    if profile.get('apis'):
        apis_aot = tomlkit.aot()
        for api in profile['apis']:
            item = tomlkit.table()
            converted = _convert_api(api)
            for k, v in converted.items():
                if k == 'options':
                    opts_aot = tomlkit.aot()
                    for opt_dict in v:
                        opt_item = tomlkit.table()
                        for ok, ov in opt_dict.items():
                            opt_item[ok] = ov
                        opts_aot.append(opt_item)
                    item.append('options', opts_aot)
                else:
                    item[k] = v
            apis_aot.append(item)
        tbl.append('api', apis_aot)

    doc.add(name, tbl)


def yaml_to_runner_toml(yaml_path: str) -> str:
    """Convert an entire hagent.yaml (all profiles) into a single TOML string.

    Each profile becomes a top-level ``[name]`` table.  This is the
    migration path: ``hagent.yaml`` → ``runner.toml``.

    Args:
        yaml_path: Path to hagent.yaml.

    Returns:
        TOML-formatted string containing all profiles.
    """
    data = load_yaml(yaml_path)
    doc = tomlkit.document()

    doc.add(tomlkit.comment('runner.toml — auto-generated from hagent.yaml'))
    doc.add(tomlkit.comment(f'source: {Path(yaml_path).resolve()}'))
    doc.add(tomlkit.nl())

    meta = tomlkit.table()
    meta['schema_version'] = SCHEMA_VERSION
    meta['created'] = datetime.now(timezone.utc).isoformat()
    meta['source_yaml'] = str(Path(yaml_path).resolve())
    doc['meta'] = meta

    for profile in data.get('profiles', []):
        _add_profile_to_doc(doc, profile)

    return tomlkit.dumps(doc)


def yaml_to_tag_toml(
    yaml_path: str,
    profile_name: str,
    inputs: Optional[Dict[str, str]] = None,
    overrides: Optional[Dict[str, str]] = None,
    output_dir: Optional[str] = None,
) -> str:
    """High-level: load YAML, select profile, return TOML string.

    Args:
        yaml_path: Path to hagent.yaml.
        profile_name: Profile name to snapshot.
        inputs: Optional named input tags.
        overrides: Optional --set KEY=VALUE overrides to persist.
        output_dir: Optional explicit output directory.

    Returns:
        TOML-formatted string ready to write to config.toml.
    """
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
    """High-level: load YAML, select profile, write config.toml.

    Creates parent directories as needed.
    """
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

    Args:
        yaml_path: Path to hagent.yaml.
        tag_name: Tag identifier (directory name under tags/).
        profile_name: Profile name to snapshot from the YAML.
        cache_dir: Explicit cache directory (defaults to HAGENT_CACHE_DIR).
        inputs: Optional named input tags.
        overrides: Optional --set KEY=VALUE overrides to persist.
        output_dir: Optional explicit output directory for the tag.
        force: If True, overwrite existing tag.

    Returns:
        Path to the created config.toml.

    Raises:
        ValueError: If tag already exists (and not --force), or profile not found.
        EnvironmentError: If HAGENT_CACHE_DIR is not set and cache_dir is None.
    """
    if cache_dir is None:
        cache_dir = os.environ.get('HAGENT_CACHE_DIR')
        if not cache_dir:
            raise EnvironmentError('HAGENT_CACHE_DIR not set and --cache-dir not provided')

    tag_dir = Path(cache_dir) / 'tags' / tag_name
    toml_path = tag_dir / 'config.toml'

    if tag_dir.exists() and not force:
        raise ValueError(f"tag '{tag_name}' already exists at {tag_dir}; use --force to overwrite")

    # Create tag directory structure
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
