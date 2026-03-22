"""CLI parsing and dispatch for the runner."""

import os
import sys
from typing import Dict, List, Optional, Tuple

from . import config as cfg
from .commands import run_command
from .tag import TagError, setup_tag


def _parse_kv_args(args: List[str], flag: str) -> Tuple[Dict[str, str], List[str]]:
    """Extract --flag KEY=VALUE pairs from args.

    Returns (parsed_dict, remaining_args).
    """
    parsed = {}
    remaining = []
    i = 0
    while i < len(args):
        if args[i] == flag and i + 1 < len(args):
            kv = args[i + 1]
            if '=' not in kv:
                print(f"error: {flag} expects KEY=VALUE, got: {kv}", file=sys.stderr)
                sys.exit(1)
            k, v = kv.split('=', 1)
            parsed[k.strip()] = v.strip()
            i += 2
        elif args[i].startswith(flag + '='):
            kv = args[i][len(flag) + 1 :]
            if '=' not in kv:
                print(f"error: {flag} expects KEY=VALUE, got: {kv}", file=sys.stderr)
                sys.exit(1)
            k, v = kv.split('=', 1)
            parsed[k.strip()] = v.strip()
            i += 1
        else:
            remaining.append(args[i])
            i += 1
    return parsed, remaining


def _find_runner_toml(config_path: Optional[str] = None) -> str:
    """Locate runner.toml.

    Search order: explicit path, $HAGENT_REPO_DIR/runner.toml, ./runner.toml.
    """
    if config_path:
        if not os.path.exists(config_path):
            print(f"error: config not found: {config_path}", file=sys.stderr)
            sys.exit(1)
        return config_path

    candidates = []
    repo_dir = os.environ.get('HAGENT_REPO_DIR')
    if repo_dir:
        candidates.append(os.path.join(repo_dir, 'runner.toml'))
    candidates.append(os.path.join(os.getcwd(), 'runner.toml'))

    for c in candidates:
        if os.path.exists(c):
            return c

    print('error: runner.toml not found', file=sys.stderr)
    if repo_dir:
        print(f'  searched: {repo_dir}/runner.toml and ./runner.toml', file=sys.stderr)
    else:
        print('  searched: ./runner.toml (set HAGENT_REPO_DIR for broader search)', file=sys.stderr)
    sys.exit(1)


def _extract_flag(args: List[str], flag: str) -> Tuple[bool, List[str]]:
    """Extract a boolean flag from args."""
    if flag in args:
        remaining = [a for a in args if a != flag]
        return True, remaining
    return False, args


def _extract_option(args: List[str], flag: str) -> Tuple[Optional[str], List[str]]:
    """Extract a --flag VALUE option from args."""
    remaining = []
    value = None
    i = 0
    while i < len(args):
        if args[i] == flag and i + 1 < len(args):
            value = args[i + 1]
            i += 2
        elif args[i].startswith(flag + '='):
            value = args[i][len(flag) + 1 :]
            i += 1
        else:
            remaining.append(args[i])
            i += 1
    return value, remaining


def cmd_setup(args: List[str]) -> int:
    """Handle: runner setup <tag> --name <profile> [options]

    <tag> is either a plain name (stored in <cache>/tags/<tag>/)
    or a path (stored directly there).
    """
    if not args or args[0] in ('--help', '-h'):
        print('usage: runner setup <tag> --name <profile> [--input N=T]...')
        print('       [--set K=V]... [--force] [--reuse] [--config PATH]')
        print()
        print('<tag> can be a name (tst1) or a path (./my_dir, /abs/path).')
        print('Names are stored under $HAGENT_CACHE_DIR/tags/<tag>/.')
        print('Paths are used directly.')
        return 0

    tag = args[0]
    rest = args[1:]

    # Extract flags
    name, rest = _extract_option(rest, '--name')
    if not name:
        print('error: --name <profile> is required', file=sys.stderr)
        return 1

    config_path, rest = _extract_option(rest, '--config')
    cache_dir, rest = _extract_option(rest, '--cache-dir')
    force, rest = _extract_flag(rest, '--force')
    reuse, rest = _extract_flag(rest, '--reuse')

    if force and reuse:
        print('error: --force and --reuse are mutually exclusive', file=sys.stderr)
        return 1

    inputs, rest = _parse_kv_args(rest, '--input')
    overrides, rest = _parse_kv_args(rest, '--set')

    if rest:
        print(f"error: unexpected arguments: {' '.join(rest)}", file=sys.stderr)
        return 1

    runner_toml = _find_runner_toml(config_path)

    try:
        toml_path = setup_tag(
            runner_toml_path=runner_toml,
            tag=tag,
            profile_name=name,
            cache_dir=cache_dir,
            inputs=inputs or None,
            overrides=overrides or None,
            force=force,
            reuse=reuse,
        )
        print(f'setup {tag} ({name}) -> {toml_path}')
        return 0
    except (TagError, ValueError, FileNotFoundError) as e:
        print(f'error: {e}', file=sys.stderr)
        return 1


def _load_config_file(path: str) -> tuple:
    """Load a config file (TOML or YAML).

    Returns (data, format) where format is 'toml' or 'yaml'.
    """
    if path.endswith(('.yaml', '.yml')):
        from .yaml2toml import load_yaml

        return load_yaml(path), 'yaml'
    else:
        return cfg.load_runner_toml(path), 'toml'


def _get_profiles_from_file(data: dict, fmt: str) -> List[tuple]:
    """Get (name, description) pairs for all profiles in a config file."""
    if fmt == 'yaml':
        result = []
        for p in data.get('profiles', []):
            name = p.get('name', '<unnamed>')
            desc = p.get('title', p.get('description', ''))
            result.append((name, desc))
        return result
    else:
        reserved = {'meta', 'default'}
        result = []
        for k in data:
            if k in reserved:
                continue
            desc = ''
            if isinstance(data.get(k), dict):
                desc = data[k].get('description', '')
            result.append((k, desc))
        return result


def _get_apis_from_file(data: dict, fmt: str, profile_name: str) -> dict:
    """Get APIs dict for a profile from a config file (TOML or YAML)."""
    if fmt == 'yaml':
        from .yaml2toml import find_profile

        profile = find_profile(data, profile_name)
        apis = {}
        for api in profile.get('apis', []):
            name = api.get('name', '')
            if name:
                apis[name] = api
        return apis
    else:
        merged = cfg.merge_default_and_profile(data, profile_name)
        return merged.get('api', {})


def _get_apis_from_tag(tag_config: dict) -> dict:
    """Get APIs dict from a tag's config.toml."""
    apis = tag_config.get('api', {})
    return dict(apis) if isinstance(apis, dict) else {}


def _print_profiles(profiles: List[tuple]) -> None:
    """Print a list of (name, description) profile entries."""
    if not profiles:
        print('no profiles found')
        return
    print(f'profiles ({len(profiles)}):')
    for name, desc in profiles:
        if desc:
            print(f'  {name:<24s} {desc}')
        else:
            print(f'  {name}')


def _print_apis(apis: dict, label: str) -> None:
    """Print a dict of {api_name: api_data} entries."""
    if not apis:
        print(f'no APIs in {label}')
        return
    print(f'{label} APIs ({len(apis)}):')
    for api_name, api_data in apis.items():
        desc = api_data.get('description', '')
        cmd = api_data.get('command', '')
        if desc:
            print(f'  {api_name:<24s} {desc}')
        else:
            print(f'  {api_name:<24s} {cmd}')


def cmd_config(args: List[str]) -> int:
    """Handle: runner config <path> [--list] [--name <profile>]"""
    if not args or args[0] in ('--help', '-h'):
        print('usage: runner config <path> --list')
        print('       runner config <path> --name <profile> --list')
        print()
        print('Inspect a config file (runner.toml or hagent.yaml) before setup.')
        print()
        print('examples:')
        print('  runner config runner.toml --list')
        print('  runner config runner.toml --name gcd --list')
        print('  runner config ../hagent.yaml --list')
        print('  runner config ../hagent.yaml --name gcd --list')
        return 0

    path = args[0]
    rest = args[1:]

    list_flag, rest = _extract_flag(rest, '--list')
    name, rest = _extract_option(rest, '--name')

    if rest:
        print(f"error: unexpected arguments: {' '.join(rest)}", file=sys.stderr)
        return 1

    if not list_flag:
        print('error: --list is required (use --help for usage)', file=sys.stderr)
        return 1

    try:
        data, fmt = _load_config_file(path)
    except (FileNotFoundError, ValueError) as e:
        print(f'error: {e}', file=sys.stderr)
        return 1

    if name is None:
        _print_profiles(_get_profiles_from_file(data, fmt))
        return 0
    else:
        try:
            apis = _get_apis_from_file(data, fmt, name)
        except ValueError as e:
            print(f'error: {e}', file=sys.stderr)
            return 1
        _print_apis(apis, name)
        return 0


def cmd_list(args: List[str]) -> int:
    """Handle: runner list <tag>"""
    if not args or args[0] in ('--help', '-h'):
        print('usage: runner list <tag>')
        print()
        print('List APIs available in an existing tag.')
        return 0

    tag_name = args[0]
    rest = args[1:]

    cache_dir, rest = _extract_option(rest, '--cache-dir')

    if rest:
        print(f"error: unexpected arguments: {' '.join(rest)}", file=sys.stderr)
        return 1

    try:
        from .tag import get_tag_dir, validate_tag

        tag_dir = get_tag_dir(tag_name, cache_dir)
        tag_config = validate_tag(tag_dir)
    except TagError as e:
        print(f'error: {e}', file=sys.stderr)
        return 1

    profile_name = tag_config.get('meta', {}).get('profile_name', tag_name)
    apis = _get_apis_from_tag(tag_config)
    _print_apis(apis, f'{tag_name} ({profile_name})')
    return 0


def cmd_run(api_name: str, args: List[str]) -> int:
    """Handle: runner <cmd> <tag> [--set K=V]... [--verbose]"""
    if not args or args[0] in ('--help', '-h'):
        print(f'usage: runner {api_name} <tag> [--set K=V]... [--verbose]')
        return 0

    tag_name = args[0]
    rest = args[1:]

    verbose, rest = _extract_flag(rest, '--verbose')
    cache_dir, rest = _extract_option(rest, '--cache-dir')
    overrides, rest = _parse_kv_args(rest, '--set')

    if rest:
        print(f"error: unexpected arguments: {' '.join(rest)}", file=sys.stderr)
        return 1

    try:
        return run_command(
            api_name=api_name,
            tag_name=tag_name,
            cache_dir=cache_dir,
            overrides=overrides or None,
            verbose=verbose,
        )
    except TagError as e:
        print(f'error: {e}', file=sys.stderr)
        return 1


def print_help() -> int:
    """Print top-level help."""
    print('usage: runner <command> <tag> [options]')
    print()
    print('built-in commands:')
    print('  setup    Create a new tag from a runner.toml profile')
    print('  config   Inspect a config file (profiles and APIs)')
    print('  list     List APIs in an existing tag')
    print('  help     Show this help')
    print()
    print('Any other command is treated as an API name:')
    print('  runner lint tst1')
    print('  runner compile tst1')
    print('  runner synth_asic tst1 --set top=MyModule')
    print()
    print('setup usage:')
    print('  runner setup <tag> --name <profile> [--input N=T]...')
    print('  runner setup <tag> --name <profile> [--set K=V]... [--force] [--reuse]')
    print()
    print('<tag> is a name (tst1) or a path (./my_dir, /abs/path).')
    print()
    print('run usage:')
    print('  runner <cmd> <tag> [--set K=V]... [--verbose]')
    return 0


def main(argv: Optional[List[str]] = None) -> int:
    """Entry point for the runner CLI."""
    args = argv if argv is not None else sys.argv[1:]

    if not args or args[0] in ('--help', '-h', 'help'):
        return print_help()

    cmd = args[0]
    rest = args[1:]

    BUILTINS = {
        'setup': cmd_setup,
        'config': cmd_config,
        'list': cmd_list,
    }

    if cmd in BUILTINS:
        return BUILTINS[cmd](rest)
    else:
        return cmd_run(cmd, rest)


if __name__ == '__main__':
    sys.exit(main())
