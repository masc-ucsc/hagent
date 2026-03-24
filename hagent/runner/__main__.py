"""CLI parsing and dispatch for the runner."""

import os
import sys
from typing import Annotated, Optional

import click
import typer

from . import config as cfg
from .commands import run_command
from .tag import TagError, setup_tag
from .tester import run_tests

app = typer.Typer(
    name='runner',
    no_args_is_help=True,
    add_completion=False,
    pretty_exceptions_enable=False,
    rich_markup_mode=None,
)


def _find_runner_toml(config_path: Optional[str] = None) -> str:
    """Locate runner.toml.

    Search order: explicit path, $HAGENT_REPO_DIR/runner.toml, ./runner.toml.
    """
    if config_path:
        if not os.path.exists(config_path):
            _error(f'config not found: {config_path}')
        return config_path

    candidates = []
    repo_dir = os.environ.get('HAGENT_REPO_DIR')
    if repo_dir:
        candidates.append(os.path.join(repo_dir, 'runner.toml'))
    candidates.append(os.path.join(os.getcwd(), 'runner.toml'))

    for c in candidates:
        if os.path.exists(c):
            return c

    msg = 'runner.toml not found'
    if repo_dir:
        msg += f'\n  searched: {repo_dir}/runner.toml and ./runner.toml'
    else:
        msg += '\n  searched: ./runner.toml (set HAGENT_REPO_DIR for broader search)'
    _error(msg)
    return ''  # unreachable, keeps type checker happy


def _error(msg: str, hint: Optional[str] = None) -> None:
    print(f'error: {msg}', file=sys.stderr)
    if hint:
        print(f'  (use "runner {hint} --help" for options and examples)', file=sys.stderr)
    raise typer.Exit(1)


def _parse_kv_list(pairs: Optional[list[str]]) -> dict[str, str]:
    """Parse ['K=V', ...] into {K: V}."""
    if not pairs:
        return {}
    result = {}
    for kv in pairs:
        if '=' not in kv:
            _error(f'expected KEY=VALUE, got: {kv}')
        k, v = kv.split('=', 1)
        result[k.strip()] = v.strip()
    return result


def _load_config_file(path: str) -> tuple:
    """Load a config file (TOML or YAML).

    Returns (data, format) where format is 'toml' or 'yaml'.
    """
    if path.endswith(('.yaml', '.yml')):
        from .yaml2toml import load_yaml

        return load_yaml(path), 'yaml'
    else:
        return cfg.load_runner_toml(path), 'toml'


def _get_profiles_from_file(data: dict, fmt: str) -> list[tuple]:
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


def _print_profiles(profiles: list[tuple]) -> None:
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


def _print_api_detail(api_name: str, api_data: dict) -> None:
    """Print detail for a single API including its options."""
    desc = api_data.get('description', '')
    cmd = api_data.get('command', '')
    print(f'{api_name}:')
    if desc:
        print(f'  description: {desc}')
    if cmd:
        print(f'  command: {cmd}')
    cwd = api_data.get('cwd', '')
    if cwd:
        print(f'  cwd: {cwd}')
    options = api_data.get('options', [])
    if not options:
        print('  options: (none)')
    else:
        print(f'  options ({len(options)}):')
        for opt in options:
            opt_name = opt.get('name', '')
            opt_desc = opt.get('description', '')
            opt_default = opt.get('default', None)
            line = f'    {opt_name:<20s} {opt_desc}'
            if opt_default is not None:
                line += f'  [default: {opt_default!r}]'
            print(line)


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


@app.command()
def config(
    path: Annotated[Optional[str], typer.Argument(help='Path to runner.toml or hagent.yaml')] = None,
    list: Annotated[bool, typer.Option('--list', help='List profiles or APIs')] = False,
    name: Annotated[Optional[str], typer.Option('--name', help='Show APIs for this profile')] = None,
) -> None:
    """Inspect a config file needed for creating a tag.

    \b
    Examples:
        runner config --list
        runner config --list --name gcd
        runner config ./repo/runner.toml --list
        runner config ../hagent.yaml --name gcd --list
    """
    if not list:
        _error('--list is required', hint='config')

    resolved = path if path else _find_runner_toml()

    try:
        data, fmt = _load_config_file(resolved)
    except (FileNotFoundError, ValueError) as e:
        _error(str(e), hint='config')
        return  # unreachable

    print(f'config: {resolved}')
    if name is None:
        _print_profiles(_get_profiles_from_file(data, fmt))
    else:
        try:
            apis = _get_apis_from_file(data, fmt, name)
        except ValueError as e:
            _error(str(e), hint='config')
            return
        _print_apis(apis, name)


@app.command()
def setup(
    tag: Annotated[str, typer.Argument(help='Tag name (tst1) or path (./my_dir, /abs/path)')],
    name: Annotated[str, typer.Option('--name', help='Profile name from runner.toml')],
    input: Annotated[Optional[list[str]], typer.Option('--input', help='Named input as NAME=TAG (repeatable)')] = None,
    set: Annotated[Optional[list[str]], typer.Option('--set', help='Config override as KEY=VALUE (repeatable)')] = None,
    force: Annotated[bool, typer.Option('--force', help='Delete and recreate existing tag')] = False,
    reuse: Annotated[bool, typer.Option('--reuse', help='Reuse existing tag directory')] = False,
    config: Annotated[Optional[str], typer.Option('--config', help='Path to runner.toml')] = None,
    cache_dir: Annotated[Optional[str], typer.Option('--cache-dir', help='Override cache directory')] = None,
) -> None:
    """Create a new tag from a runner.toml profile.

    \b
    Examples:
        runner setup tst1 --name gcd
        runner setup tst1 --name gcd --config ./repo/runner.toml
        runner setup ./my_build --name dualissue_d
        runner setup tst2 --name gcd --input orig_verilog=tst1
        runner setup tst1 --name gcd --set memory=8 --force
    """
    if force and reuse:
        _error('--force and --reuse are mutually exclusive', hint='setup')

    inputs = _parse_kv_list(input)
    overrides = _parse_kv_list(set)
    runner_toml = _find_runner_toml(config)

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
    except (TagError, ValueError, FileNotFoundError) as e:
        _error(str(e), hint='setup')


@app.command()
def status(
    tag: Annotated[str, typer.Argument(help='Tag name or path')],
    cache_dir: Annotated[Optional[str], typer.Option('--cache-dir', help='Override cache directory')] = None,
) -> None:
    """Show status and API list for an existing tag.

    \b
    Examples:
        runner status tst1
        runner status ./my_build
    """
    try:
        from .tag import get_tag_dir, validate_tag

        tag_dir = get_tag_dir(tag, cache_dir)
        tag_config = validate_tag(tag_dir)
    except TagError as e:
        _error(str(e), hint='status')
        return

    profile_name = tag_config.get('meta', {}).get('profile_name', tag)
    apis = _get_apis_from_tag(tag_config)
    _print_apis(apis, f'{tag} ({profile_name})')


def _tag_exists(tag: str, cache_dir: Optional[str] = None) -> bool:
    """Check if a tag directory exists."""
    try:
        from .tag import get_tag_dir

        tag_dir = get_tag_dir(tag, cache_dir)
        return os.path.isdir(tag_dir) and os.path.isfile(os.path.join(tag_dir, 'config.toml'))
    except (TagError, Exception):
        return False


@app.command()
def run(
    first: Annotated[str, typer.Argument(help='API name or tag (if tag, defaults to test)')],
    second: Annotated[Optional[str], typer.Argument(help='Tag name or path')] = None,
    set: Annotated[Optional[list[str]], typer.Option('--set', help='Config override as KEY=VALUE (repeatable)')] = None,
    verbose: Annotated[bool, typer.Option('--verbose', help='Show full output')] = False,
    quiet: Annotated[bool, typer.Option('--quiet', help='Only show summary (tests)')] = False,
    filter: Annotated[Optional[str], typer.Option('--filter', help='Run only tests matching glob pattern')] = None,
    jobs: Annotated[Optional[int], typer.Option('--jobs', help='Max parallel test workers (default: ncpus)')] = None,
    fail_fast: Annotated[bool, typer.Option('--fail-fast', help='Stop after first failure (tests)')] = False,
    timeout: Annotated[int, typer.Option('--timeout', help='Per-test timeout in seconds')] = 300,
    list: Annotated[bool, typer.Option('--list', help='List tests without running them')] = False,
    cache_dir: Annotated[Optional[str], typer.Option('--cache-dir', help='Override cache directory')] = None,
) -> None:
    """Run an API in a tag.

    \b
    runner run <api> <tag> [options]   Run a specific API
    runner run <tag> [options]         Run tests (shorthand for: run test <tag>)
    Examples:
      runner run lint tst1
      runner run compile tst1 --verbose
      runner run synth tst1 --set top=MyModule
      runner run tst1                     (run tests)
      runner run tst1 --list              (list tests)
      runner run tst1 --jobs 8
      runner run tst1 --filter 'test_alu*'
      runner run test tst1 --fail-fast
    """
    if second is not None:
        # Two positional args: runner run <api> <tag>
        api_name = first
        tag_name = second
    else:
        # One positional arg: could be a tag (run tests) or a mistake
        if _tag_exists(first, cache_dir):
            api_name = 'test'
            tag_name = first
        else:
            _error(f'tag not found: {first}', hint='run')
            return  # unreachable

    # --list handling
    if list:
        if second is None and api_name == 'test':
            # runner run <tag> --list → show available APIs
            try:
                from .tag import get_tag_dir, validate_tag

                tag_dir = get_tag_dir(tag_name, cache_dir)
                tag_config = validate_tag(tag_dir)
            except TagError as e:
                _error(str(e), hint='run')
                return
            profile_name = tag_config.get('meta', {}).get('profile_name', tag_name)
            apis = _get_apis_from_tag(tag_config)
            _print_apis(apis, f'{tag_name} ({profile_name})')
            raise typer.Exit(0)
        elif api_name != 'test':
            # runner run <api> <tag> --list → show API options
            try:
                from .tag import get_tag_dir, validate_tag

                tag_dir = get_tag_dir(tag_name, cache_dir)
                tag_config = validate_tag(tag_dir)
            except TagError as e:
                _error(str(e), hint='run')
                return
            apis = _get_apis_from_tag(tag_config)
            if api_name not in apis:
                _error(f"API '{api_name}' not found in tag '{tag_name}'", hint='run')
                return
            _print_api_detail(api_name, apis[api_name])
            raise typer.Exit(0)
        # else: api_name == 'test' with explicit second arg → falls through to run_tests(list_only=True)

    overrides = _parse_kv_list(set)

    try:
        if api_name == 'test':
            rc = run_tests(
                tag_name=tag_name,
                cache_dir=cache_dir,
                filter_pattern=filter,
                jobs=jobs,
                fail_fast=fail_fast,
                timeout=timeout,
                verbose=verbose,
                quiet=quiet,
                list_only=list,
            )
        else:
            rc = run_command(
                api_name=api_name,
                tag_name=tag_name,
                cache_dir=cache_dir,
                overrides=overrides or None,
                verbose=verbose,
            )
        raise typer.Exit(rc)
    except TagError as e:
        _error(str(e), hint='run')


def main(argv: Optional[list[str]] = None) -> int:
    """Entry point for the runner CLI."""
    args = argv if argv is not None else sys.argv[1:]

    # No args or 'help' → show help
    if not args or args[0] == 'help':
        args = ['--help']

    try:
        result = app(args, standalone_mode=False, prog_name='runner')
        if isinstance(result, int):
            return result
        return 0
    except SystemExit as e:
        return e.code if isinstance(e.code, int) else 0
    except click.exceptions.NoArgsIsHelpError:
        return 0
    except click.exceptions.MissingParameter as e:
        cmd = args[0] if args else ''
        print(f'error: missing required option: {e.param.name}', file=sys.stderr)
        if cmd:
            print(f'  (use "runner {cmd} --help" for options and examples)', file=sys.stderr)
        return 1
    except click.exceptions.UsageError as e:
        cmd = args[0] if args else ''
        print(f'error: {e.format_message()}', file=sys.stderr)
        if cmd:
            print(f'  (use "runner {cmd} --help" for options and examples)', file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
