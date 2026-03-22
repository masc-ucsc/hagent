"""Single-command execution for the runner."""

import os
import sys
import time
from typing import Dict, Optional

from . import config as cfg
from . import render
from .tag import TagError, get_tag_dir, resolve_input_dirs, validate_tag


def run_command(
    api_name: str,
    tag_name: str,
    cache_dir: Optional[str] = None,
    overrides: Optional[Dict[str, str]] = None,
    verbose: bool = False,
) -> int:
    """Execute a single API command against a tag.

    Returns the command's exit code.
    """
    # Load tag config
    tag_dir = get_tag_dir(tag_name, cache_dir)
    tag_config = validate_tag(tag_dir)

    # Find the API
    api_config = cfg.get_api_config(tag_config, api_name)
    if api_config is None:
        available = cfg.list_api_names(tag_config)
        print(f"error: no API '{api_name}' in tag '{tag_name}'", file=sys.stderr)
        if available:
            print(f"  available: {', '.join(available)}", file=sys.stderr)
        return 1

    # Apply ephemeral overrides
    if overrides:
        tag_config = cfg.apply_overrides(tag_config, overrides)
        api_config = cfg.get_api_config(tag_config, api_name) or api_config

    # Resolve input dirs
    inputs = tag_config.get('inputs', {})
    input_dirs = {}
    if inputs:
        input_dirs = resolve_input_dirs(dict(inputs), cache_dir)

    # Build placeholder context
    context = cfg.build_context(tag_name, tag_dir, input_dirs, api_config)

    # Resolve option overrides into context
    if overrides:
        for opt in api_config.get('options', []):
            opt_name = opt.get('name', '')
            if opt_name and opt_name in overrides:
                fmt = opt.get('format', '')
                if fmt:
                    context[opt_name] = fmt.replace('{value}', overrides[opt_name])
                else:
                    context[opt_name] = overrides[opt_name]

    # Resolve command and cwd
    command = api_config.get('command', '')
    if not command:
        print(f"error: API '{api_name}' has no command", file=sys.stderr)
        return 1

    command = cfg.resolve_options(command, api_config, overrides)
    command = cfg.resolve_placeholders(command, context)
    command = os.path.expandvars(command)

    cwd = api_config.get('cwd', '')
    if cwd:
        cwd = cfg.resolve_placeholders(cwd, context)
        cwd = os.path.expandvars(cwd)

    # Build environment
    env = cfg.build_env(tag_config, tag_dir)

    # Resolve cwd again with the built env
    if cwd:
        for k, v in env.items():
            cwd = cwd.replace(f'${k}', v)

    # Execute via Builder
    log_path = os.path.join(tag_dir, 'logs', f'{api_name}.log')
    os.makedirs(os.path.dirname(log_path), exist_ok=True)

    start = time.monotonic()
    exit_code, stdout, stderr = _execute(command, cwd, env, verbose)
    elapsed = time.monotonic() - start

    # Write log
    with open(log_path, 'w') as f:
        f.write(f'# runner {api_name} {tag_name}\n')
        f.write(f'# command: {command}\n')
        f.write(f'# cwd: {cwd}\n')
        f.write(f'# exit_code: {exit_code}\n\n')
        if stdout:
            f.write('=== stdout ===\n')
            f.write(stdout)
            f.write('\n')
        if stderr:
            f.write('=== stderr ===\n')
            f.write(stderr)
            f.write('\n')

    # Print compact result
    render.print_result(
        api_name=api_name,
        exit_code=exit_code,
        elapsed_secs=elapsed,
        log_path=log_path,
        stderr_tail=stderr,
        tag_name=tag_name,
        verbose=verbose,
    )

    # In verbose mode, also print stdout
    if verbose and stdout:
        print(stdout)

    return exit_code


def _execute(command: str, cwd: str, env: dict, verbose: bool) -> tuple:
    """Execute command via Builder.run_cmd().

    Falls back to subprocess if Builder setup fails.
    Returns (exit_code, stdout, stderr).
    """
    try:
        from hagent.inou.builder import Builder

        builder = Builder()
        if builder.setup():
            effective_cwd = cwd if cwd else '.'
            exit_code, stdout, stderr = builder.run_cmd(command, effective_cwd, env, quiet=not verbose)
            return exit_code, stdout, stderr
    except Exception:
        pass

    # Fallback to subprocess
    import subprocess

    try:
        result = subprocess.run(
            command,
            shell=True,
            cwd=cwd if cwd else None,
            env=env,
            capture_output=True,
            text=True,
        )
        return result.returncode, result.stdout, result.stderr
    except Exception as e:
        return 1, '', str(e)
