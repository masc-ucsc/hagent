"""Parallel test orchestration for the runner."""

import fnmatch
import os
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import List, Optional

import tomlkit

from . import config as cfg
from . import render
from .tag import TagError, get_tag_dir, resolve_input_dirs, validate_tag


class TestResult:
    """Result of a single test execution."""

    __slots__ = ('name', 'exit_code', 'elapsed', 'stdout', 'stderr', 'skipped')

    def __init__(self, name: str, exit_code: int, elapsed: float, stdout: str = '', stderr: str = '', skipped: bool = False):
        self.name = name
        self.exit_code = exit_code
        self.elapsed = elapsed
        self.stdout = stdout
        self.stderr = stderr
        self.skipped = skipped


def discover_tests(tag_config: dict, tag_dir: str, env: dict) -> List[str]:
    """Discover test names from tag config.

    Uses `tests.list` (static list) or `tests.list_cmd` (command that prints
    test names, one per line).  Static list takes precedence.
    """
    tests = tag_config.get('tests', {})
    if not isinstance(tests, dict):
        return []

    # Static list
    test_list = tests.get('list', [])
    if test_list:
        return list(test_list)

    # Dynamic discovery via command
    list_cmd = tests.get('list_cmd', '')
    if list_cmd:
        cwd = tests.get('cwd', tag_dir)
        try:
            result = subprocess.run(
                list_cmd,
                shell=True,
                cwd=cwd,
                env=env,
                capture_output=True,
                text=True,
                timeout=60,
            )
            if result.returncode == 0:
                return [line.strip() for line in result.stdout.splitlines() if line.strip()]
        except Exception:
            pass

    return []


def filter_tests(test_names: List[str], pattern: Optional[str]) -> List[str]:
    """Filter test names by glob pattern."""
    if not pattern:
        return test_names
    return [t for t in test_names if fnmatch.fnmatch(t, pattern)]


def load_test_history(tag_dir: str) -> dict:
    """Load test history from <tag>/tests.toml."""
    path = os.path.join(tag_dir, 'tests.toml')
    if not os.path.exists(path):
        return {}
    try:
        with open(path, 'r') as f:
            return dict(tomlkit.parse(f.read()))
    except Exception:
        return {}


def save_test_history(tag_dir: str, history: dict) -> None:
    """Save test history to <tag>/tests.toml."""
    path = os.path.join(tag_dir, 'tests.toml')
    with open(path, 'w') as f:
        f.write(tomlkit.dumps(history))


def order_tests(test_names: List[str], history: dict) -> List[str]:
    """Order tests: previously failed first, then by name."""
    failed = []
    rest = []
    for t in test_names:
        info = history.get(t, {})
        if isinstance(info, dict) and info.get('status') == 'FAIL':
            failed.append(t)
        else:
            rest.append(t)
    return failed + rest


def _run_single_test(
    test_name: str,
    run_cmd: str,
    build_cmd: str,
    tag_config: dict,
    tag_name: str,
    tag_dir: str,
    env: dict,
    timeout: int,
    verbose: bool,
) -> TestResult:
    """Execute a single test and return its result."""
    # Build placeholder context
    inputs = tag_config.get('inputs', {})
    input_dirs = {}
    if inputs:
        try:
            input_dirs = resolve_input_dirs(dict(inputs))
        except TagError:
            pass

    context = cfg.build_context(tag_name, tag_dir, input_dirs)
    context['test_name'] = test_name

    # Resolve command
    command = cfg.resolve_placeholders(run_cmd, context)
    command = command.replace('{test_name}', test_name)

    cwd = tag_config.get('tests', {}).get('cwd', '')
    if cwd:
        cwd = cfg.resolve_placeholders(cwd, context)

    # Resolve Docker
    docker_image = cfg.get_docker_image(tag_config)

    # Log file
    log_path = os.path.join(tag_dir, 'logs', f'test_{test_name}.log')
    os.makedirs(os.path.dirname(log_path), exist_ok=True)

    start = time.monotonic()

    try:
        from .commands import _execute

        exit_code, stdout, stderr = _execute(
            command,
            cwd or '.',
            env,
            verbose,
            docker_image=docker_image,
        )
    except Exception as e:
        exit_code = 1
        stdout = ''
        stderr = str(e)

    elapsed = time.monotonic() - start

    # Write log
    with open(log_path, 'w') as f:
        f.write(f'# test {test_name}\n')
        f.write(f'# command: {command}\n')
        f.write(f'# exit_code: {exit_code}\n\n')
        if stdout:
            f.write('=== stdout ===\n')
            f.write(stdout)
            f.write('\n')
        if stderr:
            f.write('=== stderr ===\n')
            f.write(stderr)
            f.write('\n')

    return TestResult(
        name=test_name,
        exit_code=exit_code,
        elapsed=elapsed,
        stdout=stdout,
        stderr=stderr,
    )


def run_tests(
    tag_name: str,
    cache_dir: Optional[str] = None,
    filter_pattern: Optional[str] = None,
    jobs: Optional[int] = None,
    fail_fast: bool = False,
    timeout: int = 300,
    verbose: bool = False,
    quiet: bool = False,
    list_only: bool = False,
) -> int:
    """Run tests for a tag.

    Returns 0 if all tests pass, 1 otherwise.
    """
    # Load tag config
    tag_dir = get_tag_dir(tag_name, cache_dir)
    tag_config = validate_tag(tag_dir)

    tests_config = tag_config.get('tests', {})
    if not tests_config or not isinstance(tests_config, dict):
        print(f"error: no [tests] section in tag '{tag_name}'", file=sys.stderr)
        return 1

    # Build environment
    env = cfg.build_env(tag_config, tag_dir)

    # Get test timeout from config (CLI overrides config)
    config_timeout = tests_config.get('timeout', 300)
    if timeout == 300:  # default, check config
        timeout = config_timeout

    # Discover tests
    test_names = discover_tests(tag_config, tag_dir, env)
    if not test_names:
        print('no tests found', file=sys.stderr)
        return 1

    # Filter
    test_names = filter_tests(test_names, filter_pattern)
    if not test_names:
        print(f'no tests matching: {filter_pattern}', file=sys.stderr)
        return 1

    # List only
    if list_only:
        for t in test_names:
            print(t)
        return 0

    # Order by history (failed-first)
    history = load_test_history(tag_dir)
    test_names = order_tests(test_names, history)

    # Run build step if configured
    build_cmd = tests_config.get('build', '')
    if build_cmd:
        context = cfg.build_context(tag_name, tag_dir)
        build_cmd_resolved = cfg.resolve_placeholders(build_cmd, context)
        build_cwd = tests_config.get('cwd', '')
        if build_cwd:
            build_cwd = cfg.resolve_placeholders(build_cwd, context)

        if not quiet:
            print(f'building ({len(test_names)} tests queued)...', file=sys.stderr)

        from .commands import _execute

        docker_image = cfg.get_docker_image(tag_config)
        start = time.monotonic()
        exit_code, stdout, stderr = _execute(
            build_cmd_resolved,
            build_cwd or '.',
            env,
            verbose,
            docker_image=docker_image,
        )
        elapsed = time.monotonic() - start

        log_path = os.path.join(tag_dir, 'logs', 'test_build.log')
        os.makedirs(os.path.dirname(log_path), exist_ok=True)
        with open(log_path, 'w') as f:
            f.write(f'# build step\n# command: {build_cmd_resolved}\n# exit_code: {exit_code}\n\n')
            if stdout:
                f.write('=== stdout ===\n')
                f.write(stdout + '\n')
            if stderr:
                f.write('=== stderr ===\n')
                f.write(stderr + '\n')

        render.print_result('build', exit_code, elapsed, log_path, stderr, tag_name, verbose)

        if exit_code != 0:
            return 1

    # Run tests
    run_cmd = tests_config.get('run', '')
    if not run_cmd:
        print('error: tests.run command not configured', file=sys.stderr)
        return 1

    max_jobs = jobs if jobs else min(os.cpu_count() or 1, len(test_names))
    results: List[TestResult] = []
    failed = False

    if max_jobs == 1 or len(test_names) == 1:
        # Sequential execution
        for test_name in test_names:
            result = _run_single_test(
                test_name,
                run_cmd,
                build_cmd,
                tag_config,
                tag_name,
                tag_dir,
                env,
                timeout,
                verbose,
            )
            results.append(result)
            if not quiet:
                log_path = os.path.join(tag_dir, 'logs', f'test_{test_name}.log')
                render.print_result(test_name, result.exit_code, result.elapsed, log_path, result.stderr, tag_name, verbose)
            if result.exit_code != 0:
                failed = True
                if fail_fast:
                    break
    else:
        # Parallel execution
        with ThreadPoolExecutor(max_workers=max_jobs) as executor:
            futures = {}
            for test_name in test_names:
                fut = executor.submit(
                    _run_single_test,
                    test_name,
                    run_cmd,
                    build_cmd,
                    tag_config,
                    tag_name,
                    tag_dir,
                    env,
                    timeout,
                    verbose,
                )
                futures[fut] = test_name

            for fut in as_completed(futures):
                result = fut.result()
                results.append(result)
                if not quiet:
                    log_path = os.path.join(tag_dir, 'logs', f'test_{result.name}.log')
                    render.print_result(result.name, result.exit_code, result.elapsed, log_path, result.stderr, tag_name, verbose)
                if result.exit_code != 0:
                    failed = True
                    if fail_fast:
                        executor.shutdown(wait=False, cancel_futures=True)
                        break

    # Update history
    for r in results:
        history[r.name] = {
            'status': 'PASS' if r.exit_code == 0 else 'FAIL',
            'duration': round(r.elapsed, 2),
            'last_run': time.strftime('%Y-%m-%dT%H:%M:%S'),
        }
    save_test_history(tag_dir, history)

    # Summary
    passed = sum(1 for r in results if r.exit_code == 0)
    failed_count = sum(1 for r in results if r.exit_code != 0)
    skipped = len(test_names) - len(results)

    if not quiet:
        print(file=sys.stderr)
        print(f'RESULT: {passed} passed, {failed_count} failed, {skipped} skipped', file=sys.stderr)

    return 1 if failed else 0
