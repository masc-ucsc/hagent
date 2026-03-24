"""Compact output formatting for the runner."""

import sys


def format_duration(seconds: float) -> str:
    """Format a duration for display."""
    if seconds < 60:
        return f'{seconds:.1f}s'
    minutes = int(seconds) // 60
    secs = seconds - minutes * 60
    return f'{minutes}m{secs:.0f}s'


def print_result(
    api_name: str,
    exit_code: int,
    elapsed_secs: float,
    log_path: str = '',
    stderr_tail: str = '',
    tag_name: str = '',
    verbose: bool = False,
) -> None:
    """Print a compact one-line result to stderr."""
    dur = format_duration(elapsed_secs)
    label = 'PASS' if exit_code == 0 else 'FAIL'
    line = f'{label} {api_name:<20s} {dur}'
    print(line, file=sys.stderr)

    if exit_code != 0:
        if log_path:
            print(f'  log: {log_path}', file=sys.stderr)
        if tag_name:
            print(f'  repro: runner run {api_name} {tag_name} --verbose', file=sys.stderr)
        if verbose and stderr_tail:
            for sline in stderr_tail.strip().splitlines()[-20:]:
                print(f'  | {sline}', file=sys.stderr)
