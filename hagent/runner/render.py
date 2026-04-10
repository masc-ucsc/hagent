"""Compact output formatting for the runner."""

import json
import os
import sys
import time


def format_duration(seconds: float) -> str:
    """Format a duration for display."""
    if seconds < 60:
        return f'{seconds:.1f}s'
    minutes = int(seconds) // 60
    secs = seconds - minutes * 60
    return f'{minutes}m{secs:.0f}s'


def build_result_record(
    api_name: str,
    exit_code: int,
    elapsed_secs: float,
    log_path: str = '',
    tag_name: str = '',
    step_type: str = 'api',
) -> dict:
    """Build a structured result record for JSONL output."""
    return {
        'step': api_name,
        'type': step_type,
        'tag': tag_name,
        'status': 'PASS' if exit_code == 0 else 'FAIL',
        'exit_code': exit_code,
        'duration': round(elapsed_secs, 2),
        'log': log_path,
        'timestamp': time.strftime('%Y-%m-%dT%H:%M:%S'),
    }


def append_jsonl(tag_dir: str, record: dict) -> None:
    """Append a JSON record to <tag>/runner_results.jsonl."""
    jsonl_path = os.path.join(tag_dir, 'runner_results.jsonl')
    with open(jsonl_path, 'a') as f:
        f.write(json.dumps(record) + '\n')


def print_result(
    api_name: str,
    exit_code: int,
    elapsed_secs: float,
    log_path: str = '',
    stderr_tail: str = '',
    tag_name: str = '',
    verbose: bool = False,
    tag_dir: str = '',
    step_type: str = 'api',
) -> None:
    """Print result as JSONL to stdout and compact text to stderr.

    Also appends to <tag>/runner_results.jsonl if tag_dir is provided.
    """
    record = build_result_record(api_name, exit_code, elapsed_secs, log_path, tag_name, step_type)

    # JSONL to stdout (default agent-facing format)
    print(json.dumps(record))

    # Compact text to stderr (human-readable)
    dur = format_duration(elapsed_secs)
    label = 'PASS' if exit_code == 0 else 'FAIL'
    line = f'{label} {api_name:<20s} {dur}'
    print(line, file=sys.stderr)

    if exit_code != 0:
        if log_path:
            print(f'  log: {log_path}', file=sys.stderr)
        if tag_name:
            print(f'  repro: runner run {api_name} @{tag_name} --verbose', file=sys.stderr)
        if verbose and stderr_tail:
            for sline in stderr_tail.strip().splitlines()[-20:]:
                print(f'  | {sline}', file=sys.stderr)

    # Append to runner_results.jsonl
    if tag_dir:
        append_jsonl(tag_dir, record)
