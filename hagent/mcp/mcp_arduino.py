#!/usr/bin/env python3
"""
MCP Command: Arduino

Arduino development tool with unified CLI and MCP interfaces.
Provides complete Arduino workflow: board setup, sketch creation, building, uploading, and monitoring.
"""

import argparse
import sys
import os
import subprocess
import shutil
from typing import Dict, Any, Optional, List, Tuple
import difflib
import re
import json
import sys as _sys
import os as _os
import pty
import select
import time
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
from config_sync import fetch_remote_configs

def get_mcp_schema() -> Dict[str, Any]:
    """Return MCP tool schema for Arduino development command."""

    available_apis = [
        'install',
        'list_boards',
        'new_sketch',
        'compile',
        'upload',
        'monitor',
        'cli',
        'env',
        'refresh_config',
    ]

    return {
        'name': 'hagent_arduino',
        'description': 'Arduino development tool for managing boards, sketches, compiling, and uploading. USE THIS TOOL for all Arduino operations; DO NOT run arduino-cli directly in the shell.',
        'inputSchema': {
            'type': 'object',
            'properties': {
                'api': {
                    'type': 'string',
                    'description': 'API command to execute',
                    'enum': available_apis,
                },
                'args': {
                    'type': 'string',
                    'description': 'Arguments for the API command:\n'
                    '- install: (OPTIONAL) Board identifier (e.g., "nanor4"). Lists available boards if ambiguous. Automatically installs the required core.\n'
                    '- list_boards: (NO ARGS) Lists currently connected Arduino boards. Returns a filtered list of identified boards with FQBNs.\n'
                    '- new_sketch: (REQUIRED) Sketch name\n'
                    '- compile: (OPTIONAL) Sketch name. Defaults to "Blink". AUTOMATICALLY uses FQBN from installed config. DO NOT pass flags manually.\n'
                    '- upload: (OPTIONAL) Sketch name. Defaults to "Blink". AUTOMATICALLY detects port and FQBN from config. DO NOT pass flags manually.\n'
                    '- monitor: (NO ARGS) Does not use the `args` parameter. The `timeout` parameter can be used to set the duration (default: 30s).\n'
                    '- cli: (REQUIRED) Arbitrary arduino-cli command string\n'
                    '- refresh_config: (NO ARGS) Fetches latest board configs from the remote repository.',
                },
                'timeout': {
                    'type': 'integer',
                    'description': 'Timeout in seconds for monitor command (default: 30)',
                    'default': 30,
                },
            },
            'required': ['api'],
        },
    }


# ==============================================================================
# INTERNAL HELPER FUNCTIONS
# ==============================================================================


def initialize_arduino_env() -> Dict[str, Any]:
    """
    Source export.sh and load environment variables.
    Returns a result dict with 'success', 'stdout', 'stderr'.
    """
    # Locate export.sh in HAGENT_CACHE_DIR
    cache_dir = os.environ.get('HAGENT_CACHE_DIR', '.')
    arduino_toolkit_path = os.path.join(cache_dir, 'arduino-toolkit')
    export_sh_path = os.path.join(arduino_toolkit_path, 'export.sh')

    if not os.path.exists(export_sh_path):
        return {
            'success': False,
            'exit_code': 1,
            'stdout': '',
            'stderr': f"Arduino toolkit not found at {arduino_toolkit_path}. Please run 'api_install' tool first to setup the Arduino toolkit.",
        }

    # Source export.sh in a separate process and load the dumped ENV variables
    # Use a one-liner Python command to avoid heredoc syntax issues
    cmd_str = f"source {export_sh_path} >/dev/null 2>&1 && python3 -c 'import os, json; print(json.dumps(dict(os.environ)))'"

    try:
        # Use shell=True with bash to ensure 'source' works
        export_proc = subprocess.run(cmd_str, shell=True, executable='/bin/bash', capture_output=True, text=True, check=True)
        os.environ.update(json.loads(export_proc.stdout))

        if not shutil.which('arduino-cli'):
            return {
                'success': False,
                'exit_code': 1,
                'stdout': '',
                'stderr': 'arduino-cli not found in PATH after sourcing export.sh',
            }

        return {'success': True, 'stdout': '', 'stderr': ''}
    except (subprocess.CalledProcessError, json.JSONDecodeError) as e:
        stderr = e.stderr if hasattr(e, 'stderr') else str(e)
        return {'success': False, 'exit_code': 1, 'stdout': '', 'stderr': f'Failed to initialize Arduino environment: {stderr}'}


def _run_monitor(port: str, fqbn: str, timeout: int = 30) -> Dict[str, Any]:
    """
    Internal helper to run arduino-cli monitor using a PTY so the process
    thinks it has a real terminal, preventing immediate EOF-driven exit.
    """

    if not port:
        return {
            'success': False,
            'exit_code': 1,
            'stdout': '',
            'stderr': 'No port specified for monitor',
        }

    monitor_cmd = f'arduino-cli monitor -p {port} --fqbn {fqbn}'

    try:
        if not shutil.which('arduino-cli'):
            res = initialize_arduino_env()
            if not res['success']:
                return res

        master_fd, slave_fd = pty.openpty()

        proc = subprocess.Popen(
            monitor_cmd,
            stdout=slave_fd,
            stderr=slave_fd,
            stdin=slave_fd,
            close_fds=True,
            shell=True,
        )
        os.close(slave_fd)

        chunks = []
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            remaining = deadline - time.monotonic()
            r, _, _ = select.select([master_fd], [], [], remaining)
            if r:
                try:
                    data = os.read(master_fd, 1024).decode('utf-8', errors='replace')
                    chunks.append(data)
                except OSError:
                    break

        proc.kill()
        proc.wait()
        os.close(master_fd)

        return {
            'success': True,
            'exit_code': 0,
            'stdout': ''.join(chunks),
            'stderr': '',
        }

    except Exception as e:
        return {'success': False, 'exit_code': 1, 'stdout': '', 'stderr': str(e)}


def _get_connected_boards() -> List[Dict[str, Any]]:
    """
    Get list of connected boards using arduino-cli board list.
    """
    if not shutil.which('arduino-cli'):
        res = initialize_arduino_env()
        if not res['success']:
            return []

    try:
        res = subprocess.run('arduino-cli board list --format json', shell=True, capture_output=True, text=True, check=True)
        data = json.loads(res.stdout)
        if isinstance(data, list):
            return data
        elif isinstance(data, dict):
            return data.get('detected_ports', [])
        return []
    except Exception:
        return []


def _resolve_board_info(target_fqbn: Optional[str] = None) -> Tuple[Optional[str], Optional[str]]:
    """
    Resolve FQBN and Port.
    """
    connected = _get_connected_boards()

    # Helper to find port for a specific FQBN in connected list
    def find_port_for_fqbn(fqbn_to_find):
        for item in connected:
            boards = item.get('matching_boards', item.get('boards', []))
            for b in boards:
                if b.get('fqbn') == fqbn_to_find:
                    return item.get('port', {}).get('address', item.get('address'))
        return None

    # Helper to find first valid board in connected list
    def find_any_board():
        for item in connected:
            boards = item.get('matching_boards', item.get('boards', []))
            if boards:
                return boards[0].get('fqbn'), item.get('port', {}).get('address', item.get('address'))
        return None, None

    detected_port = None

    if target_fqbn:
        # Case 1: Specific FQBN provided, find its port
        detected_port = find_port_for_fqbn(target_fqbn)
        return target_fqbn, detected_port

    # Case 2: No specific FQBN, try auto-detect any connected board
    detected_fqbn, detected_port = find_any_board()
    return detected_fqbn, detected_port


def _get_available_ports_hint() -> str:
    """
    Build a human-readable hint of available serial ports for error messages.
    """
    connected = _get_connected_boards()
    lines = []
    for item in connected:
        addr = item.get('port', {}).get('address') or item.get('address', '')
        label = item.get('port', {}).get('protocol_label') or item.get('protocol_label', '')
        props = item.get('port', {}).get('properties') or item.get('properties', {})
        vid = props.get('vid', '')
        pid = props.get('pid', '')
        detail = label
        if vid:
            detail += f', VID:{vid}'
            if pid:
                detail += f' PID:{pid}'
        lines.append(f'  {addr}  [{detail}]' if detail else f'  {addr}')
    if not lines:
        return '  (no serial ports detected)'
    return '\n'.join(lines)


def _get_board_info_from_md() -> Dict[str, str]:
    """
    Extract board metadata from AGENTS.md, GEMINI.md, or CLAUDE.md in the repo directory.
    """
    repo_dir = os.environ.get('HAGENT_REPO_DIR', '.')
    for filename in ['AGENTS.md', 'GEMINI.md', 'CLAUDE.md']:
        path = os.path.join(repo_dir, filename)
        if os.path.exists(path):
            try:
                with open(path, 'r') as f:
                    content = f.read()

                # Extract FQBN (look for `- `fqbn`: identifier`)
                fqbn_match = re.search(r'-\s*`fqbn`\s*:\s*([a-zA-Z0-9_:]+)', content)
                # Extract Core (look for `- `core`: identifier`)
                core_match = re.search(r'-\s*`core`\s*:\s*([a-zA-Z0-9_:]+)', content)

                info = {}
                if fqbn_match:
                    info['fqbn'] = fqbn_match.group(1).strip()
                if core_match:
                    info['core'] = core_match.group(1).strip()

                if info:
                    return info
            except Exception:
                pass
    return {}


def _parse_board_config(file_path: str) -> Dict[str, str]:
    """
    Parses a board configuration Markdown file to extract metadata.
    """
    try:
        with open(file_path, 'r') as f:
            content = f.read()

        board_match = re.search(r'-\s*`board`\s*:\s*([a-zA-Z0-9_:]+)', content)
        board_id = board_match.group(1).strip() if board_match else ''

        model_match = re.search(r'-\s*`model`\s*:\s*(.+)$', content, re.MULTILINE)
        model_name = model_match.group(1).strip() if model_match else board_id

        return {
            'name': model_name,
            'model': board_id,
            'file_name': file_path,
            'short_name': os.path.basename(file_path).replace('.md', ''),
        }
    except Exception:
        return {
            'name': os.path.basename(file_path),
            'model': '',
            'file_name': file_path,
            'short_name': os.path.basename(file_path).replace('.md', ''),
        }


def _is_core_installed(core_name: str) -> bool:
    """
    Check if the specified core is installed.
    """
    if not core_name:
        return False

    cache_dir = os.environ.get('HAGENT_CACHE_DIR', '.')
    toolkit_dir = os.path.join(cache_dir, 'arduino-toolkit')
    config_path = os.path.join(toolkit_dir, 'arduino-cli.yaml')
    config_arg = f'--config-file {config_path}' if os.path.exists(config_path) else ''

    try:
        if not shutil.which('arduino-cli'):
            res = initialize_arduino_env()
            if not res['success']:
                return False

        res = subprocess.run(f'arduino-cli {config_arg} core list --format json', shell=True, capture_output=True, text=True)
        if res.returncode != 0:
            return False

        data = json.loads(res.stdout)
        cores = data if isinstance(data, list) else data.get('platforms', data.get('cores', []))

        for c in cores:
            if c.get('id') == core_name:
                return True
    except Exception:
        pass
    return False


def _fuzzy_match_board(args: str, board_details: list) -> Optional[Dict[str, Any]]:
    """
    Find the best board match using fuzzy string matching.
    Returns a single board item if a good match is found, otherwise None.
    """
    if not args:
        return None

    # Get a list of board names and short_names to match against
    names = [b['short_name'] for b in board_details] + [b['name'] for b in board_details]

    # Find the best match
    matches = difflib.get_close_matches(args, list(set(names)), n=1, cutoff=0.5)

    if matches:
        # Find the full board_detail dictionary for the matched name
        for b in board_details:
            if b['short_name'] == matches[0] or b['name'] == matches[0]:
                return b
    return None


def _install_core(core_name: str) -> Dict[str, Any]:
    """
    Install a specific Arduino core.
    """
    if not shutil.which('arduino-cli'):
        res = initialize_arduino_env()
        if not res['success']:
            return res

    print(f'Installing core {core_name}...')
    try:
        subprocess.run('arduino-cli core update-index', shell=True, capture_output=True)
        cmd = f'arduino-cli core install {core_name}'
        res = subprocess.run(cmd, shell=True, capture_output=True, text=True, check=True)
        return {
            'success': True,
            'exit_code': 0,
            'stdout': res.stdout,
            'stderr': res.stderr,
        }
    except subprocess.CalledProcessError as e:
        return {
            'success': False,
            'exit_code': e.returncode,
            'stdout': e.stdout,
            'stderr': e.stderr,
        }


# ==============================================================================
# API FUNCTIONS
# ==============================================================================


def api_refresh_config(args: Optional[str] = None) -> Dict[str, Any]:
    """
    Refresh board and platform configurations from the remote repository.
    Returns a list of available Arduino boards after the refresh.
    """
    synced = fetch_remote_configs()

    if not synced.get('board') and not synced.get('platform'):
        return {
            'success': False,
            'exit_code': 1,
            'stdout': '',
            'stderr': 'Failed to fetch configs from remote. Check network connectivity.',
        }

    configs_board_path = os.path.join(os.environ.get('HAGENT_ROOT', '.'), 'hagent', 'mcp', 'configs', 'board')
    arduino_boards = [b for b in synced.get('board', []) if b.startswith('board_arduino_')]

    board_details = []
    for short_name in arduino_boards:
        info = _parse_board_config(os.path.join(configs_board_path, short_name + '.md'))
        board_details.append(f'{info["name"]} (ID: {info["short_name"]})')

    return {
        'success': True,
        'exit_code': 0,
        'stdout': 'Configs refreshed. Available Arduino boards:\n' + '\n'.join(board_details),
        'stderr': '',
        'boards': board_details,
    }


def api_install(args: Optional[str] = None) -> Dict[str, Any]:
    """
    Install Arduino toolkit and configure board.

    Args:
        args: Board identifier or description (e.g. "nanor4")
    """
    stdout = ''

    # 1. Install toolkit if not present (Basic setup)
    cache_dir = os.environ.get('HAGENT_CACHE_DIR', '.')
    toolkit_dir = os.path.join(cache_dir, 'arduino-toolkit')
    install_script_path = os.path.join(toolkit_dir, 'install.sh')

    if not os.path.isdir(toolkit_dir):
        try:
            repo_url = 'https://github.com/sri-ucsc/arduino-toolkit'
            print('Cloning arduino-toolkit')
            res = subprocess.run(f'git clone {repo_url}', cwd=cache_dir, shell=True, check=True, capture_output=True, text=True)
            stdout += res.stdout
        except subprocess.CalledProcessError as e:
            return {
                'success': False,
                'exit_code': e.returncode,
                'stdout': stdout + e.stdout,
                'stderr': e.stderr,
                'installation_path': toolkit_dir,
            }

    # Check if we need to run install.sh for the toolkit infrastructure
    arduino_cli_dir = os.path.join(toolkit_dir, 'arduino-cli')
    if not os.path.isdir(arduino_cli_dir):
        if os.path.exists(install_script_path):
            try:
                print('Installing Arduino CLI...')
                res = subprocess.run('./install.sh', cwd=toolkit_dir, shell=True, check=True, capture_output=True, text=True)
                stdout += res.stdout
                init_res = initialize_arduino_env()
                if not init_res['success']:
                    return init_res
            except subprocess.CalledProcessError as e:
                return {
                    'success': False,
                    'exit_code': e.returncode,
                    'stdout': stdout + e.stdout,
                    'stderr': e.stderr,
                    'installation_path': toolkit_dir,
                }

    # 2. Refresh configs from remote (best-effort, non-blocking)
    fetch_remote_configs()

    # 3. Board Selection Logic
    configs_path = os.path.join(os.environ.get('HAGENT_ROOT', '.'), 'hagent', 'mcp', 'configs')
    board_configs_path = os.path.join(configs_path, 'board')
    if not os.path.isdir(board_configs_path):
        # Fallback if configs dir not found (shouldn't happen in prod)
        return {'success': True, 'stdout': stdout + '\nToolkit installed, but no board configs found.', 'stderr': ''}

    # Filter for Arduino boards only (files starting with board_arduino_)
    board_files = [f for f in os.listdir(board_configs_path) if f.startswith('board_arduino_') and f.endswith('.md')]
    board_details = []

    for f in board_files:
        info = _parse_board_config(os.path.join(board_configs_path, f))
        board_details.append(info)

    selected_board = None

    # If args provided, try to match
    if args:
        # Exact match on short_name or name
        matches = [b for b in board_details if b['short_name'] == args or b['name'] == args]
        if len(matches) == 1:
            selected_board = matches[0]
        # If no exact match, you can uncomment the following line to use fuzzy matching.
        # else:
        #     selected_board = _fuzzy_match_board(args, board_details)

    # If no args or no match, lists candidates
    if not selected_board:
        candidates = [f'{b["name"]} (ID: {b["short_name"]})' for b in board_details]
        candidate_str = '\n'.join(candidates)

        if args:
            final_stdout = (
                f"No exact match found for '{args}'. Please specify an exact board ID from the list below:\n\n" + candidate_str
            )
        else:
            final_stdout = (
                "No board specified. Please run 'install' again with a board ID from the list below:\n\n" + candidate_str
            )

        return {
            'success': False,
            'exit_code': 1,
            'stdout': final_stdout,
            'stderr': '',  # It's a prompt, not a runtime error.
            'candidates': candidates,
        }

    # 3. Persist Selection
    repo_dir = os.environ.get('HAGENT_REPO_DIR', '.')

    # Read and concatenate config files
    combined_content = ''
    try:
        platform_file = os.path.join(configs_path, 'framework', 'platform_arduino.md')
        if os.path.exists(platform_file):
            with open(platform_file, 'r') as f:
                combined_content += f.read() + '\n\n---\n\n'

        # Add the specific board config
        with open(selected_board['file_name'], 'r') as f:
            combined_content += f.read()

        # Write to AGENTS.md, GEMINI.md, and CLAUDE.md
        for filename in ['AGENTS.md', 'GEMINI.md', 'CLAUDE.md']:
            with open(os.path.join(repo_dir, filename), 'w') as f:
                f.write(combined_content)
    except Exception as e:
        return {'success': False, 'exit_code': 1, 'stdout': stdout, 'stderr': f'Failed to create configuration files: {str(e)}'}

    stdout += f'\nBoard configured: {selected_board["name"]}\nConfiguration saved to AGENTS.md, GEMINI.md, and CLAUDE.md'

    # 4. Auto-install core if not present
    board_info = _get_board_info_from_md()
    core = board_info.get('core')
    if core:
        if _is_core_installed(core):
            stdout += f"\nCore '{core}' is already installed."
        else:
            stdout += f"\nCore '{core}' not found. Installing..."
            core_result = _install_core(core)
            if core_result.get('success'):
                stdout += f"\nCore '{core}' installed successfully."
            else:
                stdout += f"\nWarning: Failed to install core '{core}': {core_result.get('stderr', '')}"

    stdout += '\n\nIMPORTANT: New configuration files (AGENTS.md, GEMINI.md, CLAUDE.md) have been created. To ensure your agent recognizes these instructions, please perform the following:'
    stdout += "\n- Gemini CLI: Run the '/memory refresh' command."
    stdout += '\n- Claude Code / Codex: Restart your current session.'

    return {
        'success': True,
        'exit_code': 0,
        'stdout': stdout,
        'stderr': '',
        'installation_path': toolkit_dir,
        'board_config': selected_board,
    }


def api_list_boards(args: Optional[str] = None) -> Dict[str, Any]:
    """
    List connected boards.
    """
    if not shutil.which('arduino-cli'):
        res = initialize_arduino_env()
        if not res['success']:
            return res

    try:
        # Get JSON output for accurate parsing
        res = subprocess.run('arduino-cli board list --format json', shell=True, capture_output=True, text=True)
        if res.returncode != 0:
            return {
                'success': False,
                'exit_code': res.returncode,
                'stdout': '',
                'stderr': res.stderr,
            }

        try:
            data = json.loads(res.stdout)
            # The structure is a dict with 'detected_ports' list
            ports = data.get('detected_ports', [])
        except json.JSONDecodeError:
            return {
                'success': False,
                'exit_code': 1,
                'stdout': '',
                'stderr': f'Failed to parse board list JSON: {res.stdout}',
            }

        lines = []
        found_boards = []

        for p in ports:
            # Check for detected boards on this port
            matching = p.get('matching_boards', [])
            address = p.get('port', {}).get('address')

            if matching and address:
                for b in matching:
                    name = b.get('name', 'Unknown Board')
                    fqbn = b.get('fqbn')
                    if fqbn:  # Only include if it has a detected FQBN
                        lines.append(f'- {name} ({fqbn}) at {address}')
                        found_boards.append({'name': name, 'fqbn': fqbn, 'port': address})

        output_str = 'Connected Arduino Boards:\n' + '\n'.join(lines) if lines else 'No connected Arduino boards detected.'

        return {'success': True, 'exit_code': 0, 'stdout': output_str, 'stderr': '', 'boards': found_boards}
    except Exception as e:
        return {
            'success': False,
            'exit_code': 1,
            'stdout': '',
            'stderr': str(e),
        }


def api_new_sketch(args: Optional[str] = None) -> Dict[str, Any]:
    """
    Create a new Arduino sketch.
    """
    if not args:
        return {
            'success': False,
            'exit_code': 1,
            'stdout': '',
            'stderr': 'Sketch name required',
        }

    if not shutil.which('arduino-cli'):
        res = initialize_arduino_env()
        if not res['success']:
            return res

    repo_dir = os.environ.get('HAGENT_REPO_DIR', '.')

    try:
        cmd = f'arduino-cli sketch new {args}'
        res = subprocess.run(cmd, cwd=repo_dir, shell=True, capture_output=True, text=True)

        project_path = os.path.join(repo_dir, args)
        return {
            'success': res.returncode == 0,
            'exit_code': res.returncode,
            'stdout': res.stdout,
            'stderr': res.stderr,
            'project_path': project_path,
        }
    except Exception as e:
        return {
            'success': False,
            'exit_code': 1,
            'stdout': '',
            'stderr': str(e),
        }


def api_compile(args: Optional[str] = None) -> Dict[str, Any]:
    """
    Compile an Arduino sketch.
    """
    if not shutil.which('arduino-cli'):
        res = initialize_arduino_env()
        if not res['success']:
            return res

    repo_dir = os.environ.get('HAGENT_REPO_DIR', '.')

    # 1. Determine Sketch
    sketch_path = args if args else 'Blink'
    # If args contains flags, we might need more robust parsing, but for now assume
    # simple usage: either "SketchName" or "" (defaults to Blink)
    # If user passed complex flags, we pass them through, but we still need to ensure FQBN is set.

    final_args = sketch_path

    # 2. Resolve FQBN and Core from MD
    board_info = _get_board_info_from_md()
    fqbn = board_info.get('fqbn')
    core = board_info.get('core')

    if not fqbn:
        return {
            'success': False,
            'exit_code': 1,
            'stdout': '',
            'stderr': 'No board configuration found. Please run the "install" tool to select a target board first.',
        }

    # 3. Check Core Installation
    if core and not _is_core_installed(core):
        return {
            'success': False,
            'exit_code': 1,
            'stdout': '',
            'stderr': f"Core '{core}' is not installed.\nPlease run: install_core '{core}'",
        }

    # 4. Construct Command
    # Use a local build directory inside the sketch to ensure upload can find it
    build_path = os.path.join(repo_dir, sketch_path, 'build')

    if '--fqbn' not in final_args:
        final_args += f' --fqbn {fqbn}'

    # Add build-path
    cmd = f'arduino-cli compile --build-path {build_path} {final_args}'

    try:
        res = subprocess.run(cmd, cwd=repo_dir, shell=True, capture_output=True, text=True)
        return {
            'success': res.returncode == 0,
            'exit_code': res.returncode,
            'stdout': res.stdout,
            'stderr': res.stderr,
        }
    except Exception as e:
        return {
            'success': False,
            'exit_code': 1,
            'stdout': '',
            'stderr': str(e),
        }


def api_upload(args: Optional[str] = None) -> Dict[str, Any]:
    """
    Upload a sketch.
    """
    if not shutil.which('arduino-cli'):
        res = initialize_arduino_env()
        if not res['success']:
            return res

    repo_dir = os.environ.get('HAGENT_REPO_DIR', '.')

    # 1. Determine Sketch
    sketch_path = args if args else 'Blink'

    # 2. Resolve FQBN and Core from MD
    board_info = _get_board_info_from_md()
    fqbn = board_info.get('fqbn')
    core = board_info.get('core')

    if not fqbn:
        return {
            'success': False,
            'exit_code': 1,
            'stdout': '',
            'stderr': 'No board configuration found. Please run the "install" tool to select a target board first.',
        }

    # 3. Check Core Installation
    if core and not _is_core_installed(core):
        return {
            'success': False,
            'exit_code': 1,
            'stdout': '',
            'stderr': f"Core '{core}' is not installed.\nPlease run: install_core '{core}'",
        }

    # 4. Resolve Port — allow explicit override via args='port=/dev/...'
    explicit_port = None
    if args and 'port=' in args:
        for part in args.split():
            if part.startswith('port='):
                explicit_port = part.split('=', 1)[1]
                break

    if explicit_port:
        port = explicit_port
    else:
        _, port = _resolve_board_info(fqbn)

    if not port:
        hints = _get_available_ports_hint()
        return {
            'success': False,
            'exit_code': 1,
            'stdout': '',
            'stderr': (
                f"No connected board matched FQBN '{fqbn}'.\n"
                f"Ensure the board is connected and powered on.\n"
                f"If the board is connected but not detected, retry with an explicit port using args='port=/dev/...'.\n"
                f"Available ports:\n{hints}"
            ),
        }

    # 5. Upload
    # Point to the same build directory used by compile
    build_path = os.path.join(repo_dir, sketch_path, 'build')
    cmd = f'arduino-cli upload -p {port} --fqbn {fqbn} --input-dir {build_path} {sketch_path}'

    try:
        res = subprocess.run(cmd, cwd=repo_dir, shell=True, capture_output=True, text=True)
        return {
            'success': res.returncode == 0,
            'exit_code': res.returncode,
            'stdout': res.stdout,
            'stderr': res.stderr,
            'flash_result': 'Upload done' if res.returncode == 0 else 'Upload failed',
        }
    except Exception as e:
        return {
            'success': False,
            'exit_code': 1,
            'stdout': '',
            'stderr': str(e),
        }


def api_monitor(args: Optional[str] = None, timeout: int = 30) -> Dict[str, Any]:
    """Monitor serial output."""
    if not shutil.which('arduino-cli'):
        res = initialize_arduino_env()
        if not res['success']:
            return res

    board_info = _get_board_info_from_md()
    fqbn = board_info.get('fqbn')

    if not fqbn:
        return {
            'success': False,
            'exit_code': 1,
            'stdout': '',
            'stderr': 'No board configuration found. Please run the "install" tool to select a target board first.',
        }

    # Allow explicit port override via args='port=/dev/...'
    explicit_port = None
    if args and 'port=' in args:
        for part in args.split():
            if part.startswith('port='):
                explicit_port = part.split('=', 1)[1]
                break

    if explicit_port:
        port = explicit_port
    else:
        _, port = _resolve_board_info(fqbn)

    if not port:
        hints = _get_available_ports_hint()
        return {
            'success': False,
            'exit_code': 1,
            'stdout': '',
            'stderr': (
                f"No connected board matched FQBN '{fqbn}'.\n"
                f"Ensure the board is connected and powered on.\n"
                f"If the board is connected but not detected, retry with an explicit port using args='port=/dev/...'.\n"
                f"Available ports:\n{hints}"
            ),
        }

    return _run_monitor(port=port, timeout=timeout, fqbn=fqbn)


def api_cli(args: Optional[str] = None) -> Dict[str, Any]:
    """Pass-through"""
    if not shutil.which('arduino-cli'):
        res = initialize_arduino_env()
        if not res['success']:
            return res

    cmd = f'arduino-cli {args}' if args else 'arduino-cli'
    try:
        res = subprocess.run(cmd, shell=True, capture_output=True, text=True)
        return {
            'success': res.returncode == 0,
            'exit_code': res.returncode,
            'stdout': res.stdout,
            'stderr': res.stderr,
        }
    except Exception as e:
        return {
            'success': False,
            'exit_code': 1,
            'stdout': '',
            'stderr': str(e),
        }


def api_env(args: Optional[str] = None) -> Dict[str, Any]:
    """
    Display Arduino environment setup instructions.
    """
    cache_dir = os.environ.get('HAGENT_CACHE_DIR', '.')
    toolkit_dir = os.path.join(cache_dir, 'arduino-toolkit')
    export_script = os.path.join(toolkit_dir, 'export.sh')

    if not os.path.exists(export_script):
        instructions = f'Arduino Toolkit not found at {toolkit_dir}'
        return {
            'success': False,
            'exit_code': 1,
            'stdout': instructions,
            'stderr': '',
        }

    instructions = f'source {export_script}'
    return {
        'success': True,
        'exit_code': 0,
        'stdout': instructions,
        'stderr': '',
    }


def mcp_execute(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    MCP execution entry point for Arduino command.
    """
    try:
        api_name = params.get('api')
        args = params.get('args')
        timeout = params.get('timeout', 30)

        if not api_name:
            return {
                'success': False,
                'exit_code': 1,
                'stdout': '',
                'stderr': 'API command is required',
                'params_used': params,
            }

        api_handlers = {
            'install': api_install,
            'list_boards': api_list_boards,
            'new_sketch': api_new_sketch,
            'compile': api_compile,
            'upload': api_upload,
            'monitor': lambda args: api_monitor(args, timeout),
            'cli': api_cli,
            'env': api_env,
            'refresh_config': api_refresh_config,
        }

        handler = api_handlers.get(api_name)
        if not handler:
            return {
                'success': False,
                'exit_code': 1,
                'stdout': '',
                'stderr': f'Unknown API command: {api_name}',
                'params_used': params,
            }

        result = handler(args)
        if result is None:
            result = {}
        result['params_used'] = params
        return result

    except Exception as e:
        return {
            'success': False,
            'exit_code': 1,
            'stdout': '',
            'stderr': f'Command execution failed: {str(e)}',
            'params_used': params,
        }


def create_argument_parser():
    """Create argument parser for Arduino CLI."""
    parser = argparse.ArgumentParser(
        description='Arduino development tool - Complete workflow for Arduino projects',
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )

    parser.add_argument('--schema', action='store_true', help='Print MCP tool schema as JSON')
    parser.add_argument('--api', '-a', required=False, help='API command to execute')
    parser.add_argument('--args', help='Arguments for the API command')
    parser.add_argument('--timeout', type=int, default=30, help='Timeout in seconds for monitor (default: 30)')

    return parser


def main():
    """Standard CLI entry point."""
    import json

    parser = create_argument_parser()
    args = parser.parse_args()

    if args.schema:
        schema = get_mcp_schema()
        print(json.dumps(schema, indent=2))
        return 0

    if not args.api:
        parser.print_help()
        return 1

    try:
        params = {
            'api': args.api,
            'args': args.args,
            'timeout': args.timeout,
        }

        result = mcp_execute(params)

        if result and result.get('stdout'):
            print(result['stdout'])
        if result and result.get('stderr'):
            print(result['stderr'], file=sys.stderr)

        return result.get('exit_code', 1 if not result or not result.get('success', False) else 0)

    except Exception as e:
        print(f'Error: {e}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    main()
