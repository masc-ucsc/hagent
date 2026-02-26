#!/usr/bin/env python3
"""platform
MCP Command: ESP32

ESP32 development tool with unified CLI and MCP interfaces.
Provides complete ESP32 workflow: board setup, project creation, building, flashing, and monitoring.
"""

import argparse
import sys
import os
import subprocess
import shutil
import tempfile
import time
from typing import Dict, Any, Optional
import difflib
import platform
import json
import re
import sys as _sys
import os as _os
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
from config_sync import fetch_remote_configs

def get_mcp_schema() -> Dict[str, Any]:
    """Return MCP tool schema for ESP32 development command."""

    available_apis = [
        'install',
        'setup',
        'build',
        'flash',
        'check_bootloader',
        'monitor',
        'idf',
        'env',
        'refresh_config',
    ]

    return { 'name': 'hagent_esp32', 'description': 'ESP32 development tool for managing boards, projects, building, and flashing', 'inputSchema': {
            'type': 'object',
            'properties': {
                'api': {
                    'type': 'string',
                    'description': 'API command to execute',
                    'enum': available_apis,
                },
                'args': {
                    'type': 'string',
                    'description': 'Arguments for the API command: \n'
                                   '- install: (REQUIRED) Board name or description (e.g., "rust board", "board_rust_esp32_c3")\n'
                                   '- setup: (REQUIRED) New project name\n'
                                   '- build/flash: (OPTIONAL) Extra flags for idf.py\n'
                                   '- idf: (REQUIRED) Arbitrary idf.py command string\n'
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

def initialize_idf_env() -> Dict[str, Any]:
    """
    Source export.sh and load environment variables.
    Returns a result dict with 'success', 'stdout', 'stderr'.
    """
    # Source export.sh in a separate process and load the dumped ENV variables from the called process into the calling process' ENV
    print("Adding idf.py to PATH")
    cache_dir = os.environ.get("HAGENT_CACHE_DIR", ".")
    idf_path = os.path.join(cache_dir, "esp-idf")
    export_sh_path = os.path.join(idf_path, "export.sh")
    
    if not os.path.exists(export_sh_path):
        return {
            'success': False,
            'exit_code': 1,
            'stdout': '',
            'stderr': f"ESP-IDF not found at {idf_path}. Please run the 'api_install' tool first to setup the ESP-IDF toolkit."
        }

    export_script_cmd = f"bash -c 'source {export_sh_path} >/dev/null 2>&1 && python3 - <<PY\nimport os, json\nprint(json.dumps(dict(os.environ)))\nPY'"
    
    try:
        export_proc = subprocess.run(export_script_cmd, shell=True, capture_output=True, text=True, check=True)
        # Update the current Python process' ENV variables
        os.environ.update(json.loads(export_proc.stdout))
        
        if not shutil.which('idf.py'):
             return {
                'success': False,
                'exit_code': 1,
                'stdout': '',
                'stderr': "idf.py not found in PATH after sourcing export.sh"
            }
            
        return {'success': True, 'stdout': '', 'stderr': ''}
    except (subprocess.CalledProcessError, json.JSONDecodeError) as e:
        stderr = e.stderr if hasattr(e, 'stderr') else str(e)
        return {
            'success': False,
            'exit_code': 1,
            'stdout': '',
            'stderr': f"Failed to initialize ESP-IDF environment: {stderr}"
        }

def _parse_board_config(file_path: str) -> Dict[str, str]:
    """
    Parses a board configuration Markdown file to extract metadata.
    """
    try:
        with open(file_path, 'r') as f:
            content = f.read()
            
        # Extract Board Identifier (look for `- `board`: identifier`)
        board_match = re.search(r"-\s*`board`\s*:\s*([a-zA-Z0-9_]+)", content)
        board_id = board_match.group(1).strip() if board_match else "esp32"
        
        # Extract Human Readable Model (look for `- `model`: name`)
        model_match = re.search(r"-\s*`model`\s*:\s*(.+)$", content, re.MULTILINE)
        model_name = model_match.group(1).strip() if model_match else board_id
        
        return {
            'name': model_name,
            'model': board_id, # 'model' in board_details refers to the IDF target
            'file_name': file_path,
            'short_name': os.path.basename(file_path).replace('.md', '')
        }
    except Exception as e:
        print(f"Warning: Failed to parse {file_path}: {e}", file=sys.stderr)
        return {
            'name': os.path.basename(file_path),
            'model': 'esp32',
            'file_name': file_path,
            'short_name': os.path.basename(file_path).replace('.md', '')
        }

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

def _run_monitor(project_dir: str, timeout: int = 30) -> Dict[str, Any]:
    """
    Internal helper to run idf.py monitor in a specific directory.
    """
    monitor_cmd = "script -q /dev/null idf.py monitor"
    
    try:
        # Check if idf.py is in PATH, source export.sh/export.bat before running the command
        if not shutil.which('idf.py'):
            res = initialize_idf_env() 
            if not res['success']:
                return res
        proc = subprocess.Popen(monitor_cmd, stdout=subprocess.PIPE, stdin=subprocess.PIPE, text=True, shell=True, cwd=project_dir)
           
        # Communicate and read stdout from the process monitoring serial output
        # The communicate function call runs till timeout then throws an exception, which needs to be caught and handled
        out, err = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired as e:
        # This is where the function exits by default
        proc.kill()
        out, err = proc.communicate()
        return {
            'success': True,
            'exit_code': 0,
            'stdout': out or "",
            'stderr': err or ""
        }
    except Exception as e:
        return {
            'success': False,
            'exit_code': 1,
            'stdout': "",
            'stderr': str(e) 
        }
    
    # The process exits prematurely if an error is encountered
    return {
        'success': False,
        'exit_code': 1,
        'stdout': out or "",
        'stderr': err or "",
    }

# ==============================================================================
# API FUNCTIONS
# ==============================================================================

def api_refresh_config(args: Optional[str] = None) -> Dict[str, Any]:
    """
    Refresh board and platform configurations from the remote repository.
    Returns a list of available ESP32 boards after the refresh.
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
    esp32_boards = [b for b in synced.get('board', []) if b.startswith('board_idf_')]

    board_details = []
    for short_name in esp32_boards:
        info = _parse_board_config(os.path.join(configs_board_path, short_name + '.md'))
        board_details.append(f"{info['name']} (ID: {info['short_name']})")

    return {
        'success': True,
        'exit_code': 0,
        'stdout': "Configs refreshed. Available ESP32 boards:\n" + "\n".join(board_details),
        'stderr': '',
        'boards': board_details,
    }


def api_install(args: Optional[str] = None) -> Dict[str, Any]:
    """
    Install ESP-IDF toolchain and configure board.

    Args:
        args: Board description (e.g., "rust board that uses esp32")

    Returns:
        Dictionary with installation results
    """
    # TODO: Implement install logic
    # 1. Fuzzy match board description against hagent/mcp/configs/board_*.md files
    # 2. Extract ESP32 model from matched board config
    # 3. Check if ESP-IDF exists in HAGENT_CACHE_DIR/esp-idf/
    # 4. Clone ESP-IDF if needed: git clone --recursive https://github.com/espressif/esp-idf.git
    # 5. Run ./install.sh <esp32_model>
    # 6. Copy board config to HAGENT_REPO_DIR/AGENTS.md and GEMINI.md

    # Refresh configs from remote (best-effort, non-blocking)
    fetch_remote_configs()

    configs_path = os.path.join(os.environ['HAGENT_ROOT'], 'hagent', 'mcp', 'configs')
    board_configs_path = os.path.join(configs_path, 'board')
    if os.path.isdir(board_configs_path):
        # Filter for ESP32 boards only (files starting with board_rust_)
        board_files = [f for f in os.listdir(board_configs_path) if f.startswith('board_idf_') and f.endswith('.md')]
        board_details = []
        for f in board_files:
            board_info = _parse_board_config(os.path.join(board_configs_path, f))
            board_details.append(board_info)

        selected_board = None
        
        # If args are provided, try to find an exact match
        if args:
            exact_matches = [b for b in board_details if b['name'].lower() == args.lower() or b['short_name'].lower() == args.lower()]
            if len(exact_matches) == 1:
                selected_board = exact_matches[0]
            # If no exact match, you can uncomment the following line to use fuzzy matching.
            # else:
            #     selected_board = _fuzzy_match_board(args, board_details)

        if not selected_board:
            candidates = [f"{b['name']} (ID: {b['short_name']})" for b in board_details]
            candidate_str = "\n".join(candidates)
            
            if not args:
                error_msg = f"Please specify a board to install. Available boards:\n{candidate_str}"
            elif not board_details:
                error_msg = f"No boards found matching '{args}'. Please try a different search term."
            else:
                error_msg = f"No exact match found for '{args}'. Please specify an exact board ID from the list below:\n{candidate_str}"
            
            return {
                'success': False,
                'exit_code': 1,
                'stdout': '',
                'stderr': error_msg,
                'candidates': candidates
            }

        # Check if ESP-IDF exists in HAGENT_CACHE_DIR/esp-idf/; Install if missing
        idf_path = os.path.join(os.environ['HAGENT_CACHE_DIR'], 'esp-idf')
        stdout = ''
        try:
            if not os.path.isdir(idf_path):
                clone_result = subprocess.run(
                    ['git', 'clone', '--recursive', 'https://github.com/espressif/esp-idf.git'],
                    cwd=os.environ['HAGENT_CACHE_DIR'],
                    check=True,
                    capture_output=True,
                    text=True,
                )
                stdout = stdout + clone_result.stdout
            install_script = "./install.sh"
            install_result = subprocess.run([install_script, selected_board['model']], cwd=idf_path, shell=True, check=True, capture_output=True, text=True)
            # TODO Install ESP-IDF specific certificates in python 

            stdout = stdout + install_result.stdout
        except subprocess.CalledProcessError as e:
            return {
                'success': False,
                'exit_code': e.returncode,
                'stdout': e.stdout,
                'stderr': e.stderr,
            }

        # Copy board config to $HAGENT_REPO_DIR/AGENTS.md, GEMINI.md, and CLAUDE.md
        repo_dir = os.environ['HAGENT_REPO_DIR']
        
        # Read and concatenate config files
        combined_content = ""
        try:
            platform_file = os.path.join(configs_path, 'framework', 'platform_esp32.md')
            if os.path.exists(platform_file):
                with open(platform_file, 'r') as f:
                    combined_content += f.read() + "\n\n---\n\n"
            
            # Add the specific board config
            with open(selected_board['file_name'], 'r') as f:
                combined_content += f.read()
                
            # Write to AGENTS.md, GEMINI.md, and CLAUDE.md
            for filename in ['AGENTS.md', 'GEMINI.md', 'CLAUDE.md']:
                with open(os.path.join(repo_dir, filename), 'w') as f:
                    f.write(combined_content)
        except Exception as e:
            return {
                'success': False,
                'exit_code': 1,
                'stdout': stdout,
                'stderr': f"Failed to create configuration files: {str(e)}"
            }

        stdout += f"\nBoard configured: {selected_board['name']}\nConfiguration saved to AGENTS.md, GEMINI.md, and CLAUDE.md"

        stdout += "\n\nIMPORTANT: New configuration files (AGENTS.md, GEMINI.md, CLAUDE.md) have been created. To ensure your agent recognizes these instructions, please perform the following:"
        stdout += "\n- Gemini CLI: Run the '/memory refresh' command."
        stdout += "\n- Claude Code / Codex: Restart your current session."

    return {
        'success': True,
        'exit_code': 0,
        'stdout': stdout,
        'stderr': '',
        'installation_path': idf_path,
        'board_config': selected_board,
    }

def api_setup(args: Optional[str] = None) -> Dict[str, Any]:
    """
    Create a new ESP32 project.
    WARNING: This function overwrites project files in the repo directory, 
    but preserves agent configuration (.gemini, AGENTS.md, etc.) and git history.

    Args:
        args: Project name

    Returns:
        Dictionary with setup results
    """
    # 1. Verify ESP-IDF installed
    # 2. Read AGENTS.md to get target config
    # 3. Create temp directory (Staging)
    # 4. Run idf.py create-project in Staging
    # 5. Selectively clean HAGENT_REPO_DIR (Preserve .gemini, .git, etc.)
    # 6. Copy from Staging to HAGENT_REPO_DIR
    # 7. Run idf.py set-target in HAGENT_REPO_DIR
    # 8. Restore AGENTS.md/GEMINI.md

    idf_path = os.path.join(os.environ["HAGENT_CACHE_DIR"], "esp-idf")
    repo_dir = os.environ["HAGENT_REPO_DIR"]
    # Find any of the configuration files
    md_path = None
    for filename in ["AGENTS.md", "GEMINI.md", "CLAUDE.md"]:
        path = os.path.join(repo_dir, filename)
        if os.path.exists(path):
            md_path = path
            break

    if not md_path:
        return {
            'success': False,
            'exit_code': 1,
            'stdout': '',
            'stderr': 'Board configuration (AGENTS.md, GEMINI.md, or CLAUDE.md) not found. Run api_install() before running api_setup()',
        }

    # Use helper to parse target config
    board_config = _parse_board_config(md_path)
    target_config = board_config['model']

    # Files/Dirs to STRICTLY PRESERVE
    protected_items = [
        '.gemini', '.claude', '.git', '.gitignore', '.vscode',
        'AGENTS.md', 'GEMINI.md', 'CLAUDE.md'
    ]

    try:
        # Check if idf.py is in PATH, if not present, source export.sh
        if not shutil.which('idf.py'):
            res = initialize_idf_env()
            if not res['success']:
                return res

        with tempfile.TemporaryDirectory() as temp_dir:
            # 1. Create Project in Staging (Temp Dir) - Just the scaffolding
            crt_prj_cmd = f"idf.py create-project -p . {args}"
            
            subprocess.run(
                crt_prj_cmd, cwd=temp_dir, shell=True, check=True, capture_output=True, text=True
            )

            # 2. Selectively Clean Repo Directory
            for item in os.listdir(repo_dir):
                if item in protected_items:
                    continue
                
                item_path = os.path.join(repo_dir, item)
                if os.path.isfile(item_path) or os.path.islink(item_path):
                    os.unlink(item_path)
                elif os.path.isdir(item_path):
                    shutil.rmtree(item_path)

            # 3. Transplant from Staging to Repo
            # Copy everything since create-project only makes source files
            for item in os.listdir(temp_dir):
                s = os.path.join(temp_dir, item)
                d = os.path.join(repo_dir, item)
                
                if os.path.isdir(s):
                    shutil.copytree(s, d, dirs_exist_ok=True)
                else:
                    shutil.copy2(s, d)

            # 4. Initialize Configuration IN THE REPO
            # This generates sdkconfig and build/ with correct absolute paths
            set_target_cmd = f"idf.py set-target {target_config}"
            result = subprocess.run(
                set_target_cmd, cwd=repo_dir, shell=True, check=True, capture_output=True, text=True
            )

    except subprocess.CalledProcessError as e:
        return {
            'success': False,
            'exit_code': e.returncode,
            'stdout': e.stdout,
            'stderr': e.stderr,
        }
    except Exception as e:
        return {
            'success': False,
            'exit_code': 1,
            'stdout': '',
            'stderr': f"Setup failed: {str(e)}",
        }

    return {
        'success': True,
        'exit_code': 0,
        'stdout': result.stdout,
        'stderr': result.stderr,
        'project_path': repo_dir,
        'target_config': target_config
    }


def api_build(args: Optional[str] = None) -> Dict[str, Any]:
    """
    Build the current ESP32 project.

    Args:
        args: Optional build flags

    Returns:
        Dictionary with build results
    """
    # TODO: Implement build logic
    # 1. Check if idf.py is in PATH
    # 2. If not, source . $HAGENT_CACHE_DIR/esp-idf/export.sh
    # 3. Navigate to HAGENT_REPO_DIR
    # 4. Run: idf.py build
    # 5. Capture and return build output
    
    try:
        # Check if idf.py is in PATH; source export.sh/export.bat before build if not in path
        if not shutil.which('idf.py'):
            res = initialize_idf_env()
            if not res['success']:
                return res
        
        repo_dir = os.environ["HAGENT_REPO_DIR"]

        # If sdkconfig is missing, auto-run set-target using the installed board config
        if not os.path.exists(os.path.join(repo_dir, "sdkconfig")):
            board_config = _parse_board_config(
                next((os.path.join(repo_dir, f) for f in ["AGENTS.md", "GEMINI.md", "CLAUDE.md"]
                      if os.path.exists(os.path.join(repo_dir, f))), "")
            )
            target = board_config.get('model')
            if not target:
                return {
                    'success': False,
                    'exit_code': 1,
                    'stdout': '',
                    'stderr': 'sdkconfig and board configuration not found. Run `api_install` to select a board first. Run `api_setup` if the project is not initialized.',
                }
            subprocess.run(f"idf.py set-target {target}", cwd=repo_dir, shell=True, check=True, capture_output=True, text=True)

        result = subprocess.run("idf.py build", cwd=repo_dir, shell=True, capture_output=True, text=True, check=True)
        binary_location = os.path.join(os.environ["HAGENT_REPO_DIR"], 'build')

    except subprocess.CalledProcessError as e:
        return {
            'success': False,
            'exit_code': e.returncode,
            'binary_location': "",

            'stdout': e.stdout,
            'stderr': e.stderr,
        }

    return {
        'success': True,
        'binary_location': binary_location,
        'exit_code': 0,
        'stdout': result.stdout,
        'stderr': result.stderr,
    }


def api_flash(args: Optional[str] = None) -> Dict[str, Any]:
    """
    Flash firmware to ESP32 board.

    Args:
        args: Optional port specification

    Returns:
        Dictionary with flash results
    """
    # TODO: Implement flash logic
    # 1. Ensure environment is set (source export.sh if needed)
    # 2. Navigate to HAGENT_REPO_DIR
    # 3. Run: idf.py flash (with optional port arg)
    # 4. Capture flash output
    
    flash_cmd = "idf.py flash"


    try:
        # Check if idf.py is in PATH; source export.sh/export.bat before flash if not in path
        if not shutil.which('idf.py'):
            res = initialize_idf_env()
            if not res['success']:
                return res
        result = subprocess.run(
            flash_cmd, cwd=os.environ['HAGENT_REPO_DIR'], shell=True, capture_output=True, text=True, check=True
        )
    except subprocess.CalledProcessError as e:
        return {
            'success': False,
            'exit_code': e.returncode,
            'flash_status': 'Flash failed',
            'stdout': e.stdout,
            'stderr': e.stderr,
        }

    return {
        'success': True,
        'exit_code': 0,
        'stdout': result.stdout,
        'stderr': result.stderr,
        'flash_result': 'Flash done',
    }

def api_check_bootloader(args: Optional[str] = None) -> Dict[str, Any]:
    """
    Verify if the ESP32 board is connected and responsive in bootloader mode.
    
    CRITICAL: Call this tool FIRST to verify hardware connectivity. If it fails, 
    check physical connections (cable, ports), verify that the board is in 
    bootloader mode, and ensure the necessary USB-to-Serial drivers (e.g., CP210x, 
    CH34x) are installed on the host system before troubleshooting software.

    Returns:
        Dictionary with check results (success=True if chip is responsive)
    """
    check_cmd = "esptool chip-id"
    
    try:
        # Check if esptool is in PATH; source export.sh if not
        if not shutil.which('esptool'):
            res = initialize_idf_env()
            if not res['success']:
                return res
            
        # Run the chip-id command to handshake with the board
        result = subprocess.run(
            check_cmd, 
            cwd=os.environ['HAGENT_REPO_DIR'], 
            shell=True, 
            capture_output=True, 
            text=True, 
            check=True
        )
        
        return {
            'success': True,
            'exit_code': 0,
            'stdout': result.stdout,
            'stderr': result.stderr,
            'status': 'Board connected and responsive'
        }
        
    except subprocess.CalledProcessError as e:
        return {
            'success': False,
            'exit_code': e.returncode,
            'stdout': e.stdout,
            'stderr': e.stderr,
            'status': 'Board not detected or not in bootloader mode'
        }
    except Exception as e:
        return {
            'success': False,
            'exit_code': 1,
            'stdout': '',
            'stderr': str(e),
            'status': 'Error checking bootloader'
        }


def api_monitor(args: Optional[str] = None, timeout: int = 30) -> Dict[str, Any]:
    """
    Monitor serial output from ESP32.

    Args:
        args: Not used
        timeout: Timeout in seconds (default: 30)

    Returns:
        Dictionary with monitor output
    """
    # TODO: Implement monitor logic
    # 1. Ensure environment is set
    # 2. Navigate to HAGENT_REPO_DIR
    # 3. Run idf.py monitor in subprocess
    # 4. Capture output for timeout duration
    # 5. Send CTRL+] to exit monitor
    # 6. Return captured output
    
    # TODO: In _run_monitor, check if the process can be made to run without an error-driven exit; program to input ctrl+] and exit after the timout duration.
    repo_dir = os.environ["HAGENT_REPO_DIR"]
    return _run_monitor(repo_dir, timeout)



def api_idf(args: Optional[str] = None) -> Dict[str, Any]:
    """
    Pass-through to run arbitrary idf.py commands.

    Args:
        args: idf.py arguments (e.g., "menuconfig", "clean")

    Returns:
        Dictionary with idf.py command results
    """
    # TODO: Implement idf passthrough logic
    # 1. Ensure environment is set
    # 2. Navigate to HAGENT_REPO_DIR
    # 3. Run: idf.py <args>
    # 4. Capture and return output
    
    # If the string is non-empty, then it's passed down as a valid argument 
    idf_cmd = "idf.py"
    if args:
        idf_cmd += f" {args}"

    try: 
        # Check if idf.py is in the PATH, if not then source export.sh before running the command
        if not shutil.which('idf.py'):
            res = initialize_idf_env()
            if not res['success']:
                return res
        result = subprocess.run(idf_cmd, cwd=os.environ["HAGENT_REPO_DIR"], shell=True, capture_output=True, text=True, check=True)
    except subprocess.CalledProcessError as e:
        return {
            'success': False,
            'exit_code': e.returncode,
            'stdout': e.stdout,
            'stderr': e.stderr
        }

    return {
        'success': True,
        'exit_code': 0,
        'stdout': result.stdout,
        'stderr': result.stderr,
    }


def api_env(args: Optional[str] = None) -> Dict[str, Any]:
    """
    Display ESP-IDF environment setup instructions.

    Args:
        args: Not used

    Returns:
        Dictionary with environment setup instructions
    """
    from hagent.inou.path_manager import PathManager

    try:
        path_manager = PathManager()
        cache_dir = path_manager.cache_dir
    except SystemExit:
        return {
            'success': False,
            'exit_code': 1,
            'stdout': '',
            'stderr': 'HAGENT_CACHE_DIR not set. Please set it to continue.',
        }

    idf_path = cache_dir / 'esp-idf'
    export_script = idf_path / 'export.sh'

    if not export_script.exists():
        instructions = f"""ESP-IDF not found at {idf_path}

Run 'install' API first to install ESP-IDF:
  {sys.argv[0]} --api install --args "board description"
"""
        return {
            'success': False,
            'exit_code': 1,
            'stdout': instructions,
            'stderr': '',
        }

    instructions = f"""ESP-IDF Environment Setup

To use ESP-IDF tools (idf.py, esptool.py, etc.), source the environment:

  source {export_script}

Or add to your shell startup (~/.bashrc or ~/.zshrc):
  alias esp-env='source {export_script}'

Then run:
  esp-env

This sets up PATH and other variables needed for:
  - idf.py build
  - idf.py flash
  - idf.py monitor
  - esptool.py
  - xtensa/riscv toolchains
"""

    return {
        'success': True,
        'exit_code': 0,
        'stdout': instructions,
        'stderr': '',
    }


def mcp_execute(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    MCP execution entry point for ESP32 command.

    Args:
        params: Dictionary containing the input parameters from Claude Code

    Returns:
        Dictionary with execution results in a structured format
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

        # Route to appropriate API handler
        api_handlers = {
            'install': api_install,
            'setup': api_setup,
            'build': api_build,
            'flash': api_flash,
            'check_bootloader': api_check_bootloader,
            'monitor': lambda args: api_monitor(args, timeout),
            'idf': api_idf,
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

        # Execute the handler
        result = handler(args)
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
    """Create argument parser for ESP32 CLI."""
    parser = argparse.ArgumentParser(
        description='ESP32 development tool - Complete workflow for ESP32 projects',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""Examples:
  # Install ESP-IDF for rust board
  %(prog)s --api install --args "rust board that uses esp32"

  # Setup a new project
  %(prog)s --api setup --args "led_toggle"

  # Build current project
  %(prog)s --api build

  # Flash to board
  %(prog)s --api flash

  # Check if board is in bootloader mode
  %(prog)s --api check_bootloader

  # Monitor output (30s timeout)
  %(prog)s --api monitor --timeout 30

  # Run idf.py command
  %(prog)s --api idf --args "menuconfig"

  # Show environment setup instructions
  %(prog)s --api env
        """,
    )

    parser.add_argument('--schema', action='store_true', help='Print MCP tool schema as JSON')
    parser.add_argument('--api', '-a', required=False, help='API command to execute')
    parser.add_argument('--args', help='Arguments for the API command')
    parser.add_argument('--timeout', type=int, default=30, help='Timeout in seconds for monitor (default: 30)')

    return parser


def main():
    """Standard CLI entry point with both MCP schema and CLI argument handling."""
    import json

    parser = create_argument_parser()
    args = parser.parse_args()

    # Handle --schema option
    if args.schema:
        schema = get_mcp_schema()
        print(json.dumps(schema, indent=2))
        return 0

    if not args.api:
        parser.print_help()
        return 1

    try:
        # Convert CLI args to MCP params format
        params = {
            'api': args.api,
            'args': args.args,
            'timeout': args.timeout,
        }

        # Execute through MCP interface
        result = mcp_execute(params)

        # Handle output
        if result['stdout']:
            print(result['stdout'])
        if result['stderr']:
            print(result['stderr'], file=sys.stderr)

        # Return appropriate exit code
        return result.get('exit_code', 1 if not result.get('success', False) else 0)

    except Exception as e:
        print(f'Error: {e}', file=sys.stderr)
        import traceback

        traceback.print_exc()
        return 1


if __name__ == '__main__':
    sys.exit(main())
