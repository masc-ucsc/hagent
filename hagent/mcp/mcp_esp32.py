#!/usr/bin/env python3
"""
MCP Command: ESP32

ESP32 development tool with unified CLI and MCP interfaces.
Provides complete ESP32 workflow: board setup, project creation, building, flashing, and monitoring.
"""

import argparse
import sys
from typing import Dict, Any, Optional


def get_mcp_schema() -> Dict[str, Any]:
    """Return MCP tool schema for ESP32 development command."""

    available_apis = [
        'install',
        'define_board',
        'setup',
        'build',
        'flash',
        'factory_reset',
        'monitor',
        'idf',
        'env',
    ]

    return {
        'name': 'hagent_esp32',
        'description': 'ESP32 development tool for managing boards, projects, building, and flashing',
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
                    'description': 'Arguments for the API command (e.g., board description, project name, idf.py args)',
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
    # 6. Copy board config to HAGENT_REPO_DIR/AGENTS.md or CLAUDE.md

    return {
        'success': False,
        'exit_code': 1,
        'stdout': '',
        'stderr': 'api_install not implemented yet',
    }


def api_define_board(args: Optional[str] = None) -> Dict[str, Any]:
    """
    Create a new board configuration from a URL.

    Args:
        args: URL to board specification

    Returns:
        Dictionary with board definition results
    """
    # TODO: Implement define_board logic
    # 1. Accept board specification URL
    # 2. Prompt user for: board name, ESP32 model, GPIO mappings
    # 3. Create hagent/mcp/configs/board_<name>.md
    # 4. Include: board name, model, GPIO table, reference URL, example usage

    return {
        'success': False,
        'exit_code': 1,
        'stdout': '',
        'stderr': 'api_define_board not implemented yet',
    }


def api_setup(args: Optional[str] = None) -> Dict[str, Any]:
    """
    Create a new ESP32 project.

    Args:
        args: Project name

    Returns:
        Dictionary with setup results
    """
    # TODO: Implement setup logic
    # 1. Verify ESP-IDF installed (check HAGENT_CACHE_DIR/esp-idf/)
    # 2. Source export.sh: . $HAGENT_CACHE_DIR/esp-idf/export.sh
    # 3. Navigate to HAGENT_REPO_DIR
    # 4. Run: idf.py create-project -p . <project_name>
    # 5. Detect board model from AGENTS.md or CLAUDE.md
    # 6. Run: idf.py set-target <esp32_model>
    # 7. Create esp_env.sh helper script

    return {
        'success': False,
        'exit_code': 1,
        'stdout': '',
        'stderr': 'api_setup not implemented yet',
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

    return {
        'success': False,
        'exit_code': 1,
        'stdout': '',
        'stderr': 'api_build not implemented yet',
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

    return {
        'success': False,
        'exit_code': 1,
        'stdout': '',
        'stderr': 'api_flash not implemented yet',
    }


def api_factory_reset(args: Optional[str] = None) -> Dict[str, Any]:
    """
    Guide user through factory reset with hello world example.

    Args:
        args: Not used

    Returns:
        Dictionary with factory reset results
    """
    # TODO: Implement factory_reset logic
    # 1. Create/use hello world example (prints "hello NUM" every second)
    # 2. Build hello world
    # 3. Display step-by-step instructions:
    #    - Unplug USB-C
    #    - Press and hold BOOT button
    #    - Plug USB-C while holding BOOT
    #    - Release BOOT button
    #    - Wait for user confirmation at each step
    # 4. Flash hello world
    # 5. Instruct user to press RESET
    # 6. Run monitor briefly to verify

    return {
        'success': False,
        'exit_code': 1,
        'stdout': '',
        'stderr': 'api_factory_reset not implemented yet',
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

    return {
        'success': False,
        'exit_code': 1,
        'stdout': '',
        'stderr': 'api_monitor not implemented yet',
    }


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

    return {
        'success': False,
        'exit_code': 1,
        'stdout': '',
        'stderr': 'api_idf not implemented yet',
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
            'define_board': api_define_board,
            'setup': api_setup,
            'build': api_build,
            'flash': api_flash,
            'factory_reset': api_factory_reset,
            'monitor': lambda args: api_monitor(args, timeout),
            'idf': api_idf,
            'env': api_env,
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

  # Define a new board from URL
  %(prog)s --api define_board --args "https://example.com/board-spec"

  # Setup a new project
  %(prog)s --api setup --args "led_toggle"

  # Build current project
  %(prog)s --api build

  # Flash to board
  %(prog)s --api flash

  # Factory reset with hello world
  %(prog)s --api factory_reset

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
