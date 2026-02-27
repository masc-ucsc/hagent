#!/usr/bin/env python3
"""
MCP Hardware Unified Entry Point

Platform-agnostic interface to mcp_arduino.py and mcp_esp32.py.
Maps common API names across platforms so callers don't need to know
platform-specific naming conventions.

Unified API surface:
  install        - Set up toolkit and configure board
  setup          - Create a new project / sketch
  build          - Compile the project
  flash          - Upload firmware to the board
  monitor        - Open serial monitor
  env            - Show environment setup instructions
  refresh_config - Fetch latest configs from remote

Platform-specific APIs (passed through directly):
  esp32:   check_bootloader, idf
  arduino: list_boards, cli

Usage:
  python3 mcp_hw.py --platform arduino --api build --args MySketch
  python3 mcp_hw.py --platform esp32   --api flash
"""

import argparse
import sys
import json
import sys as _sys
import os as _os

_sys.path.insert(0, _os.path.join(_os.environ['HAGENT_ROOT'], 'hagent', 'mcp'))

# ==============================================================================
# API MAPPING
# ==============================================================================

# Unified name -> platform-specific name
_API_MAP = {
    'arduino': {
        'setup': 'new_sketch',
        'build': 'compile',
        'flash': 'upload',
    },
    'esp32': {
        # esp32 native names already match the unified names
    },
}

PLATFORMS = ('arduino', 'esp32')


def _resolve_api(platform: str, unified_api: str) -> str:
    """Translate a unified API name to the platform-specific name."""
    return _API_MAP.get(platform, {}).get(unified_api, unified_api)


def execute(platform: str, api: str, args: str = None, timeout: int = 30) -> dict:
    """
    Execute a unified or platform-specific API call.

    Args:
        platform: 'arduino' or 'esp32'
        api:      Unified or platform-specific API name
        args:     Arguments string passed through to the underlying tool
        timeout:  Timeout in seconds (used by monitor)

    Returns:
        Result dict from the underlying mcp_* module.
    """
    if platform == 'arduino':
        import mcp_arduino as _mod
    elif platform == 'esp32':
        import mcp_esp32 as _mod
    else:
        return {
            'success': False,
            'exit_code': 1,
            'stdout': '',
            'stderr': f"Unknown platform '{platform}'. Choose from: {', '.join(PLATFORMS)}",
        }

    native_api = _resolve_api(platform, api)
    return _mod.mcp_execute({'api': native_api, 'args': args, 'timeout': timeout})


# ==============================================================================
# CLI
# ==============================================================================


def main():
    parser = argparse.ArgumentParser(
        description='Unified hardware MCP entry point for Arduino and ESP32.',
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument('--platform', '-p', required=True, choices=PLATFORMS, help='Target platform: arduino or esp32')
    parser.add_argument('--api', '-a', required=True, help='API command to execute (unified or platform-specific)')
    parser.add_argument('--args', help='Arguments for the API command')
    parser.add_argument('--timeout', type=int, default=30, help='Timeout in seconds for monitor (default: 30)')
    parser.add_argument('--schema', action='store_true', help='Print the underlying platform MCP schema as JSON')

    cli_args = parser.parse_args()

    if cli_args.schema:
        if cli_args.platform == 'arduino':
            import mcp_arduino as _mod
        else:
            import mcp_esp32 as _mod
        print(json.dumps(_mod.get_mcp_schema(), indent=2))
        return 0

    result = execute(
        platform=cli_args.platform,
        api=cli_args.api,
        args=cli_args.args,
        timeout=cli_args.timeout,
    )

    if result.get('stdout'):
        print(result['stdout'])
    if result.get('stderr'):
        print(result['stderr'], file=sys.stderr)

    return result.get('exit_code', 0 if result.get('success') else 1)


if __name__ == '__main__':
    sys.exit(main())
