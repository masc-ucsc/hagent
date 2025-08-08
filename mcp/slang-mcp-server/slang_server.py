#!/usr/bin/env python3
"""
Slang MCP Server - Model Context Protocol server for SystemVerilog syntax checking
using the slang compiler. Integrates with Claude Code and other MCP clients.
"""

import asyncio
import subprocess
import tempfile
import os
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional

# Import MCP SDK components
from mcp.server.fastmcp import FastMCP

# Initialize FastMCP server
mcp = FastMCP('slang-syntax-checker')


class SlangError:
    """Represents a slang compiler error or warning."""

    def __init__(self, severity: str, location: str, message: str, code: Optional[str] = None):
        self.severity = severity
        self.location = location
        self.message = message
        self.code = code

    def to_dict(self) -> Dict[str, Any]:
        return {'severity': self.severity, 'location': self.location, 'message': self.message, 'code': self.code}


def find_slang_executable() -> Optional[str]:
    """Find the slang executable in common locations."""
    # Common installation paths for slang
    common_paths = [
        'slang',  # If in PATH
        '/usr/local/bin/slang',
        '/opt/slang/bin/slang',
        os.path.expanduser('~/bin/slang'),
        os.path.expanduser('~/.local/bin/slang'),
    ]

    # Check if slang is available from hagent project
    if 'HAGENT_ROOT' in os.environ:
        hagent_slang = os.path.join(os.environ['HAGENT_ROOT'], 'tools', 'slang', 'slang')
        if os.path.exists(hagent_slang):
            common_paths.insert(0, hagent_slang)

    for path in common_paths:
        try:
            result = subprocess.run([path, '--version'], capture_output=True, text=True, timeout=5)
            if result.returncode == 0:
                return path
        except (subprocess.TimeoutExpired, FileNotFoundError, PermissionError):
            continue

    return None


def parse_slang_output(output: str) -> List[SlangError]:
    """Parse slang compiler output to extract errors and warnings."""
    errors = []
    lines = output.strip().split('\n')

    for line in lines:
        if not line.strip():
            continue

        # Parse slang output format: filename:line:col: severity: message
        if ':' in line and any(sev in line.lower() for sev in ['error', 'warning', 'note']):
            parts = line.split(':', 3)
            if len(parts) >= 4:
                location = f'{parts[0]}:{parts[1]}:{parts[2]}'
                severity_and_message = parts[3].strip()

                # Extract severity
                severity = 'error'
                if severity_and_message.lower().startswith('warning'):
                    severity = 'warning'
                elif severity_and_message.lower().startswith('note'):
                    severity = 'note'

                # Extract message (everything after severity:)
                if ':' in severity_and_message:
                    message = severity_and_message.split(':', 1)[1].strip()
                else:
                    message = severity_and_message

                errors.append(SlangError(severity, location, message))

    return errors


async def run_slang_check(verilog_code: str, filename: str = 'input.sv') -> Dict[str, Any]:
    """Run slang syntax check on Verilog code."""
    slang_path = find_slang_executable()

    if not slang_path:
        return {
            'success': False,
            'error': 'slang compiler not found. Please install slang or set HAGENT_ROOT environment variable.',
            'errors': [],
            'warnings': [],
        }

    # Create temporary file
    with tempfile.NamedTemporaryFile(mode='w', suffix='.sv', delete=False) as tmp_file:
        tmp_file.write(verilog_code)
        tmp_path = tmp_file.name

    try:
        # Run slang with syntax checking options
        cmd = [slang_path, '--ignore-unknown-modules', tmp_path]

        process = await asyncio.create_subprocess_exec(*cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE)

        stdout, stderr = await process.communicate()

        # Combine stdout and stderr for parsing
        output = (stdout.decode() + stderr.decode()).strip()

        # Parse the output
        issues = parse_slang_output(output)

        errors = [issue for issue in issues if issue.severity == 'error']
        warnings = [issue for issue in issues if issue.severity == 'warning']
        notes = [issue for issue in issues if issue.severity == 'note']

        success = len(errors) == 0

        return {
            'success': success,
            'return_code': process.returncode,
            'errors': [error.to_dict() for error in errors],
            'warnings': [warning.to_dict() for warning in warnings],
            'notes': [note.to_dict() for note in notes],
            'raw_output': output if output else 'No issues found.',
        }

    except Exception as e:
        return {'success': False, 'error': f'Failed to run slang: {str(e)}', 'errors': [], 'warnings': []}
    finally:
        # Clean up temporary file
        try:
            os.unlink(tmp_path)
        except OSError:
            pass


@mcp.tool()
async def check_verilog_syntax(code: str, filename: str = 'input.sv') -> str:
    """
    Check SystemVerilog/Verilog syntax using the slang compiler.

    Args:
        code: The Verilog/SystemVerilog code to check
        filename: Optional filename for the code (used in error messages)

    Returns:
        JSON string with syntax check results including errors, warnings, and success status.
    """
    result = await run_slang_check(code, filename)

    # Format the output for better readability
    if result['success']:
        output = '✅ **Syntax Check Passed!**\n\n'
        if result.get('warnings'):
            output += f'⚠️  Found {len(result["warnings"])} warning(s):\n'
            for warning in result['warnings']:
                output += f'  - {warning["location"]}: {warning["message"]}\n'
        else:
            output += 'No syntax errors or warnings found.'
    else:
        output = '❌ **Syntax Check Failed!**\n\n'

        if result.get('error'):
            output += f'Error: {result["error"]}\n\n'

        if result.get('errors'):
            output += f'🔴 Found {len(result["errors"])} error(s):\n'
            for error in result['errors']:
                output += f'  - {error["location"]}: {error["message"]}\n'
            output += '\n'

        if result.get('warnings'):
            output += f'⚠️  Found {len(result["warnings"])} warning(s):\n'
            for warning in result['warnings']:
                output += f'  - {warning["location"]}: {warning["message"]}\n'

    # Add raw output for debugging if requested
    if result.get('raw_output') and result['raw_output'] != 'No issues found.':
        output += f'\n**Raw slang output:**\n```\n{result["raw_output"]}\n```'

    return output


@mcp.tool()
async def check_verilog_file(file_path: str) -> str:
    """
    Check syntax of a Verilog/SystemVerilog file using the slang compiler.

    Args:
        file_path: Path to the Verilog/SystemVerilog file to check

    Returns:
        JSON string with syntax check results.
    """
    try:
        # Read the file
        path = Path(file_path)
        if not path.exists():
            return f"❌ Error: File '{file_path}' does not exist."

        if not path.is_file():
            return f"❌ Error: '{file_path}' is not a file."

        # Check file extension
        valid_extensions = {'.v', '.sv', '.vh', '.svh', '.svi'}
        if path.suffix.lower() not in valid_extensions:
            return f"⚠️  Warning: '{file_path}' doesn't have a recognized Verilog extension. Checking anyway..."

        with open(path, 'r', encoding='utf-8') as f:
            code = f.read()

        # Run syntax check
        result = await run_slang_check(code, path.name)

        # Format output similar to check_verilog_syntax but with file context
        if result['success']:
            output = f"✅ **Syntax Check Passed for '{path.name}'!**\n\n"
            if result.get('warnings'):
                output += f'⚠️  Found {len(result["warnings"])} warning(s):\n'
                for warning in result['warnings']:
                    output += f'  - {warning["location"]}: {warning["message"]}\n'
            else:
                output += 'No syntax errors or warnings found.'
        else:
            output = f"❌ **Syntax Check Failed for '{path.name}'!**\n\n"

            if result.get('error'):
                output += f'Error: {result["error"]}\n\n'

            if result.get('errors'):
                output += f'🔴 Found {len(result["errors"])} error(s):\n'
                for error in result['errors']:
                    output += f'  - {error["location"]}: {error["message"]}\n'
                output += '\n'

            if result.get('warnings'):
                output += f'⚠️  Found {len(result["warnings"])} warning(s):\n'
                for warning in result['warnings']:
                    output += f'  - {warning["location"]}: {warning["message"]}\n'

        return output

    except UnicodeDecodeError:
        return f"❌ Error: Cannot read '{file_path}' - file appears to be binary or uses unsupported encoding."
    except PermissionError:
        return f"❌ Error: Permission denied reading '{file_path}'."
    except Exception as e:
        return f"❌ Error reading file '{file_path}': {str(e)}"


@mcp.tool()
async def get_slang_version() -> str:
    """
    Get the version of the slang compiler being used.

    Returns:
        Version information for the slang compiler.
    """
    slang_path = find_slang_executable()

    if not slang_path:
        return '❌ slang compiler not found. Please install slang or set HAGENT_ROOT environment variable.'

    try:
        result = subprocess.run([slang_path, '--version'], capture_output=True, text=True, timeout=10)

        if result.returncode == 0:
            return f'✅ **Slang Compiler Found!**\n\nPath: {slang_path}\nVersion: {result.stdout.strip()}'
        else:
            return f'⚠️  slang found at {slang_path} but version check failed:\n{result.stderr.strip()}'

    except subprocess.TimeoutExpired:
        return f'⚠️  slang found at {slang_path} but version check timed out.'
    except Exception as e:
        return f'❌ Error checking slang version: {str(e)}'


@mcp.tool()
async def slang_help() -> str:
    """
    Get help information about using the slang syntax checker.

    Returns:
        Help text explaining how to use the slang syntax checking tools.
    """
    return """
# Slang SystemVerilog Syntax Checker

This MCP server provides SystemVerilog syntax checking using the slang compiler.

## Available Tools:

### `check_verilog_syntax(code, filename="input.sv")`
Check syntax of SystemVerilog/Verilog code provided as a string.
- **code**: The Verilog/SystemVerilog code to check
- **filename**: Optional filename for better error reporting

### `check_verilog_file(file_path)`
Check syntax of a SystemVerilog/Verilog file on disk.
- **file_path**: Path to the .v/.sv file to check

### `get_slang_version()`
Get version information about the slang compiler being used.

### `slang_help()`
Show this help information.

## Examples:

**Check inline code:**
```
check_verilog_syntax("module test; endmodule")
```

**Check a file:**
```
check_verilog_file("/path/to/your/design.sv")
```

## Setup:

1. Install slang compiler or ensure it's in your PATH
2. Alternatively, set HAGENT_ROOT environment variable if using hagent project
3. The server will automatically locate the slang executable

## Supported File Extensions:
- `.v` - Verilog
- `.sv` - SystemVerilog
- `.vh` - Verilog header
- `.svh` - SystemVerilog header
- `.svi` - SystemVerilog include

For more information about slang: https://github.com/MikePopoloski/slang
"""


def main():
    """Run the MCP server."""
    import argparse

    parser = argparse.ArgumentParser(description='Slang MCP Server for SystemVerilog syntax checking')
    parser.add_argument('--version', action='version', version='slang-mcp-server 1.0.0')
    parser.parse_args()

    # Check if slang is available on startup
    slang_path = find_slang_executable()
    if not slang_path:
        print('Warning: slang compiler not found. Please install slang or set HAGENT_ROOT.', file=sys.stderr)
        print('The server will start but syntax checking will not work until slang is available.', file=sys.stderr)
    else:
        print(f'Info: Found slang at {slang_path}', file=sys.stderr)

    # Run the FastMCP server
    mcp.run()


if __name__ == '__main__':
    main()
