# Gemini CLI - Project Context: Arduino Toolkit

## Overview
This project is an MCP (Model Context Protocol) implementation for Arduino development, providing a unified CLI for managing boards, sketches, compilation, and uploading using `arduino-cli`.

## Key Files
- `mcp_arduino.py`: The main MCP tool implementation for Arduino.
- `mcp_esp32.py`: The MCP tool implementation for ESP32 (used as a reference).
- `install.sh`: Installation script for `arduino-cli` and toolkit dependencies.
- `export.sh`: Environment configuration script to set PATH and local data directories.
- `sketches/Blink/Blink.ino`: The default test sketch.

## Environment Configuration
The toolkit operates using two primary environment variables:
- `HAGENT_CACHE_DIR`: Directory where the toolkit and `arduino-cli` are installed.
- `HAGENT_REPO_DIR`: The user's project repository where sketches are stored.

Sketches are managed within an `arduino-toolkit/` subdirectory inside the `HAGENT_REPO_DIR` to maintain organization.

## Implementation Details & Fixes
### mcp_arduino.py
- **Auto-detection**: Updated to handle `detected_ports` and `matching_boards` JSON structure from `arduino-cli`.
- **Core Detection**: Updated `_check_core_installed` to parse the `platforms` key and use the local `--config-file`.
- **Defaulting**: `api_compile` and `api_upload` default to the `Blink` sketch and the `nanor4` board if no arguments are provided.
- **Path Handling**: Removed `__file__` references, relying on `HAGENT_CACHE_DIR` and `HAGENT_REPO_DIR`.
- **Safety**: Added `isinstance(data, list)` checks to `_get_connected_boards` to prevent crashes when `arduino-cli` returns error dictionaries.

### install.sh
- **Rosetta 2**: Modified to automatically install Rosetta 2 on Apple Silicon Macs.
- **Non-interactive**: Commented out the interactive Rosetta check to prevent hanging during automated execution.
- **Local Config**: Generates an `arduino-cli.yaml` that points to the local `.arduino15` data directory.

## Current State
- `arduino-cli` is installed in the cache directory.
- `arduino:renesas_uno` core is installed.
- `Blink.ino` is updated to cycle through Red, Green, and Blue LEDs for testing.
- `compile` and `upload` APIs are verified and functional with auto-detection.

## How to Resume
Run the following to test the full loop:
```bash
python3 mcp_arduino.py --api compile
python3 mcp_arduino.py --api upload
```
