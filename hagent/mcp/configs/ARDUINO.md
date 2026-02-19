# HAgent Arduino Tool Guide (`hagent.arduino`)

The `hagent.arduino` tool provides a unified interface for the Arduino development workflow using `arduino-cli`.

## 1. Tool Capabilities
The tool supports the following APIs:
- `install`: Sets up the Arduino toolkit and selects a board profile.
- `install_core`: Installs the required board platform (e.g., `arduino:renesas_uno`).
- `list_boards`: Scans for and lists all currently connected Arduino hardware with detected FQBNs and Ports.
- `new_sketch`: Initializes a new `.ino` sketch directory.
- `compile`: Compiles the sketch. Uses the FQBN from the installed profile automatically.
- `upload`: Uploads the compiled binary to the board. Auto-detects the port.
- `monitor`: Opens a serial monitor to view board output (default 30s timeout).

## 2. Workflow Guidelines
- **Automatic FQBN/Port:** Once `install` is called, you do not need to provide FQBN or Port arguments manually to `compile` or `upload`. The tool resolves these from the `AGENTS.md` configuration.
- **Toolkit Environment:** The tool handles the `source export.sh` requirement internally. You do not need to manage the `arduino-toolkit` paths.
- **Sketch Structure:** Arduino projects must follow the standard structure where the `.ino` file is inside a folder of the same name.

## 3. Common Troubleshooting
- **Board Not Found:** If `upload` fails, use `list_boards` to verify the hardware is physically connected and recognized by the OS.
- **Bootloader Mode:** If the board is unresponsive during upload, the user may need to **Double-tap the RESET button** to force the board into bootloader mode.
- **Missing Core:** If compilation fails with a "platform not installed" error, use `install_core` with the identifier found in the board's MD config.
