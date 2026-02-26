# HAgent Arduino Tool Guide (`hagent.arduino`)

The `hagent.arduino` tool provides a unified interface for the Arduino development workflow using `arduino-cli`.

## Mandatory Initialization Sequence

> [!IMPORTANT]
> **`install` must be the very first call in every session. Never call any other API before `install` completes.**

### Step 1: Install
- With board ID: `hagent.arduino(api="install", args="board_id")`
- Without board ID (partial setup): `hagent.arduino(api="install")` — installs the base toolkit only; useful for running `list_boards` to discover hardware before completing setup with a board ID.

### Step 2: Memory Refresh (CRITICAL)
After `install` completes, a hardware-specific context file (`AGENTS.md` / `CLAUDE.md` / `GEMINI.md`) is created in the repository containing board-specific pinout, FQBN, and recovery procedures.

**Do not chain any other tool calls after `install`.** This step requires loading the new context before proceeding. After install completes:
- **Read the file directly:** Attempt to read the newly created `AGENTS.md` (or `CLAUDE.md` / `GEMINI.md`) file from the repository to load board-specific context into the session.
- **Dynamic refresh (Gemini only):** If running in Gemini, use `/memory refresh` to reload context.
- Most LLM environments do not support a refresh command — in those cases, reading the file directly is the primary approach.

Proceeding without this step means operating without the correct board configuration.

---

## 1. Tool Capabilities
The tool supports the following APIs:
- `install`: Sets up the Arduino toolkit and selects a board profile.
- `refresh_config`: Fetches the latest board configs from the remote repository.
- `list_boards`: Scans for and lists all currently connected Arduino hardware with detected FQBNs and Ports.
- `new_sketch`: Initializes a new `.ino` sketch directory.
- `compile`: Compiles the sketch. Uses the FQBN from the installed profile automatically.
- `upload`: Uploads the compiled binary to the board. Auto-detects the port.
- `monitor`: Opens a serial monitor to view board output (default 30s timeout).

## 2. Workflow Guidelines
- **Automatic FQBN/Port:** Once `install` is called, you do not need to provide FQBN or Port arguments manually to `compile` or `upload`. The tool resolves these from the `AGENTS.md` configuration.
- **Toolkit Environment:** The tool handles the `source export.sh` requirement internally. You do not need to manage the `arduino-toolkit` paths.
- **Sketch Structure:** Arduino projects must follow the standard structure where the `.ino` file is inside a folder of the same name.

## 3. General Platform Notes
- **Repo-Centric:** All operations occur within the `HAGENT_REPO_DIR`. Do not attempt to run tools outside this directory.
- **No Direct Shell Access:** Never run `arduino-cli` directly in the shell. The tool manages environment paths internally.
- **Persistence:** Board selection is persisted in the repository. Once installed, subsequent calls to `compile` and `upload` automatically use the correct board profile.

## 4. Common Troubleshooting
- **Board Not Found:** If `upload` fails, use `list_boards` to verify the hardware is physically connected and recognized by the OS.
- **Bootloader Mode:** If the board is unresponsive during upload, the user may need to **Double-tap the RESET button** to force the board into bootloader mode.
- **Missing Core:** If compilation fails with a "platform not installed" error, use `install_core` with the identifier found in the board's MD config.
