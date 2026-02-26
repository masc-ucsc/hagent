# HAgent Platform Configuration

This file provides the essential context needed before starting any development session. Read this before any board-specific or platform-specific files are loaded.

## Tool Selection

Choose the correct HAgent tool based on the board's supported platform:

| Platform | Tool | Use When |
| -------- | ---- | -------- |
| **Arduino** | `hagent.arduino` | Board uses `.ino` sketches / Arduino framework |
| **ESP-IDF / ESP32** | `hagent.esp32` | Board uses ESP-IDF (`idf.py`) |

Refer to the board's config file (`board_*.md`) — the **Supported Platforms** section tells you which tool to use.

> **Unsupported Boards:** If no board config exists, HAgent has no pre-defined hardware profile. Double-check all pin assignments and parameters with the user before making any tool calls.

---

## Mandatory Initialization Sequence

> [!IMPORTANT]
> **`install` must be the very first call in every session, before any other API.**

### Step 1: Install
- **Arduino:** `hagent.arduino(api="install", args="board_id")`
- **ESP-IDF:** `hagent.esp32(api="install", args="board_id")`

You may omit `args` for a partial setup (installs base toolkit only), which is useful for running discovery commands (e.g., `list_boards`, `check_bootloader`) to identify the hardware before finalizing with a board ID.

### Step 2: Load Board Context (CRITICAL)
After `install` completes, a hardware-specific context file (`AGENTS.md` / `CLAUDE.md` / `GEMINI.md`) is created in the repository.

**Do not chain any other tool calls after `install`.** Load the new context first:
- **Read the file directly:** Attempt to read the newly created `AGENTS.md` (or `CLAUDE.md` / `GEMINI.md`) from the repository to bring board-specific pinout, FQBN, and recovery procedures into the session.
- **Dynamic refresh (Gemini only):** If running in Gemini, use `/memory refresh`.
- Most LLM environments do not support a refresh command — reading the file directly is the primary approach.

Proceeding without this step means operating without the correct board configuration.

---

## Platform-Specific Details
- Arduino workflow, APIs, and guidelines → `platform_arduino.md`
- ESP-IDF workflow, APIs, and guidelines → `platform_esp32.md`
