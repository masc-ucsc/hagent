# Gemini MCP Context & Progress

This document summarizes the current state of the HAgent MCP server project, covering both ESP32 and Arduino implementations, and provides context for continuing development with Gemini.

## 1. Project Overview
We are building an **MCP Server** (`hagent`) that enables LLMs (like Gemini) to interact directly with hardware boards.
*   **Goal:** Allow Gemini to "Install tools", "Create Project", "Build", "Flash", and "Monitor" embedded boards using natural language.
*   **Supported Platforms:**
    *   **ESP32** (via ESP-IDF)
    *   **Arduino** (via `arduino-cli`)
*   **Key Files:**
    *   `hagent/mcp/hagent-mcp-server.py`: The main server entry point (FastMCP).
    *   `hagent/mcp/mcp_esp32.py`: ESP32 tool implementation.
    *   `hagent/mcp/mcp_arduino.py`: Arduino tool implementation.
    *   `scripts/setup_mcp.sh`: Script to scaffold a new project directory.
    *   `hagent/mcp/configs/*.md`: Board-specific configurations and "recipes".

## 2. Architecture & Execution Flow
1.  **Gemini CLI** calls the registered script (`hagent_server.sh`).
2.  **`hagent_server.sh`** sets up env vars (`HAGENT_REPO_DIR`, `HAGENT_CACHE_DIR`) and runs `uv run hagent-mcp-server.py`.
3.  **`hagent-mcp-server.py`** discovers tools and registers them (e.g., `hagent.esp32`, `hagent.arduino`).
4.  **Mega-Tools:** The server exposes single entry points for each platform:
    *   `hagent.esp32(api='...', args='...')`
    *   `hagent.arduino(api='...', args='...')`
5.  **Persistence:** When a board is installed (`api_install`), its configuration is copied to `AGENTS.md` (and `GEMINI.md`) in the `HAGENT_REPO_DIR`. Subsequent tools read this file to auto-configure themselves.

## 3. Current Status (Feb 2026)

### General Architecture
*   **Non-Blocking:** All blocking `input()` calls have been removed or refactored into two-step handshakes or "recipes" (Markdown instructions).
*   **Output Handling:** `hagent-mcp-server.py` ensures `stdout` and `stderr` are correctly returned to the Agent.
*   **Repo-Centric:** Operations occur directly in `HAGENT_REPO_DIR` to maintain a predictable flat structure.

### ESP32 Integration
*   **`api_install`**: Implements a non-blocking two-step handshake for board selection.
*   **`api_check_bootloader`**: New tool to verify hardware connectivity (using `esptool chip-id`).
*   **`api_factory_reset`**: Removed monolithic function; replaced with "Procedures" in board config files (Recipe pattern).
*   **`api_monitor`**: Basic implementation with timeout.

### Arduino Integration
*   **Config-Driven**: FQBN and Core identifiers are extracted from `configs/*.md`.
*   **`api_install_core`**: Separated from main installation for modularity.
*   **`api_list_boards`**: Uses `arduino-cli --format json` to filter noise and return clean hardware data.
*   **`api_upload`**: Config-aware and repo-centric.
*   **Target Board**: Verified with Arduino Nano R4 (ABX00143).

## 4. Key Decisions
*   **"Assume Yes" / "Two-Step Handshake":** To handle ambiguity without blocking, tools either fail fast with a list of options (forcing the LLM to retry with specific args) or use sensible defaults.
*   **Recipe Approach:** Complex physical interactions (like holding buttons for factory reset) are moved out of Python code and into Markdown "Procedures" that the LLM reads and guides the user through.
*   **One Board Per Project:** The `AGENTS.md` persistence model enforces a single active board configuration per project directory.

## 5. Next Steps
1.  **`api_flash_test_firmware`**: Implement a safe, non-blocking tool to flash a "Hello World" example from a temporary directory for hardware verification without touching the main project.
2.  **Monitor Refinement**: Improve signal handling and timeout behavior in `api_monitor` for both platforms.
3.  **System Prompt Update**: Instruct the Agent to prioritize `GEMINI.md`/`AGENTS.md` in the repo for board-specific recipes.
4.  **Testing**: Continue verification with `gemini mcp list` and functional tests of `build`/`flash` workflows.