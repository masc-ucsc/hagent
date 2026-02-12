# Context: Interactive Blocking Resolution in MCP Tools

**Date:** February 4, 2026
**Topic:** Handling interactive user input (e.g., `input()`) in MCP tool functions (`mcp_esp32.py`).

## The Problem
Interactive functions like `api_install` (selecting a board from a list) and `api_factory_reset` (waiting for user confirmation to hold buttons) use blocking `input()` calls. This causes the MCP server/Agent to stall or hang because the LLM cannot physically type into the process's `stdin` during a tool execution.

## Brainstormed Solutions
1.  **"Assume Yes" Pattern:** Force non-interactive modes with default selections.
2.  **"Missing Parameter" Pattern (Two-Step Handshake):** Fail fast if arguments are ambiguous, returning a list of valid options. The LLM re-calls the tool with the specific parameter.
3.  **"State File" Context:** Rely on pre-configured environment variables or files to answer questions.
4.  **Asynchronous/Job Pattern:** Return a "Job Started" status and allow polling, rather than blocking the main thread.
5.  **"Recipe" / Data-Driven Approach:** Move procedural logic (like "Hold the BOOT button") out of Python code and into the Markdown board configuration.

## Selected Approach

### 1. Board Selection (`api_install`) -> Option 2 (Two-Step Handshake)
*   **Mechanism:**
    *   Remove `input()`.
    *   Logic:
        *   If `args` (board name) matches exactly one board -> Proceed.
        *   If `args` matches zero or multiple boards -> Return `success: False` with `stderr` listing the valid candidates.
    *   **Reasoning:** This forces the Agent to read the error, pick the correct board name, and call `api_install("exact_board_name")` again. Simple and effective for disambiguation.
    *   **Architecture Validation:** This belongs in Python because installation logic is **Toolkit-Specific** (ESP-IDF vs. Arduino vs. Zephyr).

### 2. Complex Workflows (`api_factory_reset`) -> Option 5 (Recipe Approach)
*   **Mechanism:**
    *   **Delete/Deprecate** the monolithic `api_factory_reset` Python function.
    *   **Update Board Configs (`configs/*.md`)**: Add a "Procedures" section (e.g., `## Factory Reset`) containing step-by-step instructions.
    *   **LLM Role:** The LLM reads this "Recipe" from the Markdown file and orchestrates the steps (Call Build -> Chat with user -> Call Flash).
*   **Reasoning:** Non-blocking and flexible for different physical hardware layouts.

### 3. Session Persistence Pattern (The "AGENTS.md" Link)
*   **Mechanism:**
    *   When a board is successfully selected via `api_install`, the toolkit script **OVERWRITES** `AGENTS.md` (or `CLAUDE.md`) in the `HAGENT_REPO_DIR` with the new board's configuration.
*   **Policy:** **One Board Per Project Directory.**
    *   We do not append; we replace.
    *   If a user needs multiple boards, they must use separate directories/repos for each firmware project.
*   **Retrieval:** Subsequent tools (`api_setup`, `api_build`) read `AGENTS.md` to automatically detect the target model.

## Completed (Feb 8, 2026)
*   **Refactored `api_install`**: Implemented non-blocking two-step handshake, metadata parsing with regex, and strict `args` requirement.
*   **Context Persistence**: Updated `api_install` to create both `AGENTS.md` and `GEMINI.md` in the target repository.
*   **Hardware Verification**: Added `api_check_bootloader` using `esptool chip-id` as a primary hardware diagnostic.
*   **Tool Cleanup**: Removed `api_factory_reset` and `api_define_board`.
*   **Interactive Recipes**: Updated `configs/board_rust_esp32_c3.md` with a non-blocking "Ask -> Confirm -> Verify" recipe for the Agent.

## Next Steps
*   **`api_flash_test_firmware`**: Implement a safe, non-blocking tool to flash a "Hello World" example from a temporary directory for hardware verification without touching the main project.
*   **Monitor Refinement**: Improve signal handling and timeout behavior in `api_monitor`.
*   **System Prompt Update**: Instruct the Agent to prioritize `GEMINI.md`/`AGENTS.md` in the repo for board-specific recipes.
