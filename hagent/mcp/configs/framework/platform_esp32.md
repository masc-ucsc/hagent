# HAgent ESP32 Tool Guide (`hagent.esp32`)

The `hagent.esp32` tool provides a unified interface for ESP32 development using the ESP-IDF (`idf.py`) and `esptool.py`.

## Mandatory Initialization Sequence

> [!IMPORTANT]
> **`install` must be the very first call in every session. Never call any other API before `install` completes.**

### Step 1: Install
- With board ID: `hagent.esp32(api="install", args="board_id")`
- Without board ID (partial setup): `hagent.esp32(api="install")` — installs the base toolchain only; useful for running `check_bootloader` to verify connectivity before completing setup with a board ID.

### Step 2: Memory Refresh (CRITICAL)
After `install` completes, a hardware-specific context file (`AGENTS.md` / `CLAUDE.md` / `GEMINI.md`) is created in the repository containing board-specific pinout, chip target, and recovery procedures.

**Do not chain any other tool calls after `install`.** This step requires loading the new context before proceeding. After install completes:
- **Read the file directly:** Attempt to read the newly created `AGENTS.md` (or `CLAUDE.md` / `GEMINI.md`) file from the repository to load board-specific context into the session.
- **Dynamic refresh (Gemini only):** If running in Gemini, use `/memory refresh` to reload context.
- Most LLM environments do not support a refresh command — in those cases, reading the file directly is the primary approach.

Proceeding without this step means operating without the correct board configuration.

---

## 1. Tool Capabilities
The tool supports the following APIs:
- `install`: Sets up the ESP-IDF toolchain and selects a hardware profile.
- `refresh_config`: Fetches the latest board configs from the remote repository.
- `setup`: Scaffolds a new ESP-IDF project.
- `build`: Compiles the project using `idf.py build`.
- `flash`: Uploads firmware to the board using `idf.py flash`.
- `check_bootloader`: Handshakes with the chip to verify connectivity.
- `monitor`: Displays serial output from the board (default 30s timeout).
- `idf`: Passthrough for arbitrary `idf.py` commands.

## 2. Workflow Guidelines
- **Hardware First:** Always call `check_bootloader` before attempting to `flash`. This verifies that the USB-to-Serial connection is active and the chip is responsive.
- **Project Scaffolding:** Use `setup` to initialize the directory. This will set the correct IDF target (e.g., `esp32s3` or `esp32c3`) based on the installed profile.
- **Automatic Environment:** The tool manages the ESP-IDF environment variables (`PATH`, `IDF_PATH`) internally. You do not need to manually source `export.sh`.

## 3. Important Safety Warnings
- **`api_setup` Data Loss:** 
  > [!CAUTION]
  > **Running `api_setup` will erase the contents of the repository directory** to ensure a clean project state. 
  > **Always warn the user and obtain explicit confirmation before calling `api_setup` if there is existing code in the directory.** 
  > Note: `.git`, `.gemini`, and configuration files like `AGENTS.md` are protected and will not be erased.

## 4. General Platform Notes
- **Repo-Centric:** All operations occur within the `HAGENT_REPO_DIR`. Do not attempt to run tools outside this directory.
- **No Direct Shell Access:** Never run `idf.py` or `esptool.py` directly in the shell. The tool manages the ESP-IDF environment internally.
- **Persistence:** Board selection is persisted in the repository. Once installed, subsequent calls to `build` and `flash` automatically use the correct chip target and hardware profile.

## 5. Common Troubleshooting
- **Bootloader Entry:** If `check_bootloader` or `flash` fails, the board may need to be put into bootloader mode manually. This typically involves **holding the BOOT button while tapping the RESET button**.
- **SDKConfig:** The `build` process relies on `sdkconfig`. If you modify project settings via `idf(args="menuconfig")`, ensure the build is triggered afterward to apply changes.
