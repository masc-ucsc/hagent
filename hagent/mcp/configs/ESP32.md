# HAgent ESP32 Tool Guide (`hagent.esp32`)

The `hagent.esp32` tool provides a unified interface for ESP32 development using the ESP-IDF (`idf.py`) and `esptool.py`.

## 1. Tool Capabilities
The tool supports the following APIs:
- `install`: Sets up the ESP-IDF toolchain and selects a hardware profile.
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

## 4. Common Troubleshooting
- **Bootloader Entry:** If `check_bootloader` or `flash` fails, the board may need to be put into bootloader mode manually. This typically involves **holding the BOOT button while tapping the RESET button**.
- **SDKConfig:** The `build` process relies on `sdkconfig`. If you modify project settings via `idf(args="menuconfig")`, ensure the build is triggered afterward to apply changes.
