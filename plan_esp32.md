# ESP32 MCP Tool Plan

## Overview
The `mcp_esp32.py` tool provides a unified interface for ESP32 development workflows, including board setup, project creation, building, flashing, and monitoring.

## Architecture

### API Commands

#### 1. `install`
**Purpose**: Install ESP-IDF toolchain and configure board-specific settings.

**Arguments**: Board description (e.g., "rust board that uses esp32")

**Workflow**:
1. Fuzzy match the board description against existing `hagent/mcp/configs/board_*.md` files
2. If no match found, list available boards and prompt user
3. If matched, extract board name and ESP32 model from the markdown file
4. Check if ESP-IDF already exists in `$HAGENT_CACHE_DIR/esp-idf/`
5. If not, clone ESP-IDF from GitHub:
   ```bash
   cd $HAGENT_CACHE_DIR
   git clone --recursive https://github.com/espressif/esp-idf.git
   cd esp-idf
   ./install.sh <esp32_model>
   ```
6. Copy board configuration markdown to `$HAGENT_REPO_DIR/AGENTS.md` or append to `CLAUDE.md`

**Output**: Path to ESP-IDF installation, board configuration details

#### 2. `define_board`
**Purpose**: Create a new board configuration from a URL or specification.

**Arguments**: URL to board specification or documentation

**Workflow**:
1. Accept board specification URL as argument
2. Prompt user to provide:
   - Board name
   - ESP32 model (esp32, esp32c3, esp32s3, etc.)
   - GPIO pin mappings
   - Special features (LED pins, button pins, etc.)
3. Create `hagent/mcp/configs/board_<name>.md` with standardized format
4. Include in markdown:
   - Board name and model
   - GPIO mapping table
   - Reference URL
   - Example usage

**Output**: Path to newly created board configuration file

#### 3. `setup`
**Purpose**: Create a new ESP32 project in the repository.

**Arguments**: Project name

**Workflow**:
1. Verify ESP-IDF is installed (check `$HAGENT_CACHE_DIR/esp-idf/`)
2. Source the environment: `. $HAGENT_CACHE_DIR/esp-idf/export.sh`
3. Navigate to `$HAGENT_REPO_DIR`
4. Run `idf.py create-project -p . <project_name>`
5. Detect board model from `AGENTS.md` or `CLAUDE.md`
6. Run `idf.py set-target <esp32_model>`
7. Create a helper script `$HAGENT_REPO_DIR/esp_env.sh` that sources export.sh

**Output**: Project path, target configuration, environment setup instructions

#### 4. `build`
**Purpose**: Build the current ESP32 project.

**Arguments**: None (optional: build flags)

**Workflow**:
1. Check if `idf.py` is in PATH
2. If not, source `. $HAGENT_CACHE_DIR/esp-idf/export.sh`
3. Navigate to `$HAGENT_REPO_DIR`
4. Run `idf.py build`
5. Capture and display build output

**Output**: Build status, binary location

#### 5. `flash`
**Purpose**: Flash the built firmware to the ESP32 board.

**Arguments**: Optional flags (e.g., port specification)

**Workflow**:
1. Ensure environment is set (source export.sh if needed)
2. Navigate to `$HAGENT_REPO_DIR`
3. Run `idf.py flash` with optional port argument
4. Capture flash output and status

**Output**: Flash status, success/failure message

#### 6. `factory_reset`
**Purpose**: Guide user through factory reset process with a hello world example.

**Arguments**: None

**Workflow**:
1. Create or use existing hello world example in a temp directory
2. Build the hello world program that prints "hello NUM" every second
3. Display step-by-step instructions:
   - Step 1: Unplug the USB-C cable from the board
   - Step 2: Press and hold the "BOOT" button
   - Step 3: While holding BOOT, plug in the USB-C cable
   - Step 4: Release the BOOT button
   - Wait for user confirmation at each step
4. Flash the hello world firmware
5. Instruct user to press the RESET button
6. Run monitor briefly to verify output
7. Display success message

**Output**: Factory reset status, verification output

#### 7. `monitor`
**Purpose**: Monitor serial output from the ESP32 board.

**Arguments**: `--timeout <seconds>` (default: 30)

**Workflow**:
1. Ensure environment is set
2. Navigate to `$HAGENT_REPO_DIR`
3. Run `idf.py monitor` in a subprocess
4. Capture output for the specified timeout period
5. Send CTRL+] signal to exit monitor
6. Display captured output

**Output**: Serial monitor output

#### 8. `idf`
**Purpose**: Pass-through command to run arbitrary `idf.py` commands.

**Arguments**: Any valid idf.py arguments (e.g., "menuconfig", "clean")

**Workflow**:
1. Ensure environment is set
2. Navigate to `$HAGENT_REPO_DIR`
3. Run `idf.py <args>`
4. Display output

**Output**: Command output

## Environment Management

### Environment Variables
- `HAGENT_CACHE_DIR`: ESP-IDF installation location
- `HAGENT_REPO_DIR`: Project workspace
- `HAGENT_BUILD_DIR`: Build outputs (optional)
- `HAGENT_EXECUTION_MODE`: docker or local

### Environment Setup
- Each command that requires `idf.py` must check if it's in PATH
- If not in PATH, source `$HAGENT_CACHE_DIR/esp-idf/export.sh`
- Create helper script `esp_env.sh` during setup for manual sourcing

## Board Configuration Format

### Standard board_*.md Structure
```markdown
# Board: <Board Name>

## Model
- ESP32 Model: <esp32c3|esp32|esp32s3|etc>

## GPIO Mapping
| Function | GPIO Pin | Notes |
|----------|----------|-------|
| LED      | GPIO8    | Built-in LED |
| Button   | GPIO9    | Boot button |
| ...      | ...      | ...   |

## Reference
- URL: <board_specification_url>
- Purchase: <optional_purchase_link>

## Example Usage
```c
// LED control example
gpio_set_direction(GPIO_NUM_8, GPIO_MODE_OUTPUT);
gpio_set_level(GPIO_NUM_8, 1);
```
```

## Implementation Notes

### Fuzzy Matching Algorithm
- Use `difflib.get_close_matches()` or similar for board name matching
- Match against both filename and content of board_*.md files
- Threshold: 60% similarity
- Present top 3 matches if no exact match

### Error Handling
- Check for ESP-IDF installation before all operations
- Validate HAGENT_CACHE_DIR and HAGENT_REPO_DIR exist
- Detect USB port availability for flash/monitor
- Handle git clone failures gracefully
- Provide helpful error messages with suggested fixes

### User Interaction
- Use clear prompts for factory_reset steps
- Confirm destructive operations
- Display progress for long-running operations (clone, build)
- Use color output where appropriate for success/error states

## Testing Strategy

### Unit Tests
- Test argument parsing for all API commands
- Mock filesystem operations
- Mock subprocess calls to idf.py

### Integration Tests
- Test with actual board configurations
- Verify environment sourcing works
- Test factory_reset flow (up to user interaction)

## Future Enhancements
- Auto-detect connected boards via USB
- Support for multiple boards/projects
- Build caching and incremental builds
- OTA (Over-The-Air) update support
- Integration with debuggers (OpenOCD, GDB)
