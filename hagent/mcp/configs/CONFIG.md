# HAgent MCP Tool Configuration & Selection

This guide helps the agent select the correct tool for hardware interaction and outlines the mandatory initialization sequence.

## 1. Tool Selection Logic

Choose the appropriate HAgent MCP tool based on the hardware and framework:

### **`hagent.arduino`**
Use this tool for any board running the **Arduino framework** (using `.ino` sketches). 
**Supported Boards (Configs available):**
- `arduino_nano_esp32` (Arduino Nano ESP32)
- `arduino_nano_r4` (Arduino Nano R4 Wi-Fi)
- `arduino_uno_r4_minima` (Arduino Uno R4 Minima)

### **`hagent.esp32`**
Use this tool for boards using the **Espressif IoT Development Framework (ESP-IDF)** or for low-level ESP32 development.
**Supported Boards (Configs available):**
- `rust_esp32_c3` (ESP32-C3 targeted for Rust/IDF)

### **Unsupported Boards Warning**
If the user's board is **not** in the list above, HAgent does not have a pre-defined hardware configuration. 
> [!WARNING]
> Programming an unsupported board is limited to the LLM's internal knowledge base. This is prone to errors. **Double-check all pin assignments and tool parameters with the user before authorizing tool calls.**

---

## 2. Mandatory Initialization Sequence

Before starting development or running build/flash commands, follow these steps:

### **Step 1: Install**
Always call the `install` API first for the specific platform tool. This must be run **once per session per board**. This sets up the internal toolkits and prepares the hardware profile.
- **Arduino:** `hagent.arduino(api="install", args="board_id")`
- **ESP32:** `hagent.esp32(api="install", args="board_id")`

> [!NOTE]
> **Specify the board ID:** Avoid running the `install` tool without the `args` parameter. Running it without a board identifier will only return a list of available boards, requiring an additional tool call to complete the installation. Identify the board from the list in Section 1 and pass its ID immediately.

### **Step 2: Memory Refresh (CRITICAL)**
After `api_install` completes, a new hardware-specific context file (`AGENTS.md` / `GEMINI.md` / `CLAUDE.md`) is created in the repository.
> [!IMPORTANT]
> **Ask the user to run `/refresh` or `/memory refresh` in the chat interface immediately after installation.**
> This is necessary to load the new pinout diagrams, FQBN identifiers, and recovery procedures into the LLM's active context.

---

## 3. General Platform Instructions
- **Repo-Centric:** All operations occur within the `HAGENT_REPO_DIR`. Do not attempt to run tools outside this directory.
- **No Direct Shell Access:** Never run `arduino-cli` or `idf.py` directly in the shell. The MCP tools manage complex environment variables and paths internally.
- **Persistence:** Board selection is persisted in the repository. Subsequent calls to `compile`, `build`, or `flash` will automatically use the correct settings from the installed profile.
