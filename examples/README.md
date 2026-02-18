# Getting Started

This directory has some simple examples so that "users", not "HAgent developers" get familiarized with HAgent.

## Verilog Adder

A simple adder with the corresponding hagent.yaml to indicate compilation options.

To copy and setup the MCP script:
```
mkdir -p ~/tmp/verilog_test
cd ~/tmp/verilog_test
XXXX_PATH_TO_HAGENT/scripts/setup_mcp.sh verilog_adder
```

To register hagent as a MCP for gemini:
```
gemini mcp add hagent ./hagent_server.sh
```

Now, in gemini-cli, you could say:
"Can you recompile and run tests for verilog_adder?"

## ESP32 LED

A simple toggle LED example for ESP32.

To setup the environment:
```bash
mkdir -p ~/tmp/esp32_test
cd ~/tmp/esp32_test
PATH_TO_HAGENT/scripts/setup_mcp.sh esp32_led
```

To register HAgent as an MCP server for Gemini:
```bash
gemini mcp add hagent ./hagent_server.sh
```

Now, in Gemini CLI, you can interact with the board. The recommended execution order is:
1. Navigate to the `repo` directory.
2. Start Gemini.
3. Use the `install` API to install required tools and select your board.
4. Use the `setup` API to initialize the project.
5. Use the `build` and `flash` APIs to compile and upload the firmware.

## Arduino LED

A simple Blink example for Arduino.

To setup the environment:
```bash
mkdir -p ~/tmp/arduino_test
cd ~/tmp/arduino_test
PATH_TO_HAGENT/scripts/setup_mcp.sh arduino_led
```

To register HAgent as an MCP server for Gemini:
```bash
gemini mcp add hagent ./hagent_server.sh
```

Now, in Gemini CLI, you can interact with the board. The recommended execution order is:
1. Navigate to the `repo` directory.
2. Start Gemini.
3. Use the `install` API to install required tools and select your board.
4. Use the `new_sketch` API to initialize a new sketch.
5. Use the `compile` and `upload` APIs to compile and upload the firmware.

## How to run a docker example

```
mkdir -p ~/tmp/potato4
cd ~/tmp/potato4
YOUR_PATH_TO_hagent/scripts/setup_mcp.sh simplechisel
```

NOTE: Remember to do the Synthesis Installation from README.md to have HAGENT_TECH_DIR set
```
# This variable should be defined already
echo $HAGENT_TECH_DIR
```

This sets the rest of the environment variables:
```
grep -e export hagent_server.sh >env.sh
source env.sh
```

This will list the available tools, and also install needed python packages:
```
$HAGENT_ROOT/hagent/mcp/mcp_build.py
```

This command will compile (generate Verilog) and then synthesize (generate netlist) a Dino simple CPU core and report timing:
```
$HAGENT_ROOT/hagent/mcp/mcp_build.py --name pipelined_nd --api compile
$HAGENT_ROOT/hagent/mcp/mcp_build.py --name pipelined_nd --api synth_asic
```

## TBD: issues, and suggestions


## Issues encountered
1. Directory naming inconsistency
   - some of the folder nad riectory names are very unclear, scirpts and examples, without clear documentation
   - It can be diffuclt to destinguish between user-facing scirpts and ones that are used for internal testing
2. MCP server argument issue
   - the setup script shoukd auto populate because it work provide for more efficent testing by avoiding manual correction

## SUGESTIONS
 - give the directories more clear and strightforward names
 - Update the Verilog MCP setup script to automatically include project parameters
