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

A simple toggle led example, you need to setup board.

To setup:
```
mkdir -p ~/tmp/esp32_test
cd ~/tmp/esp32_test
XXX_PATH_TOHAGENT/scripts/setup_mcp.sh XXX_PATH_TOHAGENT/examples/esp32_led
```

Update the repo/AGENTS.md with the board name. Then, setup the MCP:
```
gemini mcp add hagent ./hagent_server.sh
```

Now, in gemini-cli, you could say:
"Can you recompile and flash the board?"

The esp32 IDF should be installed in cache:
```
ls ~/tmp/esp32_test/cache
```

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
