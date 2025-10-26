# Getting Started

This directory has some simple examples so that "users", not "HAgent developers" get familiarized with HAgent.

## Verilog Adder

A simple adder with the corresponding hagent.yaml to indicate compilation options.

To copy and setup the MCP script:
```
mkdir -p ~/tmp/verilog_test
cd ~/tmp/verilog_test
XXXX_PATH_TO_HAGENT/scripts/setup_mcp.sh verilog-adder
```

To register hagent as a MCP for gemini:
```
gemini mcp add hagent ./hagent_server.sh
```

Now, in gemini-cli, you could say:
"Can you recompile and run tests for verilog_adder?"


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
   
