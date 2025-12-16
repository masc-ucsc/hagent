
# tool vs MCP

Model Context Protocol (MCP) is a standard to interface tools/servers/resources with LLMs like Claude.
They need a MCP client (Claude desktop, GenAIScript,.... ) to interface the LLM and the MCP servers


Several of the hagent tools could be exposed as a MCP server, and the IO files as MCP resources.

* MCP uses json, tools uses yaml (more human readable) to interface
* MCP has 4 common APIs to implement:
    + List resources
    + Read resources
    + List tools
    + Call tools

# MCP build common APIs:

To make it easier and more consistent, hagent.yaml has these names for operations:

* compile: Generates Verilog out of some HDL like Chisel
* build: Creates an executable to run simulation
* synth_asic: Synthesize for asic, it has a --top YY and --top-synthesis XX
* synth_fpga: target FPGA
* test_xx1: run test xx1 (must compile/build first)
