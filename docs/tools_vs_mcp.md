
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

