#!/usr/bin/env python3
"""
HAgent MCP Server - Ultra-simple MCP server implementation

This is a minimal MCP server that dynamically discovers and exposes 
HAgent commands from mcp_*.py files in the hagent/hagent/ directory.
"""

import json
import sys
import os
from typing import Dict, Any, List
import importlib.util
import traceback

# Add the hagent root to Python path for imports
HAGENT_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, HAGENT_ROOT)

from hagent.mcp.command_discovery import discover_mcp_commands


class HAgentMCPServer:
    """Ultra-simple MCP server for HAgent tools"""
    
    def __init__(self):
        self.commands = {}
        self._load_commands()
    
    def _load_commands(self):
        """Load all mcp_*.py commands from hagent/hagent/ directory"""
        try:
            self.commands = discover_mcp_commands()
        except Exception as e:
            print(f"Error loading commands: {e}", file=sys.stderr)
            self.commands = {}
    
    def list_tools(self) -> List[Dict[str, Any]]:
        """Return list of available tools"""
        tools = []
        for cmd_name, cmd_module in self.commands.items():
            try:
                if hasattr(cmd_module, 'get_mcp_schema'):
                    schema = cmd_module.get_mcp_schema()
                    tools.append(schema)
            except Exception as e:
                print(f"Error getting schema for {cmd_name}: {e}", file=sys.stderr)
        return tools
    
    def call_tool(self, name: str, arguments: Dict[str, Any]) -> Dict[str, Any]:
        """Execute a tool with given arguments"""
        # Find the command module by tool name
        cmd_module = None
        for cmd_name, module in self.commands.items():
            try:
                if hasattr(module, 'get_mcp_schema'):
                    schema = module.get_mcp_schema()
                    if schema.get('name') == name:
                        cmd_module = module
                        break
            except Exception:
                continue
        
        if not cmd_module:
            return {
                "isError": True,
                "content": [{"type": "text", "text": f"Tool '{name}' not found"}]
            }
        
        if not hasattr(cmd_module, 'mcp_execute'):
            return {
                "isError": True,
                "content": [{"type": "text", "text": f"Tool '{name}' missing mcp_execute function"}]
            }
        
        try:
            result = cmd_module.mcp_execute(arguments)
            return {
                "content": [{"type": "text", "text": json.dumps(result, indent=2)}]
            }
        except Exception as e:
            error_msg = f"Error executing {name}: {str(e)}\n{traceback.format_exc()}"
            return {
                "isError": True,
                "content": [{"type": "text", "text": error_msg}]
            }
    
    def handle_request(self, request: Dict[str, Any]) -> Dict[str, Any]:
        """Handle MCP request"""
        method = request.get("method")
        
        if method == "tools/list":
            return {
                "tools": self.list_tools()
            }
        elif method == "tools/call":
            params = request.get("params", {})
            name = params.get("name", "")
            arguments = params.get("arguments", {})
            return self.call_tool(name, arguments)
        else:
            return {
                "error": {
                    "code": -32601,
                    "message": f"Method not found: {method}"
                }
            }


def main():
    """Main entry point for the MCP server"""
    server = HAgentMCPServer()
    
    # Simple request processing (can be extended for full MCP protocol)
    for line in sys.stdin:
        try:
            request = json.loads(line.strip())
            response = server.handle_request(request)
            print(json.dumps(response))
        except json.JSONDecodeError:
            print(json.dumps({"error": {"code": -32700, "message": "Parse error"}}))
        except Exception as e:
            print(json.dumps({"error": {"code": -32603, "message": f"Internal error: {str(e)}"}}))


if __name__ == "__main__":
    main()