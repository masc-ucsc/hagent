"""
MCP Message Handlers for HAgent MCP Server

Contains individual handler functions for different JSON-RPC methods,
extracted from the main MCP server for better organization and maintainability.
"""

import asyncio
import json
import logging
import traceback
from typing import Any, Dict, List, Optional, Tuple


class MCPMessageHandlers:
    """Handlers for different MCP JSON-RPC methods."""

    def __init__(self, mcp_instance, raw_logger: logging.Logger):
        """
        Initialize MCP message handlers.

        Args:
            mcp_instance: FastMCP instance
            raw_logger: Logger for raw I/O operations
        """
        self.mcp_instance = mcp_instance
        self.raw_logger = raw_logger
        self.tools = []

    def set_tools(self, tools: List):
        """Set the available tools list."""
        self.tools = tools

    def handle_initialize(self, request_id: Optional[str]) -> Dict[str, Any]:
        """Handle 'initialize' method."""
        self.raw_logger.info('Handling initialize request')

        result = {
            'protocolVersion': '2025-06-18',
            'capabilities': {
                'experimental': {},
                'prompts': {'listChanged': False},
                'resources': {'subscribe': False, 'listChanged': False},
                'tools': {'listChanged': False},
            },
            'serverInfo': {'name': 'HAgentMCPServer', 'version': '1.13.0'},
        }

        return self._create_jsonrpc_response(request_id, result)

    def handle_tools_list(self, request_id: Optional[str]) -> Dict[str, Any]:
        """Handle 'tools/list' method."""
        self.raw_logger.info('Handling tools/list request')

        # Convert Tool objects to JSON-serializable dictionaries
        tools_json = []
        for tool in self.tools:
            tool_dict = {'name': tool.name, 'description': tool.description, 'inputSchema': tool.inputSchema}
            if hasattr(tool, 'outputSchema') and tool.outputSchema:
                tool_dict['outputSchema'] = tool.outputSchema
            tools_json.append(tool_dict)

        result = {'tools': tools_json}
        self.raw_logger.info(f'TOOLS LIST RESPONSE: {len(self.tools)} tools')

        return self._create_jsonrpc_response(request_id, result)

    def handle_tools_call(self, request_id: Optional[str], params: Dict[str, Any]) -> Dict[str, Any]:
        """Handle 'tools/call' method."""
        name = params.get('name', '')
        # For Gemini compatibility - handle both by id and by name
        tool_id = params.get('id', name)
        if not name and tool_id:
            name = tool_id

        arguments = params.get('arguments', {})
        self.raw_logger.info(f'TOOL CALL: {name} with arguments {json.dumps(arguments)}')

        try:
            # For FastMCP 1.13.0+, call_tool might be a coroutine
            tool_response_coroutine = self.mcp_instance.call_tool(name, arguments)

            if asyncio.iscoroutine(tool_response_coroutine):
                # Run the coroutine in a new event loop
                loop = asyncio.new_event_loop()
                tool_response = loop.run_until_complete(tool_response_coroutine)
                loop.close()
            else:
                tool_response = tool_response_coroutine

            # Process tool response and determine success/failure
            is_success, error_message = self._analyze_tool_response(tool_response)
            formatted_result = self._format_tool_response(tool_response)

            # Generate appropriate JSON-RPC response
            if is_success:
                self.raw_logger.info(f'TOOL RESPONSE SUCCESS: {name}')
                return self._create_jsonrpc_response(request_id, formatted_result)
            else:
                self.raw_logger.error(f'TOOL ERROR: {name} - {error_message or "Tool execution failed"}')
                # Create proper JSON-RPC error response
                if error_message:
                    error_data = {'type': 'text', 'text': error_message}
                    error = self._create_jsonrpc_error(-32603, error_message, error_data)
                else:
                    error = self._create_jsonrpc_error(-32603, f'Tool execution error: {name}')
                return self._create_jsonrpc_response(request_id, error=error)

        except Exception as e:
            self.raw_logger.error(f'TOOL ERROR: {name} - {str(e)}\n{traceback.format_exc()}')
            error_data = {'type': 'text', 'text': str(e)}
            error = self._create_jsonrpc_error(-32603, f'Tool execution error: {name}', error_data)
            return self._create_jsonrpc_response(request_id, error=error)

    def handle_roots_list(self, request_id: Optional[str]) -> Dict[str, Any]:
        """Handle 'roots/list' method for Gemini compatibility."""
        self.raw_logger.info('Handling roots/list request')

        # Create list of roots (tool categories)
        root_info = {'id': 'hagent', 'title': 'HAgent Tools', 'canCreateToolRoots': False}
        result = {'roots': [root_info]}

        self.raw_logger.info(f'ROOTS LIST RESPONSE: {json.dumps(result)}')
        return self._create_jsonrpc_response(request_id, result)

    def handle_roots_get(self, request_id: Optional[str], params: Dict[str, Any]) -> Dict[str, Any]:
        """Handle 'roots/get' method for Gemini compatibility."""
        self.raw_logger.info('Handling roots/get request')
        root_id = params.get('rootId')

        if root_id == 'hagent':
            # Convert the tools list to the format Gemini expects
            gemini_tools = []
            for tool in self.tools:
                gemini_tool = {
                    'id': tool.name,
                    'title': tool.name.split('.')[-1].title(),
                    'description': tool.description or '',
                }
                gemini_tools.append(gemini_tool)

            result = {
                'root': {
                    'id': 'hagent',
                    'title': 'HAgent Tools',
                    'canCreateToolRoots': False,
                    'tools': gemini_tools,
                }
            }

            self.raw_logger.info(f'ROOTS GET RESPONSE: {len(gemini_tools)} tools')
            return self._create_jsonrpc_response(request_id, result)
        else:
            error = self._create_jsonrpc_error(-32602, f'Unknown root ID: {root_id}')
            return self._create_jsonrpc_response(request_id, error=error)

    def handle_notifications_initialized(self, request_id: Optional[str]) -> Optional[Dict[str, Any]]:
        """Handle 'notifications/initialized' method."""
        self.raw_logger.info('Handling notifications/initialized request')
        # This is a notification (no id), so no response needed
        return None

    def handle_ping(self, request_id: Optional[str]) -> Dict[str, Any]:
        """Handle 'ping' method."""
        self.raw_logger.info('Handling ping request')
        return self._create_jsonrpc_response(request_id, {})

    def handle_shutdown(self, request_id: Optional[str]) -> Dict[str, Any]:
        """Handle 'shutdown' method."""
        self.raw_logger.info('Handling shutdown request')
        return self._create_jsonrpc_response(request_id, True)

    def handle_exit(self, request_id: Optional[str]) -> Tuple[Optional[Dict[str, Any]], bool]:
        """
        Handle 'exit' method.

        Returns:
            Tuple of (response, should_exit)
        """
        self.raw_logger.info('Handling exit request')
        response = self._create_jsonrpc_response(request_id, True)
        return response, True

    def handle_unknown_method(self, request_id: Optional[str], method: str) -> Dict[str, Any]:
        """Handle unknown methods."""
        self.raw_logger.error(f'UNKNOWN METHOD: {method}')
        error = self._create_jsonrpc_error(-32601, f'Method not found: {method}')
        return self._create_jsonrpc_response(request_id, error=error)

    def _analyze_tool_response(self, tool_response: Any) -> Tuple[bool, Optional[str]]:
        """
        Analyze tool response to determine success/failure and extract error messages.

        Args:
            tool_response: Response from tool execution

        Returns:
            Tuple of (is_success, error_message)
        """
        is_success = True
        error_message = None
        response_content = None

        # Handle different response types from FastMCP
        if isinstance(tool_response, list) and tool_response:
            # Check if first item in list contains our error marker
            first_item = tool_response[0]
            if hasattr(first_item, 'text') and '"_mcp_error": true' in first_item.text:
                try:
                    start_idx = first_item.text.find('{')
                    end_idx = first_item.text.rfind('}') + 1
                    if start_idx != -1 and end_idx > start_idx:
                        json_content = first_item.text[start_idx:end_idx]
                        response_content = json.loads(json_content)
                except Exception:
                    pass
        elif isinstance(tool_response, str) and '"_mcp_error": true' in tool_response:
            # Parse the JSON content from the response string
            try:
                start_idx = tool_response.find('{')
                end_idx = tool_response.rfind('}') + 1
                if start_idx != -1 and end_idx > start_idx:
                    json_content = tool_response[start_idx:end_idx]
                    response_content = json.loads(json_content)
            except Exception:
                pass
        elif isinstance(tool_response, dict) and tool_response.get('_mcp_error'):
            response_content = tool_response

        if response_content and response_content.get('_mcp_error'):
            # This is our special error marker
            is_success = False
            error_message = response_content.get('error_message', 'Tool execution failed')
        elif isinstance(tool_response, str):
            # Check if the response contains failure indicators
            if 'FAILED' in tool_response or 'exit code: 1' in tool_response or 'Execution Status: FAILED' in tool_response:
                is_success = False
        elif isinstance(tool_response, dict):
            # Check for explicit success/failure indicators in the response
            if 'success' in tool_response and not tool_response['success']:
                is_success = False
            elif 'exit_code' in tool_response and tool_response['exit_code'] != 0:
                is_success = False

        return is_success, error_message

    def _format_tool_response(self, tool_response: Any) -> Dict[str, Any]:
        """
        Format tool response for better client compatibility.

        Args:
            tool_response: Raw tool response

        Returns:
            Formatted response dictionary
        """
        if isinstance(tool_response, dict):
            # If there's a content field, keep it as is for Claude compatibility
            if 'content' not in tool_response:
                # For Gemini, wrap in a result object with content
                return {'result': tool_response}
            else:
                return tool_response
        else:
            # Handle non-dict responses
            return {'result': str(tool_response) if tool_response is not None else ''}

    def _create_jsonrpc_response(self, id: Optional[str], result: Any = None, error: Any = None) -> Dict[str, Any]:
        """Create a JSON-RPC 2.0 response."""
        response = {'jsonrpc': '2.0', 'id': id}

        if error is not None:
            response['error'] = error
        else:
            response['result'] = result

        return response

    def _create_jsonrpc_error(self, code: int, message: str, data: Any = None) -> Dict[str, Any]:
        """Create a JSON-RPC 2.0 error object."""
        error = {'code': code, 'message': message}
        if data is not None:
            error['data'] = data
        return error


def handle_mcp_stdio_request(request: Dict[str, Any], handlers: MCPMessageHandlers) -> Tuple[Optional[Dict[str, Any]], bool]:
    """
    Handle a single MCP stdio request.

    Args:
        request: Parsed JSON-RPC request
        handlers: MCPMessageHandlers instance

    Returns:
        Tuple of (response_dict, should_exit)
    """
    method = request.get('method', '')
    params = request.get('params', {})
    request_id = request.get('id')
    jsonrpc = request.get('jsonrpc', '2.0')

    handlers.raw_logger.info(f'PROCESSING METHOD: {method} (ID: {request_id}, JSON-RPC: {jsonrpc})')

    # Route to appropriate handler
    if method == 'initialize':
        return handlers.handle_initialize(request_id), False
    elif method == 'tools/list':
        return handlers.handle_tools_list(request_id), False
    elif method == 'tools/call':
        return handlers.handle_tools_call(request_id, params), False
    elif method == 'roots/list':
        return handlers.handle_roots_list(request_id), False
    elif method == 'roots/get':
        return handlers.handle_roots_get(request_id, params), False
    elif method == 'notifications/initialized':
        return handlers.handle_notifications_initialized(request_id), False
    elif method == 'ping':
        return handlers.handle_ping(request_id), False
    elif method == 'shutdown':
        return handlers.handle_shutdown(request_id), False
    elif method == 'exit':
        response, should_exit = handlers.handle_exit(request_id)
        return response, should_exit
    else:
        return handlers.handle_unknown_method(request_id, method), False
