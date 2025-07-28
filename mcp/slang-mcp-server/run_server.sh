#!/bin/bash
cd ${HAGENT}/mcp/slang-mcp-server/
exec uv run slang_server.py "$@"
