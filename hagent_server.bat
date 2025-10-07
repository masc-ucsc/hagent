@echo off
set "UV_PROJECT=D:\Github\hagent"
set "HAGENT_ROOT=D:\Github\hagent"
set "HAGENT_DOCKER=mascucsc/hagent-simplechisel:2025.09r"
set "HAGENT_EXECUTION_MODE=docker"
set "HAGENT_REPO_DIR=D:\Github\hagent\repo"
set "HAGENT_BUILD_DIR=D:\Github\hagent\build"
set "HAGENT_CACHE_DIR=D:\Github\hagent\cache"
set "HAGENT_OUTPUT_DIR=D:\Github\hagent\logs"

uv run python D:\Github\hagent\hagent\mcp\hagent-mcp-server.py %*
