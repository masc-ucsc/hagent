# HAgent MCP Integration Tests

This directory contains end-to-end integration tests for the HAgent MCP (Model Context Protocol) server. The active test validates MCP add/list with Claude and/or Gemini (whichever is available).

## Prerequisites

- **Claude CLI**: Must be installed, logged-in, and accessible in PATH
- **uv**: Python package manager (used to run tests and HAgent components)
- **Docker**: Required for HAgent build operations
- **Git**: Required for repository operations

## Test Overview

### `test_mcp_setup.py`

MCP integration that validates:

1. **MCP Connectivity**: Registers `hagent` with `claude mcp add ...` and/or `gemini mcp add ...` and verifies it shows as Connected

## Running Tests

### Option 1: Run with unittest
```bash
cd /path/to/hagent
uv run python hagent/mcp/tests/run_tests.py
```

### Option 2: Run with pytest
```bash
cd /path/to/hagent
uv run pytest hagent/mcp/tests/test_mcp_setup.py -v
```

### Option 3: Run specific test
```bash
cd /path/to/hagent
uv run python -m unittest hagent.mcp.tests.test_mcp_setup.TestMCPSetupIntegration.test_mcp_setup_and_list
```

## Test Process

Each test follows this process:

1. **Setup**: Creates a temporary directory and runs `scripts/setup_mcp.sh simplechisel`
2. **MCP Installation**: Cleans and installs the `hagent` MCP server with `claude mcp add hagent ./hagent_server.sh` and/or `gemini mcp add ...`
3. **Test Execution**: Runs connectivity scenarios
4. **Cleanup**: Removes MCP server and cleans up temporary files

## Troubleshooting

1. **Claude not found**: Install the Claude CLI and ensure it is in PATH
2. **Login required**: Run `claude login` or ensure Gemini is authenticated before executing tests
3. **Inspect artifacts**: Test runs write under `output/test_mcp_setup/` with per-test subdirectories left for debugging.

### Manual Testing

You can also run the setup manually:
```bash
mkdir /tmp/manual_test
cd /tmp/manual_test
/path/to/hagent/scripts/setup_mcp.sh simplechisel
claude mcp add hagent ./hagent_server.sh
echo "Compile GCD" | claude --disallowedTools --allowed-tools mcp__hagent__hagent_build --permission-mode bypassPermissions --debug -p
```
