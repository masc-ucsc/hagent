# HAgent MCP Integration Tests

This directory contains end-to-end integration tests for the HAgent MCP (Model Context Protocol) server with Gemini.

## Prerequisites

- **Gemini CLI**: Must be installed and accessible in PATH
- **uv**: Python package manager (used to run tests and HAgent components)
- **Docker**: Required for HAgent build operations
- **Git**: Required for repository operations

## Test Overview

### `test_gemini_setup.py`

Comprehensive integration test that validates:

1. **Schema Consistency**: Verifies that Gemini's MCP schema matches `mcp_build.py --schema`
2. **Successful Compilation**: Tests end-to-end compilation workflow with Gemini
3. **Error Handling**: Tests error detection, reporting, and iteration with compilation failures
4. **MCP Connectivity**: Verifies basic MCP server connectivity

## Running Tests

### Option 1: Run with unittest
```bash
cd /path/to/hagent
uv run python hagent/mcp/tests/run_tests.py
```

### Option 2: Run with pytest
```bash
cd /path/to/hagent
uv run pytest hagent/mcp/tests/test_gemini_setup.py -v
```

### Option 3: Run specific test
```bash
cd /path/to/hagent
uv run python -m unittest hagent.mcp.tests.test_gemini_setup.TestGeminiMCPIntegration.test_1_schema_consistency
```

## Test Process

Each test follows this process:

1. **Setup**: Creates temporary directory and runs `scripts/setup_simplechisel_mcp.sh`
2. **MCP Installation**: Cleans and installs the `hagent` MCP server in Gemini
3. **Test Execution**: Runs specific test scenarios
4. **Cleanup**: Removes MCP server and cleans up temporary files

## Test Details

### Test 1: Schema Consistency
- Calls `mcp_build.py --schema` to get expected schema
- Calls `gemini /mcp schema` to get actual schema
- Verifies key components match (tools, parameters, profiles)

### Test 2: Successful Compilation
- Uses Gemini CLI with MCP to compile the `gcd` profile
- Verifies that Verilog files are generated (`build/build_gcd/GCD.sv`)
- Checks for successful completion without errors

### Test 3: Error Handling and Iteration
- Introduces a deliberate typo in `GCD.scala` (changes `io.outputGCD` to `io_outputGCD`)
- Runs Gemini compilation command
- Verifies that:
  - Compilation error is detected and reported
  - Error message contains actionable information
  - Gemini may attempt to fix the error automatically

### Test 4: MCP Server Connectivity
- Verifies the HAgent MCP server is properly connected
- Checks `gemini mcp list` output for connectivity status

## Expected Output

Successful test run should show:
```
test_1_schema_consistency ... ok
test_2_successful_compilation ... ok  
test_3_error_handling_and_iteration ... ok
test_4_mcp_server_connectivity ... ok
```

## Troubleshooting

### Common Issues

1. **Gemini not found**: Install Gemini CLI and ensure it's in PATH
2. **Permission issues**: Ensure Docker is running and accessible
3. **Timeout issues**: Tests have generous timeouts, but very slow systems may need adjustments
4. **Network issues**: Repository cloning requires internet access

### Debug Information

Tests create a `setup_run/` directory in the HAgent root during execution. This directory is **not** cleaned up automatically, making it easy to debug test failures.

The test output includes the test directory path:
```
Test directory: /path/to/hagent/setup_run (persistent for debugging)
```

After tests complete, you can examine the setup:
```bash
cd /path/to/hagent/setup_run
ls -la  # See generated files
cat hagent_server.sh  # Examine server script
cat hagent_mcp_conf.json  # Check MCP configuration
```

To clean up after debugging:
```bash
rm -rf setup_run
```

### Manual Testing

You can also run the setup manually:
```bash
mkdir /tmp/manual_test
cd /tmp/manual_test
/path/to/hagent/scripts/setup_simplechisel_mcp.sh
gemini mcp add hagent ./hagent_server.sh
gemini --allowed-mcp-server-names "hagent" -y -p "Can you compile the gcd profile?"
```