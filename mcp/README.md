
Setup:

 1-Set the HAGENT environment variable to your hagent checkout path

 2-Launch the server

 2.1-Slang-Verilog MCP server
```
claude mcp add slang-syntax-checker ${HAGENT}/mcp/slang-mcp-server/run_server.sh
```

======
TODO:

How to do relative paths in .mcp.json

======
Coding MCP to check/learn:
  Python tools:
    https://github.com/benomahony/python_tools_mcp
    https://github.com/MarcusJellinghaus/mcp-code-checker

  Documentation extraction from github:
    https://gitmcp.io/


MCP agents: (Try to partition when it does not hurt performance)

 * FS edits in docker?
   https://github.com/safurrier/mcp-filesystem

 - Linting MCP (slang lint, ruff check, ...)

 - Format MCP (ruff format, verilog-??, ...)

 - Regression MCP (run tests subset based on changed code)
    +Report failing tests
    +Create signatures, provide "likely source of issues"

 - Debug test MCP
    + Use hints, try to debug loop

 - Synthesize MCP

 - Freq Optimize MCP
    + How to read synthesis, or call synthesis as sub-MCP?

========
Sample coordination across MCP if data must be shared.
E.g:
  Have a report_id, if passed, get from DB, otherwise try best (less contents/info)

      ```
      # test_runner_mcp.py
      from fastmcp import FastMCP

      mcp = FastMCP("TestRunner")

      @mcp.tool()
      async def run_tests(test_path: str, save_report: bool = True):
          """Run tests and optionally save detailed report"""
          result = await pytest.main([test_path, "--json-report"])

          if save_report and result.failures:
              report_id = str(uuid.uuid4())
              # Save to shared location
              save_test_report(report_id, result)
              return {
                  "status": "failed",
                  "failures": len(result.failures),
                  "report_id": report_id,
                  "summary": format_summary(result)
              }
          return {"status": "passed"}

      # bug_locator_mcp.py
      from fastmcp import FastMCP

      mcp = FastMCP("BugLocator")

      @mcp.tool()
      async def analyze_failure(report_id: str = None, failure_text: str = None):
          """Analyze test failure and suggest bug locations"""
          if report_id:
              report = load_test_report(report_id)
          else:
              report = parse_failure_text(failure_text)

          # Analyze stack traces, find relevant code
          suggestions = await analyze_failure_context(report)
          return suggestions

      @mcp.tool()
      async def get_code_context(file_path: str, line_number: int):
          """Get code context around suspected bug location"""
          # Smart context extraction...
      ```
