## HAgent Quick Guide

Follow these concise rules when working in this repo.

### Test and Run
- Always use `uv run` wrappers: `uv run pytest  -n auto --forked ...` and `uv run python ...` (never `python -m pytest`).
- Fast pytest or debug iteration: `uv run pytest --testmon --maxfail=1`.

### Code Quality (required before finishing)
- Format: `uv run ruff format hagent`.
- Lint: `uv run ruff check hagent`.

### RTL/HDL Execution Environment
- Execution mode is determined by HAGENT_DOCKER:
  - **Docker mode (recommended)**: `export HAGENT_DOCKER=mascucsc/hagent-simplechisel:2025.11`
  - **Local mode (debug/dev)**: Don't set HAGENT_DOCKER
- Both modes can set paths BUT Local mode requires all paths set. Remember these paths are NOT hagent code but RTL/Verilog/HDL code.
  - `export HAGENT_REPO_DIR=/path/to/git/root`
  - `export HAGENT_BUILD_DIR=/path/to/build`
  - `export HAGENT_CACHE_DIR=/path/to/cache`
  - `export HAGENT_OUTPUT_DIR=/path/to/output`.

### Typical Directory Layout for Hagent users, not hagent iself
- Local (host paths under your control):
  - `HAGENT_REPO_DIR/`  source
  - `HAGENT_BUILD_DIR/` build outputs
  - `HAGENT_CACHE_DIR/` internals: `inou/`, `inou/logs/`, `build/`, `venv/`
- Docker (inside container):
  - `/code/workspace/repo/`  (from `HAGENT_REPO_DIR` if set)
  - `/code/workspace/build/` (from `HAGENT_BUILD_DIR` if set)
  - `/code/workspace/cache/` (auto-managed)

### Naming Conventions
- Files: `test_*.py` (unit tests), `cli_*.py` (CLI examples), `mcp_*.py` (MCP-capable that work as CLI too).
- Symbols: prefer snake_case for functions/variables; constants use UPPER_CASE; avoid CamelCase for non-classes.

### Path Management
- **Files outside hagent/inou must use Builder**, not direct `path_manager`/`runner` access.
- **File operations**: Use `builder.filesystem.read_file()` and `builder.filesystem.write_file()` instead of `run_cmd` with `cat`.
  - **Why**: Verilog files have special characters that cause issues with Python string formatting.
  - **Example**: `content = builder.filesystem.read_file("input.v")` not `run_cmd("cat input.v")`.
- **Path handling**: Builder and filesystem automatically handle Docker vs local mode path translation.
- Use `Path.resolve()` for internal paths; avoid relative paths.
- **Environment variables**: Never access `HAGENT_*` env vars directly with `os.environ`. Use `PathManager` accessors (`repo_dir`, `build_dir`, `cache_dir`, `tech_dir`). For tests, use `PathManager.configured()` context manager instead of setting env vars.

### Handy Snippets
- Verify env: `uv run python -c "import hagent; print('HAgent OK')"`.
- Run a step (same command in both modes):
  - `uv run hagent/step/trivial/trivial.py hagent/step/trivial/tests/input1.yaml -o out.yaml`.
- To setup a testing directory, create a directory and use `./scripts/setup_simplechisel_mcp.sh`

### Notes
- Set provider keys as needed (e.g., `OPENAI_API_KEY`, `FIREWORKS_AI_API_KEY`, etc.).
- For Perfetto traces and advanced docs, see README.md.
