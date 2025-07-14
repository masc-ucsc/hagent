# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Overview

HAgent is an AI hardware agent engine for chip design tasks including code generation, verification, debugging, and tapeout. It's built as a modular pipeline system using Python with YAML-based inputs/outputs for hermetic steps.

## Development Commands

### Setup and Installation
```bash
# Install dependencies (use for most development)
uv sync --extra dev

# Update dependencies after pulling changes
uv lock && uv sync

# Verify installation
uv run python -c "import hagent; print('HAgent installed successfully')"
```

### Testing
```bash
# Run all tests
uv run pytest

# Run tests with coverage
uv run pytest --cov=hagent --cov-report=html

# Run incremental tests (faster for development)
uv run pytest --testmon

# Run specific test directory
uv run pytest hagent/step/trivial/tests/

# Verbose test output
uv run pytest -v
```

### Code Quality
```bash
# Check code issues
uv run ruff check hagent

# Format code
uv run ruff format hagent
```

### API Documentation
```bash
# Generate top-level API spec
uv run pydoc-markdown >spec.md

# Generate tool-specific documentation
uv run pydoc-markdown -p hagent/tool --render-toc >spec_tool.md
```

## Architecture

### Core Components

1. **Steps** (`hagent/step/`): Hermetic operations that read/write YAML files
   - Each step has a standalone Python executable matching the directory name
   - Inherit from core `Step` class
   - Examples: `trivial`, `get_spec_io`

2. **Tools** (`hagent/tool/`): External tool integrations
   - Each tool requires different Python libraries
   - Inherit from core `Tool` class with standard setup/error handling
   - Examples: `yosys`, `slang`, `chisel`

3. **Pipes** (`hagent/pipe/`): End-user pipelines combining steps
   - Standalone executables for complete workflows
   - Can have command line options and non-YAML inputs/outputs

4. **Core** (`hagent/core/`): Shared functionality across components

### Key Design Patterns

- **YAML-Centric**: All steps use YAML for input/output, making debugging straightforward
- **Hermetic Steps**: Each step is isolated and can run independently
- **Tool Abstraction**: Consistent interface across external tools with error handling
- **AI Integration**: Heavy use of LLMs via litellm for hardware design tasks

## Required Environment Variables

```bash
# Required for most pipelines
export OPENAI_API_KEY=your_openai_key_here

# Optional depending on LLM usage
export SAMBANOVA_API_KEY=your_sambanova_key_here
export ANTHROPIC_API_KEY=your_anthropic_key_here
export FIREWORKS_AI_API_KEY=your_fireworks_key_here

# For testing (can use dummy values)
export FIREWORKS_AI_API_KEY=dummy_key_for_testing
```

## Example Usage

### Running Individual Steps
```bash
# Run trivial step
mkdir tmp && cd tmp
uv run ../hagent/step/trivial/trivial.py ../hagent/step/trivial/tests/input1.yaml -o output.yaml
```

### Running Tools
```bash
# React agent for fixing buggy Verilog
cd tmp
uv run python3 ../hagent/tool/tests/test_react_compile_slang_simple.py ../hagent/tool/tests/buggy_verilog.v
```

## Special Features

### MCP Server Integration
The project includes a SystemVerilog syntax checker MCP server:
- Location: `mcp/slang-mcp-server/`
- Add to Claude Code: `claude mcp add slang-syntax-checker ~/projs/hagent/mcp/slang-mcp-server/run_server.sh`

### Performance Monitoring
Each run generates traceable performance data via Perfetto:
```bash
# Generate perfetto trace from YAML files
uv run ./scripts/build_perfetto_trace.py -i .

# Upload perfetto.json to https://ui.perfetto.dev/ for visualization
```

## Dependencies

- **Python**: >=3.11,<4.0 (managed by UV)
- **Package Manager**: UV (modern Python package manager)
- **Key Libraries**: litellm, pyslang, pyyaml, pytest, ruff
- **External Tools**: Yosys (for benchmarking), Docker (optional)

## Development Workflow

1. Make changes to relevant step/tool/pipe
2. Run tests: `uv run pytest --testmon`
3. Check code quality: `uv run ruff check hagent && uv run ruff format hagent`
4. Run coverage if needed: `uv run pytest --cov=hagent --cov-report=html`

## File Organization Notes

- Test files are distributed throughout the codebase alongside their components
- Each component has its own `tests/` subdirectory
- Configuration files use modern Python tooling (pyproject.toml with UV/Ruff)
- Documentation focuses on hardware design workflows and AI integration