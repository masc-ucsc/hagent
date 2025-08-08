# Intro

This file provides guidance to AI Agents like Claude Code (claude.ai/code) when working with code in this repository.

## AI Agent Guidelines

When working with this repository, please follow these important conventions:

### Testing Commands
- **ALWAYS** use `uv run pytest` for running tests, never `python -m pytest`
- This ensures proper dependency management and virtual environment isolation

### File Naming Conventions
- `test_*.py` files: Unit tests for testing individual components and functions
- `cli_*.py` files: Examples demonstrating API usage and command-line interfaces
- Both types of files may be executable, but serve different purposes in the codebase

## Overview

HAgent is an AI hardware agent engine for chip design tasks including code generation, verification, debugging, and tapeout. It's built as a modular pipeline system using Python with YAML-based inputs/outputs for hermetic steps.

## Development Commands

### Setup and Installation
```bash
# Install dependencies (dev tools + testmon)
uv sync --extra dev -g dev

# Alternative: simpler setup for basic development
uv sync --extra dev

# Update dependencies after pulling changes
uv lock && uv sync --extra dev

# Verify installation
uv run python -c "import hagent; print('HAgent installed successfully')"
```

### Testing
```bash
# Run all tests
uv run pytest

# Run fast tests only (explicit)
uv run pytest -m "not slow"

# Run slow tests only (for regression testing)
# NOTE: Regression tests currently require AWS Bedrock access via AWS_BEARER_TOKEN_BEDROCK
uv run pytest -m slow

# Run all tests including slow ones
uv run pytest -m ""

# Run tests with coverage
uv run pytest --cov=hagent --cov-report=html

# Run subset of tests with coverage
uv run pytest hagent/tool/ --cov=hagent/tool --cov-report=html

# Upload coverage to codecov manually
uv run pytest --cov --cov-branch --cov-report=xml
curl -Os https://cli.codecov.io/latest/macos/codecov  # replace macos for linux if needed
./codecov --verbose upload-process -f ./coverage.xml

# Run incremental tests (faster for development)
uv run pytest --testmon

# Run specific test directory
uv run pytest hagent/step/trivial/tests/

# Run specific test pattern
uv run pytest -k "test_trivial"

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
# Generate comprehensive API documentation (configured in pyproject.toml)
uv run pydoc-markdown

# The above command generates spec.md with module-level documentation
# For detailed class and method documentation, use Python's built-in help:
uv run python -c "from hagent.core.step import Step; help(Step)"
uv run python -c "from hagent.core.llm_wrap import LLM_wrap; help(LLM_wrap)"
uv run python -c "from hagent.tool.tool import Tool; help(Tool)"
```

## Architecture

### Core Components

1. **Steps** (`hagent/step/`): Hermetic operations that read/write YAML files
   - Each step has a standalone Python executable matching the directory name
   - Inherit from core `Step` class
   - Examples: `trivial`, `generate_diff`

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
# Required for most pipelines (LLM_wrap validates based on model prefix)
export OPENAI_API_KEY=your_openai_key_here           # for models starting with openai/*

# Optional: other providers depending on usage
export ANTHROPIC_API_KEY=your_anthropic_key_here     # for models starting with anthropic/*
export FIREWORKS_AI_API_KEY=your_fireworks_key_here  # for models starting with fireworks*
export SAMBANOVA_API_KEY=your_sambanova_key_here
export AWS_BEARER_TOKEN_BEDROCK=your_aws_bedrock_token_here  # for models starting with bedrock/*

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
uv run python ../hagent/tool/tests/test_react_compile_slang_simple.py ../hagent/tool/tests/buggy_verilog.v
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

## Output File Management

When developing HAgent components that create output files (reports, logs, generated code, trace files, etc.), **always use the output directory utilities** to maintain clean project organization:

### For Python Components

Import and use the output manager utilities:

```python
from hagent.core.output_manager import get_output_dir, get_output_path

# For creating files in the output directory
output_file = get_output_path('my_report.txt')
with open(output_file, 'w') as f:
    f.write('Generated content')

# For creating subdirectories in the output directory
import tempfile
work_dir = tempfile.mkdtemp(dir=get_output_dir(), prefix='my_component_')
```

### Key Guidelines

- **DO**: Use `get_output_path()` when creating any output files
- **DO**: Use `get_output_dir()` when creating temporary directories
- **DO**: Pass only paths under the output directory (filenames or subpaths like `logs/file.log`) to `get_output_path()`
- **DON'T**: Write files directly to the current working directory
- **DON'T**: Hard-code paths like `./output/` in your code
- **DON'T**: Pass absolute paths to `get_output_path()` (will cause program to exit with error)
- **DON'T**: Use parent directory traversal like `../...` (keeps outputs contained)

### Examples from Codebase

```python
# Equivalence checking (equiv_check.py)
work_dir = tempfile.mkdtemp(dir=get_output_dir(), prefix='equiv_check_')

# Trace generation (tracer.py)
filename = get_output_path('trace.json')

# Test output files (test_replicate_code.py)
out_file = get_output_path('test_results.yaml')
```

### API Validation

`get_output_path()` validates its input and will exit with an error if called with absolute paths. Avoid parent-directory traversal paths to ensure outputs stay contained:

```python
# ✅ CORRECT usage
get_output_path('report.txt')           # filename only
get_output_path('logs/debug.log')       # relative path

# ❌ INCORRECT usage (will exit with detailed error message)
get_output_path('/tmp/report.txt')      # absolute path
get_output_path('/Users/name/file.txt') # absolute path  
get_output_path('~/report.txt')         # home directory
get_output_path('C:\\Windows\\file.txt') # Windows absolute path
# ❌ INCORRECT usage (path traversal; not allowed)
get_output_path('../shared/data.json')  # parent directory traversal
```

This validation prevents accidental misuse and ensures consistent output file organization.

### Environment Variable Support

The output directory respects the `HAGENT_OUTPUT` environment variable:
- Default: `output/`
- Custom: Set `HAGENT_OUTPUT=/path/to/custom/dir`
- Auto-created: Directory is created automatically if it doesn't exist

This pattern keeps the project directory clean and gives users control over where generated files are stored.

