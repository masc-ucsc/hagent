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

### API Keys
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

### Execution Mode Configuration
```bash
# REQUIRED: Choose execution mode
export HAGENT_EXECUTION_MODE=docker    # Recommended for production
# OR
export HAGENT_EXECUTION_MODE=local     # For debugging/development

# For LOCAL mode - ALL required:
export HAGENT_REPO_DIR=/path/to/git/repository      # Must be a git repository root
export HAGENT_BUILD_DIR=/path/to/build/directory    # Build output directory
export HAGENT_CACHE_DIR=/path/to/cache/directory    # HAgent internal cache

# For DOCKER mode - OPTIONAL (will be mounted if provided):
export HAGENT_REPO_DIR=/path/to/git/repository      # Mounted to /code/workspace/repo
export HAGENT_BUILD_DIR=/path/to/build/directory    # Mounted to /code/workspace/build
# HAGENT_CACHE_DIR is automatically managed in Docker mode

# For BOTH modes - OPTIONAL:
export HAGENT_OUTPUT_DIR=/path/to/output/directory   # Custom logs/test results output directory
```

## Example Usage

### Running Individual Steps

#### Docker Mode (Recommended)
```bash
# Set execution mode
export HAGENT_EXECUTION_MODE=docker

# Run trivial step - Docker handles everything automatically
mkdir tmp && cd tmp
uv run ../hagent/step/trivial/trivial.py ../hagent/step/trivial/tests/input1.yaml -o output.yaml

# With optional host directory mounting
export HAGENT_REPO_DIR=/path/to/your/project
uv run ../hagent/step/trivial/trivial.py ../hagent/step/trivial/tests/input1.yaml -o output.yaml
```

#### Local Mode (Development/Debugging)
```bash
# Set execution mode and required paths
export HAGENT_EXECUTION_MODE=local
export HAGENT_REPO_DIR=$(pwd)/..                    # Git repository root
export HAGENT_BUILD_DIR=$(pwd)/build                # Build directory
export HAGENT_CACHE_DIR=$(pwd)/cache                # Cache directory

# Optional: Set custom output directory
export HAGENT_OUTPUT_DIR=$(pwd)/test_output         # Custom output directory

# Same command as Docker mode!
mkdir tmp && cd tmp
uv run ../hagent/step/trivial/trivial.py ../hagent/step/trivial/tests/input1.yaml -o output.yaml
```

### Running Tools
```bash
# React agent for fixing buggy Verilog (works in both modes)
export HAGENT_EXECUTION_MODE=docker  # or local with full path setup
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

- **Python**: >=3.13,<4.0 (managed by UV)
- **Package Manager**: UV (modern Python package manager)
- **Key Libraries**: litellm, pyslang, pyyaml, pytest, ruff, docker
- **External Tools**: Yosys (for benchmarking), Docker (recommended for production)
- **Infrastructure**: Git (required for file tracking in both modes)

## Development Workflow

1. Make changes to relevant step/tool/pipe
2. Run tests: `uv run pytest --testmon`
3. **ALWAYS run code quality checks after making changes**: `uv run ruff check hagent && uv run ruff format hagent`
4. Run coverage if needed: `uv run pytest --cov=hagent --cov-report=html`

### Code Quality Requirements

**IMPORTANT**: After modifying any code in this repository, you **must** run both ruff commands:

```bash
# Check for code issues and violations
uv run ruff check hagent

# Auto-format code to maintain consistent style
uv run ruff format hagent
```

These commands ensure code quality, consistency, and compliance with the project's style guidelines. Make this a standard part of your development process - **never commit code changes without running ruff check and format first**.

## File Organization Notes

- Test files are distributed throughout the codebase alongside their components
- Each component has its own `tests/` subdirectory
- Configuration files use modern Python tooling (pyproject.toml with UV/Ruff)
- Documentation focuses on hardware design workflows and AI integration

## Path Management and File Organization

HAgent uses a modernized path management system with structured directories based on execution mode:

### Directory Structure

```bash
# In LOCAL mode - user-controlled paths
HAGENT_REPO_DIR/     # Git repository (source code)
HAGENT_BUILD_DIR/    # Build outputs (generated Verilog, logs)
HAGENT_CACHE_DIR/    # HAgent internals (YAML files, caches)
  ├── inou/          # Step configurations, logs
  ├── inou/logs/     # Execution logs
  ├── build/         # Build cache
  └── venv/          # Python virtual environment

# In DOCKER mode - standardized container paths
/code/workspace/repo/   # Mounted from HAGENT_REPO_DIR (if provided)
/code/workspace/build/  # Mounted from HAGENT_BUILD_DIR (if provided)
/code/workspace/cache/  # HAgent internals (auto-managed)
```

### For Python Components

Use the path manager utilities for consistent file handling:

```python
from hagent.inou.path_manager import PathManager
from hagent.inou.output_manager import get_output_dir, get_output_path

# Initialize path manager (respects HAGENT_EXECUTION_MODE)
path_manager = PathManager()

# Access structured directories
repo_dir = path_manager.repo_dir      # Source code location
build_dir = path_manager.build_dir    # Build outputs
cache_dir = path_manager.cache_dir    # HAgent internals

# Cache subdirectories
log_dir = path_manager.get_log_dir()              # inou/logs/
config_dir = path_manager.get_cache_path('step.yaml')  # inou/step.yaml

# Output files (logs, test results) - respects HAGENT_OUTPUT_DIR
output_dir = get_output_dir()                     # Uses HAGENT_OUTPUT_DIR or cache/inou/logs/
log_file = get_output_path('test_results.log')   # Full path for output files
```

### Key Benefits

- **Mode Transparency**: Same code works in local and Docker modes
- **Automatic Setup**: Directories created automatically as needed  
- **Git Integration**: File tracking works consistently across modes
- **Structured Organization**: Clear separation between source, build, and cache files
- **Container Compatibility**: Docker mounts and paths handled automatically

This system eliminates manual path configuration while providing clean organization and cross-mode compatibility.

### Path Resolution Convention

**IMPORTANT**: HAgent internally always operates with fully resolved absolute paths that handle symlinks properly. When developing new components or modifying existing path-handling code:

- **Always use `Path(...).resolve()`** when converting paths to strings for storage or comparison
- **Never use relative paths** for internal operations - convert to absolute resolved paths immediately
- **Follow existing patterns** in the codebase that use `.resolve()` consistently (see PathManager, file_tracker, executor modules)

Example pattern:
```python
# CORRECT: Use resolve() to get fully resolved absolute path
output_dir = Path(user_input_dir).resolve()
return str(output_dir)

# INCORRECT: Raw path without resolution
output_dir = user_input_dir
return output_dir  # May contain unresolved symlinks or be relative
```

This ensures consistent behavior across different environments, proper symlink handling, and eliminates path comparison issues between relative and absolute paths.

