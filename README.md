
![HAgent logo](./docs/hagent_logo.png)

[![codecov](https://codecov.io/gh/masc-ucsc/hagent/graph/badge.svg?token=Hyj2VifE7j)](https://codecov.io/gh/masc-ucsc/hagent)
[![CI Status](https://github.com/masc-ucsc/hagent/actions/workflows/ubuntu.yml/badge.svg)](https://github.com/masc-ucsc/hagent/actions/workflows/ubuntu.yml)

An AI hardware agent engine that supports multiple components in chip design, including code generation, verification, debugging, and tapeout.

HAgent is an open-source infrastructure that brings the power of Large Language Models (LLMs) to hardware design. By integrating LLMs with chip design tools in a compiler-inspired pipeline, HAgent enables the creation of custom EDA flows. Its architecture leverages hermetic Docker-based steps and YAML interfaces to simplify development, debugging, and testing, making it accessible and extensible for researchers and practitioners.

## Quick Introduction

### Prerequisites

- **Python 3.13** or higher (required by the project)
- **[uv](https://docs.astral.sh/uv/getting-started/installation/)** for managing dependencies

#### Installing uv

On macOS and Linux:
```bash
curl -LsSf https://astral.sh/uv/install.sh | sh
```

On Windows:
```bash
powershell -ExecutionPolicy ByPass -c "irm https://astral.sh/uv/install.ps1 | iex"
```

Or using pip:
```bash
pip install uv
```

### Installation

1. **Clone the repository:**
```bash
git clone https://github.com/masc-ucsc/hagent.git
cd hagent
```

2. **Install dependencies with uv:**
```bash
uv sync
```

If you run tests/development (e.g., ruff needs dev extra packages):
```
uv sync --extra dev
```

3. **Verify installation:**
```bash
uv run python -c "import hagent; print('HAgent installed successfully')"
```

#### Synthesis Installation

The hagent dockers (https://github.com/masc-ucsc/docker-images) have the tools installed, but not
the large technology files. For the open source flow, the suggested setup is to use ceil:

```
python3 -m pip install --user --upgrade --no-cache-dir ciel

# List latest available PDKs for sky130
ciel ls-remote --pdk sky130 | head

# Download one like XXXX: (latest in ls-remote?)
ciel enable --pdk-family sky130 XXXX

# List installed. Example:
 ciel ls --pdk sky130
In /Users/renau/.ciel/ciel/sky130/versions:
└── e3262351fb1f5a3cc262ced1c76ebe3f2a5218fb (2025.10.15) (enabled)
```

Then ensure that you have *.lib files (no multi-corner in default HAgent OpenSTA settings):
```
ls ${HOME}/.ciel/ciel/sky130/versions/e3262351fb1f5a3cc262ced1c76ebe3f2a5218fb/sky130A/libs.ref/sky130_fd_sc_hd/lib/sky130_fd_sc_hd__tt_025C_1v80.lib
```

Set the HAGENT_TECH_DIR (same as the lib directory, not the file):
```
export HAGENT_TECH_DIR=${HOME}/.ciel/ciel/sky130/versions/e3262351fb1f5a3cc262ced1c76ebe3f2a5218fb/sky130A/libs.ref/sky130_fd_sc_hd/lib
```

#### Updating HAgent

If updating HAgent, you may need to update dependencies too:

```bash
git pull
uv lock
uv sync
```

#### Setting up API Keys

Each HAgent pipeline may use a different set of LLMs. We use LiteLLM which supports most LLM providers. Set the required API keys (depends on the pipeline you use):

```bash
# Required for most pipelines
export OPENAI_API_KEY=your_openai_key_here

# Optional - depending on which LLM you want to use
export SAMBANOVA_API_KEY=your_sambanova_key_here
export ANTHROPIC_API_KEY=your_anthropic_key_here
export FIREWORKS_AI_API_KEY=your_fireworks_key_here
```

**Note:** For testing, you can set dummy values for unused providers:
```bash
export FIREWORKS_AI_API_KEY=dummy_key_for_testing
```

#### Overriding LLM Models

You can override the LLM model specified in any configuration file by setting the `HAGENT_LLM_MODEL` environment variable:

```bash
# Override any configured model with a specific one
export HAGENT_LLM_MODEL=openai/gpt-5-mini

# This will use gpt-5-mini regardless of what's specified in YAML configs
uv run python hagent/step/trivial/trivial.py input.yaml -o output.yaml
```

This is useful for:
- Testing different models without modifying config files
- Using a preferred model across all HAgent steps
- Switching between different model providers quickly

### Quick Start

After installation, run a simple test to verify everything works:

```bash
# Run basic tests
uv run pytest hagent/step/trivial/tests/

# Run a simple trivial step (Docker mode - recommended)
export HAGENT_EXECUTION_MODE=docker
mkdir -p tmp && cd tmp
uv run ../hagent/step/trivial/trivial.py ../hagent/step/trivial/tests/input1.yaml -o output.yaml
cat output.yaml

# Alternative: Run in local mode
export HAGENT_EXECUTION_MODE=local
export HAGENT_REPO_DIR=$(pwd)
export HAGENT_BUILD_DIR=$(pwd)/build
export HAGENT_CACHE_DIR=$(pwd)/cache
# Same command works in both modes!
uv run ../hagent/step/trivial/trivial.py ../hagent/step/trivial/tests/input1.yaml -o output.yaml
```

### Usage

HAgent provides several commands to help you generate multiple Ninja files for each step in chip design.

### Examples

For detailed examples and sample usage patterns, please see [AGENTS.md](AGENTS.md).

Basic test commands:
```bash
# Set required API key for tests
export AWS_BEARER_TOKEN_BEDROCK=your_aws_bedrock_token_here  # for models starting with bedrock/*
export OPENAI_API_KEY=your_openai_key_here           # for models starting with openai/*

# Set execution mode (docker is recommended for full testing)
export HAGENT_EXECUTION_MODE=docker

# For local mode testing, also set:
# export HAGENT_EXECUTION_MODE=local
# export HAGENT_REPO_DIR=$(pwd)/tmp/local/repo
# export HAGENT_BUILD_DIR=$(pwd)/tmp/local/build
# export HAGENT_CACHE_DIR=$(pwd)/tmp/local/cache

# Optional: Set custom output directory for logs and test results
# export HAGENT_OUTPUT_DIR=/path/to/custom/output

# Run all tests
uv run pytest

# Run with testmon for faster iteration
uv run pytest --testmon
```

### File Naming Conventions

- `test_*.py`: Unit tests next to their components
- `cli_*.py`: CLI examples demonstrating API usage
- `mcp_*.py`: CLI-like examples that can also run as MCP servers

#### Execution Mode Configuration

HAgent supports two execution modes: **local** and **docker**. The mode is controlled by environment variables:

##### Local Mode
For local execution (debugging, single tasks), you must set all required environment variables:

```bash
# Required for local mode
export HAGENT_EXECUTION_MODE=local
export HAGENT_REPO_DIR=/path/to/your/git/repository     # Git repository root
export HAGENT_BUILD_DIR=/path/to/your/build/directory   # Build output directory
export HAGENT_CACHE_DIR=/path/to/your/cache/directory   # HAgent cache directory

# Optional: Set custom output directory for logs and test results
export HAGENT_OUTPUT_DIR=/path/to/your/output/directory  # Test/log output directory

# Run a step locally
uv run python hagent/step/trivial/trivial.py hagent/step/trivial/tests/input1.yaml -o output.yaml
```

##### Docker Mode (Recommended)
For Docker execution (production, complex builds), only set the execution mode:

Docker images are recommended to be derived from hagent-builer like hagent-simplechisel from https://github.com/masc-ucsc/docker-images

```bash
# Required for Docker mode
export HAGENT_EXECUTION_MODE=docker

# Optional: Mount host directories into container
export HAGENT_REPO_DIR=/path/to/your/git/repository     # Will be mounted to /code/workspace/repo
export HAGENT_BUILD_DIR=/path/to/your/build/directory   # Will be mounted to /code/workspace/build

# Optional: Set custom output directory for logs and test results
export HAGENT_OUTPUT_DIR=/path/to/your/output/directory  # Test/log output directory

# Run the same step in Docker - identical command!
uv run python hagent/step/trivial/trivial.py hagent/step/trivial/tests/input1.yaml -o output.yaml
```

**Key Benefits:**
- Same command works for both modes - only environment setup differs
- Docker mode automatically handles container setup and path mounting
- Local mode provides direct access for debugging and development

### Path Management

- **Pipes should use Builder**: All pipes should use the Builder pattern and access files through `runner.filesystem`
- **No direct path_manager/runner usage**: Pipes should not directly use `path_manager` or `runner` - use Builder instead
- **File operations**: Use `runner.filesystem.read_file()` and `runner.filesystem.write_file()` instead of `run_cmd` with `cat` for copying files, especially for Verilog files with special characters
- **Docker/Local mode**: Builder and filesystem automatically handle path translation between Docker (`/code/workspace/...`) and local modes
- Avoid hard-coded `/code/workspace/...` paths outside `hagent/inou/` or `hagent/mcp/`


## Structure

HAgent code is divided into four key components:

- **core**: Contains multiple Python files with shared functionality across steps
  - When common functionality is used by several steps or tools, the logic is to push the code to core as a Python library

- **step**: Has a subdirectory for each HAgent compiler step
  - Each step has a stand-alone Python executable that matches the directory name
  - Each step only reads and writes YAML files. There may also exist a log file that matches the output YAML name
  - Each step should be hermetic, relying only on the input YAML files or calling tools
  - Each step inherits from a core Step class and provides basic functionality
  - **Examples**: `trivial`, `get_spec_io`

- **tool**: Has a subdirectory for each external tool
  - Each tool requires a different Python library
  - Each tool inherits from a core tool class and provides a common interface to check tool existence, calling, handling warnings and errors, and other common APIs shared across most tools
  - **Examples**: `yosys`, `slang`, `chisel`

- **pipe**: Has a subdirectory for each end-user HAgent compiler
  - Each pipe has a stand-alone Python executable that matches the directory name
  - Each pipe combines several HAgent steps and is intended to be called by a user
  - Each pipe can have multiple iterative sets of step calls
  - Some differences between pipe and step:
    - A step is supposed to be simple and can have multiple running in parallel
    - A pipe can have command line options and non-YAML inputs or outputs

## Contributing

Contributions are welcome! Please open an issue or submit a pull request on GitHub.

Before any commit or pull request, `ruff` and `pytest` should pass:
```
uv run ruff format hagent
uv run ruff check hagent
uv run pytest -v
```

Or better, run `push_check.sh` before each github push.

### Maintenance Checks

- Run `bash scripts/code_check.sh` for heuristic maintenance hints (unused methods, env var/path conventions, etc.).
- Methods starting with `_` are considered internal; public-but-internal methods should generally be renamed with a leading `_`.

If you want to work on this project, reach out to Jose Renau. Most steps and pipes have a different code owner.

When contributors submit changes, feel free to add yourself to the CREDITS.txt file that each step, tool, core, and pipe has.

## License

We intend to keep HAgent perpetually open source and to use a liberal open source
[LICENSE](LICENSE) (BSD 3-Clause). As a contributor to the project, you agree that any
contributions be licensed under the terms of the BSD 3-Clause license shown at the root directory.
The BSD 3-Clause license boils down to this:

* You can freely distribute.
* You must retain the copyright notice if you redistribute.
* Binaries derived must reproduce the copyright notice (e.g. in an included readme file).
* You can not use contributor names to promote your derived products.
* There’s no warranty at all.

When you create a new code file, it should include "See LICENSE for details." in the first line of the file.

## Support

If you encounter any issues or have questions, please open an issue on GitHub.

## Build Flow

HAgent is mostly built with AI tools as a way to learn insights/ideas for HAgent flow. A typical class creation follows these steps:

### Create the API

Use the following prompt to create a first API, and iterate with human-in-the-loop until happy with it.

"""
Build a new Hagent tool API. This is a high level explanation for HAgent:
<include hagent/spec.md>

This class is a HAgent tool, as such this is a relevant information and example:
<include hagent/tool/spec.md>


Create a high level plan and Class API without code for a Hagent tool using the following characteristics:
<some explanation on what the tool should do>

A sample code that can be used as a guide for how to use the tool:
<some code snippets>
"""

### Create the Simple Example

Use the following prompt to create a simple use case example, and iterate with human-in-the-loop until happy with it. If it requires changing the API, fix it.

"""
Assuming a HAgent class with the following API, create a simple use case example that demonstrates the class usage and has some simple testing. This is not unit testing, just a sample to highlight the API usage.
<API>

As a reference, this is a simple test example for another HAgent tool
<include hagent/tool/test/test_chisel2v_simple.py -- or another closer example>
"""

### Generate the code

Use the API and the simple example, use the following prompt to implement the code.

"""
Build a Python implementation for the following class API:
<API>

This class is a HAgent tool, as such this is a relevant information and example:
<include hagent/tool/spec.md>

A sample usage for the class to implement is the following code:
<test_xxx_simple.py>

Create the class Python implementation, do not write unit test or explanation outside the class.
"""

## Troubleshooting

### Common uv Issues

#### "uv: command not found"
Make sure uv is installed and in your PATH:
```bash
# Check if uv is installed
which uv

# If not found, install uv
curl -LsSf https://astral.sh/uv/install.sh | sh
source ~/.bashrc  # or restart your terminal
```

#### "No such file or directory" when running scripts
Make sure you're in the correct directory and the script exists:
```bash
# Check current directory
pwd
ls hagent/step/trivial/

# Run from project root
cd /path/to/hagent
uv run python hagent/step/trivial/trivial.py --help
```

#### Python version issues
HAgent requires Python 3.13+. Check your Python version:
```bash
uv run python --version
# Should show Python 3.13 or higher

# If using wrong version, uv will automatically download the correct one
uv python install 3.13
```

#### API Key not working
Verify your API keys are set correctly:
```bash
echo $OPENAI_API_KEY
echo $FIREWORKS_AI_API_KEY

# Set in your shell profile (.bashrc, .zshrc, etc.)
export OPENAI_API_KEY=your_actual_key_here
```

#### Dependencies out of sync
If you encounter import errors:
```bash
# Clean and reinstall
uv sync --reinstall

# Or update lock file
uv lock --upgrade
uv sync
```

### Perfetto Stats

Each generated YAML file has a tracer entry. This can be extracted to create a Perfetto trace.
Put all the YAML files in a directory (inputs/outputs). For example:

```
uv run ./hagent/step/trivial/trivial.py ./hagent/step/trivial/tests/input1.yaml -o out.yaml
uv run ./hagent/step/trivial/trivial.py  out.yaml -o out2.yaml
```

Then run this to generate perfetto.json:
```
uv run ./scripts/build_perfetto_trace.py -i .
```

To see the results, upload the perfetto.json to https://ui.perfetto.dev/

### MCP Server Integration

- SystemVerilog syntax checker MCP server: `mcp/slang-mcp-server/`.
- Add to Claude Code: `claude mcp add slang-syntax-checker ~/projs/hagent/mcp/slang-mcp-server/run_server.sh`.

### Docker Issues

If you use macOS and Colima, you may get a "docker-credential-desktop not installed" issue. Most likely, you need to delete the "credStore" entry from your config.json at `~/.docker/config.json`

If you run Colima, you need to use virtiofs as mount point, and 32GB for XiangShan. This may require reinstalling Colima:
```
# brew install colima
rm -rf ~/.colima
colima start --mount-type virtiofs --vm-type=vz --vz-rosetta --memory 32
# brew services start colima
```

Try in the command line that you can do the following (fix Docker/Colima first, or it will not work):
```bash
docker pull ubuntu:latest
docker run -it --rm ubuntu:latest
```

For Docker/Colima, you need to have enough memory. In macOS Colima, the default is 2GB. This is fine for small runs, but not for things like XiangShan runs. Check that you have at least 32GB of memory.

```
 docker run --rm busybox cat /proc/meminfo | grep MemTotal
```

Sometimes you need to clean up leftover Docker containers, run ./cleanup.sh

#### Docker Container Management

HAgent uses a modernized container management system that automatically handles Docker setup and execution. Key features include:

**Automatic Container Setup:**
- Containers are automatically created and configured based on `HAGENT_EXECUTION_MODE`
- Host directories are mounted to standard container paths (`/code/workspace/repo`, `/code/workspace/build`)
- Environment variables are automatically set inside containers

**Path Translation:**
- Host paths are transparently translated to container paths
- File tracking works consistently across local and Docker modes
- No manual path configuration required

**Container Lifecycle:**
- Containers are automatically cleaned up after execution
- Resource management is handled transparently
- No manual Docker commands needed

**Example Docker Usage:**
```bash
# Set Docker mode
export HAGENT_EXECUTION_MODE=docker

# Optionally mount your project directory
export HAGENT_REPO_DIR=/path/to/your/project

# Run any HAgent step - Docker is handled automatically
uv run python hagent/step/trivial/trivial.py input.yaml -o output.yaml
```

The container management system eliminates the need for manual Docker commands while providing the benefits of isolated, reproducible execution environments.
