
![HAgent logo](./docs/hagent_logo.png)

# HAgent

An AI hardware agent engine to support multiple components in chip design, such as code generation, verification, debugging, and tapeout.

HAgent stands for **Hardware Agent**, and it consists of a set of Python programs and support libraries that can be used to build agents resembling a compiler pipeline (pipe). A pipeline is built out of multiple compiler passes or steps (step). Each step is hermetic with respect to HAgent and uses YAML files as input and output to simplify debugging, testing, and ease of development.

## Quick Introduction

### Prerequisites

- **Python 3.11** or higher (required by the project)
- **[uv](https://docs.astral.sh/uv/getting-started/installation/)** for managing dependencies
- **Yosys**: Required for benchmarking and testing

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

If you run test/developtment
```
uv sync --extra dev
```

3. **Verify installation:**
```bash
uv run python -c "import hagent; print('HAgent installed successfully')"
```

#### Updating HAgent

If updating HAgent, you may need to update dependencies too:

```bash
git pull
uv lock
uv sync
```

#### Setting up API Keys

Each HAgent pipeline may use a different set of LLMs. We use litellm which supports most LLM providers. Set the required API keys (depends on the pipe that you use):

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

### Quick Start

After installation, run a simple test to verify everything works:

```bash
# Run basic tests
uv run pytest hagent/step/trivial/tests/

# Run a simple trivial step
mkdir -p tmp && cd tmp
uv run ../hagent/step/trivial/trivial.py ../hagent/step/trivial/tests/input1.yaml -o output.yaml
cat output.yaml
```

### Usage

The `HAgent` script provides several commands to help you generate multiple Ninja files for each step in chip design.

### Examples

Regression test use FIREWORKS for unit testing. As such, you need to set:
```
export FIREWORKS_AI_API_KEY=whatever_key_you_like_most
```

To run all the hagent tests:
```
uv run pytest
```

To avoid running all the test all the time, use the testmon:
```
uv run pytest --testmon
```

To verbose model:
```
uv run pytest -v
```

Samples with coverage information:
```
uv run pytest --cov=hagent
uv run pytest --cov=hagent/tool --cov-report=html
```

Run a subset of tests with coverage:
```
uv run pytest hagent/tool/ --cov=hagent/tool --cov-report=html
```

[![codecov](https://codecov.io/gh/masc-ucsc/hagent/graph/badge.svg?token=Hyj2VifE7j)](https://codecov.io/gh/masc-ucsc/hagent)

Check issues and format with ruff:
```
uv run ruff check hagent
uv run ruff format hagent
```

To generate the top level API specification:
```
uv run pydoc-markdown >spec.md
uv run pydoc-markdown -p hagent/tool --render-toc  >spec_tool.md
```

#### Trivial

Run the trivial test (hagent/step/tests/test_trivial.py)
```
uv run pytest -k "test_trivial"
```

Run a command line trivial.py pass with specific input:
```
mkdir tmp
cd tmp
uv run ../hagent/step/trivial/trivial.py ../hagent/step/trivial/tests/input1.yaml -ofoo.yaml
cat foo.yaml
description: |
  test1
  2nd line
```

Gather coverage information about your step (htmlcov):
```
uv run pytest --cov=hagent/step/trivial
uv run pytest --cov=hagent/step/trivial --cov-report=html
```

## Example of some command line test cases using HAgent

Agent to iterate over buggy Verilog to fix it until it complies correctly with slang:
```
cd tmp
uv run python3 ../hagent/tool/tests/test_react_compile_slang_simple.py ../hagent/tool/tests/buggy_verilog.v
```


## Structure

HAgent code is divided into four key components:

- **core**: Contains multiple Python files with shared functionality across steps.
  - When common functionality is used by several steps or tools, the logic is to push the code to core as a Python library.

- **step**: Has a subdirectory for each HAgent compiler step.
  - Each step has a stand-alone Python executable that matches the directory name.
  - Each step only reads and writes YAML files. There may also exist a log file that matches the output YAML name.
  - Each step should be hermetic, relying only on the input YAML files or calling tools.
  - Each step inherits from a core Step class and provides basic functionality.
  - **Examples**: `trivial`, `get_spec_io`

- **tool**: Has a subdirectory for each external tool.
  - Each tool requires a different Python library.
  - Each tool inherits from a core tool class and provides a common interface to check tool existence, calling, handling warnings and errors, and other common APIs shared across most tools.
  - **Examples**: `yosys`, `slang`, `chisel`

- **pipe**: Has a subdirectory for each end-user HAgent compiler.
  - Each pipe has a stand-alone Python executable that matches the directory name.
  - Each pipe combines several HAgent steps and is intended to be called by a user.
  - Each pipe can have multiple iterative sets of step calls.
  - Some differences between pipe and step:
    - A step is supposed to be simple and can have multiple running in parallel.
    - A pipe can have command line options and non-yaml inputs or outputs.

## Contributing

Contributions are welcome! Please open an issue or submit a pull request on GitHub.

If you want to work on this project, reach out Jose Renau. Most steps and pipes have a different
code owner.

When contributors submit feel free to add yourself to the CREDITS.txt file that each step, tool, core, pipe has.

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

HAgent is mostly build with AI tools as a way to learn insights/ideas for HAgent flow. A typical
class creation follows these steps:

### Create the API

Use the following prompt, to create a first API, and iterate with Human-in-the-loop until happy with it.

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

Use the following prompt, to create a simple use case example, and iterate with Human-in-the-loop until happy with it. If it requires to change the API, fix it.

"""
Assuming a HAgent class with the following API, create a simple use case example that demonstrates the class usage and has some simple testing. This is not a unit testing, just a sample to highligh the API usage.
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
HAgent requires Python 3.11+. Check your Python version:
```bash
uv run python --version
# Should show Python 3.11 or higher

# If using wrong version, uv will automatically download the correct one
uv python install 3.11
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

### Docker Issues

If you use OSX and colima, you may get a "docker-crediential-desktop not installed" issue. More likely, you need to delete the "credStore" entry from your config.json at `~/.docker/config.json`

Try in the command line that you can do: (Fix this before, or it will not work)
```bash
docker pull ubuntu:latest
docker run -it --rm ubuntu:latest
```

