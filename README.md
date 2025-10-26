
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

### Packages Installation

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

### Synthesis Installation

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
In ${HOME}/.ciel/ciel/sky130/versions:
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

### Updating HAgent

If updating HAgent, you may need to update dependencies too:

```bash
git pull
uv lock
uv sync
```

### Setting up API Keys

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

### Overriding LLM Models

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

## MCP Quick Start

Check the [examples/README.md](examples/README.md) for simple examples on how to interface HAgent as a MCP server.

## Pass Quick Start

After installation, run a simple test to verify everything works:

```bash
# Run basic tests
uv run pytest hagent/step/trivial/tests/

# Run a simple trivial step (Docker mode - recommended)
export HAGENT_DOCKER=mascucsc/hagent-simplechisel:2025.10
mkdir -p tmp && cd tmp
uv run ../hagent/step/trivial/trivial.py ../hagent/step/trivial/tests/input1.yaml -o output.yaml
cat output.yaml

# Alternative: Run in local mode (don't set HAGENT_DOCKER)
unset HAGENT_DOCKER
export HAGENT_REPO_DIR=$(pwd)
export HAGENT_BUILD_DIR=$(pwd)/build
export HAGENT_CACHE_DIR=$(pwd)/cache
# Same command works in both modes!
uv run ../hagent/step/trivial/trivial.py ../hagent/step/trivial/tests/input1.yaml -o output.yaml
```

For detailed examples and sample usage patterns, please see [AGENTS.md](AGENTS.md).

For developer, check the [docs/developer.md](docs/developer.md) intro guide.

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
