# Installation and Setup

This guide covers all the steps needed to install and configure HAgent.

## Prerequisites

- **Python 3.13** or higher (required by the project)
- **[uv](https://docs.astral.sh/uv/getting-started/installation/)** for managing dependencies

## Installing uv

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

## Packages Installation

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

## Synthesis Installation

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

## Updating HAgent

If updating HAgent, you may need to update dependencies too:

```bash
git pull
uv lock
uv sync
```

## Setting up API Keys

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

## Overriding LLM Models

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
