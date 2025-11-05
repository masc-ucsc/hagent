
![HAgent logo](./docs/hagent_logo.png)

[![codecov](https://codecov.io/gh/masc-ucsc/hagent/graph/badge.svg?token=Hyj2VifE7j)](https://codecov.io/gh/masc-ucsc/hagent)
[![CI Status](https://github.com/masc-ucsc/hagent/actions/workflows/ubuntu.yml/badge.svg)](https://github.com/masc-ucsc/hagent/actions/workflows/ubuntu.yml)

**HAgent** is an open-source AI hardware agent framework that integrates **Large Language Models (LLMs)** with hardware design tools for **code generation, verification, debugging, and synthesis**.  
By combining LLM reasoning with compiler-style workflows, HAgent enables flexible and reproducible **EDA pipelines** for chip design research and automation.

Its modular architecture uses **Docker-based builds** and **YAML-driven APIs** to simplify setup, ensure reproducibility, and streamline collaboration between engineers and researchers.


## Installation and Setup

Before using HAgent, ensure that you have **Docker** installed on your system.

For complete installation and setup — including Python dependencies, API keys, and synthesis tools — please see:  
👉 [docs/install.md](docs/install.md)

If you encounter any issues with Docker, see:  
👉 [docs/docker_issues.md](docs/docker_issues.md)


## MCP Quick Start

Check the [examples/README.md](examples/README.md) for simple examples on how to interface HAgent as a MCP server.

## Pass Quick Start

After installation, run a simple test to verify everything works:

```bash
# Run basic tests
uv run pytest -n auto --forked hagent/step/trivial/tests/

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
