
# HAgent

An AI hardware agent engine to support multiple components in chip design, such as code generation, verification, debugging, and tapeout.

HAgent stands for **Hardware Agent**, and it consists of a set of Python programs and support libraries that can be used to build agents resembling a compiler pipeline (pipe). A pipeline is built out of multiple compiler passes or steps (step). Each step is hermetic with respect to HAgent and uses YAML files as input and output to simplify debugging, testing, and ease of development.

## Quick Introduction

### Prerequisites

- **Python 3.8** or higher
- **[Poetry](https://python-poetry.org/docs/#installation)** for managing dependencies
- **Yosys**: Required for benchmarking and testing

### Installation

Install with Python Poetry:

```bash
poetry install
```

If updating HAgent, you may need to update Poetry dependencies too:

```bash
poetry lock
poetry install
```

Each HAgent pipeline may use a different set of LLMs. Overall, we use litellm which support most LLM providers. Set the required API keys (depends on the pipe that you use):

```bash
export OPENAI_API_KEY=.....
export SAMBANOVA_API_KEY=....
```

### Usage

The `HAgent` script provides several commands to help you generate multiple Ninja files for each step in chip design.

### Examples

To run all the hagent tests:
```
poetry run pytest
```

Dumping coverage information:
```
poetry run pytest --cov=hagent
```

#### Trivial

Run the trivial test (hagent/step/tests/test_trivial.py)
```
poetry run pytest -k "test_trivial"
```

Run a command line trivial.py pass with specific input:
```
mkdir tmp
cd tmp
poetry run ../hagent/step/trivial/trivial.py ../hagent/step/trivial/tests/input1.yaml -ofoo.yaml
cat foo.yaml
description: |
  test1
  2nd line
```

Gather coverage information about your step (htmlcov):
```
poetry run pytest --cov=hagent/step/trivial
poetry run pytest --cov=hagent/step/trivial --cov-report=html
```

## Structure

HAgent code is divided into four key components:

- **core**: Contains multiple Python files with shared functionality across steps.
  - When common functionality is used by several steps or tools, the logic is to push the code to core as a Python library.

- **step**: Has a subdirectory for each HAgent compiler step.
  - Each step has a stand-alone Python executable that matches the directory name.
  - Each step only reads and writes YAML files.
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

