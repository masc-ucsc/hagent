
## Hagent Overview

An AI hardware agent engine to support multiple components in chip design, such as code generation, verification, debugging, and tapeout.

HAgent stands for **Hardware Agent**, and it consists of a set of Python programs and support libraries that can be used to build agents resembling a compiler pipeline (pipe). A pipeline is built out of multiple compiler passes or steps (step). Each step is hermetic with respect to HAgent and uses YAML files as input and output to simplify debugging, testing, and ease of development.

### Structure

HAgent code is divided into four key components. Each with a separate directory:

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

Each Python step or tool should have its own unit tests that run when using `poetry run pytest`

