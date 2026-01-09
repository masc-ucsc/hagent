
## Debug Mode

HAgent provides a debug mode that enables detailed logging and verbose output for troubleshooting and development.

### Enabling Debug Mode

**MCP Server:**
```bash
# Run MCP server with debug logging
uv run python hagent/mcp/hagent-mcp-server.py --debug
```

**CLI Tools:**
```bash
# Run mcp_build.py with debug mode
uv run python hagent/mcp/mcp_build.py --debug --api compile --name gcd
```

### What Debug Mode Does

When debug mode is enabled:

1. **Logging Level**: Changes from INFO to DEBUG, showing all debug messages
2. **Command Preview**: Logs the actual command that will be executed (with `[DEBUG]` prefix)
3. **Verbose Output**: Builder runs with `quiet=False` for detailed execution output
4. **Environment Variable**: Sets `HAGENT_MCP_DEBUG=1` so all tools can detect debug mode
5. **Log Files**: All debug output goes to `logs/hagent_mcp_server.log`

### Debug Output Examples

When debug mode is active, you'll see messages like:
```
[DEBUG] Getting command for debugging...
[DEBUG] Command to execute:
docker run --rm -v /path/to/repo:/code/workspace/repo ... compile_command
[DEBUG] Retrying with profile query as title_query
```

### Automatic Debug Propagation

When the MCP server runs with `--debug`, all tools called through MCP automatically inherit debug mode - no need to pass it explicitly. The `HAGENT_MCP_DEBUG=1` environment variable ensures consistent debug behavior across all components.

### Log File Locations

- `logs/hagent_mcp_server.log` - Main server and tool debug messages
- `logs/hagent_mcp_server_io.log` - Raw MCP protocol I/O (debug mode only)
- `logs/hagent_mcp_hagent_build.log` - Transaction logs for build commands

## Execution Mode Configuration

HAgent supports two execution modes: **local** and **docker**. The mode is controlled by environment variables:

### Local Mode
For local execution (debugging, single tasks), you must set all required environment variables:

```bash
# Required for local mode (don't set HAGENT_DOCKER)
unset HAGENT_DOCKER
export HAGENT_REPO_DIR=/path/to/your/git/repository     # Git repository root
export HAGENT_BUILD_DIR=/path/to/your/build/directory   # Build output directory
export HAGENT_CACHE_DIR=/path/to/your/cache/directory   # HAgent cache directory

# Optional: Set custom output directory for logs and test results
export HAGENT_OUTPUT_DIR=/path/to/your/output/directory  # Test/log output directory

# Run a step locally
uv run python hagent/step/trivial/trivial.py hagent/step/trivial/tests/input1.yaml -o output.yaml
```

### Docker Mode (Recommended)
For Docker execution (production, complex builds), set HAGENT_DOCKER to your docker image:

Docker images are recommended to be derived from hagent-builer like hagent-simplechisel from https://github.com/masc-ucsc/docker-images

```bash
# Required for Docker mode - set HAGENT_DOCKER to activate docker mode
export HAGENT_DOCKER=mascucsc/hagent-simplechisel:2026.01

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

## Path Management

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

Or better, run `./scripts/push_check.sh` before each github push.

## Maintenance Checks

- Run `bash scripts/code_check.sh` for heuristic maintenance hints (unused methods, env var/path conventions, etc.).
- Methods starting with `_` are considered internal; public-but-internal methods should generally be renamed with a leading `_`.

If you want to work on this project, reach out to Jose Renau. Most steps and pipes have a different code owner.

When contributors submit changes, feel free to add yourself to the CREDITS.txt file that each step, tool, core, and pipe has.


## Support

If you encounter any issues or have questions, please open an issue on GitHub.


## Troubleshooting


### Dependencies out of sync
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

### Docker Issues

If you use macOS and Colima, you may get a "docker-credential-desktop not installed" issue. Most likely, you need to delete the "credStore" entry from your config.json at `~/.docker/config.json`

If you run Colima, you need to use virtiofs as mount point, and 32GB for XiangShan. This may require reinstalling Colima:
```
# brew install colima lima
colima stop -f
rm -rf ~/.colima
colima start --mount-type virtiofs --vm-type=vz --memory 32
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

Sometimes you need to clean up leftover Docker containers, run ./scripts/cleanup.sh

### Docker Container Management

HAgent uses a modernized container management system that automatically handles Docker setup and execution. Key features include:

**Automatic Container Setup:**
- Containers are automatically created and configured when `HAGENT_DOCKER` is set
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
# Set Docker mode by setting HAGENT_DOCKER
export HAGENT_DOCKER=mascucsc/hagent-simplechisel:2026.01

# Optionally mount your project directory
export HAGENT_REPO_DIR=/path/to/your/project

# Run any HAgent step - Docker is handled automatically
uv run python hagent/step/trivial/trivial.py input.yaml -o output.yaml
```

### Manual Docker Debugging with `scripts/docker_args.sh`

For debugging and experimentation, you can manually start a container using the same arguments that `Runner.py` would use. The `scripts/docker_args.sh` script reads the `HAGENT_*` environment variables and prints a `docker run` command with the correct mounts:

```bash
export HAGENT_DOCKER=mascucsc/hagent-simplechisel:2026.01
export HAGENT_REPO_DIR=/path/to/your/git/repository
export HAGENT_BUILD_DIR=/path/to/your/build/directory
export HAGENT_CACHE_DIR=/path/to/your/cache/directory

# Preview the docker command that matches Runner.py
./scripts/docker_args.sh

# Open an interactive shell in the container with the same mounts
$(./scripts/docker_args.sh) /bin/bash
```

This is useful to quickly inspect the container environment, verify mounts, or reproduce issues interactively while using the exact same Docker layout as normal HAgent runs.

The container management system eliminates the need for manual Docker commands while providing the benefits of isolated, reproducible execution environments.
