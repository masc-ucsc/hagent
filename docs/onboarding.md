This guide explains how to set up and run the __HAgent MCP server__ locally for development and debugging, and how to connect AI tools such as __Gemini__ to interact with it.

# Overview
We provide a unified setup script, [`scripts/setup_mcp.sh`](https://github.com/masc-ucsc/hagent/blob/main/scripts/setup_mcp.sh), that automates environment initialization for different hardware cores used with HAgent MCP server. By specifying a desired core as an argument, the script will create the corresponding directory structure and genrate all required files. The available cores can be found in the [MASC group’s docker-images repo](https://github.com/masc-ucsc/docker-images).

# What the Setup Script Does
The setup script prepares a ready-to-run environment for a specific core’s MCP server within the `HAgent` framework. Its main steps are:
1. __Launch the Core’s Docker Container__
The script first spins up the corresponding Docker image for the selected core. These images come preconfigured with build tools (e.g., `riscv-gnu-toolchain`) and dependencies.

2. __Copy Key Directories from the Container__
Once the container is running, the script copies several directories from the container back to the host:
- `repo/`: source repository
- `build/`: build artifacts
- `cache/`: cached toolchains and intermediate data

This allows us to reuse the container’s self-contained environment __locally__ without having Gemini directly interact with Docker.
__Note__: Gemini currently has no awareness of Docker containers. To avoid introducing extra complexity (e.g., running another MCP server inside Docker), we mirror files locally and use [volume mounting](https://github.com/masc-ucsc/hagent/blob/d4709b03c1cc037232628359d90dcf82922319cb/hagent/inou/container_manager.py#L555) between the host and the container at runtime.

3. __Set Up Directory Mounts__
The HAgent server mounts local directories into the container so that commands executed within the container are reflected on our host machine. For example, if Gemini runs `make` inside `/code/workspace/repo`, the build occurs inside the container, but the generated files appear locally as well.

⚠️ __Important__:
Do not run Gemini from the `HAgent` root directory — it will modify files in place.
Always work from a project-specific directory (e.g., `/tmp/potato`).

4. __Generate a Runnable MCP Server Script__
Finally, the setup script creates a shell script (e.g., `hagent_server.sh`) that launches the `HAgent` MCP server.
This script can be:
- Executed manually to test `HAgent`
- Registered with Gemini for automated use

# Integrating with Gemini
We use [FastMCP](https://github.com/jlowin/fastmcp) to build and integrate MCP servers/clients. `FastMCP` supports multiple communication modes:
- HTTP service
- Server-Sent Events (SSE)
- Local `stdio` (used by `HAgent`)

Since `HAgent` runs via `stdio`, you must register it manually with Gemini:
```sh
gemini mcp add hagent ./hagent_server.sh
```
This command needs to be run once per new working directory, since Gemini stores configuration locally.

5. __Running Gemini with HAgent__
Once the MCP server is registered, you can start Gemini as usual:
```sh
gemini
```
When launched, Gemini will:
1. Search for an `hagent.yaml` file (typically under `repo/`)
2. Load the configured profile
3. Execute commands via the `HAgent` MCP server using the appropriate schema

This allows seamless AI-driven interaction with your hardware core environment through HAgent.

# Example
An example setup walkthrough can be found in [`examples/README.md`](https://github.com/masc-ucsc/hagent/blob/main/examples/README.md).
