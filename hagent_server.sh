#!/bin/bash
export UV_PROJECT="/soe/czeng14/projects/hagent"
export HAGENT_ROOT="/soe/czeng14/projects/hagent"
export HAGENT_DOCKER="mascucsc/hagent-simplechisel:2025.11"
export HAGENT_REPO_DIR="/soe/czeng14/projects/hagent/repo"
export HAGENT_BUILD_DIR="/soe/czeng14/projects/hagent/build"
export HAGENT_CACHE_DIR="/soe/czeng14/projects/hagent/cache"
export HAGENT_OUTPUT_DIR="/soe/czeng14/projects/hagent/logs"
uv run python ${HAGENT_ROOT}/hagent/mcp/hagent-mcp-server.py "$@"
#uv run python ${HAGENT_ROOT}/hagent/mcp/mcp_build.py --help
