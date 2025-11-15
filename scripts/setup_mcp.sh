#!/bin/bash
#
# Generic setup script for an MCP server
# Usage: ./setup_mcp.sh <project> [target_dir]
# Example: ./setup_mcp.sh soomrv ~/tmp/potato
#
# Creates the necessary directory structure and configuration files
# for running the HAgent MCP server with <project>
#
# Optimization: Uses cached template in .cache/setup_<project>_mcp for faster setup

set -e
PROJECT_NAME="${1:-}"
BASE_DIR=${2:-$(pwd)}
if [[ -z "$PROJECT_NAME" ]]; then
  echo "Usage: $0 <project> [target_dir]" >&2
  echo "Available projects: cva6, simplechisel, soomrv, verilog-adder, xiangshan" >&2
  exit 1
fi

# Normalize project name to lowercase for portability (macOS bash lacks ${var,,})
PROJECT_NAME=$(printf '%s' "$PROJECT_NAME" | tr '[:upper:]' '[:lower:]')

case "$PROJECT_NAME" in
cva6)
  DOCKER_IMAGE="mascucsc/hagent-cva6:2025.10"
  GIT_URL="https://github.com/openhwgroup/cva6.git"
  ;;
simplechisel)
  DOCKER_IMAGE="mascucsc/hagent-simplechisel:2025.10"
  GIT_URL="https://github.com/masc-ucsc/simplechisel.git"
  ;;
soomrv)
  DOCKER_IMAGE="mascucsc/hagent-soomrv:2025.11"
  GIT_URL="https://github.com/mathis-s/SoomRV.git"
  ;;
verilog-adder)
  DOCKER_IMAGE="mascucsc/hagent-builder:2025.10"
  GIT_URL=""
  EXAMPLE_SOURCE_DIR="${HAGENT_ROOT}/examples/verilog_adder"
  ;;
xiangshan)
  DOCKER_IMAGE="mascucsc/hagent-xiangshan:2025.10"
  GIT_URL="https://github.com/OpenXiangShan/XiangShan.git"
  ;;
*)
  # Check if it's a directory in examples or a direct path
  if [[ -d "${HAGENT_ROOT}/examples/${PROJECT_NAME}" ]]; then
    EXAMPLE_SOURCE_DIR="${HAGENT_ROOT}/examples/${PROJECT_NAME}"
    DOCKER_IMAGE="mascucsc/hagent-builder:2025.10"
    GIT_URL=""
  elif [[ -d "$PROJECT_NAME" ]]; then
    EXAMPLE_SOURCE_DIR="$(cd "$PROJECT_NAME" && pwd)" # Get absolute path
    DOCKER_IMAGE="mascucsc/hagent-builder:2025.10"
    GIT_URL=""
  else
    echo "Unknown project: '$PROJECT_NAME'" >&2
    echo "Available projects: cva6, simplechisel, soomrv, verilog-adder, xiangshan" >&2
    echo "Or specify a directory in examples/ or a full path to a directory" >&2
    exit 1
  fi
  ;;
esac

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
HAGENT_ROOT=${HAGENT_ROOT:-$(cd "${SCRIPT_DIR}/.." && pwd)}
CACHE_TEMPLATE_DIR="${HAGENT_ROOT}/.cache/setup_${PROJECT_NAME}_mcp"

create_template() {
  echo "Creating cached template at ${CACHE_TEMPLATE_DIR}..."
  mkdir -p "${CACHE_TEMPLATE_DIR}/build" "${CACHE_TEMPLATE_DIR}/cache/mcp" "${CACHE_TEMPLATE_DIR}/logs"

  # Populate repo via shallow clone if not already cached
  if [[ -n "$GIT_URL" ]]; then
    if [[ ! -d "${CACHE_TEMPLATE_DIR}/repo/.git" ]]; then
      echo "Cloning ${PROJECT_NAME} repo (shallow) into template..."
      rm -rf "${CACHE_TEMPLATE_DIR}/repo" 2>/dev/null || true
      if ! command -v git >/dev/null 2>&1; then
        echo "Error: git not found but required to clone ${GIT_URL}" >&2
        exit 1
      fi
      # TODO: we probabaly need to use different 'git clone' commands for cva6 and xiangshan
      if ! git clone --depth 1 "$GIT_URL" "${CACHE_TEMPLATE_DIR}/repo"; then
        echo "Error: git clone failed for ${GIT_URL}" >&2
        exit 1
      fi
      echo "Clone completed."
    else
      echo "Using existing cached repo at ${CACHE_TEMPLATE_DIR}/repo"
    fi
  else
    if [[ -n "${EXAMPLE_SOURCE_DIR:-}" ]]; then
      echo "Populating repo from bundled example at ${EXAMPLE_SOURCE_DIR}."
      if [[ ! -d "$EXAMPLE_SOURCE_DIR" ]]; then
        echo "Error: example directory not found at ${EXAMPLE_SOURCE_DIR}" >&2
        exit 1
      fi
      rm -rf "${CACHE_TEMPLATE_DIR}/repo"
      mkdir -p "${CACHE_TEMPLATE_DIR}/repo"
      cp -a "${EXAMPLE_SOURCE_DIR}/." "${CACHE_TEMPLATE_DIR}/repo/"
    else
      echo "Error: no git repository or example directory specified for $PROJECT_NAME" >&2
      exit 1
    fi
  fi

  echo "Template created."
}

# Try docker extraction first
if [[ ! -d "${CACHE_TEMPLATE_DIR}" ]]; then
  echo "Template not found — attempting to extract from Docker image ${DOCKER_IMAGE}..."
  mkdir -p "${CACHE_TEMPLATE_DIR}"
  CONTAINER_ID=$(docker create "${DOCKER_IMAGE}" /bin/bash 2>/dev/null || true)
  if [[ -n "$CONTAINER_ID" ]]; then
    echo "Copying /code/workspace/* ..."
    for d in build cache repo logs; do
      docker cp --archive=false "${CONTAINER_ID}:/code/workspace/${d}" "${CACHE_TEMPLATE_DIR}/" 2>/dev/null || mkdir -p "${CACHE_TEMPLATE_DIR}/${d}"
    done
    docker rm -f "$CONTAINER_ID" >/dev/null 2>&1
    echo "Template extracted from Docker."
  else
    echo "Docker extraction failed; using local template."
    create_template
  fi
else
  echo "Using cached template at ${CACHE_TEMPLATE_DIR}"
fi

# Copy to target
mkdir -p "${BASE_DIR}"
for d in repo build cache logs; do
  cp -a "${CACHE_TEMPLATE_DIR}/${d}" "${BASE_DIR}/" 2>/dev/null || mkdir -p "${BASE_DIR}/${d}"
done
mkdir -p "${BASE_DIR}/cache/mcp"

if [[ -n "${EXAMPLE_SOURCE_DIR:-}" ]]; then
  if [[ ! -d "$EXAMPLE_SOURCE_DIR" ]]; then
    echo "Error: example directory not found at ${EXAMPLE_SOURCE_DIR}" >&2
    exit 1
  fi
  if [[ ! -d "${BASE_DIR}/repo" ]] || [[ -z "$(ls -A "${BASE_DIR}/repo" 2>/dev/null)" ]]; then
    echo "Copying example from ${EXAMPLE_SOURCE_DIR} into target repo directory."
    mkdir -p "${BASE_DIR}/repo"
    cp -a "${EXAMPLE_SOURCE_DIR}/." "${BASE_DIR}/repo/"
  fi
fi

# Write server launcher
cat >"${BASE_DIR}/hagent_server.sh" <<EOF
#!/bin/bash
export UV_PROJECT="${HAGENT_ROOT}"
export HAGENT_ROOT="${HAGENT_ROOT}"
export HAGENT_DOCKER="${DOCKER_IMAGE}"
export HAGENT_REPO_DIR="${BASE_DIR}/repo"
export HAGENT_BUILD_DIR="${BASE_DIR}/build"
export HAGENT_CACHE_DIR="${BASE_DIR}/cache"
export HAGENT_OUTPUT_DIR="${BASE_DIR}/logs"
uv run python \${HAGENT_ROOT}/hagent/mcp/hagent-mcp-server.py "\$@"
#uv run python \${HAGENT_ROOT}/hagent/mcp/mcp_build.py --help
EOF
chmod +x "${BASE_DIR}/hagent_server.sh"

echo
echo "Setup complete for project '${PROJECT_NAME}'."
echo
echo "Directory structure created:"
echo "- ${BASE_DIR}/repo  (for source code)"
echo "- ${BASE_DIR}/build (for build outputs)"
echo "- ${BASE_DIR}/cache (for cached files)"
echo "- ${BASE_DIR}/cache/mcp (for MCP transaction logs)"
echo
echo "Generated files:"
echo "- ${BASE_DIR}/hagent_server.sh (executable server launcher)"
echo
echo "To use with Gemini:"
echo "  gemini mcp add hagent ${BASE_DIR}/hagent_server.sh"
echo
echo "To test manually:"
echo "  ${BASE_DIR}/hagent_server.sh"
echo
