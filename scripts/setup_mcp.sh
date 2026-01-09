#!/bin/bash
#
# Generic setup script for an MCP server
# Usage: ./setup_mcp.sh <project> [target_dir]
# Example: ./setup_mcp.sh soomrv ~/tmp/potato
#
# Creates the necessary directory structure and configuration files
# for running the HAgent MCP server with <project>
#
# Docker-based projects: Extracts from docker image and caches in .cache/setup_<project>_mcp_<version>
# Example projects: Copies directly from examples/ directory (no caching)

set -e

EXECUTION_MODE="docker"
TEMP_ARGS=()
while (("$#")); do
  case "$1" in
  --local)
    EXECUTION_MODE="local"
    shift
    ;;
  -*)
    echo "Error: Unsupported flag $1" >&2
    exit 1
    ;;
  *)
    TEMP_ARGS+=("$1")
    shift
    ;;
  esac
done
set -- "${TEMP_ARGS[@]}"
PROJECT_NAME="${1:-}"
BASE_DIR=${2:-$(pwd)}
if [[ -z "$PROJECT_NAME" ]]; then
  echo "Usage: $0 <project> [target_dir]" >&2
  echo "Available projects: cva6, simplechisel, soomrv, verilog-adder, xiangshan, esp32_led" >&2
  exit 1
fi

# Normalize project name to lowercase for portability (macOS bash lacks ${var,,})
PROJECT_NAME=$(printf '%s' "$PROJECT_NAME" | tr '[:upper:]' '[:lower:]')

# Set HAGENT_ROOT early so it can be used in EXAMPLE_SOURCE_DIR paths
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
HAGENT_ROOT=${HAGENT_ROOT:-$(cd "${SCRIPT_DIR}/.." && pwd)}

case "$PROJECT_NAME" in
cva6)
  DOCKER_IMAGE="mascucsc/hagent-cva6:2026.01"
  ;;
simplechisel)
  DOCKER_IMAGE="mascucsc/hagent-simplechisel:2026.01"
  ;;
soomrv)
  DOCKER_IMAGE="mascucsc/hagent-soomrv:2025.12"
  ;;
verilog-adder)
  DOCKER_IMAGE="mascucsc/hagent-builder:2026.01"
  EXAMPLE_SOURCE_DIR="${HAGENT_ROOT}/examples/verilog_adder"
  ;;
xiangshan)
  DOCKER_IMAGE="mascucsc/hagent-xiangshan:2025.12"
  ;;
esp32_led)
  DOCKER_IMAGE="mascucsc/hagent-builder:2026.01"
  EXAMPLE_SOURCE_DIR="${HAGENT_ROOT}/examples/esp32_led"
  ;;
*)
  # Check if it's a directory in examples or a direct path
  if [[ -d "${HAGENT_ROOT}/examples/${PROJECT_NAME}" ]]; then
    EXAMPLE_SOURCE_DIR="${HAGENT_ROOT}/examples/${PROJECT_NAME}"
    DOCKER_IMAGE="mascucsc/hagent-builder:2026.01"
  elif [[ -d "$PROJECT_NAME" ]]; then
    EXAMPLE_SOURCE_DIR="$(cd "$PROJECT_NAME" && pwd)" # Get absolute path
    DOCKER_IMAGE="mascucsc/hagent-builder:2026.01"
  else
    echo "Unknown project: '$PROJECT_NAME'" >&2
    echo "Available projects: cva6, simplechisel, soomrv, verilog-adder, xiangshan, esp32_led" >&2
    echo "Or specify a directory in examples/ or a full path to a directory" >&2
    exit 1
  fi
  ;;
esac

# Extract docker version from image tag (e.g., "mascucsc/hagent-simplechisel:2026.01" -> "2025.12")
DOCKER_VERSION=$(echo "$DOCKER_IMAGE" | sed 's/.*://')
CACHE_TEMPLATE_DIR="${HAGENT_ROOT}/.cache/setup_${PROJECT_NAME}_mcp_${DOCKER_VERSION}"

# Handle example-based projects (skip cache, copy directly)
if [[ -n "${EXAMPLE_SOURCE_DIR:-}" ]]; then
  echo "Setting up example project from ${EXAMPLE_SOURCE_DIR}..."
  if [[ ! -d "$EXAMPLE_SOURCE_DIR" ]]; then
    echo "Error: example directory not found at ${EXAMPLE_SOURCE_DIR}" >&2
    exit 1
  fi

  # Create target directories
  mkdir -p "${BASE_DIR}/repo" "${BASE_DIR}/build" "${BASE_DIR}/cache" "${BASE_DIR}/logs"
  mkdir -p "${BASE_DIR}/cache/mcp"

  # Copy example source to repo
  echo "Copying example from ${EXAMPLE_SOURCE_DIR} into target repo directory."
  cp -a "${EXAMPLE_SOURCE_DIR}/." "${BASE_DIR}/repo/"

else
  # Handle docker-based projects (use cache with version)
  if [[ ! -d "${CACHE_TEMPLATE_DIR}" ]]; then
    echo "Template not found — extracting from Docker image ${DOCKER_IMAGE}..."
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
      echo "Error: Failed to extract template from Docker image ${DOCKER_IMAGE}" >&2
      echo "Please ensure Docker is running and the image is available." >&2
      exit 1
    fi
  else
    echo "Using cached template at ${CACHE_TEMPLATE_DIR}"
  fi

  # Copy from cache to target
  mkdir -p "${BASE_DIR}"
  for d in repo build cache logs; do
    cp -a "${CACHE_TEMPLATE_DIR}/${d}" "${BASE_DIR}/" 2>/dev/null || mkdir -p "${BASE_DIR}/${d}"
  done
  mkdir -p "${BASE_DIR}/cache/mcp"
fi

# Write server launcher
if [[ "$EXECUTION_MODE" == "local" ]]; then
  MODE_EXPORT='export HAGENT_EXECUTION_MODE="local"'
else
  MODE_EXPORT="export HAGENT_DOCKER=\"${DOCKER_IMAGE}\""
fi

cat >"${BASE_DIR}/hagent_server.sh" <<EOF
#!/bin/bash
export UV_PROJECT="${HAGENT_ROOT}"
export HAGENT_ROOT="${HAGENT_ROOT}"
${MODE_EXPORT}
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
