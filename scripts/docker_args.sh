#!/bin/bash
# Generate Docker arguments based on HAGENT_* environment variables

# Check if HAGENT_DOCKER is set
if [ -z "$HAGENT_DOCKER" ]; then
    echo "Error: HAGENT_DOCKER is not set" >&2
    exit 1
fi

# Determine HAGENT_ROOT: use env var or derive from script location
if [ -n "$HAGENT_ROOT" ]; then
    HAGENT_ROOT_DIR="$HAGENT_ROOT"
else
    # Get the directory where this script is located, then go up one level
    SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
    HAGENT_ROOT_DIR="$(dirname "$SCRIPT_DIR")"
fi

# Build the docker command
DOCKER_ARGS="docker run --rm -it"

# Mount hagent code
DOCKER_ARGS="$DOCKER_ARGS -v $HAGENT_ROOT_DIR:/code/hagent"

# Add volume mounts for each defined HAGENT_* variable
if [ -n "$HAGENT_TECH_DIR" ]; then
    DOCKER_ARGS="$DOCKER_ARGS -v $HAGENT_TECH_DIR:/code/workspace/tech"
fi

if [ -n "$HAGENT_REPO_DIR" ]; then
    DOCKER_ARGS="$DOCKER_ARGS -v $HAGENT_REPO_DIR:/code/workspace/repo"
fi

if [ -n "$HAGENT_BUILD_DIR" ]; then
    DOCKER_ARGS="$DOCKER_ARGS -v $HAGENT_BUILD_DIR:/code/workspace/build"
fi

if [ -n "$HAGENT_CACHE_DIR" ]; then
    DOCKER_ARGS="$DOCKER_ARGS -v $HAGENT_CACHE_DIR:/code/workspace/cache"
fi

if [ -n "$HAGENT_OUTPUT_DIR" ]; then
    DOCKER_ARGS="$DOCKER_ARGS -v $HAGENT_OUTPUT_DIR:/code/workspace/output"
fi

# Add the docker image
DOCKER_ARGS="$DOCKER_ARGS $HAGENT_DOCKER"

echo "$DOCKER_ARGS"
