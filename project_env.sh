#!/bin/bash
#
# Source this file to set up your shell environment for the HAgent project.
# Usage: source ./project_env.sh
#

echo "Setting HAgent project environment variables..."

export UV_PROJECT="/Users/sri/Documents/hagent"
export HAGENT_ROOT="/Users/sri/Documents/hagent"
export HAGENT_DOCKER="mascucsc/hagent-simplechisel:2025.09r"
export HAGENT_EXECUTION_MODE="docker"
export HAGENT_REPO_DIR="/Users/sri/Documents/hagent/repo"
export HAGENT_BUILD_DIR="/Users/sri/Documents/hagent/build"
export HAGENT_CACHE_DIR="/Users/sri/Documents/hagent/cache"
export HAGENT_OUTPUT_DIR="/Users/sri/Documents/hagent/logs"

echo "Environment variables set."
echo "Your project repository is: $HAGENT_REPO_DIR"
