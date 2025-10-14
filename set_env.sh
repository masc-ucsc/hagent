#!/bin/bash
# This script sets the environment variables for the HAgent project.
# To apply these variables to your current shell session, run:
# source set_env.sh

echo "Setting HAgent environment variables for bash/zsh..."

export HAGENT_ROOT="/Users/sri/Documents/hagent"
export UV_PROJECT="/Users/sri/Documents/hagent"
export HAGENT_DOCKER="mascucsc/hagent-simplechisel:2025.09r"
export HAGENT_EXECUTION_MODE="docker"
export HAGENT_REPO_DIR="/Users/sri/Documents/hagent/repo"
export HAGENT_BUILD_DIR="/Users/sri/Documents/hagent/build"
export HAGENT_CACHE_DIR="/Users/sri/Documents/hagent/cache"
export HAGENT_OUTPUT_DIR="/Users/sri/Documents/hagent/logs"

echo "Environment variables set. You can now run project commands."
