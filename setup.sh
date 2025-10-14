#!/bin/bash
#
# This script creates the necessary directory structure for a new HAgent project
# without cloning any repository.
#

echo "Creating project directories in the current folder..."

mkdir -p ./repo
mkdir -p ./build
mkdir -p ./cache/mcp
mkdir -p ./logs

echo "Project directories (repo, build, cache, logs) created successfully."

# Define absolute paths for the environment script
HAGENT_ROOT_PATH="/Users/sri/Documents/hagent"
PROJECT_DIR_ABS="$(pwd)"

# Create a script that exports the necessary environment variables
cat > ./project_env.sh <<EOF
#!/bin/bash
#
# Source this file to set up your shell environment for the HAgent project.
# Usage: source ./project_env.sh
#

echo "Setting HAgent project environment variables..."

export UV_PROJECT="${HAGENT_ROOT_PATH}"
export HAGENT_ROOT="${HAGENT_ROOT_PATH}"
export HAGENT_DOCKER="mascucsc/hagent-simplechisel:2025.09r"
export HAGENT_EXECUTION_MODE="docker"
export HAGENT_REPO_DIR="${PROJECT_DIR_ABS}/repo"
export HAGENT_BUILD_DIR="${PROJECT_DIR_ABS}/build"
export HAGENT_CACHE_DIR="${PROJECT_DIR_ABS}/cache"
export HAGENT_OUTPUT_DIR="${PROJECT_DIR_ABS}/logs"

echo "Environment variables set."
echo "Your project repository is: \$HAGENT_REPO_DIR"
EOF

# Make the environment script executable
chmod +x ./project_env.sh

echo ""
echo "Setup complete!"
echo "A script named 'project_env.sh' has been created to set your environment."
echo "To configure your current shell session, please run:"
echo ""
echo "  source ./project_env.sh"
echo ""
