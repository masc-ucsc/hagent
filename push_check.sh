#!/bin/bash

# HAgent Pre-Push Check Script
# Runs linting and tests to ensure code quality before pushing
# Usage: ./push_check.sh [--bypass-on-fail]

set -e

# Colors for output
# Use ANSI 256-color "orange" (208) for better readability on light/dark backgrounds.
# Fallback to magenta if 256 colors are unavailable.
RESET='\033[0m'
RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'

# Detect 256-color support (non-fatal best effort)
if command -v tput >/dev/null 2>&1 && [ "$(tput colors 2>/dev/null || echo 0)" -ge 256 ]; then
  ORANGE='\033[38;5;208m'
else
  ORANGE='\033[35m' # fallback (magenta) is generally readable on light/dark themes
fi

# Respect NO_COLOR if set (https://no-color.org/)
if [ -n "${NO_COLOR:-}" ]; then
  RED=''
  GREEN=''
  BLUE=''
  ORANGE=''
  RESET=''
fi

# Configuration
BYPASS_ON_FAIL=false
if [[ "${1:-}" == "--bypass-on-fail" ]]; then
  BYPASS_ON_FAIL=true
fi

# Function to print colored output
print_status() {
  local color="$1"
  local message="$2"
  # Use -e to interpret escapes; colors may be empty when NO_COLOR is set
  echo -e "${color}${message}${RESET}"
}

print_header() {
  echo ""
  print_status "$BLUE" "============================================"
  print_status "$BLUE" "$1"
  print_status "$BLUE" "============================================"
}

# Function to handle failures
handle_failure() {
  local step="$1"
  local exit_code="$2"

  print_status "$RED" "❌ FAILED: $step (exit code: $exit_code)"

  if [[ $BYPASS_ON_FAIL == true ]]; then
    print_status "$ORANGE" ""
    print_status "$ORANGE" "⚠️  WARNING: --bypass-on-fail flag is set"
    print_status "$ORANGE" "⚠️  Continuing despite failure in: $step"
    print_status "$ORANGE" "⚠️  Please fix these issues before pushing to main branch!"
    print_status "$ORANGE" ""
    return 0
  else
    print_status "$RED" ""
    print_status "$RED" "💥 Pre-push checks failed!"
    print_status "$RED" "Please fix the above issues before pushing."
    print_status "$RED" ""
    print_status "$ORANGE" "To bypass this check (not recommended), run:"
    print_status "$ORANGE" "  ./push_check.sh --bypass-on-fail"
    print_status "$ORANGE" ""
    exit "$exit_code"
  fi
}

# Start of checks
print_header "🚀 HAgent Pre-Push Quality Checks"
print_status "$BLUE" "Running code quality checks before push..."
echo ""

# Check if we're in a git repository
if ! git rev-parse --git-dir >/dev/null 2>&1; then
  print_status "$RED" "❌ Not in a git repository!"
  exit 1
fi

# Show current git status
print_header "📋 Git Status"
git status --short
if [[ -n "$(git status --porcelain)" ]]; then
  print_status "$ORANGE" "⚠️  You have uncommitted changes"
fi
echo ""

# Check 1: Ruff linting
print_header "🔍 Running Ruff Linter"
print_status "$BLUE" "Checking code style and quality..."

if uv run ruff check hagent; then
  print_status "$GREEN" "✅ Ruff linting passed"
else
  handle_failure "Ruff linting" $?
fi

# Check 2: Run tests
print_header "🧪 Running Test Suite"
print_status "$BLUE" "Running all tests..."

if uv run pytest; then
  print_status "$GREEN" "✅ All tests passed"
else
  handle_failure "Test suite" $?
fi

# Success message
print_header "✅ All Checks Passed!"
print_status "$GREEN" "🎉 Great job! Your code is ready to push."
print_status "$GREEN" ""
print_status "$GREEN" "Code quality summary:"
print_status "$GREEN" "  ✓ Linting: Passed"
print_status "$GREEN" "  ✓ Tests: Passed"
print_status "$GREEN" ""
print_status "$BLUE" "You can now safely push your changes:"
print_status "$BLUE" "  git push"
print_status "$BLUE" ""

exit 0
