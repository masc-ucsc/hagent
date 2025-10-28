#!/usr/bin/env bash
set -euo pipefail

# HAgent code maintenance checks entrypoint.
# Adds more checks over time; returns non-zero if any issues are found.

ROOT_DIR="${1:-.}"
cd "$ROOT_DIR"

issues=0

section() {
  echo "==> $1"
}

note() {
  echo "    $1"
}

# Select python runner (prefer uv for venv management)
PYTHON_RUN="python3"
if command -v uv >/dev/null 2>&1; then
  PYTHON_RUN="uv run python"
fi

# 1) Method privacy/usage checks (same-file-or-tests for private; suggest private for internal-only)
section "Method privacy checks"
privacy_issues=0
for dir in hagent scripts; do
  if ! $PYTHON_RUN scripts/method_privacy_check.py "$dir"; then
    privacy_issues=1
  fi
done
if [ $privacy_issues -eq 0 ]; then
  note "No method privacy issues found."
else
  issues=$((issues+1))
fi

# Helper to filter disallowed paths (anything NOT under allowed roots)
is_allowed_path() {
  # $1 is a path; return success if allowed
  case "$1" in
    hagent/inou/*|hagent/mcp/*|scripts/*) return 0;;
    *) return 1;;
  esac
}

# 2) HAGENT_.*_DIR usage only in mcp/, hagent/inou/, or scripts/
section "HAGENT_*_DIR usage scope"
found=0
while IFS= read -r line; do
  IFS=: read -r file lineno rest <<<"$line"
  # skip test files entirely
  if echo "$file" | grep -qi 'test'; then continue; fi
  if ! is_allowed_path "$file"; then
    var=$(echo "$rest" | grep -oE 'HAGENT_[A-Z_]*_DIR' | head -n1)
    echo "ENVVAR: $file:$lineno: $var used outside hagent/mcp/, hagent/inou/, or scripts/. Hint: Move usage into allowed directories or use PathManager."
    found=1
  fi
done < <(rg -n --no-heading -t py 'HAGENT_.*_DIR' hagent scripts || true)
if [ $found -eq 1 ]; then
  issues=$((issues+1))
else
  note "No disallowed HAGENT_*_DIR usages found."
fi

# 3) '/code/workspace/' only in mcp/, hagent/inou/, or scripts/
section "Container path references (/code/workspace) scope"
found=0
while IFS= read -r line; do
  IFS=: read -r file lineno rest <<<"$line"
  # skip test files entirely
  if echo "$file" | grep -qi 'test'; then continue; fi
  if ! is_allowed_path "$file"; then
    echo "CONTAINER: $file:$lineno: '/code/workspace/' used outside hagent/mcp/, hagent/inou/, or scripts/. Hint: Centralize path handling (PathManager or allowed directories)."
    found=1
  fi
done < <(rg -n --no-heading -t py '/code/workspace/' hagent scripts || true)
if [ $found -eq 1 ]; then
  issues=$((issues+1))
else
  note "No disallowed '/code/workspace/' references found."
fi

# 4) Methods never called anywhere (including tests) -> add test or remove
section "Never-called methods"
never_called_issues=0
for dir in hagent scripts; do
  if ! $PYTHON_RUN scripts/method_never_called_check.py "$dir"; then
    never_called_issues=1
  fi
done
if [ $never_called_issues -eq 0 ]; then
  note "No never-called methods found."
else
  issues=$((issues+1))
fi

# 5) Coverage-guided: public methods with zero hits in coverage.xml
if [ -f coverage.xml ]; then
  section "Coverage: public methods with 0 hits"
  if $PYTHON_RUN scripts/coverage_public_unused.py coverage.xml; then
    note "No uncovered public methods found in coverage.xml."
  else
    issues=$((issues+1))
  fi
else
  note "No coverage.xml found; skipping coverage-based hints."
fi

# 6) Code complexity checks (spaghetti code detection)
section "Code complexity checks"
complexity_issues=0
for dir in hagent scripts; do
  if ! $PYTHON_RUN scripts/avoid_spagetti_code.py "$dir"; then
    complexity_issues=1
  fi
done
if [ $complexity_issues -eq 0 ]; then
  note "No complexity issues found."
else
  issues=$((issues+1))
fi

if [ "$issues" -ne 0 ]; then
  echo "\nOne or more checks reported issues."
  exit 1
else
  echo "\nAll checks passed."
fi
