#!/usr/bin/env python3
"""
Backward compatibility wrapper for hagent-build.py.

This script maintains the original CLI interface while delegating to the new
shared implementation in hagent.core.tests.cli_hagent_build.
"""

import sys
from pathlib import Path

# Add the project root to the path so we can import hagent modules
project_root = Path(__file__).parent.parent
sys.path.insert(0, str(project_root))

try:
    from hagent.core.tests.cli_hagent_build import main
except ImportError:
    print("Error: Could not import the new hagent-build implementation.", file=sys.stderr)
    print("Please ensure the hagent package is properly installed.", file=sys.stderr)
    sys.exit(1)


if __name__ == '__main__':
    print(f'hagent-builder using conf.yaml configuration (delegating to shared implementation)')
    sys.exit(main())
