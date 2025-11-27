"""
Test runner for HAgent MCP integration tests.

Usage:
    uv run python hagent/mcp/tests/run_tests.py                    # Run all tests
    uv run pytest hagent/mcp/tests/test_mcp_setup.py              # Run with pytest
    uv run python -m pytest hagent/mcp/tests/                     # Run all tests with pytest
"""

import sys
import unittest
from pathlib import Path

# Add the hagent root to the Python path
hagent_root = Path(__file__).parent.parent.parent.parent
sys.path.insert(0, str(hagent_root))

# Import test modules (after path setup)
from test_mcp_setup import TestMCPSetupIntegration  # noqa: E402


def main():
    """Run the tests with proper configuration."""
    # Create test loader
    loader = unittest.TestLoader()

    # Create test suite
    suite = unittest.TestSuite()

    # Add test classes
    suite.addTests(loader.loadTestsFromTestCase(TestMCPSetupIntegration))

    # Configure test runner
    runner = unittest.TextTestRunner(
        verbosity=2,
        buffer=True,  # Capture stdout/stderr during tests
        failfast=False,  # Continue running tests even if one fails
    )

    # Run tests
    result = runner.run(suite)

    # Return appropriate exit code
    return 0 if result.wasSuccessful() else 1


if __name__ == '__main__':
    sys.exit(main())
