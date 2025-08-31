"""
Unit test for Gemini MCP integration with HAgent.

This test performs end-to-end testing of the MCP server integration with Gemini,
including setup, schema validation, successful compilation, and error handling.

Usage:
    # Run all active tests (schema validation and connectivity)
    uv run python hagent/mcp/tests/test_gemini_setup.py
    uv run pytest hagent/mcp/tests/test_gemini_setup.py
    uv run python -m unittest hagent.mcp.tests.test_gemini_setup

    # Run only fast tests (same as above, slow tests are currently disabled)
    uv run pytest hagent/mcp/tests/test_gemini_setup.py -m "not slow"

    # Run specific test
    uv run pytest hagent/mcp/tests/test_gemini_setup.py::TestGeminiMCPIntegration::test_1_schema_consistency

Note: test_2_successful_compilation and test_3_error_handling_and_iteration are currently
disabled due to Gemini workspace directory issues. They can be re-enabled once Gemini is fixed.
"""

import json
import os
import shutil
import subprocess
import unittest
import uuid
from pathlib import Path

import pytest


class TestGeminiMCPIntegration(unittest.TestCase):
    """Test suite for Gemini MCP integration with HAgent."""

    @classmethod
    def setUpClass(cls):
        """Set up test environment - run once for all tests."""
        # Get the HAgent root directory
        cls.hagent_root = Path(__file__).parent.parent.parent.parent
        cls.setup_script = cls.hagent_root / 'scripts' / 'setup_simplechisel_mcp.sh'

        # Check if Gemini is installed
        try:
            result = subprocess.run(['gemini', '--version'], capture_output=True, text=True, timeout=10)
            if result.returncode != 0:
                raise subprocess.CalledProcessError(result.returncode, 'gemini --version')
        except (subprocess.CalledProcessError, FileNotFoundError, subprocess.TimeoutExpired):
            raise unittest.SkipTest('Gemini is not installed or not accessible')

        # Create base test directory in the hagent root for easier debugging
        cls.base_test_dir = cls.hagent_root / 'setup_run'
        cls.original_cwd = Path.cwd()

        # Clean up any existing setup_run directory
        if cls.base_test_dir.exists():
            shutil.rmtree(cls.base_test_dir)
        cls.base_test_dir.mkdir(exist_ok=True)

        print(f'Base test directory: {cls.base_test_dir} (persistent for debugging)')

    @classmethod
    def tearDownClass(cls):
        """Clean up test environment."""
        # Change back to original directory
        os.chdir(cls.original_cwd)

        # Leave setup_run directory for debugging - user can clean up manually
        print(f'Base test directory left for debugging: {cls.base_test_dir}')
        print('To clean up: rm -rf setup_run')

    def setUp(self):
        """Set up each individual test."""
        # Create unique test directory for this test instance
        test_id = str(uuid.uuid4())[:8]
        test_name = self._testMethodName
        self.test_dir = self.base_test_dir / f'{test_name}_{test_id}'
        self.test_dir.mkdir(exist_ok=True)

        # Create unique MCP server name to avoid conflicts
        self.mcp_server_name = f'hagent_{test_name}_{test_id}'

        # Change to test directory
        os.chdir(self.test_dir)

        # Set up environment using the setup script
        print(f'Setting up test environment in {self.test_dir}')
        print(f'Using MCP server name: {self.mcp_server_name}')
        result = subprocess.run(
            [str(self.setup_script)],
            capture_output=True,
            text=True,
            timeout=120,
            env={**os.environ, 'HAGENT_ROOT': str(self.hagent_root)},
        )

        if result.returncode != 0:
            self.fail(f'Setup script failed: {result.stderr}')

        # Verify expected file was created
        hagent_server_path = self.test_dir / 'hagent_server.sh'
        if not hagent_server_path.exists():
            self.fail('Expected file hagent_server.sh was not created by setup script')

        # Clean up any existing MCP servers in Gemini (with this test's name)
        self._cleanup_gemini_mcps()

        # Install the hagent MCP server with unique name
        self._install_hagent_mcp()

    def tearDown(self):
        """Clean up after each test."""
        # Remove the unique MCP server from Gemini
        try:
            subprocess.run(['gemini', 'mcp', 'remove', self.mcp_server_name], capture_output=True, text=True, timeout=30)
        except subprocess.TimeoutExpired:
            pass  # Ignore timeout during cleanup

    def _cleanup_gemini_mcps(self):
        """Remove MCP servers from Gemini to start clean."""
        try:
            # Get list of existing MCP servers
            result = subprocess.run(['gemini', 'mcp', 'list'], capture_output=True, text=True, timeout=30)

            if result.returncode == 0:
                # Parse output to find MCP server names that match this test
                lines = result.stdout.split('\n')
                for line in lines:
                    if ':' in line and ('Connected' in line or 'Disconnected' in line):
                        # Extract server name (format: "✓ name: path (stdio) - Connected")
                        server_name = line.split(':')[0].strip().lstrip('✓✗ ')
                        # Only remove servers that start with this test's pattern or exact match
                        if server_name and (
                            server_name == self.mcp_server_name or server_name.startswith(f'hagent_{self._testMethodName}')
                        ):
                            try:
                                subprocess.run(
                                    ['gemini', 'mcp', 'remove', server_name], capture_output=True, text=True, timeout=30
                                )
                            except subprocess.TimeoutExpired:
                                pass  # Ignore individual removal failures
        except subprocess.TimeoutExpired:
            pass  # Ignore if cleanup fails

    def _install_hagent_mcp(self):
        """Install the hagent MCP server in Gemini with unique name."""
        hagent_server_path = self.test_dir / 'hagent_server.sh'

        # Make sure the server script is executable
        hagent_server_path.chmod(0o755)

        # Remove any existing MCP server with this name first
        subprocess.run(
            ['gemini', 'mcp', 'remove', self.mcp_server_name], capture_output=True, text=True, timeout=30, cwd=str(self.test_dir)
        )
        # Note: We don't check return code for remove since it's OK if server doesn't exist

        # Add the hagent MCP server with unique name (run from the test directory with relative path)
        result = subprocess.run(
            ['gemini', 'mcp', 'add', self.mcp_server_name, './hagent_server.sh'],
            capture_output=True,
            text=True,
            timeout=60,
            cwd=str(self.test_dir),
        )

        if result.returncode != 0:
            self.fail(f'Failed to install {self.mcp_server_name} MCP server: {result.stderr}')

        # Verify installation
        result = subprocess.run(['gemini', 'mcp', 'list'], capture_output=True, text=True, timeout=30, cwd=str(self.test_dir))

        if result.returncode != 0 or f'{self.mcp_server_name}:' not in result.stdout:
            self.fail(f'{self.mcp_server_name} MCP server not found in list: {result.stdout}')

    def test_1_schema_consistency(self):
        """Test that /mcp schema is consistent with mcp_build.py --schema."""
        # Get schema from mcp_build.py using uv run
        result = subprocess.run(
            ['uv', 'run', 'python', 'hagent/mcp/mcp_build.py', '--schema'],
            capture_output=True,
            text=True,
            timeout=30,
            cwd=str(self.hagent_root),
            env={**os.environ, 'HAGENT_ROOT': str(self.hagent_root), 'UV_PROJECT': str(self.hagent_root)},
        )

        if result.returncode != 0:
            self.fail(f'Failed to get schema from mcp_build.py: {result.stderr}')

        try:
            json.loads(result.stdout)  # Validate JSON format
        except json.JSONDecodeError as e:
            self.fail(f'Invalid JSON from mcp_build.py --schema: {e}')

        # Get schema from Gemini MCP using direct prompt with unique server name
        result = subprocess.run(
            [
                'gemini',
                '--allowed-mcp-server-names',
                self.mcp_server_name,
                '-y',
                '-p',
                'What tools are available? Can you show me the schema for hagent_build?',
            ],
            capture_output=True,
            text=True,
            timeout=60,
            cwd=str(self.test_dir),
        )

        if result.returncode != 0:
            self.fail(f'Failed to get schema from Gemini: {result.stderr}')

        # The Gemini schema output might be more complex, so we'll check key components
        gemini_output = result.stdout

        # Verify key schema elements are present
        self.assertIn('hagent_build', gemini_output, 'hagent_build tool not found in Gemini schema')

        # Check that expected parameters are mentioned
        expected_params = ['name', 'profile', 'api', 'dry_run']
        for param in expected_params:
            self.assertIn(param, gemini_output, f"Parameter '{param}' not found in Gemini schema")

        # Note: Profile validation skipped since test environment may not have hagent.yaml configured
        print('Schema validation passed - hagent_build tool found with expected parameters')

    @pytest.mark.skip(reason='Gemini workspace directory issues - disable until Gemini is fixed')
    @pytest.mark.slow
    def test_2_successful_compilation(self):
        """Test successful compilation with Gemini."""
        print(f'Starting compilation test from directory: {self.test_dir}')
        print(f'Hagent server script exists: {(self.test_dir / "hagent_server.sh").exists()}')

        # Check if MCP server is properly connected before running compilation
        mcp_check = subprocess.run(['gemini', 'mcp', 'list'], capture_output=True, text=True, timeout=30, cwd=str(self.test_dir))
        print(f'MCP status check return code: {mcp_check.returncode}')
        print(f'MCP status output: {mcp_check.stdout}')
        if mcp_check.stderr:
            print(f'MCP status stderr: {mcp_check.stderr}')

        # Skip test if MCP server is not properly connected
        if f'{self.mcp_server_name}:' not in mcp_check.stdout or 'Connected' not in mcp_check.stdout:
            self.skipTest(f'MCP server not properly connected: {mcp_check.stdout}')

        try:
            # Run a simpler test first - just ask for available tools
            print('Testing basic MCP tool access...')
            simple_result = subprocess.run(
                [
                    'gemini',
                    '--allowed-mcp-server-names',
                    self.mcp_server_name,
                    '-y',
                    '-p',
                    'What tools do you have available?',
                ],
                capture_output=True,
                text=True,
                timeout=60,  # Shorter timeout for tool listing
                cwd=str(self.test_dir),
            )
            print(f'Simple test return code: {simple_result.returncode}')
            print(f'Simple test output length: {len(simple_result.stdout)}')
            if simple_result.returncode != 0:
                print(f'Simple test stderr: {simple_result.stderr}')
                self.skipTest(f'Basic MCP tool access failed: {simple_result.stderr}')

            # Now try the actual compilation
            print('Starting Gemini compilation command...')
            result = subprocess.run(
                [
                    'gemini',
                    '--allowed-mcp-server-names',
                    self.mcp_server_name,
                    '-y',  # Auto-confirm
                    '-p',
                    'Can you compile the gcd profile? This should generate Verilog output.',
                ],
                capture_output=True,
                text=True,
                timeout=300,  # Increased timeout for compilation + LLM processing
                cwd=str(self.test_dir),  # Run from test directory with proper setup
            )
        except subprocess.TimeoutExpired as e:
            print('Process timed out after timeout seconds')
            print(f'Partial stdout: {e.stdout[:1000] if e.stdout else "None"}')
            print(f'Partial stderr: {e.stderr[:1000] if e.stderr else "None"}')
            self.fail('Gemini compilation command timed out')

        print(f'Gemini process completed with return code: {result.returncode}')
        print(f'Stdout length: {len(result.stdout)}')
        print(f'Stderr length: {len(result.stderr)}')

        if result.returncode != 0:
            print(f'Gemini stderr: {result.stderr}')
            print(f'Gemini stdout: {result.stdout}')
            self.fail(f'Gemini command failed with return code {result.returncode}: {result.stderr}')

        # Check that output contains success indicators
        output = result.stdout.lower()
        print(f'First 500 chars of output: {result.stdout[:500]}')

        # More lenient error checking - compilation might have warnings
        if 'failed' in output or 'compilation error' in output:
            self.fail(f'Compilation failed in output: {result.stdout}')

        # Check that expected build artifacts were created
        build_dir = self.test_dir / 'build'
        expected_artifacts = [
            build_dir / 'build_gcd' / 'GCD.sv',
            build_dir / 'build_gcd' / 'GCD.v',
        ]

        # At least one of these should exist
        artifact_found = False
        for artifact in expected_artifacts:
            if artifact.exists():
                artifact_found = True
                print(f'Found build artifact: {artifact}')
                break

        if not artifact_found:
            # List what was actually created
            if build_dir.exists():
                build_contents = list(build_dir.rglob('*'))
                print(f'Build directory contents: {build_contents}')
            self.fail(f'No expected build artifacts found. Expected one of: {expected_artifacts}')

    @pytest.mark.skip(reason='Gemini workspace directory issues - disable until Gemini is fixed')
    @pytest.mark.slow
    def test_3_error_handling_and_iteration(self):
        """Test error handling with compilation failure and iteration."""
        # Introduce a typo in the GCD.scala file
        gcd_file = self.test_dir / 'repo' / 'src' / 'main' / 'scala' / 'gcd' / 'GCD.scala'

        if not gcd_file.exists():
            self.fail(f'GCD.scala file not found at {gcd_file}')

        # Read the file
        original_content = gcd_file.read_text()

        # Introduce typo: change io.outputGCD to io_outputGCD
        typo_content = original_content.replace('io.outputGCD := x', 'io_outputGCD := x')

        if typo_content == original_content:
            self.fail('Failed to introduce typo - original pattern not found')

        # Write the file with typo
        gcd_file.write_text(typo_content)

        try:
            # Run Gemini command that should encounter the error
            result = subprocess.run(
                [
                    'gemini',
                    '--allowed-mcp-server-names',
                    self.mcp_server_name,
                    '-y',  # Auto-confirm
                    '-p',
                    'Can you recompile gcd? I made some changes that might have issues.',
                ],
                capture_output=True,
                text=True,
                timeout=240,
            )

            # The command might succeed or fail depending on Gemini's ability to fix the error
            # What's important is that it should mention the compilation error
            output = result.stdout.lower()

            # Check that error information is present and actionable
            error_indicators = ['compilation failed', 'error', 'not found', 'scala', 'gcd.scala']

            found_indicators = [indicator for indicator in error_indicators if indicator in output]

            if len(found_indicators) < 2:
                self.fail(f'Expected to find error indicators in output. Found: {found_indicators}. Output: {result.stdout}')

            # Check if Gemini was able to fix the issue
            final_content = gcd_file.read_text()
            if 'io.outputGCD := x' in final_content:
                print('✓ Gemini successfully fixed the compilation error')
            else:
                print('⚠ Gemini detected the error but may not have fixed it completely')
                # This is still a success as long as the error was properly communicated

        finally:
            # Restore original file content for cleanup
            gcd_file.write_text(original_content)

    def test_4_mcp_server_connectivity(self):
        """Test basic MCP server connectivity."""
        # Verify the server is listed as connected
        result = subprocess.run(['gemini', 'mcp', 'list'], capture_output=True, text=True, timeout=30)

        if result.returncode != 0:
            self.fail(f'Failed to list MCP servers: {result.stderr}')

        # Check that the unique MCP server is connected
        output = result.stdout
        self.assertIn(f'{self.mcp_server_name}:', output, f'{self.mcp_server_name} server not found in MCP list')
        self.assertIn('Connected', output, f'{self.mcp_server_name} server not connected')


if __name__ == '__main__':
    # Configure test runner
    unittest.main(verbosity=2, failfast=True)
