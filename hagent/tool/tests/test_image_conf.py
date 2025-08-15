#!/usr/bin/env python3
"""
Simple test example for Image_conf class.

This test demonstrates how to:
1. Setup a file_manager with the simplechisel image
2. Load YAML configuration using Image_conf
3. List all available commands
4. Run a specific command (GCD compile)
"""

import os
import pytest
from hagent.tool.file_manager import File_manager
from hagent.tool.image_conf import Image_conf


@pytest.fixture(scope='session', autouse=True)
def setup_hagent_environment():
    """Setup HAGENT environment variables for Docker mode tests."""
    import tempfile

    original_env = {}

    # Save original environment
    hagent_vars = ['HAGENT_EXECUTION_MODE', 'HAGENT_REPO_DIR', 'HAGENT_BUILD_DIR', 'HAGENT_CACHE_DIR']
    for var in hagent_vars:
        original_env[var] = os.environ.get(var)

    # Set Docker mode environment with host-accessible paths for testing
    os.environ['HAGENT_EXECUTION_MODE'] = 'docker'

    # Use local directories that tests can actually create and access
    repo_dir = os.path.abspath('.')  # Current working directory
    build_dir = os.path.join(tempfile.gettempdir(), 'hagent_test_build')
    cache_dir = os.path.join(tempfile.gettempdir(), 'hagent_test_cache')

    # Create directories if they don't exist
    os.makedirs(build_dir, exist_ok=True)
    os.makedirs(cache_dir, exist_ok=True)

    os.environ['HAGENT_REPO_DIR'] = repo_dir
    os.environ['HAGENT_BUILD_DIR'] = build_dir
    os.environ['HAGENT_CACHE_DIR'] = cache_dir

    yield

    # Restore original environment
    for var, value in original_env.items():
        if value is None:
            os.environ.pop(var, None)
        else:
            os.environ[var] = value


class TestImageConf:
    """Test suite for Image_conf functionality."""

    @pytest.fixture
    def file_manager(self):
        """Create and setup a File_manager instance with simplechisel image."""
        fm = File_manager(image='mascucsc/hagent-simplechisel:2025.08')

        assert fm.setup(), f'Setup failed: {fm.get_error()}'

        # Copy the hagent.yaml file to the container at the expected location
        from pathlib import Path

        # Find the hagent.yaml file in the repository
        project_root = Path(__file__).parent.parent.parent.parent  # Go up to project root
        yaml_file = project_root / 'local' / 'simplechisel' / 'repo' / 'hagent.yaml'

        if yaml_file.exists():
            # Copy to the working directory where Image_conf will look for it
            success = fm.copy_file(str(yaml_file), 'hagent.yaml')
            if not success:
                print(f'Warning: Failed to copy hagent.yaml: {fm.get_error()}')
        else:
            print(f'Warning: hagent.yaml not found at {yaml_file}')

        yield fm
        # Cleanup: ensure the instance is properly destroyed
        try:
            del fm
        except Exception:
            pass

    @pytest.fixture
    def image_conf(self):
        """Create an Image_conf instance."""
        return Image_conf()

    def test_list_all_commands(self, file_manager, image_conf):
        """Test listing all available commands from hagent.yaml."""
        fm = file_manager
        ic = image_conf

        # Setup Image_conf with file_manager and let it find YAML file automatically
        assert ic.setup(fm), f'Image_conf setup failed: {ic.get_error()}'

        # Get all available commands
        commands = ic.get_commands()
        assert len(commands) > 0, 'Should have at least one command'

        print('\n=== Available Commands ===')
        for cmd in commands:
            print(f'ID: {cmd["id"]}')
            print(f'  Profile: {cmd["profile_name"]}')
            print(f'  Profile Description: {cmd["profile_description"]}')
            print(f'  API Name: {cmd["api_name"]}')
            print(f'  API Command: {cmd["api_command"]}')
            print(f'  API Description: {cmd["api_description"]}')
            print()

        # Verify we have the expected GCD compile command
        gcd_commands = [
            cmd for cmd in commands if 'compile' in cmd['api_name'].lower() and 'gcd' in cmd['api_description'].lower()
        ]
        assert len(gcd_commands) > 0, 'Should have at least one GCD compile command'

    def test_run_echo_compile_command(self, file_manager, image_conf):
        """Test running the echo command."""
        fm = file_manager
        ic = image_conf

        # Setup Image_conf with file_manager and let it find YAML file automatically
        assert ic.setup(fm), f'Image_conf setup failed: {ic.get_error()}'

        # Get all commands to find the GCD compile command
        commands = ic.get_commands()

        # Find the echo build_dir command (which should echo HAGENT_BUILD_DIR)
        echo_cmd = None
        for cmd in commands:
            if 'build_dir' in cmd['api_name'].lower() and 'echo' in cmd['profile_name'].lower():
                echo_cmd = cmd
                break

        assert echo_cmd is not None, f'Echo build_dir command not found. Available commands: {[c["id"] for c in commands]}'

        print('\n=== Running Echo Build Dir Command ===')
        print(f'Command ID: {echo_cmd["id"]}')
        print(f'API Command: {echo_cmd["api_command"]}')
        print(f'API Description: {echo_cmd["api_description"]}')
        print()

        # Run the echo build_dir command
        exit_code, stdout, stderr = ic.run_command(echo_cmd['id'])

        print(f'Exit code: {exit_code}')
        if stdout:
            print(f'STDOUT:\n{stdout}')
        if stderr:
            print(f'STDERR:\n{stderr}')

        # Check that the command executed (exit code should be 0 for successful echo)
        assert exit_code == 0, f'Echo build_dir command failed with exit code {exit_code}. STDERR: {stderr}'

        # Verify that some expected files were generated (based on the output tracking)
        # The exact files depend on the YAML configuration, but we can check if tracking worked
        tracked_files = fm.get_current_tracked_files()
        print(f'\nTracked files after echo command: {tracked_files}')

    def test_get_profiles_and_profile_commands(self, file_manager, image_conf):
        """Test getting profiles and commands for specific profiles."""
        fm = file_manager
        ic = image_conf

        # Setup Image_conf
        assert ic.setup(fm), f'Image_conf setup failed: {ic.get_error()}'

        # Get all profiles
        profiles = ic.get_profiles()
        assert len(profiles) > 0, 'Should have at least one profile'

        print('\n=== Available Profiles ===')
        for profile in profiles:
            profile_name = profile.get('name', 'Unknown')
            description = profile.get('description', 'No description')
            memory = profile.get('memory', 0)
            print(f'Profile: {profile_name}')
            print(f'  Description: {description}')
            print(f'  Memory: {memory}GB')

            # Get commands for this profile
            profile_commands = ic.get_profile_commands(profile_name)
            print(f'  Commands ({len(profile_commands)}):')
            for cmd in profile_commands:
                print(f'    - {cmd["api_name"]}: {cmd["api_description"]}')
            print()

    def test_command_info(self, file_manager, image_conf):
        """Test getting detailed command information."""
        fm = file_manager
        ic = image_conf

        # Setup Image_conf
        assert ic.setup(fm), f'Image_conf setup failed: {ic.get_error()}'

        # Get all commands and test detailed info for the first one
        commands = ic.get_commands()
        assert len(commands) > 0, 'Should have at least one command'

        first_cmd = commands[0]
        cmd_info = ic.get_command_info(first_cmd['id'])

        assert cmd_info is not None, f'Should get command info for {first_cmd["id"]}'
        assert 'profile_name' in cmd_info
        assert 'profile_description' in cmd_info
        assert 'api_name' in cmd_info
        assert 'api_command' in cmd_info
        assert 'api_description' in cmd_info
        assert 'profile' in cmd_info

        print(f'\n=== Command Info for {first_cmd["id"]} ===')
        print(f'Profile: {cmd_info["profile_name"]}')
        print(f'Profile Description: {cmd_info["profile_description"]}')
        print(f'API Name: {cmd_info["api_name"]}')
        print(f'API Command: {cmd_info["api_command"]}')
        print(f'API Description: {cmd_info["api_description"]}')


def test_cva6_image():
    """CVA6 test that can be run directly for quick testing."""
    print('Running Image_conf CVA6 test...')

    try:
        # Create file manager and image conf
        fm = File_manager(image='mascucsc/hagent-cva6:2025.08')
        assert fm.setup(), f'File_manager setup failed: {fm.get_error()}'

        fm.run('ls /code/hagent')

        ic = Image_conf()  # read the hagent.yaml and create commands
        assert ic.setup(fm), f'Image_conf setup failed: {ic.get_error()}'

        cmd_to_run = ic.get_command('spec', 'run_slang')
        if cmd_to_run:
            print(f'\nRunning command: {cmd_to_run["id"]}')
            print(f'API Command: {cmd_to_run["api_command"]}')

            exit_code, stdout, stderr = ic.run_command(cmd_to_run['id'])
            print(f'Exit code: {exit_code}')
            if stdout:
                print(f'STDOUT (first 500 chars): {stdout[:500]}')
            if stderr:
                print(f'STDERR (first 500 chars): {stderr[:500]}')

            json = fm.get_file_content('load_store_unit.json')
            if json:
                print(f'json (first 500 chars): {json[:500]}')

            # fm.image_checkpoint("potato")

        else:
            print('No compile commands found')
            # List all commands
            commands = ic.get_commands()
            print(f'\nFound {len(commands)} commands:')
            for cmd in commands:
                print(f'  {cmd["id"]}: {cmd["api_description"]}')

    except Exception as e:
        print(f'✗ Test failed: {e}')
        raise


# Standalone test runner for quick testing
def test_image_conf_standalone():
    """Standalone test that can be run directly for quick testing."""
    print('Running Image_conf standalone test...')

    try:
        # Create file manager and image conf
        fm = File_manager(image='mascucsc/hagent-simplechisel:2025.08')
        assert fm.setup(), f'File_manager setup failed: {fm.get_error()}'

        ic = Image_conf()
        assert ic.setup(fm), f'Image_conf setup failed: {ic.get_error()}'

        # List all commands
        commands = ic.get_commands()
        print(f'\nFound {len(commands)} commands:')
        for cmd in commands:
            print(f'  {cmd["id"]}: {cmd["api_description"]}')

        # fm.run("echo 'hello' > potato.txt")
        # fm.image_checkpoint("potato")

        # Find and run a GCD compile command
        compile_commands = [
            cmd for cmd in commands if 'compile' in cmd['api_name'].lower() and 'gcd' in cmd['api_description'].lower()
        ]
        if compile_commands:
            cmd_to_run = compile_commands[0]
            print(f'\nRunning command: {cmd_to_run["id"]}')
            print(f'API Command: {cmd_to_run["api_command"]}')

            exit_code, stdout, stderr = ic.run_command(cmd_to_run['id'])
            print(f'Exit code: {exit_code}')
            if stdout:
                print(f'STDOUT (first 500 chars): {stdout[:500]}')
            if stderr:
                print(f'STDERR (first 500 chars): {stderr[:500]}')

            if exit_code == 0:
                print('✓ Command executed successfully!')
            else:
                print(f'⚠ Command failed with exit code {exit_code}')
        else:
            print('No compile commands found')

        print('✓ Standalone test completed!')

    except Exception as e:
        print(f'✗ Test failed: {e}')
        raise


if __name__ == '__main__':
    # test_image_conf_standalone()
    test_cva6_image()
