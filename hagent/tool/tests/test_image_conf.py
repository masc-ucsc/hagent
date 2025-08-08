#!/usr/bin/env python3
"""
Simple test example for Image_conf class.

This test demonstrates how to:
1. Setup a file_manager with the simplechisel image
2. Load YAML configuration using Image_conf
3. List all available commands
4. Run a specific command (GCD compile)
"""

import pytest
from hagent.tool.file_manager import File_manager
from hagent.tool.image_conf import Image_conf


class TestImageConf:
    """Test suite for Image_conf functionality."""

    @pytest.fixture
    def file_manager(self):
        """Create and setup a File_manager instance with simplechisel image."""
        fm = File_manager(image='mascucsc/hagent-simplechisel:2025.07')
        assert fm.setup(workdir='/code/simplechisel'), f'Setup failed: {fm.get_error()}'
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

        # Setup Image_conf with file_manager and YAML file
        yaml_path = '/code/simplechisel/hagent.yaml'
        assert ic.setup(fm, yaml_path), f'Image_conf setup failed: {ic.get_error()}'

        # Get all available commands
        commands = ic.get_commands()
        assert len(commands) > 0, 'Should have at least one command'

        print('\n=== Available Commands ===')
        for cmd in commands:
            print(f'ID: {cmd["id"]}')
            print(f'  Profile: {cmd["profile"]}')
            print(f'  Name: {cmd["name"]}')
            print(f'  Command: {cmd["command"]}')
            print(f'  Description: {cmd["description"]}')
            print()

        # Verify we have the expected GCD compile command
        gcd_commands = [cmd for cmd in commands if 'compile' in cmd['name'].lower() and 'gcd' in cmd['description'].lower()]
        assert len(gcd_commands) > 0, 'Should have at least one GCD compile command'

    def test_run_gcd_compile_command(self, file_manager, image_conf):
        """Test running the GCD compile command."""
        fm = file_manager
        ic = image_conf

        # Setup Image_conf with file_manager and YAML file
        yaml_path = '/code/simplechisel/hagent.yaml'
        assert ic.setup(fm, yaml_path), f'Image_conf setup failed: {ic.get_error()}'

        # Get all commands to find the GCD compile command
        commands = ic.get_commands()

        # Find the GCD compile command
        gcd_compile_cmd = None
        for cmd in commands:
            if 'compile' in cmd['name'].lower() and 'gcd' in cmd['description'].lower():
                gcd_compile_cmd = cmd
                break

        assert gcd_compile_cmd is not None, f'GCD compile command not found. Available commands: {[c["id"] for c in commands]}'

        print('\n=== Running GCD Compile Command ===')
        print(f'Command ID: {gcd_compile_cmd["id"]}')
        print(f'Command: {gcd_compile_cmd["command"]}')
        print(f'Description: {gcd_compile_cmd["description"]}')
        print()

        # Run the GCD compile command
        exit_code, stdout, stderr = ic.run_command(gcd_compile_cmd['id'])

        print(f'Exit code: {exit_code}')
        if stdout:
            print(f'STDOUT:\n{stdout}')
        if stderr:
            print(f'STDERR:\n{stderr}')

        # Check that the command executed (exit code should be 0 for successful compilation)
        assert exit_code == 0, f'GCD compile command failed with exit code {exit_code}. STDERR: {stderr}'

        # Verify that some expected files were generated (based on the output tracking)
        # The exact files depend on the YAML configuration, but we can check if tracking worked
        tracked_files = fm.get_current_tracked_files()
        print(f'\nTracked files after compilation: {tracked_files}')

    def test_get_profiles_and_profile_commands(self, file_manager, image_conf):
        """Test getting profiles and commands for specific profiles."""
        fm = file_manager
        ic = image_conf

        # Setup Image_conf
        yaml_path = '/code/simplechisel/hagent.yaml'
        assert ic.setup(fm, yaml_path), f'Image_conf setup failed: {ic.get_error()}'

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
                print(f'    - {cmd["name"]}: {cmd["description"]}')
            print()

    def test_command_info(self, file_manager, image_conf):
        """Test getting detailed command information."""
        fm = file_manager
        ic = image_conf

        # Setup Image_conf
        yaml_path = '/code/simplechisel/hagent.yaml'
        assert ic.setup(fm, yaml_path), f'Image_conf setup failed: {ic.get_error()}'

        # Get all commands and test detailed info for the first one
        commands = ic.get_commands()
        assert len(commands) > 0, 'Should have at least one command'

        first_cmd = commands[0]
        cmd_info = ic.get_command_info(first_cmd['id'])

        assert cmd_info is not None, f'Should get command info for {first_cmd["id"]}'
        assert 'profile_name' in cmd_info
        assert 'api_name' in cmd_info
        assert 'command' in cmd_info
        assert 'description' in cmd_info
        assert 'profile' in cmd_info

        print(f'\n=== Command Info for {first_cmd["id"]} ===')
        print(f'Profile: {cmd_info["profile_name"]}')
        print(f'API Name: {cmd_info["api_name"]}')
        print(f'Command: {cmd_info["command"]}')
        print(f'Description: {cmd_info["description"]}')


# Standalone test runner for quick testing
def test_image_conf_standalone():
    """Standalone test that can be run directly for quick testing."""
    print('Running Image_conf standalone test...')

    try:
        # Create file manager and image conf
        fm = File_manager(image='mascucsc/hagent-simplechisel:2025.07')
        assert fm.setup(workdir='/code/simplechisel'), f'File_manager setup failed: {fm.get_error()}'

        ic = Image_conf()
        yaml_path = '/code/simplechisel/hagent.yaml'
        assert ic.setup(fm, yaml_path), f'Image_conf setup failed: {ic.get_error()}'

        # List all commands
        commands = ic.get_commands()
        print(f'\nFound {len(commands)} commands:')
        for cmd in commands:
            print(f'  {cmd["id"]}: {cmd["description"]}')

        # fm.run("echo 'hello' > potato.txt")
        # fm.image_checkpoint("potato")

        # Find and run a GCD compile command
        compile_commands = [cmd for cmd in commands if 'compile' in cmd['name'].lower() and 'gcd' in cmd['description'].lower()]
        if compile_commands:
            cmd_to_run = compile_commands[0]
            print(f'\nRunning command: {cmd_to_run["id"]}')
            print(f'Command: {cmd_to_run["command"]}')

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
    test_image_conf_standalone()
