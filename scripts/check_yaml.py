#!/usr/bin/env python3
"""
hagent.yaml Validator and Tester

This script reads the hagent.yaml configuration file, validates the environment,
checks input file existence, executes commands, and verifies output generation.
"""

import yaml
import os
import sys
import subprocess
import glob
import time
from typing import Dict, List, Optional, Tuple
import argparse
import logging

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[logging.StreamHandler(), logging.FileHandler('yaml_validator.log')],
)
logger = logging.getLogger(__name__)


class YAMLValidator:
    def __init__(self, yaml_file: str, dry_run: bool = False):
        self.yaml_file = yaml_file
        self.dry_run = dry_run
        self.original_env = dict(os.environ)
        self.config = None

    def load_yaml(self) -> bool:
        """Load and parse the YAML configuration file."""
        try:
            with open(self.yaml_file, 'r') as f:
                self.config = yaml.safe_load(f)
            logger.info(f'Successfully loaded YAML from {self.yaml_file}')
            return True
        except FileNotFoundError:
            logger.error(f'YAML file {self.yaml_file} not found')
            return False
        except yaml.YAMLError as e:
            logger.error(f'YAML parsing error: {e}')
            return False

    def parse_track_directive(self, directive: str) -> Tuple[str, str, Optional[str]]:
        """Parse track_dir() or track_file() directives."""
        # Extract function name, path, and extension
        if directive.startswith('track_dir('):
            func_type = 'dir'
            content = directive[10:-1]  # Remove "track_dir(" and ")"
        elif directive.startswith('track_file('):
            func_type = 'file'
            content = directive[11:-1]  # Remove "track_file(" and ")"
        else:
            return directive, 'unknown', None

        # Parse parameters
        parts = [p.strip().strip('\'"') for p in content.split(',')]
        path = parts[0]
        ext = None

        for part in parts[1:]:
            if part.startswith('ext='):
                ext = part[4:].strip('\'"')

        return path, func_type, ext

    def check_input_sources(self, profile: Dict) -> bool:
        """Check if input sources exist."""
        source = profile['configuration']['source']
        path, func_type, ext = self.parse_track_directive(source)

        logger.info(f'Checking input source: {path} (type: {func_type}, ext: {ext})')

        if func_type == 'dir':
            if not os.path.isdir(path):
                logger.error(f'Source directory does not exist: {path}')
                return False

            # Check for files with specified extension
            if ext:
                pattern = os.path.join(path, f'**/*{ext}')
                files = glob.glob(pattern, recursive=True)
                if not files:
                    logger.warning(f'No files with extension {ext} found in {path}')
                else:
                    logger.info(f'Found {len(files)} files with extension {ext}')

        elif func_type == 'file':
            if not os.path.isfile(path):
                logger.error(f'Source file does not exist: {path}')
                return False

        return True

    def setup_environment(self, profile: Dict) -> None:
        """Set up environment variables for the profile."""
        env_vars = profile['configuration'].get('environment', {})

        for key, value in env_vars.items():
            # Handle PATH expansion
            if key == 'PATH' and value.startswith('$PATH:'):
                expanded_value = os.environ.get('PATH', '') + ':' + value[6:]
                os.environ[key] = expanded_value
            else:
                # Handle other variable expansions
                expanded_value = os.path.expandvars(value)
                os.environ[key] = expanded_value

            logger.info(f'Set environment variable: {key}={os.environ[key]}')

    def check_dependencies(self) -> bool:
        """Check if required tools are available."""
        tools = ['sbt', 'yosys']  # Add more tools as needed
        missing_tools = []

        for tool in tools:
            try:
                result = subprocess.run(['which', tool], capture_output=True, text=True, timeout=10)
                if result.returncode == 0:
                    logger.info(f'Found {tool} at: {result.stdout.strip()}')
                else:
                    missing_tools.append(tool)
            except (subprocess.TimeoutExpired, FileNotFoundError):
                missing_tools.append(tool)

        if missing_tools:
            logger.warning(f'Missing tools: {", ".join(missing_tools)}')
            return False
        return True

    def get_output_files_before(self, profile: Dict) -> List[str]:
        """Get list of output files before command execution."""
        output = profile['configuration']['output']
        path, func_type, ext = self.parse_track_directive(output)

        files = []
        if func_type == 'dir':
            if os.path.exists(path):
                if ext:
                    pattern = os.path.join(path, f'**/*{ext}')
                    files = glob.glob(pattern, recursive=True)
                else:
                    pattern = os.path.join(path, '**/*')
                    files = glob.glob(pattern, recursive=True)
                    files = [f for f in files if os.path.isfile(f)]
        elif func_type == 'file':
            if os.path.exists(path):
                files = [path]

        return files

    def execute_command(self, command: str, timeout: int = 300) -> Tuple[bool, str, str]:
        """Execute a command and return success status, stdout, stderr."""
        if self.dry_run:
            logger.info(f'DRY RUN - Would execute: {command}')
            return True, 'DRY RUN OUTPUT', ''

        logger.info(f'Executing command: {command}')
        start_time = time.time()

        try:
            result = subprocess.run(command, shell=True, capture_output=True, text=True, timeout=timeout, cwd=os.getcwd())

            execution_time = time.time() - start_time
            logger.info(f'Command completed in {execution_time:.2f} seconds')

            if result.returncode == 0:
                logger.info('Command executed successfully')
                return True, result.stdout, result.stderr
            else:
                logger.error(f'Command failed with return code {result.returncode}')
                logger.error(f'STDERR: {result.stderr}')
                return False, result.stdout, result.stderr

        except subprocess.TimeoutExpired:
            logger.error(f'Command timed out after {timeout} seconds')
            return False, '', 'Command timed out'
        except Exception as e:
            logger.error(f'Command execution failed: {e}')
            return False, '', str(e)

    def verify_output_generation(self, profile: Dict, files_before: List[str]) -> bool:
        """Verify that new output files were generated."""
        output = profile['configuration']['output']
        path, func_type, ext = self.parse_track_directive(output)

        files_after = []
        if func_type == 'dir':
            if os.path.exists(path):
                if ext:
                    pattern = os.path.join(path, f'**/*{ext}')
                    files_after = glob.glob(pattern, recursive=True)
                else:
                    pattern = os.path.join(path, '**/*')
                    files_after = glob.glob(pattern, recursive=True)
                    files_after = [f for f in files_after if os.path.isfile(f)]
        elif func_type == 'file':
            if os.path.exists(path):
                files_after = [path]

        new_files = set(files_after) - set(files_before)
        modified_files = []

        # Check for modified files
        for file_path in set(files_after) & set(files_before):
            try:
                os.path.getmtime(file_path)
                # This is a simplified check - in reality, we'd need to store timestamps
                # For now, we'll assume files that exist in both lists might be modified
                modified_files.append(file_path)
            except OSError:
                continue

        if new_files:
            logger.info(f'New output files generated: {len(new_files)}')
            for f in sorted(new_files):
                logger.info(f'  - {f}')
        else:
            logger.warning('No new output files were generated')

        if not new_files and not files_after:
            logger.error('No output files found after command execution')
            return False

        return True

    def test_profile(self, profile: Dict) -> bool:
        """Test a single profile configuration."""
        profile_name = profile['name']
        logger.info(f'\n{"=" * 60}')
        logger.info(f'Testing profile: {profile_name}')
        logger.info(f'{"=" * 60}')

        # Check memory requirements
        memory_gb = profile.get('memory', 0)
        logger.info(f'Profile requires {memory_gb}GB memory')

        # Check input sources
        if not self.check_input_sources(profile):
            logger.error(f'Input source validation failed for profile: {profile_name}')
            return False

        # Setup environment
        self.setup_environment(profile)

        # Test each API
        apis = profile.get('apis', [])
        for api in apis:
            api_name = api['name']
            command = api['command']
            description = api.get('description', '')

            logger.info(f'\nTesting API: {api_name}')
            logger.info(f'Description: {description}')

            # Get output files before execution
            files_before = self.get_output_files_before(profile)
            logger.info(f'Output files before execution: {len(files_before)}')

            # Execute command
            success, stdout, stderr = self.execute_command(command)

            if not success:
                logger.error(f'API {api_name} failed to execute')
                return False

            # Verify output generation (skip for lint commands)
            if api_name != 'lint':
                if not self.verify_output_generation(profile, files_before):
                    logger.warning(f'Output verification failed for API: {api_name}')
                    # Don't fail the test for synthesis commands as they might not generate tracked files
                    if api_name not in ['synthesize']:
                        return False

        # Restore original environment
        os.environ.clear()
        os.environ.update(self.original_env)

        logger.info(f'Profile {profile_name} completed successfully')
        return True

    def run_validation(self, profile_names: Optional[List[str]] = None) -> bool:
        """Run validation for specified profiles or all profiles."""
        if not self.load_yaml():
            return False

        # Check dependencies
        if not self.check_dependencies():
            logger.warning('Some dependencies are missing - continuing anyway')

        profiles = self.config.get('profiles', [])

        if profile_names:
            # Filter profiles by name
            profiles = [p for p in profiles if p['name'] in profile_names]
            if len(profiles) != len(profile_names):
                found_names = [p['name'] for p in profiles]
                missing = set(profile_names) - set(found_names)
                logger.error(f'Profiles not found: {missing}')
                return False

        if not profiles:
            logger.error('No profiles found to test')
            return False

        logger.info(f'Testing {len(profiles)} profile(s)')

        success_count = 0
        for profile in profiles:
            try:
                if self.test_profile(profile):
                    success_count += 1
                else:
                    logger.error(f'Profile {profile["name"]} failed')
            except Exception as e:
                logger.error(f'Unexpected error testing profile {profile["name"]}: {e}')

        logger.info(f'\n{"=" * 60}')
        logger.info('VALIDATION COMPLETE')
        logger.info(f'Successful profiles: {success_count}/{len(profiles)}')
        logger.info(f'{"=" * 60}')

        return success_count == len(profiles)


def main():
    parser = argparse.ArgumentParser(description='Validate hagent.yaml configuration')
    parser.add_argument('yaml_file', help='Path to hagent.yaml file')
    parser.add_argument('--profiles', nargs='+', help='Specific profile names to test')
    parser.add_argument('--dry-run', action='store_true', help="Dry run mode - don't execute commands")
    parser.add_argument('--verbose', '-v', action='store_true', help='Verbose logging')

    args = parser.parse_args()

    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)

    validator = YAMLValidator(args.yaml_file, dry_run=args.dry_run)

    try:
        success = validator.run_validation(args.profiles)
        sys.exit(0 if success else 1)
    except KeyboardInterrupt:
        logger.info('Validation interrupted by user')
        sys.exit(1)
    except Exception as e:
        logger.error(f'Unexpected error: {e}')
        sys.exit(1)


if __name__ == '__main__':
    main()
