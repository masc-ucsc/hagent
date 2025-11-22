"""Locator - Map between HDL representations (VCD, Verilog, Chisel, Netlist).

This module provides intelligent mapping between different hardware design representations
with caching support. It integrates with the Builder infrastructure to extract configuration
from hagent.yaml.
"""

import json
import os
import re
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import List, Optional

from hagent.inou.builder import Builder
from hagent.tool.code_scope import Code_scope
from hagent.tool.module_finder import Module_finder


class RepresentationType(Enum):
    """Types of HDL representations that can be mapped."""

    VERILOG = 'verilog'  # RTL Verilog source
    NETLIST = 'netlist'  # Post-synthesis netlist (Verilog)
    CHISEL = 'chisel'  # Chisel/Scala source
    VCD = 'vcd'  # VCD waveform hierarchy


@dataclass
class SourceLocation:
    """Represents a source code location with optional line range."""

    file_path: str  # Absolute path to source file
    module_name: str  # Module/class name
    line_start: int  # Starting line number
    line_end: int  # Ending line number (same as start for exact match)
    confidence: float  # 0.0-1.0 confidence score
    representation: RepresentationType  # Type of representation


class Locator:
    """Map variables and code between HDL representations with caching."""

    def __init__(self, config_path: Optional[str] = None, profile_name: Optional[str] = None, debug: bool = False):
        """Initialize Locator.

        Args:
            config_path: Path to hagent.yaml (auto-discovered if None)
            profile_name: Specific profile to use (required for operations needing config)
            debug: If True, show verbose output from run_cmd calls
        """
        self.config_path = config_path
        self.profile_name = profile_name
        self.debug = debug
        self.builder: Optional[Builder] = None
        self._error: str = ''
        self._cache_dir: Optional[Path] = None
        self._profile_config: Optional[dict] = None

    def _debug_print(self, message: str) -> None:
        """Print debug message to stderr if debug mode is enabled."""
        if self.debug:
            import sys

            print(f'[DEBUG] {message}', file=sys.stderr)

    def setup(self) -> bool:
        """Initialize Builder and load configuration.

        Returns:
            True if setup successful, False otherwise
        """
        self._debug_print(f'setup() called with profile_name={self.profile_name}, config_path={self.config_path}')
        try:
            # Get docker image from environment if in docker mode
            docker_image = os.environ.get('HAGENT_DOCKER')
            self._debug_print(f'Docker image: {docker_image or "None (local mode)"}')

            # Initialize builder (pass docker_image for docker mode)
            self.builder = Builder(self.config_path, docker_image=docker_image)
            if not self.builder.setup():
                self._error = f'Builder setup failed: {self.builder.get_error()}'
                return False

            # Verify builder's runner is properly initialized
            if not self.builder.runner:
                self._error = 'Builder runner not initialized'
                return False

            # Load profile configuration
            self._profile_config = self._load_profile_config()
            if not self._profile_config:
                return False

            # Setup cache directory
            cache_base = Path(self.builder.runner.path_manager.cache_dir)
            self._cache_dir = cache_base / 'locator' / self.profile_name
            self._debug_print(f'Cache directory: {self._cache_dir}')

            # Create cache directory using filesystem API (works in both local and Docker modes)
            self.builder.filesystem.makedirs(str(self._cache_dir), exist_ok=True)

            self._debug_print(f'Setup completed successfully')
            return True
        except Exception as e:
            self._error = f'Setup failed: {e!s}'
            return False

    def locate_vcd(self, to: RepresentationType, vcd_variable: str) -> List[SourceLocation]:
        """Map a VCD hierarchical signal to source locations in target representation.

        VCD signals include hierarchy (e.g., "top.cpu.alu.result"), which provides module context.
        slang-hier maps the hierarchy to modules but doesn't provide leaf variables, so this method:
        1. Extracts the deepest module from the VCD path
        2. Uses slang-hier to find the corresponding Verilog module
        3. Calls locate_variable() to find the variable within that module

        Args:
            to: Target representation (VERILOG, CHISEL, or NETLIST)
            vcd_variable: Hierarchical VCD signal path (e.g., "top.cpu.alu.result")

        Returns:
            List of SourceLocation objects in target representation,
            sorted by confidence (highest first)
        """
        self._debug_print(f'locate_vcd() called: vcd_variable={vcd_variable}, to={to.value}')
        try:
            result = self._find_vcd_in_hierarchy(vcd_variable, to)
            self._debug_print(f'locate_vcd() returning {len(result)} location(s)')
            return result
        except Exception as e:
            self._error = f'VCD mapping failed: {e!s}'
            self._debug_print(f'locate_vcd() failed: {e!s}')
            return []

    def map_variable(
        self, to: RepresentationType, from_type: RepresentationType, variable: str, module: str
    ) -> List[SourceLocation]:
        """Map a variable from one representation to another (cross-representation mapping).

        Args:
            to: Target representation type
            from_type: Source representation type (must differ from 'to')
            variable: Variable name to map (supports regex patterns)
            module: Module/class name in source representation (case-insensitive match)

        Returns:
            List of SourceLocation objects in target representation,
            sorted by confidence (highest first)

        Supported mappings:
            - VERILOG ↔ CHISEL (using module_finder)
            - VERILOG ↔ NETLIST (TODO: requires synalign - currently returns error)
        """
        self._debug_print(f'map_variable() called: variable={variable}, from={from_type.value}, to={to.value}, module={module}')
        # Validate same-representation requests
        if to == from_type:
            self._error = 'same representation mapping not supported'
            return []

        # Check for synalign-dependent mappings
        if (
            (from_type == RepresentationType.VERILOG and to == RepresentationType.NETLIST)
            or (from_type == RepresentationType.NETLIST and to == RepresentationType.VERILOG)
            or (from_type == RepresentationType.NETLIST and to == RepresentationType.CHISEL)
            or (from_type == RepresentationType.CHISEL and to == RepresentationType.NETLIST)
        ):
            self._error = 'synalign not integrated'
            return []

        try:
            return self._find_variable_cross_representation(variable, from_type, to, module_hint=module)
        except Exception as e:
            self._error = f'Cross-representation mapping failed: {e!s}'
            return []

    def locate_variable(self, to: RepresentationType, variable: str, module: Optional[str] = None) -> List[SourceLocation]:
        """Find variable occurrences within a single representation (single-representation lookup).

        Args:
            to: Representation type to search in (VERILOG, CHISEL, or NETLIST)
            variable: Variable name or regex pattern to find
            module: Optional module/class name to constrain search (case-insensitive)
                   If None, searches across all modules in the profile's file list

        Returns:
            List of SourceLocation objects where variable is defined/assigned,
            sorted by confidence (highest first)
        """
        self._debug_print(f'locate_variable() called: variable={variable}, to={to.value}, module={module}')
        try:
            result = self._find_variable_in_files(variable, to, module_hint=module)
            self._debug_print(f'locate_variable() returning {len(result)} location(s)')
            return result
        except Exception as e:
            self._error = f'Variable lookup failed: {e!s}'
            self._debug_print(f'locate_variable() failed: {e!s}')
            return []

    def locate_code(self, to: RepresentationType, from_type: RepresentationType, diff_patch: str) -> List[SourceLocation]:
        """Map code changes (unified diff) from one representation to another.

        Args:
            to: Target representation type to map to
            from_type: Source representation type of the diff
            diff_patch: Unified diff string showing changes

        Returns:
            List of SourceLocation objects in target representation,
            sorted by confidence (highest first)
        """
        self._debug_print(f'locate_code() called: from={from_type.value}, to={to.value}, diff_length={len(diff_patch)}')
        # Validate same-representation requests
        if to == from_type:
            self._error = 'same representation mapping not supported'
            return []

        # Check for synalign-dependent mappings
        if (
            (from_type == RepresentationType.VERILOG and to == RepresentationType.NETLIST)
            or (from_type == RepresentationType.NETLIST and to == RepresentationType.VERILOG)
            or (from_type == RepresentationType.NETLIST and to == RepresentationType.CHISEL)
            or (from_type == RepresentationType.CHISEL and to == RepresentationType.NETLIST)
        ):
            self._error = 'synalign not integrated'
            return []

        try:
            result = self._map_diff_to_target(diff_patch, from_type, to)
            self._debug_print(f'locate_code() returning {len(result)} location(s)')
            return result
        except Exception as e:
            self._error = f'Code mapping failed: {e!s}'
            self._debug_print(f'locate_code() failed: {e!s}')
            return []

    def invalidate_cache(self, force: bool = False) -> None:
        """Invalidate cached data for the current profile.

        Args:
            force: If True, delete all cache regardless of validity
        """
        if not self._cache_dir:
            return

        if force:
            # Delete all cache files
            for cache_file in self._cache_dir.glob('*.cache'):
                cache_file.unlink()
            metadata_file = self._cache_dir / 'metadata.json'
            if metadata_file.exists():
                metadata_file.unlink()
        else:
            # Just delete metadata to force revalidation
            metadata_file = self._cache_dir / 'metadata.json'
            if metadata_file.exists():
                metadata_file.unlink()

    def get_error(self) -> str:
        """Get last error message following Tool pattern."""
        return self._error

    def cleanup(self) -> None:
        """Clean up resources (Builder, file handles, etc.)."""
        if self.builder:
            self.builder.cleanup()
            self.builder = None

    def __enter__(self):
        """Context manager entry."""
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        """Context manager exit."""
        self.cleanup()
        return False

    # Private methods

    def _load_profile_config(self) -> Optional[dict]:
        """Load and validate profile configuration from Builder."""
        if not self.builder:
            self._error = 'Builder not initialized'
            return None

        if not self.profile_name:
            self._error = 'Profile name not specified'
            return None

        try:
            # Get profile configuration from builder
            config = self.builder.config
            profiles = config.get('profiles', [])
            for profile in profiles:
                if profile.get('name') == self.profile_name:
                    return profile

            self._error = f"Profile '{self.profile_name}' not found in configuration"
            return None
        except Exception as e:
            self._error = f'Failed to load profile config: {e!s}'
            return None

    def _get_synthesis_command(self) -> Optional[dict]:
        """Extract synthesis/slang command info from profile configuration.

        Returns:
            Dict with 'command' and 'cwd' keys if found, None otherwise.
            Checks in order:
            1. Explicit slang-hier API entry (highest priority)
            2. Commands containing 'slang'
            3. Commands containing 'synth.rb'
            4. synthesize/compile APIs
        """
        if not self._profile_config:
            return None

        apis = self._profile_config.get('apis', [])

        # Priority 1: Look for explicit slang-hier API
        for api in apis:
            command = api.get('command', '')
            if 'slang-hier' in command:
                return {'command': command, 'cwd': api.get('cwd', '$HAGENT_REPO_DIR')}

        # Priority 2: Look for slang commands in synth-related APIs
        for api in apis:
            command = api.get('command', '')
            api_name = api.get('name', '')
            if 'slang' in command and ('synth' in api_name or api_name in ['synthesize', 'compile']):
                return {'command': command, 'cwd': api.get('cwd', '$HAGENT_REPO_DIR')}

        # Priority 3: Look for synth.py/synth.rb in commands (these support --dry-run)
        # Check command content, not API name - any API can use synth.py
        for api in apis:
            command = api.get('command', '')
            if 'synth.py' in command or 'synth.rb' in command:
                return {'command': command, 'cwd': api.get('cwd', '$HAGENT_REPO_DIR')}

        # Priority 4: Look for synthesize/compile/synth_* commands
        for api in apis:
            api_name = api.get('name', '')
            if api_name.startswith('synth') or api_name in ['synthesize', 'compile']:
                command = api.get('command', '')
                if command:
                    return {'command': command, 'cwd': api.get('cwd', '$HAGENT_REPO_DIR')}

        return None

    def _extract_slang_args_from_synth(self, command: str, cwd: str) -> Optional[str]:
        """Extract slang arguments from synth.py by running with --dry-run.

        Args:
            command: The synthesis command (e.g., synth.py ...)
            cwd: Working directory for the command

        Returns:
            Slang arguments string if successful, None otherwise
        """
        if 'synth.py' not in command and 'synth.rb' not in command:
            return None

        try:
            # Add --dry-run to the command to get slang arguments without running synthesis
            dry_run_cmd = f'{command} --dry-run'

            # Execute the dry-run command
            exit_code, stdout, stderr = self.builder.runner.run_cmd(dry_run_cmd, cwd=cwd, quiet=(not self.debug))

            if exit_code != 0:
                return None

            # Parse the output to extract "Slang arguments: ..." line
            for line in stdout.splitlines():
                if line.strip().startswith('Slang arguments:'):
                    # Extract everything after "Slang arguments:"
                    slang_args = line.split('Slang arguments:', 1)[1].strip()
                    return slang_args

            return None
        except Exception:
            return None

    def _extract_verilog_files_from_command(self, command: str) -> List[str]:
        """Extract Verilog file patterns from a synthesis/slang command.

        Looks for patterns like:
        - *.sv, *.v
        - build_dir/*.sv
        - specific file names ending in .v or .sv
        """
        # Extract tokens that look like Verilog files or patterns
        verilog_patterns = []

        # Match patterns like: *.sv, *.v, dir/*.sv, dir/*.v, file.v, file.sv
        tokens = command.split()
        for token in tokens:
            # Remove quotes
            token = token.strip('\'"')

            # Check if it's a Verilog file pattern or filename
            if token.endswith('.sv') or token.endswith('.v') or '*.sv' in token or '*.v' in token:
                # Expand environment variables if present
                if '$' in token:
                    # Simple expansion for common vars
                    token = token.replace('$HAGENT_BUILD_DIR', str(self.builder.runner.path_manager.build_dir))
                    token = token.replace('$HAGENT_REPO_DIR', str(self.builder.runner.path_manager.repo_dir))

                verilog_patterns.append(token)

        return verilog_patterns

    def _build_hierarchy_cache(self, target_type: Optional[RepresentationType] = None) -> dict:
        """Execute slang-hier and parse output into hierarchy mapping.

        Args:
            target_type: Optional target representation type (currently not used, kept for API compatibility)
        """
        self._debug_print(f'_build_hierarchy_cache() called')
        # Check cache first
        cached = self._load_cache('hierarchy')
        if cached is not None:
            self._debug_print(f'Using cached hierarchy with {len(cached)} entries')
            return cached

        if not self.builder:
            return {}

        self._debug_print(f'Building hierarchy cache (no cache found)')

        # Get synthesis command info from profile
        cmd_info = self._get_synthesis_command()
        slang_hier_cmd = None
        cwd = None

        if cmd_info:
            base_command = cmd_info['command']
            cwd = cmd_info['cwd']

            # Substitute template variables like {{top}} and {{top_synth}} with defaults from API options
            # Get the API definition to access option defaults
            apis = self._profile_config.get('apis', []) if self._profile_config else []
            synth_api = None
            for api in apis:
                if 'synth.py' in api.get('command', ''):
                    synth_api = api
                    break

            # Substitute template variables with their default values from options
            if synth_api and 'options' in synth_api:
                for option in synth_api['options']:
                    option_name = option.get('name', '')
                    default_value = option.get('default', '')
                    if option_name and default_value:
                        # Replace {{option_name}} with default value
                        base_command = base_command.replace(f'{{{{{option_name}}}}}', default_value)

            # Remove any remaining unsubstituted templates (empty optional params)
            import re as re_module

            base_command = re_module.sub(r'\{\{[^}]+\}\}', '', base_command)

            # Check if this is already a slang-hier command
            if 'slang-hier' in base_command:
                slang_hier_cmd = base_command
            else:
                # Always use RTL files from -F filelist.f for hierarchy
                # (works for both verilog and netlist targets)
                # Try to extract slang args from synth.py/synth.rb using --dry-run
                slang_args = self._extract_slang_args_from_synth(base_command, cwd)

                if slang_args:
                    # Use the slang arguments from synth.py --dry-run
                    slang_hier_cmd = f'slang-hier {slang_args}'
                else:
                    # Fallback: Extract Verilog file patterns from the command
                    verilog_patterns = self._extract_verilog_files_from_command(base_command)

                    if verilog_patterns:
                        # Construct slang-hier command using the same files
                        slang_hier_cmd = f'slang-hier {" ".join(verilog_patterns)}'

        # Fallback: construct default slang-hier command from build directory
        if not slang_hier_cmd:
            # Try to get output directory from profile config
            output_dir = None
            if self._profile_config:
                config = self._profile_config.get('configuration', {})
                output = config.get('output', '')
                # Parse track_build_dir('build_xxx', ext='.sv') pattern
                import re as re_module

                match = re_module.search(r"track_build_dir\('([^']+)'", output)
                if match:
                    output_dir = match.group(1)

            if output_dir:
                # Use profile-specific build directory to avoid conflicts
                # Exclude netlist.v to avoid redefinition errors with RTL
                slang_hier_cmd = f'slang-hier $(find {output_dir} -name "*.sv" -o \\( -name "*.v" -a ! -name "netlist.v" \\))'
                cwd = '$HAGENT_BUILD_DIR'
            else:
                # Fallback to all .sv files (safer than .v which might include netlists)
                slang_hier_cmd = 'slang-hier *.sv **/*.sv'
                cwd = '$HAGENT_BUILD_DIR'

        try:
            # Ensure --ignore-unknown-modules is present in slang-hier command
            # This is needed to handle technology-specific cells in netlists
            if '--ignore-unknown-modules' not in slang_hier_cmd:
                # Insert after 'slang-hier' command
                slang_hier_cmd = slang_hier_cmd.replace('slang-hier', 'slang-hier --ignore-unknown-modules', 1)

            # Use runner.run_cmd() to execute slang-hier (not run_api)
            # This ensures proper path handling and environment
            if not cwd:
                cwd = str(self.builder.runner.path_manager.repo_dir)

            # run_cmd returns (exit_code, stdout, stderr)
            # Use quiet based on debug flag
            self._debug_print(f'Running slang-hier command: {slang_hier_cmd}')
            self._debug_print(f'Working directory: {cwd}')
            exit_code, stdout, stderr = self.builder.runner.run_cmd(slang_hier_cmd, cwd=cwd, quiet=(not self.debug))

            if exit_code != 0:
                self._error = f'slang-hier failed (exit {exit_code}): {stderr}'
                self._debug_print(f'slang-hier failed with exit code {exit_code}')
                return {}

            # Parse hierarchy output
            hierarchy = self._parse_slang_hierarchy(stdout)
            self._debug_print(f'Parsed {len(hierarchy)} hierarchy entries')

            # Add metadata about how this cache was generated
            hierarchy['_metadata'] = {
                'slang_hier_command': slang_hier_cmd,
                'cwd': cwd,
                'profile': self.profile_name,
            }

            # Save to cache
            self._save_cache('hierarchy', hierarchy)

            return hierarchy
        except Exception as e:
            self._error = f'Failed to build hierarchy cache: {e!s}'
            return {}

    def _build_mapping_cache(self, from_type: RepresentationType, to_type: RepresentationType) -> dict:
        """Build mapping between two representations using module_finder or other tools.

        Supports:
        - VERILOG <-> CHISEL (using module_finder)
        - VERILOG <-> NETLIST (planned; currently raises "synalign not integrated")
        """
        cache_key = f'{from_type.value}_{to_type.value}'

        # Check cache first
        cached = self._load_cache(cache_key)
        if cached is not None:
            return cached

        mapping = {}

        # Handle Verilog <-> Chisel mapping
        if (from_type == RepresentationType.VERILOG and to_type == RepresentationType.CHISEL) or (
            from_type == RepresentationType.CHISEL and to_type == RepresentationType.VERILOG
        ):
            mapping = self._build_verilog_chisel_mapping()

        # Save to cache
        if mapping:
            self._save_cache(cache_key, mapping)

        return mapping

    def _build_verilog_chisel_mapping(self) -> dict:
        """Build Verilog <-> Chisel mapping using module_finder."""
        if not self.builder:
            return {}

        try:
            # Use builder's tracked files (works in both Docker and local modes)
            # The profile configuration already tracks repo and build directories
            chisel_files_set = self.builder.get_tracked_files(ext_filter='.scala')
            verilog_v_files = self.builder.get_tracked_files(ext_filter='.v')
            verilog_sv_files = self.builder.get_tracked_files(ext_filter='.sv')

            # Combine .v and .sv files, filter out netlist.v
            verilog_files = [Path(f) for f in (verilog_v_files | verilog_sv_files) if 'netlist.v' not in f]
            chisel_files = list(chisel_files_set)

            if not chisel_files or not verilog_files:
                return {}

            # Use module_finder to create mapping
            finder = Module_finder()
            mapping = {}

            # chisel_files is already a list of strings from get_tracked_files
            for verilog_file in verilog_files:
                # Extract module name from verilog file
                module_name = verilog_file.stem

                # Use find_modules with empty diff (we just want module name matching)
                hits = finder.find_modules(
                    scala_files=chisel_files,
                    verilog_module=module_name,
                    verilog_diff='',  # Empty diff means just match by module name
                )

                if hits:
                    # Extract unique file names from hits
                    matched_files = list(set(hit.file_name for hit in hits))
                    mapping[str(verilog_file)] = {
                        'chisel_files': matched_files,
                        'module_name': module_name,
                    }

            return mapping
        except Exception as e:
            self._error = f'Failed to build Verilog-Chisel mapping: {e!s}'
            return {}

    def _load_cache(self, cache_type: str) -> Optional[dict]:
        """Load cache file if valid, None otherwise."""
        if not self._cache_dir or not self.builder:
            return None

        cache_file = self._cache_dir / f'{cache_type}.cache'

        # Check if file exists and read using filesystem
        try:
            content = self.builder.filesystem.read_text(str(cache_file))
            if content is None:
                return None
        except Exception:
            return None

        if not self._is_cache_valid(cache_type):
            return None

        try:
            return json.loads(content)
        except Exception:
            # Cache corrupted, return None to rebuild
            return None

    def _save_cache(self, cache_type: str, data: dict) -> None:
        """Save cache data with metadata."""
        if not self._cache_dir or not self.builder:
            return

        cache_file = self._cache_dir / f'{cache_type}.cache'

        try:
            # Write cache using filesystem (works in both Docker and local modes)
            content = json.dumps(data, indent=2)
            self.builder.filesystem.write_text(str(cache_file), content)

            # Update metadata
            self._update_metadata(cache_type)
        except Exception as e:
            self._error = f'Failed to save cache: {e!s}'

    def _is_cache_valid(self, cache_type: str) -> bool:
        """Check if cache is valid based on file mtimes.

        Note: File mtime validation is disabled in Docker mode as it's complex
        to check mtimes across Docker boundary. Cache is always considered valid
        if it exists in Docker mode.
        """
        if not self._cache_dir or not self.builder:
            return False

        metadata_file = self._cache_dir / 'metadata.json'

        # Check if metadata exists using filesystem
        if not self.builder.filesystem.exists(str(metadata_file)):
            return False

        try:
            content = self.builder.filesystem.read_text(str(metadata_file))
            metadata = json.loads(content)

            cache_metadata = metadata.get(cache_type, {})
            if not cache_metadata:
                return False

            # TODO: File mtime validation disabled for Docker mode
            # Would need to implement stat() in filesystem API
            # For now, just check if metadata exists
            return True
        except Exception:
            return False

    def _update_metadata(self, cache_type: str) -> None:
        """Update metadata for cache type.

        Note: File tracking is simplified in Docker mode - we just record
        that the cache exists but don't track individual file mtimes.
        """
        if not self._cache_dir or not self.builder:
            return

        metadata_file = self._cache_dir / 'metadata.json'

        # Load existing metadata
        metadata = {}
        if self.builder.filesystem.exists(str(metadata_file)):
            try:
                content = self.builder.filesystem.read_text(str(metadata_file))
                metadata = json.loads(content)
            except Exception:
                metadata = {}

        # Simplified metadata - just record that cache was created
        # TODO: Add proper file tracking using filesystem API when needed
        import time

        metadata[cache_type] = {
            'files': {},  # File tracking disabled for Docker compatibility
            'timestamp': time.time(),
        }

        # Save metadata
        try:
            content = json.dumps(metadata, indent=2)
            self.builder.filesystem.write_text(str(metadata_file), content)
        except Exception as e:
            self._error = f'Failed to update metadata: {e!s}'

    def _find_matching_class_ranges(self, lines: List[str], module_name: str) -> List[tuple]:
        """Find class/object definitions that match module_name.

        Returns:
            List of tuples (start_line, end_line, class_name) in 1-indexed line numbers
        """
        ranges = []
        class_pattern = re.compile(r'^\s*class\s+(\w+)')
        object_pattern = re.compile(r'^\s*object\s+(\w+)')

        for i, line in enumerate(lines, 1):
            # Check for class or object definition
            class_match = class_pattern.match(line)
            object_match = object_pattern.match(line)

            match = class_match or object_match
            if not match:
                continue

            class_name = match.group(1)

            # Check if class name matches module name (case-insensitive)
            if class_name.lower() != module_name.lower():
                continue

            # Find the end of this class/object
            end_line = self._find_class_end(lines, i - 1)  # Convert to 0-indexed

            ranges.append((i, end_line, class_name))

        return ranges

    def _find_class_end(self, lines: List[str], start_idx: int) -> int:
        """Find the end line of a class by matching braces using Code_scope.

        Args:
            lines: List of source lines
            start_idx: 0-indexed start line

        Returns:
            1-indexed end line number
        """
        if start_idx >= len(lines):
            return start_idx + 1

        # Use Code_scope for better scope parsing (handles comments, strings, etc.)
        try:
            code_text = '\n'.join(lines)
            scope_parser = Code_scope(code_text, line_limit=1000)  # Large limit for classes

            # Find scopes that contain or start at this line
            for start, end in scope_parser.scopes:
                if start == start_idx:
                    return end + 1  # Convert to 1-indexed

            # If Code_scope didn't find it, fall back to simple brace matching
            return self._simple_brace_match(lines, start_idx)
        except Exception:
            # Fall back if Code_scope fails
            return self._simple_brace_match(lines, start_idx)

    def _simple_brace_match(self, lines: List[str], start_idx: int) -> int:
        """Simple fallback for brace matching without Code_scope.

        Args:
            lines: List of source lines
            start_idx: 0-indexed start line

        Returns:
            1-indexed end line number
        """
        brace_count = 0
        found_opening = False

        for i in range(start_idx, len(lines)):
            line = lines[i]

            # Count braces (simplified - doesn't handle strings/comments)
            for char in line:
                if char == '{':
                    brace_count += 1
                    found_opening = True
                elif char == '}':
                    brace_count -= 1

            # If we've found the opening and returned to balance, we're done
            if found_opening and brace_count == 0:
                return i + 1  # Convert to 1-indexed

        # If we couldn't find the end, return a reasonable estimate
        return min(start_idx + 100, len(lines))

    def _is_comment_line(self, line: str) -> bool:
        """Check if a line is a comment (Scala/Chisel style).

        Handles:
        - // single-line comments
        - /* */ block comments (simplified - only checks if line starts with /*)
        - /** */ doc comments
        """
        stripped = line.strip()

        # Empty lines
        if not stripped:
            return False

        # Single-line comment
        if stripped.startswith('//'):
            return True

        # Block comment start (simplified check)
        if stripped.startswith('/*') or stripped.startswith('/**'):
            return True

        # Line that's part of a multi-line comment (starts with *)
        if stripped.startswith('*'):
            return True

        return False

    def _build_variable_regex(self, variable: str, for_verilog: bool = False) -> str:
        """Build a flexible regex pattern to match variable names with transformations.

        Handles common name transformations between Chisel and Verilog:
        - io_ prefix (Chisel adds to IO variables)
        - Optional underscore prefixes/suffixes (some compilers add these)
        - Bus expansions (foo → foo_33_)
        - Common suffixes (_bits, _valid, _ready, _data, _addr, _q, _d)
        - Array indexing patterns

        Args:
            variable: Base variable name to search for
            for_verilog: If True, generate pattern for Verilog (more permissive)

        Returns:
            Regex pattern string
        """
        # For Chisel: strip io_ prefix if present (Chisel defines 'aluop', Verilog has 'io_aluop')
        search_var = variable
        if not for_verilog and variable.startswith('io_'):
            search_var = variable[3:]  # Strip 'io_' for Chisel search

        # Escape special regex characters in the base variable name
        escaped_var = re.escape(search_var)

        if for_verilog:
            # Verilog pattern: handle io_ prefix, underscores, bus expansions, suffixes
            # Pattern explanation:
            # (?<!\w)           - Not preceded by word char (word boundary)
            # (?:io_)?          - Optional io_ prefix
            # (?:\w*_)?         - Optional prefix with underscore (e.g., _foo, tmp_foo)
            # {escaped_var}     - The actual variable name
            # (?:_(?:bits|valid|ready|data|addr|q|d|\d+))* - Optional suffixes
            # (?!\w)            - Not followed by word char (word boundary)
            pattern = rf'(?<!\w)(?:io_)?(?:\w*_)?{escaped_var}(?:_(?:bits|valid|ready|data|addr|q|d|\d+))*(?!\w)'
        else:
            # Chisel pattern: handle Chisel naming conventions
            # Matches variations like:
            # - aluop (variable name)
            # - io.aluop (IO reference)
            # - io_aluop (if searching with Verilog name)
            # - _aluop (internal signals)
            #
            # Pattern: match the variable with optional prefixes and dot notation
            # (?<!\w)           - Not preceded by word char
            # (?:io[_.])?       - Optional io_ or io. prefix
            # (?:\w*_)?         - Optional prefix with underscore
            # {escaped_var}     - The actual variable name
            # (?!\w)            - Not followed by word char (word boundary)
            pattern = rf'(?<!\w)(?:io[_.])?(?:\w*_)?{escaped_var}(?!\w)'

        return pattern

    def _parse_slang_hierarchy(self, slang_output: str) -> dict:
        """Parse slang-hier output into hierarchical mapping.

        Handles two formats:
        1. JSON format (if slang-hier outputs JSON)
        2. Text format: Module="Name" Instance="path.to.instance" File="file.sv"
        """
        try:
            # Try to parse as JSON first
            hierarchy = json.loads(slang_output)
            return hierarchy
        except json.JSONDecodeError:
            # Parse text format output from slang-hier
            # Example line: Module="ALUControl" Instance="PipelinedDualIssueCPU.pipeB_aluControl" File="build_pipelined_d/ALUControl.sv"
            hierarchy = {}

            for line in slang_output.splitlines():
                line = line.strip()
                if not line or line.startswith('#') or line.startswith('Top level') or line.startswith('Build succeeded'):
                    continue

                # Extract Module, Instance, and File using regex
                module_match = re.search(r'Module="([^"]+)"', line)
                instance_match = re.search(r'Instance="([^"]+)"', line)
                file_match = re.search(r'File="([^"]+)"', line)

                if module_match and instance_match and file_match:
                    module_name = module_match.group(1)
                    instance_path = instance_match.group(1)
                    file_path = file_match.group(1)

                    # Store in hierarchy dict with instance path as key
                    hierarchy[instance_path] = {
                        'module': module_name,
                        'file': file_path,
                        'instance': instance_path,
                    }

            return hierarchy

    def _find_vcd_in_hierarchy(self, hier_path: str, target_type: RepresentationType) -> List[SourceLocation]:
        """Match VCD hierarchical path against slang hierarchy to find source locations.

        Supports:
        1. Full hierarchy path: "PipelinedDualIssueCPU.pipeB_aluControl.io_aluop"
        2. Profile name substitution: "pipelined_d.pipeB_aluControl.io_aluop" → auto-replace with top module
        3. Partial hierarchy suffix: "pipeB_aluControl.io_aluop" → matches any instance ending with pipeB_aluControl
        4. Case-insensitive matching: "gcd.x" matches "GCD" module
        """
        self._debug_print(f'_find_vcd_in_hierarchy() called: hier_path={hier_path}, target={target_type.value}')
        hierarchy = self._build_hierarchy_cache(target_type=target_type)
        if not hierarchy:
            self._debug_print(f'No hierarchy cache available')
            return []

        # Extract variable name from hierarchical path (last component)
        parts = hier_path.split('.')
        var_name = parts[-1] if parts else hier_path

        # Extract module hierarchy (all but last component)
        # e.g., "top.cpu.alu.result" → "top.cpu.alu"
        module_path = '.'.join(parts[:-1]) if len(parts) > 1 else ''
        self._debug_print(f'Extracted variable={var_name}, module_path={module_path}')

        # Try to find matching hierarchy entries
        matching_entries = []

        if module_path:
            # Strategy 1: Exact match (case-sensitive first for performance)
            if module_path in hierarchy:
                matching_entries.append(hierarchy[module_path])
            # Strategy 1b: Case-insensitive exact match
            elif not matching_entries:
                module_path_lower = module_path.lower()
                for inst_path, info in hierarchy.items():
                    if inst_path.lower() == module_path_lower:
                        matching_entries.append(info)
                        break
            else:
                # Strategy 2: Replace first component with actual top module if it matches profile name
                first_component = parts[0] if parts else ''
                if first_component == self.profile_name:
                    # Find the actual top module from hierarchy
                    for instance_path, info in hierarchy.items():
                        if '.' not in instance_path:  # Top-level module
                            actual_top = instance_path
                            # Replace profile name with actual top module
                            new_module_path = actual_top + '.' + '.'.join(parts[1:-1])
                            if new_module_path in hierarchy:
                                matching_entries.append(hierarchy[new_module_path])
                            break

                # Strategy 3: Hierarchical suffix matching
                # Match if module_path is a suffix of any hierarchy instance
                if not matching_entries:
                    for instance_path, info in hierarchy.items():
                        if instance_path.endswith('.' + module_path) or instance_path == module_path:
                            matching_entries.append(info)

        # Also check if full path (without variable) is in hierarchy
        if hier_path in hierarchy:
            matching_entries.append(hierarchy[hier_path])

        if not matching_entries:
            # No matches found
            self._debug_print(f'No matching hierarchy entries found for {module_path}')
            return []

        self._debug_print(f'Found {len(matching_entries)} matching hierarchy entries')
        for entry in matching_entries:
            self._debug_print(f'  - Module: {entry.get("module", "?")}, File: {entry.get("file", "?")}')

        # Search in all matching files
        locations = []
        seen_files = set()  # Avoid duplicate searches in same file

        # For NETLIST target: search for escaped identifier in netlist file
        if target_type == RepresentationType.NETLIST:
            # In flat netlists, hierarchical signals use escaped identifiers
            # Example: PipelinedCPU.aluControl.io_aluop → \aluControl.io_aluop
            # (backslash prefix, space suffix, without top module)

            # Get netlist file path from synth.py command
            cmd_info = self._get_synthesis_command()
            if cmd_info:
                base_command = cmd_info['command']
                # Substitute templates
                apis = self._profile_config.get('apis', []) if self._profile_config else []
                for api in apis:
                    if 'synth.py' in api.get('command', ''):
                        if 'options' in api:
                            for option in api['options']:
                                option_name = option.get('name', '')
                                default_value = option.get('default', '')
                                if option_name and default_value:
                                    base_command = base_command.replace(f'{{{{{option_name}}}}}', default_value)
                        break

                # Extract netlist path
                import re as re_module

                netlist_match = re_module.search(r'--netlist\s+(\S+)', base_command)
                if netlist_match:
                    netlist_file = netlist_match.group(1)

                    # Construct escaped identifier pattern from hierarchical path
                    # Remove top module from path: PipelinedCPU.aluControl.io_aluop → aluControl.io_aluop
                    hierarchical_name = '.'.join(parts[1:]) if len(parts) > 1 else var_name

                    # Search for escaped identifier: \aluControl.io_aluop (with space after)
                    # Escaped identifiers in Verilog: backslash + name + space
                    escaped_pattern = f'\\\\{re_module.escape(hierarchical_name)}\\s'

                    # Search directly in netlist file (inline to avoid regex transformation)
                    netlist_path = Path(self.builder.runner.path_manager.build_dir) / netlist_file
                    try:
                        content = self.builder.filesystem.read_text(str(netlist_path))
                        if content:
                            lines = content.splitlines()
                            for i, line in enumerate(lines, 1):
                                if re_module.search(escaped_pattern, line):
                                    locations.append(
                                        SourceLocation(
                                            file_path=str(netlist_path),
                                            module_name='',
                                            line_start=i,
                                            line_end=i,
                                            confidence=1.0,
                                            representation=target_type,
                                        )
                                    )
                    except Exception:
                        pass

        # For Chisel target: first find Verilog locations, then map to Chisel
        elif target_type == RepresentationType.CHISEL:
            # Step 1: Find variable in Verilog files from hierarchy
            verilog_files_with_var = set()

            for module_info in matching_entries:
                module_name = module_info.get('module', '')
                file_path = module_info.get('file', '')

                if not file_path or file_path in seen_files:
                    continue

                seen_files.add(file_path)

                # Find variable in this specific Verilog file
                verilog_locs = self._find_variable_in_specific_file(
                    variable=var_name, file_path=file_path, module_name=module_name, representation=RepresentationType.VERILOG
                )

                if verilog_locs:
                    # Track which Verilog files have this variable
                    verilog_files_with_var.add(file_path)

            # Step 2: Map each Verilog file to target representation
            seen_target_files = set()

            for verilog_file_path in verilog_files_with_var:
                # Use Module_finder to map this specific Verilog file to Chisel
                chisel_file = self._map_verilog_file_to_chisel(verilog_file_path)

                if chisel_file and chisel_file not in seen_target_files:
                    seen_target_files.add(chisel_file)

                    # Search for variable in the mapped Chisel file
                    # The regex pattern in _build_variable_regex handles name variations
                    chisel_locs = self._find_variable_in_specific_file(
                        variable=var_name,
                        file_path=chisel_file,
                        module_name='',  # Module name not critical for Chisel
                        representation=target_type,
                    )
                    locations.extend(chisel_locs)

        else:
            # For Verilog target: search directly in hierarchy files
            for module_info in matching_entries:
                module_name = module_info.get('module', '')
                file_path = module_info.get('file', '')

                if not file_path or file_path in seen_files:
                    continue

                seen_files.add(file_path)

                file_locations = self._find_variable_in_specific_file(
                    variable=var_name, file_path=file_path, module_name=module_name, representation=RepresentationType.VERILOG
                )
                locations.extend(file_locations)

        return locations

    def _find_variable_cross_representation(
        self,
        variable: str,
        from_type: RepresentationType,
        to_type: RepresentationType,
        module_hint: Optional[str] = None,
    ) -> List[SourceLocation]:
        """Find variable across Verilog-Chisel representations.

        Algorithm:
        1. Find variable in source representation (from_type)
        2. Map source file to target representation files
        3. Search for variable in target files
        """
        mapping = self._build_mapping_cache(from_type, to_type)
        if not mapping:
            return []

        locations = []

        # Determine source and target based on from_type
        if from_type == RepresentationType.VERILOG:
            # Verilog -> Chisel
            for verilog_file, mapping_info in mapping.items():
                chisel_files = mapping_info.get('chisel_files', [])
                module_name = mapping_info.get('module_name', '')

                # Filter by module hint if provided
                if module_hint and module_name.lower() != module_hint.lower():
                    continue

                # Step 1: Verify variable exists in Verilog file (source)
                verilog_locs = self._find_variable_in_specific_file(
                    variable=variable,
                    file_path=verilog_file,
                    module_name=module_name,
                    representation=from_type,
                )

                if not verilog_locs:
                    # Variable not found in source Verilog file, skip this mapping
                    continue

                # Step 2 & 3: Variable found in Verilog, now search in mapped Chisel files
                for chisel_file in chisel_files:
                    chisel_path = Path(chisel_file)

                    # Search for variable in file, within the matching class/module
                    # Use filesystem API for reading (works in both Docker and local)
                    try:
                        content = self.builder.filesystem.read_text(str(chisel_path))
                        if not content:
                            continue
                        lines = content.splitlines()

                        # Find the class that matches the module name
                        class_ranges = self._find_matching_class_ranges(lines, module_name)

                        if not class_ranges:
                            continue

                        # Build flexible regex pattern (Chisel pattern - simpler)
                        pattern = self._build_variable_regex(variable, for_verilog=False)
                        for start_line, end_line, class_name in class_ranges:
                            for i in range(start_line, end_line + 1):
                                if i > len(lines):
                                    break
                                line = lines[i - 1]  # Convert to 0-indexed

                                # Skip comments
                                if self._is_comment_line(line):
                                    continue

                                if re.search(pattern, line):
                                    locations.append(
                                        SourceLocation(
                                            file_path=str(chisel_path),
                                            module_name=class_name,
                                            line_start=i,
                                            line_end=i,
                                            confidence=0.85,
                                            representation=to_type,
                                        )
                                    )
                    except Exception:
                        continue

        elif from_type == RepresentationType.CHISEL:
            # Chisel -> Verilog (reverse mapping)
            # TODO: Implement if needed
            pass

        return locations

    def _map_verilog_file_to_chisel(self, verilog_file_path: str) -> Optional[str]:
        """Map a Verilog file to its corresponding Chisel source file.

        Args:
            verilog_file_path: Relative Verilog file path (e.g., "build_pipelined_d/ALUControl.sv")

        Returns:
            Relative Chisel file path or None if not found
        """
        if not self.builder or not self._profile_config:
            return None

        try:
            # Get Chisel directories from profile config
            config = self._profile_config.get('configuration', {})
            source_spec = config.get('source', '')

            # Parse source directory from track_repo_dir('src/main/scala', ext='.scala')
            match = re.search(r"track_repo_dir\('([^']+)'", source_spec)
            if not match:
                return None

            chisel_dir = match.group(1)
            chisel_full_dir = Path(self.builder.runner.path_manager.repo_dir) / chisel_dir

            if not chisel_full_dir.exists():
                return None

            # Extract module name from Verilog file
            module_name = verilog_file_path.split('/')[-1].replace('.sv', '').replace('.v', '')

            # Search for Chisel file with similar name (case-insensitive)
            for chisel_file in chisel_full_dir.rglob('*.scala'):
                if module_name.lower() in chisel_file.stem.lower():
                    # Return relative path from repo_dir
                    return str(chisel_file.relative_to(self.builder.runner.path_manager.repo_dir))

            return None
        except Exception:
            return None

    def _find_variable_in_specific_file(
        self, variable: str, file_path: str, module_name: str, representation: RepresentationType
    ) -> List[SourceLocation]:
        """Find variable in a specific file (used when hierarchy specifies exact file).

        Args:
            variable: Variable name to search for
            file_path: Specific file to search (relative to build/repo dir)
            module_name: Module name for the result
            representation: Representation type

        Returns:
            List of SourceLocation objects
        """
        if not self.builder:
            return []

        locations = []

        # Construct full path based on representation type
        if representation == RepresentationType.VERILOG or representation == RepresentationType.NETLIST:
            # Verilog files are relative to build_dir
            base_dir = Path(self.builder.runner.path_manager.build_dir)
        else:
            # Chisel files are relative to repo_dir
            base_dir = Path(self.builder.runner.path_manager.repo_dir)

        full_path = base_dir / file_path
        self._debug_print(f'Searching for variable "{variable}" in file: {full_path}')

        # Read file using filesystem API (works in both Docker and local modes)
        try:
            content = self.builder.filesystem.read_text(str(full_path))
            if not content:
                return []
            lines = content.splitlines()

            # Build flexible pattern based on representation type
            pattern = self._build_variable_regex(variable, for_verilog=(representation == RepresentationType.VERILOG))

            for i, line in enumerate(lines, 1):
                # Skip comments for Chisel
                if representation == RepresentationType.CHISEL and self._is_comment_line(line):
                    continue

                if re.search(pattern, line):
                    locations.append(
                        SourceLocation(
                            file_path=str(full_path),
                            module_name=module_name,
                            line_start=i,
                            line_end=i,
                            confidence=1.0,  # High confidence since from hierarchy
                            representation=representation,
                        )
                    )
            if locations:
                self._debug_print(f'  Found {len(locations)} match(es) in {full_path}')
        except Exception as e:
            self._debug_print(f'  Error reading file {full_path}: {e}')
            return []

        return locations

    def _find_variable_in_files(
        self, variable: str, representation: RepresentationType, module_hint: Optional[str] = None
    ) -> List[SourceLocation]:
        """Find where a variable is defined/assigned within files of given representation.

        Args:
            variable: Variable name or regex pattern to search for
            representation: Representation type to search in
            module_hint: Optional module/class name filter (case-insensitive)

        Returns:
            List of SourceLocation objects sorted by confidence
        """
        self._debug_print(
            f'_find_variable_in_files() called: variable={variable}, representation={representation.value}, module_hint={module_hint}'
        )
        if not self.builder:
            return []

        locations = []

        # Determine search directory and file extension
        if representation == RepresentationType.CHISEL:
            search_dir = Path(self.builder.runner.path_manager.repo_dir)
            extensions = ['*.scala']
        elif representation == RepresentationType.VERILOG:
            search_dir = Path(self.builder.runner.path_manager.build_dir)
            extensions = ['*.v', '*.sv']
        else:
            return []

        self._debug_print(f'Searching in directory: {search_dir} with extensions: {extensions}')

        # Search for variable in files
        for ext in extensions:
            for file_path in search_dir.glob(f'**/{ext}'):
                try:
                    with file_path.open('r') as f:
                        content = f.read()
                        lines = content.splitlines()

                    # For Chisel, use class-based filtering
                    if representation == RepresentationType.CHISEL and module_hint:
                        # Find matching classes
                        class_ranges = self._find_matching_class_ranges(lines, module_hint)

                        if not class_ranges:
                            continue

                        # Build flexible pattern for Chisel (simpler word boundary)
                        pattern = self._build_variable_regex(variable, for_verilog=False)
                        for start_line, end_line, class_name in class_ranges:
                            for i in range(start_line, end_line + 1):
                                if i > len(lines):
                                    break
                                line = lines[i - 1]  # Convert to 0-indexed

                                # Skip comments
                                if self._is_comment_line(line):
                                    continue

                                if re.search(pattern, line):
                                    locations.append(
                                        SourceLocation(
                                            file_path=str(file_path),
                                            module_name=class_name,
                                            line_start=i,
                                            line_end=i,
                                            confidence=0.90,
                                            representation=representation,
                                        )
                                    )
                    else:
                        # For Verilog or Chisel without module_hint, search entire file
                        # Try to extract module/class name from file
                        if representation == RepresentationType.VERILOG:
                            module_match = re.search(r'module\s+(\w+)', content)
                            module_name = module_match.group(1) if module_match else file_path.stem
                        else:
                            # Chisel: try to find first class
                            class_match = re.search(r'class\s+(\w+)', content)
                            module_name = class_match.group(1) if class_match else file_path.stem

                        # Filter by module_hint if provided (case-insensitive)
                        if module_hint and module_name.lower() != module_hint.lower():
                            continue

                        # Build flexible pattern based on representation type
                        # For Verilog, use permissive pattern to handle name transformations
                        pattern = self._build_variable_regex(variable, for_verilog=(representation == RepresentationType.VERILOG))
                        for i, line in enumerate(lines, 1):
                            # Skip comments for Chisel
                            if representation == RepresentationType.CHISEL and self._is_comment_line(line):
                                continue

                            if re.search(pattern, line):
                                locations.append(
                                    SourceLocation(
                                        file_path=str(file_path),
                                        module_name=module_name,
                                        line_start=i,
                                        line_end=i,
                                        confidence=0.85 if module_hint else 0.75,
                                        representation=representation,
                                    )
                                )
                except Exception:
                    continue

        # Sort by confidence
        locations.sort(key=lambda x: x.confidence, reverse=True)

        self._debug_print(f'_find_variable_in_files() found {len(locations)} total location(s)')
        return locations

    def _map_diff_to_target(
        self, diff_patch: str, from_type: RepresentationType, to_type: RepresentationType
    ) -> List[SourceLocation]:
        """Map diff changes from one representation to another."""
        # Extract file and changed lines from diff
        file_info = self._parse_diff_header(diff_patch)
        if not file_info:
            return []

        file_path = file_info['file']
        changed_lines = file_info['changed_lines']

        # Get module name from file
        module_name = Path(file_path).stem

        # If mapping Verilog -> Chisel
        if from_type == RepresentationType.VERILOG and to_type == RepresentationType.CHISEL:
            mapping = self._build_mapping_cache(from_type, to_type)

            # Find Chisel files for this Verilog module
            for verilog_file, mapping_info in mapping.items():
                if Path(verilog_file).stem == module_name:
                    chisel_files = mapping_info.get('chisel_files', [])

                    locations = []
                    for chisel_file in chisel_files:
                        # Estimate line range in Chisel (heuristic)
                        # This is a simplified approach - could be improved with better mapping
                        chisel_path = Path(chisel_file)
                        if chisel_path.exists():
                            try:
                                with chisel_path.open('r') as f:
                                    total_lines = len(f.readlines())

                                # Heuristic: assume similar relative position in file
                                locations.append(
                                    SourceLocation(
                                        file_path=str(chisel_path),
                                        module_name=module_name,
                                        line_start=max(1, changed_lines[0] - 10),
                                        line_end=min(total_lines, changed_lines[-1] + 10),
                                        confidence=0.70,
                                        representation=RepresentationType.CHISEL,
                                    )
                                )
                            except Exception:
                                continue

                    return locations

        return []

    def _parse_diff_header(self, diff_patch: str) -> Optional[dict]:
        """Parse unified diff to extract file and changed lines."""
        lines = diff_patch.splitlines()

        file_path = None
        changed_lines = []

        for line in lines:
            # Extract file from +++ header
            if line.startswith('+++'):
                match = re.match(r'\+\+\+ [ab]/(.+)', line)
                if match:
                    file_path = match.group(1)

            # Extract changed line numbers from @@ headers
            if line.startswith('@@'):
                match = re.match(r'@@ -\d+,?\d* \+(\d+),?(\d*) @@', line)
                if match:
                    start_line = int(match.group(1))
                    num_lines = int(match.group(2)) if match.group(2) else 1
                    changed_lines.extend(range(start_line, start_line + num_lines))

        if not file_path or not changed_lines:
            return None

        return {'file': file_path, 'changed_lines': changed_lines}
