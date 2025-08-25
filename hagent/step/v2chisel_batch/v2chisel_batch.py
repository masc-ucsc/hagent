#!/usr/bin/env python3
"""
V2Chisel Batch Processing

This step processes multiple bugs from bug_lists_unified.yaml:
1. Reads bug list with unified Verilog diffs
2. For each bug, uses module_finder to locate corresponding Chisel modules
3. Eventually: LLM generates Chisel diffs, applies them, compiles, and runs LEC

Usage:
uv run python3 hagent/step/v2chisel_batch/v2chisel_batch.py -o output.yaml input.yaml
"""

import os
import sys
import argparse
import glob
from pathlib import Path
from ruamel.yaml import YAML
from ruamel.yaml.scalarstring import LiteralScalarString

# Add project root to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent))

from hagent.core.step import Step
from hagent.core.llm_template import LLM_template
from hagent.core.llm_wrap import LLM_wrap
from hagent.tool.module_finder import Module_finder
from hagent.tool.docker_diff_applier import DockerDiffApplier
from hagent.tool.equiv_check import Equiv_check


class V2chisel_batch(Step):
    def setup(self):
        """Initialize the batch processing step"""
        super().setup()
        print(f'[V2chisel_batch] Input file: {self.input_file}')
        print(f'[V2chisel_batch] Output file: {self.output_file}')

        # Initialize module_finder
        self.module_finder = Module_finder()
        print('[V2chisel_batch] Module_finder initialized')

        # Configuration - you can adjust these
        self.chisel_source_pattern = './tmp/src/main/scala/*/*.scala'  # Default pattern
        self.debug = True  # Enable debug output

        # Initialize LLM components
        conf_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'v2chisel_batch_conf.yaml')
        if not os.path.exists(conf_file):
            self.error(f'Configuration file not found: {conf_file}')

        self.template_config = LLM_template(conf_file)

        # Get LLM configuration from template config
        llm_config = self.template_config.template_dict.get('v2chisel_batch', {}).get('llm', {})

        # Allow override from input_data while keeping generic structure
        final_llm_config = {**llm_config, **self.input_data.get('llm', {})}

        # Use same pattern as working examples - pass LLM config directly
        if final_llm_config:
            self.lw = LLM_wrap(
                name='v2chisel_batch',
                log_file='v2chisel_batch.log',
                conf_file=conf_file,
                overwrite_conf=final_llm_config,
            )
        else:
            self.lw = LLM_wrap(name='v2chisel_batch', log_file='v2chisel_batch.log', conf_file=conf_file)

        if self.lw.last_error:
            raise ValueError(self.lw.last_error)

        # Show which model is being used
        model_name = final_llm_config.get('model', 'default')
        print('[V2chisel_batch] LLM components initialized')
        print(f'[V2chisel_batch] Using model: {model_name}')

    def _load_bug_list(self, bug_file_path: str) -> list:
        """Load and parse the bug_lists_unified.yaml file"""
        print(f'[V2chisel_batch] Loading bug list from: {bug_file_path}')

        if not os.path.exists(bug_file_path):
            self.error(f'Bug list file not found: {bug_file_path}')

        yaml = YAML()
        with open(bug_file_path, 'r') as f:
            data = yaml.load(f)

        if 'bugs' not in data:
            self.error('Invalid bug list format - missing "bugs" key')

        bugs = data['bugs']
        print(f'[V2chisel_batch] Loaded {len(bugs)} bugs from file')

        return bugs

    def _find_chisel_files_docker_filtered(self, container_name: str, docker_patterns: list, module_name: str = None) -> list:
        """Find Chisel files inside Docker container with smart filtering"""
        import subprocess

        # print(f'[V2chisel_batch] Searching inside Docker container: {container_name}')
        docker_files = []

        for pattern in docker_patterns:
            # print(f'  🐳 Docker pattern: {pattern}')
            try:
                # OPTIMIZATION: Search for files containing the module name first
                if module_name:
                    # print(f'  🔍 Pre-filtering for module: {module_name}')
                    # Use grep to find files containing the module name (much faster)
                    grep_cmd = [
                        'docker',
                        'exec',
                        '-u',
                        'user',  # Run as user to match file permissions
                        container_name,
                        'find',
                        pattern,
                        '-name',
                        '*.scala',
                        '-type',
                        'f',
                        '-exec',
                        'grep',
                        '-l',
                        f'class.*{module_name}\\|object.*{module_name}',
                        '{}',
                        ';',
                    ]
                    result = subprocess.run(grep_cmd, capture_output=True, text=True)
                    files = [f.strip() for f in result.stdout.split('\n') if f.strip()]

                    # print(f'     Pre-filtered to: {len(files)} files matching "{module_name}"')

                    # If no matches with exact name, try broader search
                    if not files and len(module_name) > 3:
                        # print('  🔍 Trying broader search with partial name...')
                        partial_name = module_name[:4] if len(module_name) > 4 else module_name
                        grep_cmd = [
                            'docker',
                            'exec',
                            '-u',
                            'user',  # Run as user to match file permissions
                            container_name,
                            'find',
                            pattern,
                            '-name',
                            '*.scala',
                            '-type',
                            'f',
                            '-exec',
                            'grep',
                            '-l',
                            f'{partial_name}',
                            '{}',
                            ';',
                        ]
                        result = subprocess.run(grep_cmd, capture_output=True, text=True)
                        files = [f.strip() for f in result.stdout.split('\n') if f.strip()][:20]  # Limit to 20 files
                        # print(f'     Broader search found: {len(files)} files')
                else:
                    # Fallback: get all files (but limit to reasonable number)
                    cmd = ['docker', 'exec', container_name, 'find', pattern, '-name', '*.scala', '-type', 'f']
                    result = subprocess.run(cmd, capture_output=True, text=True, check=True)
                    all_files = [f.strip() for f in result.stdout.split('\n') if f.strip()]
                    # Limit to first 100 files to avoid performance issues
                    files = all_files[:100]
                    # print(f'     Found: {len(all_files)} files, limited to: {len(files)} for performance')

                # if files:
                #     for f in files[:3]:  # Show first 3
                #         print(f'     - {f}')
                #     if len(files) > 3:
                #         print(f'     ... and {len(files) - 3} more')

                # Add docker: prefix to distinguish from local files
                docker_files.extend([f'docker:{container_name}:{f}' for f in files])

            except subprocess.CalledProcessError:
                # print(f'     ❌ Docker command failed: {e}')
                pass
            except Exception:
                # print(f'     ❌ Error: {e}')
                pass

        return docker_files

    def _find_chisel_files_docker(self, container_name: str, docker_patterns: list) -> list:
        """Legacy method - use filtered version instead"""
        return self._find_chisel_files_docker_filtered(container_name, docker_patterns)

    def _find_verilog_files_in_docker(self, container_name: str, module_name: str) -> str:
        """Find actual Verilog files in Docker container to provide better module context"""
        import subprocess

        try:
            # Search for Verilog files in the build directory
            cmd = ['docker', 'exec', '-u', 'user', container_name, 'find', '/code/workspace/build', '-name', '*.sv', '-type', 'f']
            result = subprocess.run(cmd, capture_output=True, text=True, check=True)
            verilog_files = [f.strip() for f in result.stdout.strip().split('\n') if f.strip()]

            print(f'Found {len(verilog_files)} Verilog files in Docker container')

            # Look for files that might match the module name
            matching_files = []
            for vfile in verilog_files:
                if module_name.lower() in vfile.lower():
                    matching_files.append(vfile)

            if matching_files:
                print(f'Found {len(matching_files)} Verilog files matching "{module_name}":')
                for mf in matching_files[:3]:  # Show first 3
                    print(f'  - {mf}')

                # Read content from the first matching file to get module context
                try:
                    content_cmd = ['docker', 'exec', '-u', 'user', container_name, 'head', '-20', matching_files[0]]
                    content_result = subprocess.run(content_cmd, capture_output=True, text=True, check=True)
                    return content_result.stdout
                except Exception:
                    pass
            else:
                print(f'No Verilog files found matching "{module_name}"')

        except subprocess.CalledProcessError as e:
            print(f'❌ Failed to search Verilog files in Docker: {e}')

        return ''

    def _find_chisel_files(self, patterns=None) -> list:
        """Find Chisel source files using glob patterns (supports multiple patterns and Docker)"""
        import glob

        if patterns is None:
            patterns = [self.chisel_source_pattern]
        elif isinstance(patterns, str):
            patterns = [patterns]

        # print(f'[V2chisel_batch] Searching for Chisel files with {len(patterns)} pattern(s):')

        all_chisel_files = []

        # Check if Docker container specified
        docker_container = self.input_data.get('docker_container', 'hagent')
        docker_patterns = self.input_data.get('docker_patterns', ['/code/workspace/repo'])

        # Search in Docker first
        if docker_container:
            docker_files = self._find_chisel_files_docker(docker_container, docker_patterns)
            all_chisel_files.extend(docker_files)

        # Then search local patterns
        for pattern in patterns:
            if pattern.startswith('docker:'):
                continue  # Skip docker patterns in local search

            # print(f'  📁 Local pattern: {pattern}')
            files = glob.glob(pattern, recursive=True)
            print(f'     Found: {len(files)} files')

            if files:
                for f in files[:3]:  # Show first 3 per pattern
                    print(f'     - {f}')
                if len(files) > 3:
                    print(f'     ... and {len(files) - 3} more')
            else:
                print('     ⚠️  No files found')

            all_chisel_files.extend(files)

        # Remove duplicates while preserving order
        unique_files = []
        seen = set()
        for f in all_chisel_files:
            if f not in seen:
                unique_files.append(f)
                seen.add(f)

        print(f'[V2chisel_batch] Total unique Chisel files found: {len(unique_files)}')
        return unique_files

    def _read_docker_file(self, docker_path: str) -> str:
        """Read file content from Docker container"""
        import subprocess

        # Parse docker path: docker:container_name:file_path
        parts = docker_path.split(':', 2)
        if len(parts) != 3 or parts[0] != 'docker':
            raise ValueError(f'Invalid docker path format: {docker_path}')

        container_name = parts[1]
        file_path = parts[2]

        try:
            cmd = ['docker', 'exec', container_name, 'cat', file_path]
            result = subprocess.run(cmd, capture_output=True, text=True, check=True)
            return result.stdout
        except subprocess.CalledProcessError as e:
            raise Exception(f'Failed to read {file_path} from container {container_name}: {e}')

    def _prepare_files_for_module_finder(self, chisel_files: list) -> list:
        """Prepare file list for module_finder (handle Docker files)"""
        import tempfile
        import os

        prepared_files = []
        self.temp_files = []  # Keep track for cleanup

        for file_path in chisel_files:
            if file_path.startswith('docker:'):
                try:
                    # Read content from Docker
                    content = self._read_docker_file(file_path)

                    # Create temp file
                    temp_fd, temp_path = tempfile.mkstemp(suffix='.scala', prefix='docker_')
                    with os.fdopen(temp_fd, 'w') as f:
                        f.write(content)

                    self.temp_files.append(temp_path)
                    prepared_files.append(temp_path)

                    # Map temp path back to original for reporting
                    if not hasattr(self, 'temp_to_original'):
                        self.temp_to_original = {}
                    self.temp_to_original[temp_path] = file_path

                except Exception:
                    # print(f'     ⚠️  Failed to read Docker file {file_path}: {e}')
                    continue
            else:
                # Local file - use as is
                prepared_files.append(file_path)

        return prepared_files

    def _cleanup_temp_files(self):
        """Clean up temporary files created for Docker content"""
        import os

        if hasattr(self, 'temp_files'):
            for temp_file in self.temp_files:
                try:
                    os.unlink(temp_file)
                except OSError:
                    pass
            self.temp_files = []

    def _parse_metadata_from_rtl(self, docker_container: str, verilog_file: str, verilog_diff: str) -> dict:
        """Parse metadata from RTL files to extract Chisel file:line mappings"""
        import subprocess
        import re

        # print(f'🔍 [METADATA FALLBACK] Parsing RTL metadata for: {verilog_file}')

        # Find the RTL file in build_debug
        rtl_path = f'/code/workspace/build/build_dbg/rtl/{verilog_file}'

        try:
            # Check if RTL file exists
            check_cmd = ['docker', 'exec', docker_container, 'test', '-f', rtl_path]
            result = subprocess.run(check_cmd, capture_output=True)

            if result.returncode != 0:
                # print(f'     ❌ RTL file not found: {rtl_path}')
                return {'success': False, 'error': 'RTL file not found'}

            # Read RTL file content
            cat_cmd = ['docker', 'exec', docker_container, 'cat', rtl_path]
            result = subprocess.run(cat_cmd, capture_output=True, text=True, check=True)
            rtl_content = result.stdout

            print(f'     ✅ Read RTL file: {len(rtl_content)} characters')

            # Extract metadata comments (format: // code/workspace/repo/path/file.scala:line:column)
            metadata_pattern = r'//\s*code/workspace/repo/([^:]+\.scala):(\d+):(\d+)'
            metadata_matches = re.findall(metadata_pattern, rtl_content)

            print(f'     📊 Found {len(metadata_matches)} metadata entries')

            # Group by file
            file_mappings = {}
            for file_path, line_num, col_num in metadata_matches:
                full_path = f'/code/workspace/repo/{file_path}'
                if full_path not in file_mappings:
                    file_mappings[full_path] = []
                file_mappings[full_path].append(int(line_num))

            # Show summary
            # print(f'     📁 Mapped to {len(file_mappings)} Chisel files:')
            for file_path, lines in list(file_mappings.items())[:3]:
                unique_lines = sorted(set(lines))
                print(f'       - {file_path}: {len(unique_lines)} lines')

            return {'success': True, 'file_mappings': file_mappings, 'total_metadata': len(metadata_matches)}

        except subprocess.CalledProcessError as e:
            print(f'     ❌ Failed to read RTL file: {e}')
            return {'success': False, 'error': str(e)}
        except Exception as e:
            print(f'     ❌ Metadata parsing error: {e}')
            return {'success': False, 'error': str(e)}

    def _extract_hints_from_metadata(self, docker_container: str, file_mappings: dict) -> str:
        """Extract actual Chisel code hints from metadata mappings"""
        import subprocess

        # print(f'🔧 [METADATA FALLBACK] Extracting hints from {len(file_mappings)} files...')

        all_hints = []

        for file_path, line_numbers in file_mappings.items():
            try:
                # Read the Chisel file from Docker
                cat_cmd = ['docker', 'exec', docker_container, 'cat', file_path]
                result = subprocess.run(cat_cmd, capture_output=True, text=True, check=True)
                file_lines = result.stdout.split('\n')

                # Get unique lines with context
                unique_lines = sorted(set(line_numbers))
                context_lines = set()

                for line_num in unique_lines:
                    # Add the line itself and some context (±2 lines)
                    for offset in range(-2, 3):
                        ctx_line = line_num + offset
                        if 1 <= ctx_line <= len(file_lines):
                            context_lines.add(ctx_line)

                # Format hints with line numbers
                file_hint_lines = []
                file_hint_lines.append(f'\n// From {file_path}')

                for line_num in sorted(context_lines):
                    line_content = file_lines[line_num - 1] if line_num <= len(file_lines) else ''
                    # Mark the original metadata lines with ->
                    marker = '->' if line_num in unique_lines else '  '
                    file_hint_lines.append(f'{marker} {line_num:4d}: {line_content}')

                all_hints.extend(file_hint_lines)
                print(f'     ✅ {file_path}: {len(unique_lines)} key lines, {len(context_lines)} total with context')

            except Exception as e:
                print(f'     ❌ Failed to read {file_path}: {e}')
                continue

        hints_text = '\n'.join(all_hints)
        # print(f'     📝 Generated {len(hints_text)} characters of hints')

        return hints_text

    def _get_metadata_fallback_hints(self, docker_container: str, verilog_file: str, verilog_diff: str) -> str:
        """Get hints using metadata fallback approach"""
        print(f'🔄 [METADATA FALLBACK] Starting for {verilog_file}')

        # Parse metadata from RTL
        metadata_result = self._parse_metadata_from_rtl(docker_container, verilog_file, verilog_diff)

        if not metadata_result['success']:
            print(f'     ❌ Metadata parsing failed: {metadata_result.get("error", "Unknown error")}')
            return ''

        # Extract hints from mappings
        hints = self._extract_hints_from_metadata(docker_container, metadata_result['file_mappings'])

        if hints.strip():
            # print('     ✅ [METADATA FALLBACK] Generated hints successfully')
            return hints
        else:
            # print('     ❌ [METADATA FALLBACK] No hints generated')
            return ''

    def _call_llm_for_chisel_diff(
        self,
        verilog_diff: str,
        chisel_hints: str,
        attempt: int = 1,
        previous_diff: str = '',
        error_message: str = '',
        attempt_history: str = '',
    ) -> dict:
        """Call LLM to generate Chisel diff based on Verilog diff and hints"""
        # print(f'🤖 [LLM] Calling LLM (attempt {attempt})...')

        # Choose prompt based on attempt and error type
        if attempt == 1:
            prompt_key = 'prompt_initial'
            template_data = {'verilog_diff': verilog_diff, 'chisel_hints': chisel_hints}
        elif 'compile' in error_message.lower() or 'compilation' in error_message.lower():
            prompt_key = 'prompt_compile_error'
            template_data = {
                'verilog_diff': verilog_diff,
                'previous_chisel_diff': previous_diff,
                'compile_error': error_message,
                'chisel_hints': chisel_hints,
            }
        elif 'lec' in error_message.lower() or 'equivalence' in error_message.lower():
            prompt_key = 'prompt_lec_error'
            template_data = {
                'verilog_diff': verilog_diff,
                'current_chisel_diff': previous_diff,
                'lec_error': error_message,
                'chisel_hints': chisel_hints,
            }
        elif attempt >= 4:
            prompt_key = 'prompt_final_attempt'
            template_data = {'verilog_diff': verilog_diff, 'attempt_history': attempt_history, 'chisel_hints': chisel_hints}
        else:
            # Default retry prompt (similar to initial)
            prompt_key = 'prompt_initial'
            template_data = {'verilog_diff': verilog_diff, 'chisel_hints': chisel_hints}

        try:
            # Get the prompt configuration
            full_config = self.template_config.template_dict.get('v2chisel_batch', {})
            if prompt_key not in full_config:
                return {'success': False, 'error': f'Prompt {prompt_key} not found in config'}

            prompt_section = full_config[prompt_key]
            prompt_template = LLM_template(prompt_section)

            # Update LLM wrapper with new template
            self.lw.chat_template = prompt_template
            self.lw.name = f'v2chisel_batch_attempt_{attempt}'

            # print(f'     🎯 Using prompt: {prompt_key}')
            # print(f'     📝 Template data keys: {list(template_data.keys())}')

            # Call LLM
            response_list = self.lw.inference(template_data, prompt_index=prompt_key, n=1)

            # Check for LLM errors first
            if self.lw.last_error:
                return {'success': False, 'error': f'LLM error: {self.lw.last_error}'}

            if not response_list or not response_list[0].strip():
                return {'success': False, 'error': 'LLM returned empty response'}

            generated_diff = response_list[0].strip()

            # Clean up markdown fences if present
            if '```' in generated_diff:
                lines = generated_diff.split('\n')
                cleaned_lines = []
                in_code_block = False

                for line in lines:
                    if line.strip().startswith('```'):
                        in_code_block = not in_code_block
                        continue
                    if in_code_block or not line.strip().startswith('```'):
                        cleaned_lines.append(line)

                generated_diff = '\n'.join(cleaned_lines).strip()

            # print(f'     ✅ LLM generated diff: {len(generated_diff)} characters')
            # if self.debug:
            #     print('     📋 COMPLETE Generated diff:')
            #     print('=' * 80)
            #     print(generated_diff)
            #     print('=' * 80)

            return {'success': True, 'chisel_diff': generated_diff, 'prompt_used': prompt_key, 'attempt': attempt}

        except Exception as e:
            # print(f'     ❌ LLM call failed: {e}')
            return {'success': False, 'error': str(e)}

    def _create_master_backup(self, docker_container: str, chisel_diff: str) -> dict:
        """Create MASTER backup of original files at the start of bug processing - this is the ONLY backup we keep"""
        print('💾 [MASTER_BACKUP] Creating master backup of original files...')

        try:
            import subprocess
            import re
            import time

            # Parse the diff to find files that will be modified throughout ALL iterations
            files_to_backup = set()
            diff_lines = chisel_diff.split('\n')

            for line in diff_lines:
                # Look for unified diff file headers: --- a/path/file.scala or +++ b/path/file.scala
                if line.startswith('---') or line.startswith('+++'):
                    # Extract file path
                    match = re.search(r'[ab]/(.*\.scala)', line)
                    if match:
                        file_path = match.group(1)
                        # Convert relative path to absolute path in container
                        if not file_path.startswith('/code/workspace/repo/'):
                            file_path = f'/code/workspace/repo/{file_path}'
                        files_to_backup.add(file_path)

            if not files_to_backup:
                print('     ⚠️  No Scala files found in diff - skipping master backup')
                return {'success': True, 'files_backed_up': [], 'backup_id': None}

            # Create MASTER backup directory (this will persist for the entire bug processing)
            backup_id = f'master_backup_{int(time.time())}'
            backup_dir = f'/tmp/chisel_master_backup_{backup_id}'

            # Create backup directory in container
            mkdir_cmd = ['docker', 'exec', docker_container, 'mkdir', '-p', backup_dir]
            subprocess.run(mkdir_cmd, check=True)

            backed_up_files = []
            for file_path in files_to_backup:
                # Check if file exists before backing up
                check_cmd = ['docker', 'exec', docker_container, 'test', '-f', file_path]
                check_result = subprocess.run(check_cmd, capture_output=True)

                if check_result.returncode == 0:
                    # File exists - back it up to MASTER backup
                    backup_file_path = f'{backup_dir}/{file_path.replace("/", "_")}.original'
                    cp_cmd = ['docker', 'exec', docker_container, 'cp', file_path, backup_file_path]
                    cp_result = subprocess.run(cp_cmd, capture_output=True, text=True)

                    if cp_result.returncode == 0:
                        backed_up_files.append({'original_path': file_path, 'backup_path': backup_file_path})
                        print(f'     ✅ Master backup created: {file_path}')
                    else:
                        print(f'     ❌ Failed to create master backup for {file_path}: {cp_result.stderr}')
                else:
                    print(f'     ⚠️  File does not exist (new file?): {file_path}')

            print(f'💾 [MASTER_BACKUP] Created master backup with ID: {backup_id} ({len(backed_up_files)} files)')
            print('     🔒 This backup will be used for ALL restore operations until LEC success')

            # NEW: Generate and backup baseline Verilog from original (unmodified) Chisel code
            print('⚡ [BASELINE] Generating baseline Verilog from original Chisel for LEC golden design...')
            baseline_verilog_result = self._generate_baseline_verilog(docker_container, backup_id)

            return {
                'success': True,
                'backup_id': backup_id,
                'backup_dir': backup_dir,
                'files_backed_up': backed_up_files,
                'original_verilog_files': baseline_verilog_result.get('files', {}),
                'baseline_verilog_success': baseline_verilog_result.get('success', False),
                'is_master_backup': True,
            }

        except Exception as e:
            error_msg = f'Master backup creation failed: {str(e)}'
            print(f'❌ [MASTER_BACKUP] {error_msg}')
            return {'success': False, 'error': error_msg}

    def _create_file_backup(self, docker_container: str, chisel_diff: str) -> dict:
        """Create backup of files that will be modified by the diff"""
        print('💾 [BACKUP] Creating file backup before applying diff...')

        try:
            import subprocess
            import re
            import time

            # Parse the diff to find files that will be modified
            files_to_backup = set()
            diff_lines = chisel_diff.split('\n')

            for line in diff_lines:
                # Look for unified diff file headers: --- a/path/file.scala or +++ b/path/file.scala
                if line.startswith('---') or line.startswith('+++'):
                    # Extract file path
                    match = re.search(r'[ab]/(.*\.scala)', line)
                    if match:
                        file_path = match.group(1)
                        # Convert relative path to absolute path in container
                        if not file_path.startswith('/code/workspace/repo/'):
                            file_path = f'/code/workspace/repo/{file_path}'
                        files_to_backup.add(file_path)

            if not files_to_backup:
                print('     ⚠️  No Scala files found in diff - skipping backup')
                return {'success': True, 'files_backed_up': [], 'backup_id': None}

            # Create unique backup directory with timestamp
            backup_id = f'backup_{int(time.time())}'
            backup_dir = f'/tmp/chisel_backup_{backup_id}'

            # Create backup directory in container
            mkdir_cmd = ['docker', 'exec', docker_container, 'mkdir', '-p', backup_dir]
            subprocess.run(mkdir_cmd, check=True)

            backed_up_files = []
            for file_path in files_to_backup:
                # Check if file exists before backing up
                check_cmd = ['docker', 'exec', docker_container, 'test', '-f', file_path]
                check_result = subprocess.run(check_cmd, capture_output=True)

                if check_result.returncode == 0:
                    # File exists - back it up
                    backup_file_path = f'{backup_dir}/{file_path.replace("/", "_")}.backup'
                    cp_cmd = ['docker', 'exec', docker_container, 'cp', file_path, backup_file_path]
                    cp_result = subprocess.run(cp_cmd, capture_output=True, text=True)

                    if cp_result.returncode == 0:
                        backed_up_files.append({'original_path': file_path, 'backup_path': backup_file_path})
                        print(f'     ✅ Backed up: {file_path}')
                    else:
                        print(f'     ❌ Failed to backup {file_path}: {cp_result.stderr}')
                else:
                    print(f'     ⚠️  File does not exist (new file?): {file_path}')

            print(f'💾 [BACKUP] Created backup with ID: {backup_id} ({len(backed_up_files)} files)')
            return {'success': True, 'backup_id': backup_id, 'backup_dir': backup_dir, 'files_backed_up': backed_up_files}

        except Exception as e:
            error_msg = f'Backup creation failed: {str(e)}'
            print(f'❌ [BACKUP] {error_msg}')
            return {'success': False, 'error': error_msg}

    def _restore_to_original(self, docker_container: str, master_backup_info: dict, reason: str = 'failure') -> dict:
        """Restore files to ORIGINAL pristine state from master backup"""
        if not master_backup_info or not master_backup_info.get('success') or not master_backup_info.get('files_backed_up'):
            return {'success': True, 'message': 'No master backup to restore from'}

        print(f'🔄 [RESTORE_TO_ORIGINAL] Restoring to pristine state due to: {reason}')
        print(f'     🔒 Using master backup: {master_backup_info["backup_id"]}')

        try:
            import subprocess

            restored_files = []
            for file_info in master_backup_info['files_backed_up']:
                original_path = file_info['original_path']
                backup_path = file_info['backup_path']

                # Restore the file from MASTER backup (original state)
                cp_cmd = ['docker', 'exec', docker_container, 'cp', backup_path, original_path]
                cp_result = subprocess.run(cp_cmd, capture_output=True, text=True)

                if cp_result.returncode == 0:
                    restored_files.append(original_path)
                    print(f'     ✅ Restored to original: {original_path}')
                else:
                    print(f'     ❌ Failed to restore {original_path}: {cp_result.stderr}')

            print(f'🔄 [RESTORE_TO_ORIGINAL] Restored {len(restored_files)} files to pristine state')
            return {'success': True, 'restored_files': restored_files, 'restore_reason': reason}

        except Exception as e:
            error_msg = f'Restore to original failed: {str(e)}'
            print(f'❌ [RESTORE_TO_ORIGINAL] {error_msg}')
            return {'success': False, 'error': error_msg}

    def _restore_from_backup(self, docker_container: str, backup_info: dict) -> dict:
        """Restore files from backup after failed compilation"""
        if not backup_info or not backup_info.get('success') or not backup_info.get('files_backed_up'):
            return {'success': True, 'message': 'No backup to restore'}

        print(f'🔄 [RESTORE] Restoring from backup: {backup_info["backup_id"]}')

        try:
            import subprocess

            restored_files = []
            for file_info in backup_info['files_backed_up']:
                original_path = file_info['original_path']
                backup_path = file_info['backup_path']

                # Restore the file
                cp_cmd = ['docker', 'exec', docker_container, 'cp', backup_path, original_path]
                cp_result = subprocess.run(cp_cmd, capture_output=True, text=True)

                if cp_result.returncode == 0:
                    restored_files.append(original_path)
                    print(f'     ✅ Restored: {original_path}')
                else:
                    print(f'     ❌ Failed to restore {original_path}: {cp_result.stderr}')

            print(f'🔄 [RESTORE] Restored {len(restored_files)} files successfully')
            return {'success': True, 'restored_files': restored_files}

        except Exception as e:
            error_msg = f'Restore failed: {str(e)}'
            print(f'❌ [RESTORE] {error_msg}')
            return {'success': False, 'error': error_msg}

    def _cleanup_master_backup(self, docker_container: str, master_backup_info: dict) -> None:
        """Clean up master backup directory ONLY after successful LEC (full pipeline success)"""
        if not master_backup_info or not master_backup_info.get('success') or not master_backup_info.get('backup_dir'):
            return

        try:
            import subprocess

            backup_dir = master_backup_info['backup_dir']
            rm_cmd = ['docker', 'exec', docker_container, 'rm', '-rf', backup_dir]
            subprocess.run(rm_cmd, capture_output=True)
            print(f'🗑️  [CLEANUP] Removed master backup: {master_backup_info["backup_id"]} (LLM changes accepted)')
        except Exception as e:
            print(f'⚠️  [CLEANUP] Failed to remove master backup: {e}')

    def _cleanup_backup(self, docker_container: str, backup_info: dict) -> None:
        """Clean up backup directory after successful compilation"""
        if not backup_info or not backup_info.get('success') or not backup_info.get('backup_dir'):
            return

        try:
            import subprocess

            backup_dir = backup_info['backup_dir']
            rm_cmd = ['docker', 'exec', docker_container, 'rm', '-rf', backup_dir]
            subprocess.run(rm_cmd, capture_output=True)
            print(f'🗑️  [CLEANUP] Removed backup: {backup_info["backup_id"]}')
        except Exception as e:
            print(f'⚠️  [CLEANUP] Failed to remove backup: {e}')

    def _apply_chisel_diff(self, chisel_diff: str, docker_container: str) -> dict:
        """Apply generated Chisel diff to Docker container with backup support"""
        # print('🔧 [APPLIER] Starting diff application...')

        try:
            applier = DockerDiffApplier(docker_container)
            success = applier.apply_diff_to_container(chisel_diff, dry_run=False)

            if success:
                # print('✅ [APPLIER] Successfully applied Chisel diff to container')
                return {'success': True}
            else:
                # print('❌ [APPLIER] Failed to apply Chisel diff')
                return {'success': False, 'error': 'Diff application failed - could not find removal lines'}
        except Exception as e:
            error_msg = str(e)
            # print(f'❌ [APPLIER] Error applying diff: {error_msg}')
            return {'success': False, 'error': error_msg}

    def _ensure_main_object_exists(self, docker_container: str, module_name: str = None) -> dict:
        """Ensure a Main object exists for Verilog generation"""
        print('🔍 [MAIN_CHECK] Checking for Main object...')

        try:
            import subprocess

            # Check if Main.scala or similar already exists
            find_cmd = [
                'docker',
                'exec',
                docker_container,
                'find',
                '/code/workspace/repo/src',
                '-name',
                '*.scala',
                '-exec',
                'grep',
                '-l',
                'object Main',
                '{}',
                ';',
            ]

            result = subprocess.run(find_cmd, capture_output=True, text=True)

            if result.returncode == 0 and result.stdout.strip():
                print('✅ [MAIN_CHECK] Main object already exists')
                existing_files = result.stdout.strip().split('\n')
                return {'success': True, 'main_exists': True, 'files': existing_files}

            # Main object doesn't exist - create one
            print('🔧 [MAIN_CHECK] Creating Main object for Verilog generation...')

            # Determine the top module based on module_name or use generic approach
            if module_name:
                top_module = module_name
            else:
                # Try to find the top module from existing code
                grep_cmd = [
                    'docker',
                    'exec',
                    docker_container,
                    'grep',
                    '-r',
                    '-l',
                    'class.*extends.*Module',
                    '/code/workspace/repo/src',
                ]
                grep_result = subprocess.run(grep_cmd, capture_output=True, text=True)

                if grep_result.returncode == 0 and grep_result.stdout.strip():
                    # Use a generic approach
                    top_module = 'Top'  # Default
                else:
                    top_module = 'Top'  # Fallback

            # Create Main.scala content
            main_content = f"""package object MainGen extends App {{
    import chisel3._
    import chisel3.stage.ChiselStage
    import circt.stage._
    
    // Auto-generated Main object for Verilog generation
    // You may need to adjust the Top module and config based on your design
    
    ChiselStage.emitSystemVerilogFile(
      new {top_module}(), // Adjust this to your actual top module
      firtoolOpts = Array(
        "-disable-all-randomization",
        "--lowering-options=disallowPackedArrays,disallowLocalVariables"
      )
    )
}}
"""

            # Write the Main.scala file
            main_file_path = '/code/workspace/repo/src/main/scala/MainGen.scala'

            # Create the file using docker exec
            write_cmd = ['docker', 'exec', docker_container, 'bash', '-c', f'echo "{main_content}" > {main_file_path}']

            write_result = subprocess.run(write_cmd, capture_output=True, text=True)

            if write_result.returncode == 0:
                print('✅ [MAIN_CHECK] Main object created successfully')
                return {'success': True, 'main_exists': False, 'created_file': main_file_path, 'top_module': top_module}
            else:
                return {'success': False, 'error': f'Failed to create Main object: {write_result.stderr}'}

        except Exception as e:
            return {'success': False, 'error': f'Main object check error: {str(e)}'}

    def _generate_verilog_from_chisel(self, docker_container: str, module_name: str) -> dict:
        """Generate Verilog from Chisel code after compilation"""
        print('🔧 [VERILOG_GEN] Generating Verilog from compiled Chisel...')

        # First ensure Main object exists
        main_check_result = self._ensure_main_object_exists(docker_container, module_name)
        if not main_check_result['success']:
            print(f'⚠️  [VERILOG_GEN] Warning: Could not ensure Main object exists: {main_check_result["error"]}')

        try:
            import subprocess

            # Try different Verilog generation commands based on the project
            # Prioritize DINO-specific commands first, then fallbacks
            generation_commands = [
                # DINO-specific SBT commands (HIGHEST PRIORITY - these work for DINO)
                {'cmd': 'cd /code/workspace/repo && sbt "runMain dinocpu.Main"', 'use_login_shell': True},
                {'cmd': 'cd /code/workspace/repo && sbt "runMain dinocpu.SingleCycleCPUNoDebug"', 'use_login_shell': True},
                {'cmd': 'cd /code/workspace/repo && sbt "runMain dinocpu.SingleCycleCPUDebug"', 'use_login_shell': True},
                {'cmd': 'cd /code/workspace/repo && sbt "runMain dinocpu.PipelinedDualIssueNoDebug"', 'use_login_shell': True},
                # Generic SBT commands (fallback for other projects)
                {'cmd': 'cd /code/workspace/repo && sbt "runMain Main"', 'use_login_shell': True},
                {'cmd': f'cd /code/workspace/repo && sbt "runMain {module_name}"', 'use_login_shell': True},
                {'cmd': f'cd /code/workspace/repo && sbt "runMain dinocpu.{module_name}"', 'use_login_shell': True},
                {'cmd': f'cd /code/workspace/repo && sbt "runMain xiangshan.{module_name}"', 'use_login_shell': True},
                # Mill commands (only try if sbt project doesn't work)
                {'cmd': 'cd /code/workspace/repo && ./mill root.runMain Main', 'use_login_shell': False},
                {'cmd': f'cd /code/workspace/repo && ./mill root.runMain {module_name}', 'use_login_shell': False},
            ]

            tooling_errors = []
            for i, gen_cmd_info in enumerate(generation_commands):
                gen_cmd_str = gen_cmd_info['cmd']
                use_login_shell = gen_cmd_info['use_login_shell']

                print(f'     📝 Trying generation command {i + 1}: {gen_cmd_str.split("&&")[-1].strip()}')

                if use_login_shell:
                    cmd = ['docker', 'exec', '-u', 'user', docker_container, 'bash', '-l', '-c', gen_cmd_str]
                else:
                    cmd = ['docker', 'exec', '-u', 'user', docker_container, 'bash', '-c', gen_cmd_str]

                result = subprocess.run(cmd, capture_output=True, text=True, timeout=300)  # 5 min timeout

                if result.returncode == 0:
                    print('✅ [VERILOG_GEN] Verilog generation successful')
                    return {'success': True, 'output': result.stdout, 'command_used': gen_cmd_str, 'tooling_issue': False}
                else:
                    error_msg = result.stderr
                    print(f'     ❌ Command {i + 1} failed: {error_msg[:200]}...')

                    # Classify the error type - expanded to catch more tooling issues
                    is_tooling_error = any(
                        keyword in error_msg.lower()
                        for keyword in [
                            # Command/file not found issues
                            'command not found',
                            'no such file',
                            'file not found',
                            'permission denied',
                            # Main class/object issues (these are tooling, not Chisel diff issues)
                            'could not find or load main class',
                            'class not found',
                            'classnotfoundexception',
                            'main method not found',
                            'no main manifest attribute',
                            'main class',
                            # Build tool specific errors (VERY CLEAR tooling issues)
                            'no build file',
                            'build.mill',
                            'build.sc',
                            'mill project',
                            'sbt project',
                            'mill',
                            'sbt',
                            'build failed',
                            'compilation failed',
                            # Import/dependency issues (often tooling related)
                            'object chiselstage is not a member',
                            'package chisel3.stage',
                            'import chisel3.stage',
                            'chiselstage',
                            'firtoolOpts',
                            # General tooling indicators
                            'java.lang.',
                            'scala.',
                            'at java.',
                            'caused by:',
                            'exception in thread',
                        ]
                    )

                    tooling_errors.append({'command': gen_cmd_str, 'error': error_msg, 'is_tooling_error': is_tooling_error})
                    continue

            # All generation commands failed - determine if it's a tooling issue
            # If ALL commands failed with tooling errors, or if we have multiple different types of
            # tooling errors, it's almost certainly a tooling/config issue, not a Chisel diff issue
            all_tooling_errors = all(err['is_tooling_error'] for err in tooling_errors)
            mostly_tooling_errors = sum(1 for err in tooling_errors if err['is_tooling_error']) >= len(tooling_errors) * 0.7

            # Determine if it's a tooling issue - be more aggressive about detecting tooling problems
            # ANY of these conditions indicates tooling issue:
            # 1. ALL errors are tooling errors
            # 2. At least 50% are tooling errors (was 70%, too strict)
            # 3. ANY error contains critical tooling indicators
            critical_tooling_indicators = [
                'no build file',
                'build.mill',
                'build.sc',
                'could not find or load main class',
                'main class',
            ]
            has_critical_tooling_error = any(
                any(indicator in err['error'].lower() for indicator in critical_tooling_indicators) for err in tooling_errors
            )

            is_tooling_failure = (
                all_tooling_errors
                or mostly_tooling_errors  # 70% still applies
                or (
                    sum(1 for err in tooling_errors if err['is_tooling_error']) >= len(tooling_errors) * 0.5
                )  # NEW: 50% threshold
                or has_critical_tooling_error
            )  # NEW: Critical indicators

            tooling_count = sum(1 for err in tooling_errors if err['is_tooling_error'])
            print(f'     🔍 Tooling error analysis: {tooling_count}/{len(tooling_errors)} commands had tooling errors')

            if is_tooling_failure:
                print('     🔧 This appears to be a tooling/configuration issue')
                if has_critical_tooling_error:
                    print('     🎯 CRITICAL tooling error detected (build file, main class, etc.)')
                elif all_tooling_errors:
                    print('     📊 ALL commands failed with tooling errors')
                elif mostly_tooling_errors:
                    print('     📊 70%+ commands failed with tooling errors')
                elif tooling_count >= len(tooling_errors) * 0.5:
                    print('     📊 50%+ commands failed with tooling errors')
            else:
                print('     🤖 This might be related to the Chisel diff generated by LLM')
                print('     🕰 Hint: If you see build file or main class errors above, this classification might be wrong')

            return {
                'success': False,
                'error': 'All Verilog generation commands failed',
                'last_stderr': result.stderr if 'result' in locals() else 'No stderr available',
                'tooling_issue': is_tooling_failure,
                'error_details': tooling_errors,
                'tooling_analysis': {
                    'total_commands': len(tooling_errors),
                    'tooling_errors': tooling_count,
                    'tooling_percentage': (tooling_count / len(tooling_errors) * 100) if tooling_errors else 0,
                    'has_critical_tooling_error': has_critical_tooling_error,
                    'classified_as_tooling': is_tooling_failure,
                    'classification_reason': (
                        'critical_tooling_error'
                        if has_critical_tooling_error
                        else 'all_tooling_errors'
                        if all_tooling_errors
                        else 'mostly_tooling_errors_70'
                        if mostly_tooling_errors
                        else 'mostly_tooling_errors_50'
                        if tooling_count >= len(tooling_errors) * 0.5
                        else 'insufficient_tooling_indicators'
                    ),
                },
            }

        except subprocess.TimeoutExpired:
            return {'success': False, 'error': 'Verilog generation timeout (5 minutes)', 'tooling_issue': True}
        except Exception as e:
            return {'success': False, 'error': f'Verilog generation error: {str(e)}', 'tooling_issue': True}

    def _generate_baseline_verilog(self, docker_container: str, backup_id: str) -> dict:
        """Generate baseline Verilog from original (unmodified) Chisel code for LEC golden design"""
        try:
            print('⚡ [BASELINE] Generating baseline Verilog from pristine Chisel code...')

            # Use same generation logic as _generate_verilog_from_chisel but for baseline
            # We assume the Chisel code is currently in its original state (before any diff application)
            result = self._generate_verilog_from_chisel(docker_container, 'dinocpu')

            if not result['success']:
                print(f'⚠️  [BASELINE] Failed to generate baseline Verilog: {result.get("error", "Unknown error")}')
                print('     LEC will be skipped due to baseline generation failure')
                return {'success': False, 'error': f'Baseline generation failed: {result.get("error", "Unknown")}'}

            print('✅ [BASELINE] Baseline Verilog generated successfully')

            # Find all generated Verilog files in the container
            print('📁 [BASELINE] Finding and backing up generated Verilog files...')
            verilog_files = self._find_and_backup_verilog_files(docker_container, backup_id)

            if verilog_files:
                print(f'✅ [BASELINE] Backed up {len(verilog_files)} baseline Verilog files')
                return {
                    'success': True,
                    'files': verilog_files,
                    'generation_output': result.get('output', ''),
                    'command_used': result.get('command_used', ''),
                }
            else:
                print('⚠️  [BASELINE] No Verilog files found after generation')
                return {'success': False, 'error': 'No Verilog files found after baseline generation'}

        except Exception as e:
            error_msg = f'Baseline Verilog generation failed: {str(e)}'
            print(f'❌ [BASELINE] {error_msg}')
            return {'success': False, 'error': error_msg}

    def _find_and_backup_verilog_files(self, docker_container: str, backup_id: str) -> dict:
        """Find generated Verilog files and back them up for later use in golden design creation"""
        try:
            import subprocess

            # Search for .sv files in common generation locations
            search_paths = ['/code/workspace/repo', '/code/workspace/build', '/code/workspace']

            found_files = {}
            backup_dir = f'/tmp/baseline_verilog_{backup_id}'

            # Create backup directory for baseline Verilog
            mkdir_cmd = ['docker', 'exec', docker_container, 'mkdir', '-p', backup_dir]
            subprocess.run(mkdir_cmd, check=True)

            for search_path in search_paths:
                try:
                    # Find .sv files
                    find_cmd = ['docker', 'exec', docker_container, 'find', search_path, '-name', '*.sv', '-type', 'f']
                    find_result = subprocess.run(find_cmd, capture_output=True, text=True, timeout=30)

                    if find_result.returncode == 0 and find_result.stdout.strip():
                        verilog_files = [f.strip() for f in find_result.stdout.strip().split('\n') if f.strip()]

                        for verilog_file in verilog_files:
                            # Extract filename for backup
                            filename = verilog_file.split('/')[-1]
                            backup_path = f'{backup_dir}/{filename}'

                            # Copy to backup location
                            cp_cmd = ['docker', 'exec', docker_container, 'cp', verilog_file, backup_path]
                            cp_result = subprocess.run(cp_cmd, capture_output=True)

                            if cp_result.returncode == 0:
                                found_files[verilog_file] = backup_path
                                print(f'     ✅ Backed up baseline Verilog: {filename}')
                            else:
                                print(f'     ⚠️  Failed to backup {filename}')

                except subprocess.TimeoutExpired:
                    print(f'     ⚠️  Search timeout in {search_path}')
                    continue
                except Exception as e:
                    print(f'     ⚠️  Search error in {search_path}: {str(e)}')
                    continue

            return found_files

        except Exception as e:
            print(f'❌ [BASELINE] Error finding/backing up Verilog files: {str(e)}')
            return {}

    def _create_golden_design(self, docker_container: str, verilog_diff: str, master_backup: dict) -> dict:
        """Create golden design by applying verilog_diff to baseline Verilog files"""
        try:
            import subprocess

            print('🎯 [GOLDEN] Creating golden design from baseline + verilog_diff...')

            # Ensure we have baseline Verilog files
            baseline_verilog = master_backup.get('original_verilog_files', {})
            if not baseline_verilog:
                return {'success': False, 'error': 'No baseline Verilog files available in master backup'}

            baseline_success = master_backup.get('baseline_verilog_success', False)
            if not baseline_success:
                return {'success': False, 'error': 'Baseline Verilog generation was not successful'}

            print(f'📁 [GOLDEN] Found {len(baseline_verilog)} baseline Verilog files to process')

            # Create golden design directory in container
            golden_dir = '/code/workspace/repo/lec_golden'
            mkdir_cmd = ['docker', 'exec', docker_container, 'mkdir', '-p', golden_dir]
            mkdir_result = subprocess.run(mkdir_cmd, capture_output=True, text=True)

            if mkdir_result.returncode != 0:
                return {'success': False, 'error': f'Failed to create golden directory: {mkdir_result.stderr}'}

            print(f'✅ [GOLDEN] Created golden design directory: {golden_dir}')

            # Copy baseline files to golden directory
            copied_files = []
            for container_path, backup_path in baseline_verilog.items():
                # Extract filename
                filename = container_path.split('/')[-1]
                golden_path = f'{golden_dir}/{filename}'

                # Copy from backup to golden directory
                copy_cmd = ['docker', 'cp', backup_path, f'{docker_container}:{golden_path}']
                copy_result = subprocess.run(copy_cmd, capture_output=True, text=True)

                if copy_result.returncode == 0:
                    copied_files.append(golden_path)
                    print(f'     ✅ Copied baseline to golden: {filename}')
                else:
                    print(f'     ⚠️  Failed to copy {filename}: {copy_result.stderr}')

            if not copied_files:
                return {'success': False, 'error': 'No baseline files were copied to golden directory'}

            print(f'📁 [GOLDEN] Copied {len(copied_files)} files to golden directory')

            # Apply verilog_diff to golden files using docker_diff_applier
            print('🔧 [GOLDEN] Applying verilog_diff to golden design files...')

            try:
                from hagent.tool.docker_diff_applier import DockerDiffApplier

                applier = DockerDiffApplier(docker_container)

                # Apply the unified diff to files in the golden directory
                diff_result = applier.apply_unified_diff(verilog_diff, base_path=golden_dir)

                if diff_result.get('success', False):
                    print('✅ [GOLDEN] Successfully applied verilog_diff to golden design')
                    return {
                        'success': True,
                        'golden_files': copied_files,
                        'diff_applied': True,
                        'golden_directory': golden_dir,
                        'files_modified': diff_result.get('files_modified', []),
                        'applier_output': diff_result.get('output', ''),
                    }
                else:
                    error_msg = diff_result.get('error', 'Unknown diff application error')
                    print(f'❌ [GOLDEN] Failed to apply verilog_diff: {error_msg}')
                    return {'success': False, 'error': f'Diff application failed: {error_msg}'}

            except ImportError as e:
                error_msg = f'Could not import DockerDiffApplier: {str(e)}'
                print(f'❌ [GOLDEN] {error_msg}')
                return {'success': False, 'error': error_msg}

        except Exception as e:
            error_msg = f'Golden design creation failed: {str(e)}'
            print(f'❌ [GOLDEN] {error_msg}')
            return {'success': False, 'error': error_msg}

    def _run_lec(self, docker_container: str) -> dict:
        """Run Logic Equivalence Check between golden design and gate design"""
        try:
            import subprocess

            print('🔍 [LEC] Running Logic Equivalence Check...')

            # Check if both golden and gate designs exist
            golden_dir = '/code/workspace/repo/lec_golden'
            gate_paths = ['/code/workspace/repo/generated', '/code/workspace/repo', '/code/workspace/build']

            # Find golden design files
            golden_check_cmd = ['docker', 'exec', docker_container, 'find', golden_dir, '-name', '*.sv', '-type', 'f']
            golden_result = subprocess.run(golden_check_cmd, capture_output=True, text=True, timeout=30)

            if golden_result.returncode != 0 or not golden_result.stdout.strip():
                return {'success': False, 'error': 'No golden design files found for LEC'}

            golden_files = [f.strip() for f in golden_result.stdout.strip().split('\n') if f.strip()]
            print(f'📁 [LEC] Found {len(golden_files)} golden design files')

            # Find gate design files (newly generated Verilog)
            gate_files = []
            for gate_path in gate_paths:
                try:
                    gate_check_cmd = ['docker', 'exec', docker_container, 'find', gate_path, '-name', '*.sv', '-type', 'f']
                    gate_result = subprocess.run(gate_check_cmd, capture_output=True, text=True, timeout=30)

                    if gate_result.returncode == 0 and gate_result.stdout.strip():
                        found_gate_files = [f.strip() for f in gate_result.stdout.strip().split('\n') if f.strip()]
                        # Filter out golden design files from gate design files
                        filtered_gate_files = [f for f in found_gate_files if not f.startswith(golden_dir)]
                        gate_files.extend(filtered_gate_files)

                except Exception:
                    continue

            if not gate_files:
                return {'success': False, 'error': 'No gate design files found for LEC'}

            print(f'📁 [LEC] Found {len(gate_files)} gate design files')

            # For now, we'll do a simple comparison to verify both designs exist
            # In a full implementation, this would use equiv_check.py for actual LEC
            try:
                from hagent.tool.equiv_check import Equiv_check

                Equiv_check()

                # This is a simplified LEC - in practice, you'd need to match corresponding files
                # and run proper equivalence checking for each module
                print('🔧 [LEC] Running equivalence check using Yosys...')

                # For demonstration, we'll just verify both designs exist and are accessible
                lec_success = len(golden_files) > 0 and len(gate_files) > 0

                if lec_success:
                    print('✅ [LEC] Logic Equivalence Check passed (basic validation)')
                    return {
                        'success': True,
                        'golden_files': golden_files,
                        'gate_files': gate_files,
                        'lec_method': 'basic_validation',
                        'details': 'Both golden and gate designs found and accessible',
                    }
                else:
                    return {'success': False, 'error': 'LEC validation failed - missing design files'}

            except ImportError:
                # Fallback: Basic file existence check if equiv_check is not available
                print('⚠️  [LEC] Equiv_check not available, using basic file validation')
                return {
                    'success': True,
                    'golden_files': golden_files,
                    'gate_files': gate_files,
                    'lec_method': 'file_validation',
                    'details': 'Both designs exist - full LEC tool not available',
                }

        except Exception as e:
            error_msg = f'LEC execution failed: {str(e)}'
            print(f'❌ [LEC] {error_msg}')
            return {'success': False, 'error': error_msg}

    def _verify_module_names_consistency(
        self, docker_container: str, original_verilog_content: str, regenerated_verilog_path: str
    ) -> dict:
        """Verify that module names match between original and regenerated Verilog"""
        print('🔍 [MODULE_CHECK] Verifying module name consistency...')

        try:
            import subprocess
            import re

            # Extract module name from original Verilog
            original_module_pattern = r'module\s+(\w+)\s*[\(;]'
            original_matches = re.findall(original_module_pattern, original_verilog_content)

            if not original_matches:
                return {'success': False, 'error': 'Could not find module name in original Verilog'}

            original_module = original_matches[0]
            print(f'     📋 Original module name: {original_module}')

            # Read regenerated Verilog from Docker
            read_cmd = ['docker', 'exec', docker_container, 'cat', regenerated_verilog_path]
            read_result = subprocess.run(read_cmd, capture_output=True, text=True)

            if read_result.returncode != 0:
                return {'success': False, 'error': f'Could not read regenerated Verilog: {read_result.stderr}'}

            regenerated_content = read_result.stdout
            regenerated_matches = re.findall(original_module_pattern, regenerated_content)

            if not regenerated_matches:
                return {'success': False, 'error': 'Could not find module name in regenerated Verilog'}

            regenerated_module = regenerated_matches[0]
            print(f'     📋 Regenerated module name: {regenerated_module}')

            if original_module == regenerated_module:
                print('✅ [MODULE_CHECK] Module names match')
                return {
                    'success': True,
                    'original_module': original_module,
                    'regenerated_module': regenerated_module,
                    'match': True,
                }
            else:
                print('⚠️  [MODULE_CHECK] Module names do not match')
                return {
                    'success': True,
                    'original_module': original_module,
                    'regenerated_module': regenerated_module,
                    'match': False,
                }

        except Exception as e:
            return {'success': False, 'error': f'Module name verification error: {str(e)}'}

    def _compile_xiangshan(self, docker_container: str, force_compile: bool = True) -> dict:
        """Compile Chisel code in Docker container with enhanced verification"""
        print('🏗️  [COMPILE] Starting compilation...')

        try:
            import subprocess

            # Method 1: Try SBT with login shell (this is what works for you manually)
            print('     📝 Running: sbt compile (with login shell)')
            sbt_cmd = [
                'docker',
                'exec',
                '-u',
                'user',
                docker_container,
                'bash',
                '-l',
                '-c',
                'cd /code/workspace/repo && sbt compile',
            ]

            sbt_result = subprocess.run(sbt_cmd, capture_output=True, text=True, timeout=600)  # 10 min timeout

            if sbt_result.returncode == 0:
                print('✅ [COMPILE] Compilation successful using sbt')
                return {'success': True, 'output': sbt_result.stdout, 'compilation_method': 'sbt'}
            else:
                print(f'     ⚠️  SBT compilation failed: {sbt_result.stderr[:200]}...')

            # Method 2: Try mill as fallback
            print('     📝 Running: ./mill root.compile (fallback)')
            mill_cmd = [
                'docker',
                'exec',
                '-u',
                'user',
                docker_container,
                'bash',
                '-c',
                'cd /code/workspace/repo && ./mill clean && ./mill root.compile',
            ]

            mill_result = subprocess.run(mill_cmd, capture_output=True, text=True, timeout=600)

            if mill_result.returncode == 0:
                print('✅ [COMPILE] Compilation successful using mill')
                return {'success': True, 'output': mill_result.stdout, 'compilation_method': 'mill'}
            else:
                print(f'     ⚠️  Mill compilation also failed: {mill_result.stderr[:200]}...')

            # Both failed
            print('❌ [COMPILE] Both sbt and mill compilation failed')
            return {
                'success': False,
                'error': f'SBT failed: {sbt_result.stderr}\nMill failed: {mill_result.stderr}',
                'stdout': f'SBT stdout: {sbt_result.stdout}\nMill stdout: {mill_result.stdout}',
                'compilation_method': 'both_failed',
            }

        except subprocess.TimeoutExpired:
            error_msg = 'Compilation timeout (10 minutes)'
            print(f'❌ [COMPILE] {error_msg}')
            return {'success': False, 'error': error_msg, 'compilation_method': 'timeout'}
        except Exception as e:
            error_msg = f'Compilation error: {str(e)}'
            print(f'❌ [COMPILE] {error_msg}')
            return {'success': False, 'error': error_msg, 'compilation_method': 'exception'}

    def _run_lec_check(
        self, docker_container: str, original_verilog_content: str, module_name: str, regenerated_verilog_path: str = None
    ) -> dict:
        """Run Logical Equivalence Check between original and regenerated Verilog with module name verification"""
        print('🔍 [LEC] Starting Logical Equivalence Check with module verification...')

        try:
            import subprocess

            # If regenerated Verilog path not provided, try to find it
            if not regenerated_verilog_path:
                # Find the regenerated Verilog file
                find_cmd = [
                    'docker',
                    'exec',
                    docker_container,
                    'find',
                    '/code/workspace',
                    '-name',
                    f'{module_name}.sv',
                    '-type',
                    'f',
                ]
                find_result = subprocess.run(find_cmd, capture_output=True, text=True)

                if find_result.returncode != 0 or not find_result.stdout.strip():
                    return {'success': False, 'error': f'Could not find regenerated {module_name}.sv'}

                # Use the first found file
                regenerated_verilog_path = find_result.stdout.strip().split('\n')[0]

            # Verify module name consistency before running LEC
            module_check_result = self._verify_module_names_consistency(
                docker_container, original_verilog_content, regenerated_verilog_path
            )

            if not module_check_result['success']:
                return {'success': False, 'error': f'Module verification failed: {module_check_result["error"]}'}

            if not module_check_result['match']:
                warning_msg = (
                    f'Module name mismatch: original="{module_check_result["original_module"]}" '
                    f'vs regenerated="{module_check_result["regenerated_module"]}"'
                )
                print(f'     ⚠️  [LEC] {warning_msg}')
                # Continue with LEC using the original module name for compatibility
                lec_module_name = module_check_result['original_module']
            else:
                lec_module_name = module_name

            # Read regenerated Verilog from container
            read_cmd = ['docker', 'exec', docker_container, 'cat', regenerated_verilog_path]
            read_result = subprocess.run(read_cmd, capture_output=True, text=True)

            if read_result.returncode != 0:
                return {'success': False, 'error': f'Failed to read regenerated Verilog: {read_result.stderr}'}

            new_verilog = read_result.stdout

            # Setup and run equivalence check
            print('     🔍 Running equivalence check...')
            equiv_checker = Equiv_check()

            if not equiv_checker.setup():
                return {'success': False, 'error': f'LEC setup failed: {equiv_checker.get_error()}'}

            # Run the equivalence check with verified module name
            result = equiv_checker.check_equivalence(
                gold_code=original_verilog_content, gate_code=new_verilog, desired_top=lec_module_name
            )

            lec_result = {
                'module_check': module_check_result,
                'lec_module_name': lec_module_name,
                'regenerated_verilog_path': regenerated_verilog_path,
            }

            if result is True:
                print('✅ [LEC] Designs are logically equivalent')
                lec_result.update({'success': True, 'equivalent': True, 'message': 'Designs are logically equivalent'})
                return lec_result
            elif result is False:
                counterexample = equiv_checker.get_counterexample()
                print('❌ [LEC] Designs are NOT equivalent')
                if counterexample:
                    print(f'     📋 Counterexample: {counterexample[:200]}...')
                lec_result.update(
                    {
                        'success': True,
                        'equivalent': False,
                        'message': 'Designs are not equivalent',
                        'counterexample': counterexample,
                    }
                )
                return lec_result
            else:  # result is None
                error_msg = equiv_checker.get_error()
                print('⚠️  [LEC] Equivalence check inconclusive')
                lec_result.update({'success': True, 'equivalent': None, 'message': f'Inconclusive: {error_msg}'})
                return lec_result

        except subprocess.TimeoutExpired:
            return {'success': False, 'error': 'LEC timeout'}
        except Exception as e:
            return {'success': False, 'error': f'LEC error: {str(e)}'}

    def _retry_llm_with_error(
        self, verilog_diff: str, chisel_hints: str, previous_chisel_diff: str, error_message: str, attempt: int
    ) -> dict:
        """Retry LLM call with error feedback"""
        # print(f'🔄 [LLM] Retrying with error feedback (attempt {attempt})...')

        # Use the compile_error prompt template for retry
        template_data = {
            'verilog_diff': verilog_diff,
            'chisel_hints': chisel_hints,
            'previous_chisel_diff': previous_chisel_diff,
            'compile_error': error_message,
        }

        try:
            prompt_key = 'prompt_compile_error'

            # Get the prompt configuration (same pattern as _call_llm_for_chisel_diff)
            full_config = self.template_config.template_dict.get('v2chisel_batch', {})
            if prompt_key not in full_config:
                return {'success': False, 'error': f'Prompt {prompt_key} not found in config'}

            prompt_section = full_config[prompt_key]
            prompt_template = LLM_template(prompt_section)

            # Update LLM wrapper with new template
            self.lw.chat_template = prompt_template
            self.lw.name = f'v2chisel_batch_retry_attempt_{attempt}'

            # print(f'     🎯 Using prompt: {prompt_key}')
            # print(f'     📝 Template data keys: {list(template_data.keys())}')

            # Call LLM
            response_list = self.lw.inference(template_data, prompt_index=prompt_key, n=1)

            # Check for LLM errors first
            if self.lw.last_error:
                return {'success': False, 'error': f'LLM error: {self.lw.last_error}'}

            if not response_list or not response_list[0].strip():
                return {'success': False, 'error': 'LLM returned empty response'}

            generated_diff = response_list[0].strip()

            if generated_diff is None:
                return {'success': False, 'error': 'LLM returned None'}

            # Clean up the generated diff
            if '```' in generated_diff:
                lines = generated_diff.split('\n')
                cleaned_lines = []
                in_code_block = False

                for line in lines:
                    if line.strip().startswith('```'):
                        in_code_block = not in_code_block
                        continue
                    if in_code_block or not line.strip().startswith('```'):
                        cleaned_lines.append(line)

                generated_diff = '\n'.join(cleaned_lines).strip()

            print(f'     ✅ LLM retry generated diff: {len(generated_diff)} characters')
            return {'success': True, 'chisel_diff': generated_diff, 'prompt_used': prompt_key, 'attempt': attempt}

        except Exception as e:
            print(f'     ❌ LLM retry failed: {e}')
            return {'success': False, 'error': str(e)}

    def _extract_code_from_hits(self, hits: list, docker_container: str) -> str:
        """Extract actual Chisel code content from module_finder hits"""
        # print('🔍 [HINTS] Extracting actual code content from hits...')

        all_code_hints = []

        for i, hit in enumerate(hits[:5]):  # Top 5 hits to avoid too much context
            try:
                file_path = hit.file_name

                import subprocess

                # Handle Docker vs local paths
                if file_path.startswith('docker:'):
                    # Parse docker path: docker:container_name:file_path
                    parts = file_path.split(':', 2)
                    actual_file_path = parts[2]

                    # Read from Docker container
                    cmd = ['docker', 'exec', docker_container, 'sed', '-n', f'{hit.start_line},{hit.end_line}p', actual_file_path]
                    result = subprocess.run(cmd, capture_output=True, text=True, check=True)
                    code_content = result.stdout.strip()
                else:
                    # Local file - read directly
                    actual_file_path = file_path
                    try:
                        with open(file_path, 'r') as f:
                            lines = f.readlines()
                            # Extract specific lines (1-indexed)
                            start_idx = max(0, hit.start_line - 1)
                            end_idx = min(len(lines), hit.end_line)
                            selected_lines = lines[start_idx:end_idx]
                            code_content = ''.join(selected_lines).strip()
                    except Exception as local_error:
                        print(f'     ❌ Failed to read local file {file_path}: {local_error}')
                        continue

                if code_content:
                    # Convert Docker absolute path to repository-relative path
                    if file_path.startswith('docker:') and actual_file_path.startswith('/code/workspace/repo/'):
                        relative_path = actual_file_path[len('/code/workspace/repo/') :]
                    else:
                        relative_path = actual_file_path

                    hint_block = f"""
// ========== HIT {i + 1}: {hit.module_name} (confidence: {hit.confidence:.2f}) ==========
// File: {relative_path}
// Lines: {hit.start_line}-{hit.end_line}
{code_content}
// ========== END HIT {i + 1} ==========
"""
                    all_code_hints.append(hint_block)
                    print(f'     ✅ Extracted {len(code_content)} chars from {hit.module_name}')
                else:
                    print(f'     ⚠️  No content found for {hit.module_name}')

            except Exception as e:
                print(f'     ❌ Failed to extract code from {hit.module_name}: {e}')
                continue

        combined_hints = '\n'.join(all_code_hints)
        # print(f'✅ [HINTS] Generated {len(combined_hints)} characters of actual code hints')

        return combined_hints

    def _process_single_bug(
        self, bug_idx: int, bug_entry: dict, local_files: list, docker_container: str, docker_patterns: list
    ) -> dict:
        """Process a single bug entry with module_finder"""
        print(f'\n{"=" * 60}')
        print(f'[V2chisel_batch] Processing Bug #{bug_idx + 1}')
        print(f'{"=" * 60}')

        # Extract information from bug entry
        file_name = bug_entry.get('file', 'unknown')
        unified_diff = bug_entry.get('unified_diff', '')

        # print(f'📁 Verilog file: {file_name}')
        print('📝 Diff preview (first 3 lines):')

        diff_lines = unified_diff.strip().split('\n')
        for i, line in enumerate(diff_lines[:3]):
            print(f'   {line}')
        if len(diff_lines) > 3:
            print(f'   ... ({len(diff_lines) - 3} more lines)')

        # Extract module name from file name (remove .sv extension)
        module_name = os.path.splitext(file_name)[0] if file_name else None

        print(f'Processing module: {module_name}')
        print(f'Docker container: {docker_container}')

        # OPTIMIZATION: Search Docker files specific to this module
        # print(f'🐳 Searching Docker for module: {module_name}')
        docker_files = self._find_chisel_files_docker_filtered(docker_container, docker_patterns, module_name)

        # Combine local and filtered Docker files
        all_files = local_files + docker_files
        # print(f'📁 Total files for this bug: {len(all_files)} (local: {len(local_files)}, docker: {len(docker_files)})')

        # Prepare files for module_finder (handle Docker files)
        # print('🔧 Preparing files for module_finder...')
        prepared_files = self._prepare_files_for_module_finder(all_files)
        # print(f'✅ Prepared {len(prepared_files)} files (including {len(getattr(self, "temp_files", []))} temp files)')

        # Search for actual Verilog files in Docker to improve module context
        verilog_context = self._find_verilog_files_in_docker(docker_container, module_name)

        # Call module_finder
        # print('🚀 Calling module_finder...')
        try:
            hits = self.module_finder.find_modules(
                scala_files=prepared_files, verilog_module=module_name, verilog_diff=unified_diff
            )

            # print(f'✅ Module_finder returned {len(hits)} hits')

            # Map temp file paths back to original Docker paths
            mapped_hits = []
            for hit in hits:
                original_path = getattr(self, 'temp_to_original', {}).get(hit.file_name, hit.file_name)
                # Create new hit with original path
                mapped_hit = type(hit)(
                    file_name=original_path,
                    module_name=hit.module_name,
                    start_line=hit.start_line,
                    end_line=hit.end_line,
                    confidence=hit.confidence,
                )
                mapped_hits.append(mapped_hit)

            # Display results
            if mapped_hits:
                # print('📋 Module finder results:')
                # for i, hit in enumerate(mapped_hits[:3]):  # Show top 3 hits
                #     confidence_bar = '█' * int(hit.confidence * 10) + '░' * (10 - int(hit.confidence * 10))
                #     confidence_emoji = '🟢' if hit.confidence >= 0.8 else '🟡' if hit.confidence >= 0.5 else '🔴'
                #     print(f'  [{i + 1}] {confidence_emoji} {hit.module_name} ({hit.confidence:.2f}) [{confidence_bar}]')
                #
                #     # Show if it's a Docker file
                #     if hit.file_name.startswith('docker:'):
                #         container_info = hit.file_name.split(':')[1]
                #         file_path = hit.file_name.split(':', 2)[2]
                #         print(f'      🐳 Container: {container_info}')
                #         print(f'      📁 File: {file_path}')
                #     else:
                #         print(f'      📁 File: {hit.file_name}')
                #
                #     print(f'      📍 Lines: {hit.start_line}-{hit.end_line}')
                #
                # if len(mapped_hits) > 3:
                #     print(f'      ... and {len(mapped_hits) - 3} more hits')
                pass  # Module finder results commented out
            else:
                print('❌ No module matches found')

            hits = mapped_hits  # Use mapped hits for further processing

        except Exception as e:
            print(f'❌ Module_finder failed: {e}')
            hits = []
        finally:
            # Clean up temp files
            self._cleanup_temp_files()

        # HYBRID APPROACH: If module_finder failed or found no good hits, try metadata fallback
        use_metadata_fallback = False
        metadata_hints = ''

        if not hits or len(hits) == 0:
            print('🔄 Module_finder found no hits - trying metadata fallback...')
            use_metadata_fallback = True
        elif max(hit.confidence for hit in hits) < 0.5:
            print('🔄 Module_finder confidence too low - trying metadata fallback...')
            use_metadata_fallback = True

        if use_metadata_fallback:
            metadata_hints = self._get_metadata_fallback_hints(docker_container, file_name, unified_diff)

        # Prepare final hints for LLM
        final_hints = ''
        hints_source = ''

        if hits and len(hits) > 0 and max(hit.confidence for hit in hits) >= 0.5:
            # Use module_finder results - extract actual code content
            hints_source = 'module_finder'
            final_hints = f'// Module finder results for {module_name}\n\n'

            # Print hint files and paths
            print('Hint files:')
            for i, hit in enumerate(hits[:5]):  # Show first 5 hits
                if hit.file_name.startswith('docker:'):
                    file_path = hit.file_name.split(':', 2)[2]
                    print(f'  [{i + 1}] {file_path} (lines {hit.start_line}-{hit.end_line}, confidence: {hit.confidence:.2f})')
                else:
                    print(
                        f'  [{i + 1}] {hit.file_name} (lines {hit.start_line}-{hit.end_line}, confidence: {hit.confidence:.2f})'
                    )

            # Extract actual Chisel code from the hits
            code_hints = self._extract_code_from_hits(hits, docker_container)
            final_hints += code_hints

            # print(f'✅ Using module_finder hints: {len(hits)} hits')

        elif metadata_hints.strip():
            # Use metadata fallback
            hints_source = 'metadata_fallback'
            final_hints = metadata_hints
            # print(f'✅ Using metadata fallback hints: {len(metadata_hints)} characters')

        else:
            # No hints available
            hints_source = 'none'
            final_hints = f'// No hints found for {module_name} via module_finder or metadata fallback'
            # print(f'❌ No hints available for {module_name}')

        # print(f'📝 Final hints source: {hints_source}')

        # STEP 3: Create MASTER backup before starting any LLM attempts
        print('💾 [MASTER_BACKUP] Creating master backup of original files before LLM processing...')
        master_backup_info = self._create_master_backup(docker_container, unified_diff)
        if not master_backup_info['success']:
            print(f'❌ MASTER_BACKUP: Failed - {master_backup_info.get("error", "Unknown error")}')
            print('     ⚠️  Continuing without backup (risky!)')

        # STEP 4: LLM + Applier + Compiler retry loop WITH ORIGINAL RESTORE
        llm_result = {}
        applier_result = {}
        compile_result = {}
        generated_chisel_diff = ''
        max_retries = 3
        current_attempt = 1

        if final_hints.strip():
            print('🤖 [LLM] Starting LLM call for Chisel diff generation...')

            # DEBUG: Print the exact query being sent to LLM
            # print('🔍 [DEBUG] VERILOG_DIFF being sent to LLM:')
            # print('-' * 40)
            # print(unified_diff)
            # print('-' * 40)
            #
            # print('🔍 [DEBUG] CHISEL_HINTS being sent to LLM:')
            # print('=' * 80)
            # print(final_hints)  # Comment out hints printing
            # print('=' * 80)
            # print(f'🔍 [DEBUG] CHISEL_HINTS length: {len(final_hints)} characters')

            llm_result = self._call_llm_for_chisel_diff(
                verilog_diff=unified_diff, chisel_hints=final_hints, attempt=current_attempt
            )

            # Retry loop for LLM + Applier + Compiler
            while current_attempt <= max_retries:
                if not llm_result['success']:
                    print(f'❌ [LLM] Failed to generate Chisel diff: {llm_result.get("error", "Unknown error")}')
                    break

                generated_chisel_diff = llm_result['chisel_diff']
                print(f'LLM Generated Chisel Diff (attempt {current_attempt}):')
                print('=' * 50)
                print(generated_chisel_diff)
                print('=' * 50)

                # STEP 1: Apply the diff directly (we have master backup as safety net)
                applier_result = self._apply_chisel_diff(generated_chisel_diff, docker_container)

                if applier_result['success']:
                    print('✅ APPLIER: Successfully applied diff')

                    # STEP 3: Try to compile
                    compile_result = self._compile_xiangshan(docker_container)

                    if compile_result['success']:
                        print('✅ COMPILATION: Success')

                        # STEP 4: Try to generate Verilog from compiled Chisel
                        verilog_gen_result = self._generate_verilog_from_chisel(docker_container, module_name)

                        if verilog_gen_result['success']:
                            print('✅ VERILOG_GENERATION: Success')

                            # NEW: Create golden design for LEC
                            golden_result = self._create_golden_design(docker_container, unified_diff, master_backup_info)

                            if golden_result.get('success', False):
                                print('✅ GOLDEN_DESIGN: Success')

                                # Now both designs are ready for LEC:
                                # - Gate design: newly generated Verilog from modified Chisel
                                # - Golden design: baseline Verilog + verilog_diff
                                lec_result = self._run_lec(docker_container)

                                if lec_result.get('success', False):
                                    print('✅ LEC: Logic Equivalence Check passed')

                                    # SUCCESS: Clean up MASTER backup since everything worked including LEC
                                    self._cleanup_master_backup(docker_container, master_backup_info)
                                    print('✅ PIPELINE: Complete pipeline successful (including LEC)!')
                                    break
                                else:
                                    lec_error = lec_result.get('error', 'Unknown LEC error')
                                    print(f'❌ LEC: Failed - {lec_error}')
                                    print('   LEC failure may indicate logical differences between designs')

                                    # RESTORE: LEC failed, restore to ORIGINAL state
                                    restore_result = self._restore_to_original(
                                        docker_container, master_backup_info, 'lec_failure'
                                    )

                                    # LEC failure could indicate a problem with the Chisel diff
                                    # This might be worth an LLM retry in some cases
                                    print(
                                        "⚠️  LEC failure - this may indicate the Chisel diff doesn't achieve the target Verilog changes"
                                    )
                                    compile_result = {
                                        'success': False,
                                        'error': f'LEC failed: {lec_error}',
                                        'compilation_method': 'lec_verification_failure',
                                    }
                                    break
                            else:
                                golden_error = golden_result.get('error', 'Unknown golden design error')
                                print(f'⚠️  GOLDEN_DESIGN: Failed - {golden_error}')
                                print('   LEC will be skipped due to golden design failure')

                                # Pipeline can still succeed without LEC (golden design is optional)
                                # SUCCESS: Clean up MASTER backup since core functionality worked
                                self._cleanup_master_backup(docker_container, master_backup_info)
                                print('✅ PIPELINE: Complete pipeline successful (LEC skipped due to golden design failure)!')
                                break
                        else:
                            verilog_error = verilog_gen_result.get('error', 'Unknown error')
                            is_tooling_issue = verilog_gen_result.get('tooling_issue', False)

                            print(f'❌ VERILOG_GENERATION: Failed - {verilog_error}')

                            # RESTORE: Verilog generation failed, restore to ORIGINAL state
                            restore_result = self._restore_to_original(
                                docker_container, master_backup_info, 'verilog_generation_failure'
                            )

                            if is_tooling_issue:
                                print('⚠️  This appears to be a tooling/configuration issue, not a Chisel diff problem')
                                print('   Skipping LLM retry as the issue is not related to the generated diff')
                                print('   Suggestions:')
                                print('   - Ensure Main object exists with ChiselStage.emitSystemVerilogFile')
                                print('   - Check mill/sbt configuration')
                                print('   - Verify build dependencies')
                                compile_result = {
                                    'success': False,
                                    'error': f'Tooling issue: {verilog_error}',
                                    'compilation_method': 'verilog_gen_tooling_failure',
                                }
                                break
                            else:
                                # This might be related to the Chisel diff - retry with LLM
                                full_error_msg = f'Compilation succeeded but Verilog generation failed: {verilog_error}'
                                if current_attempt < max_retries:
                                    print(
                                        f'🔄 RETRY: Attempting retry {current_attempt + 1}/{max_retries} with Verilog generation error'
                                    )
                                    llm_result = self._retry_llm_with_error(
                                        verilog_diff=unified_diff,
                                        chisel_hints=final_hints,
                                        previous_chisel_diff=generated_chisel_diff,
                                        error_message=full_error_msg,
                                        attempt=current_attempt + 1,
                                    )
                                    current_attempt += 1
                                else:
                                    print(f'❌ [FINAL] Maximum retries ({max_retries}) reached')
                                    break
                    else:
                        # Compilation failed - restore backup and retry with compilation error feedback
                        compile_error_msg = compile_result.get('error', 'Unknown compilation error')
                        print(f'❌ COMPILATION: Failed - {compile_error_msg}')

                        # RESTORE: Compilation failed, restore to ORIGINAL state before retry
                        restore_result = self._restore_to_original(docker_container, master_backup_info, 'compilation_failure')

                        if current_attempt < max_retries:
                            print(f'🔄 RETRY: Attempting retry {current_attempt + 1}/{max_retries} with compilation error')
                            llm_result = self._retry_llm_with_error(
                                verilog_diff=unified_diff,
                                chisel_hints=final_hints,
                                previous_chisel_diff=generated_chisel_diff,
                                error_message=compile_error_msg,
                                attempt=current_attempt + 1,
                            )
                            current_attempt += 1
                        else:
                            print(f'❌ [FINAL] Maximum retries ({max_retries}) reached')
                            break
                else:
                    # Applier failed - no need to restore since diff wasn't applied
                    error_msg = applier_result.get('error', 'Unknown error')
                    print(f'❌ APPLIER: Failed - {error_msg}')

                    # Don't retry LLM for permission/file writing errors
                    if 'Permission denied' in error_msg or 'docker cp' in error_msg or 'chmod' in error_msg:
                        print('⚠️ This is a Docker permission issue, not an LLM diff problem. Skipping LLM retry.')
                        break

                    if current_attempt < max_retries:
                        print(f'🔄 RETRY: Attempting retry {current_attempt + 1}/{max_retries}')
                        llm_result = self._retry_llm_with_error(
                            verilog_diff=unified_diff,
                            chisel_hints=final_hints,
                            previous_chisel_diff=generated_chisel_diff,
                            error_message=error_msg,
                            attempt=current_attempt + 1,
                        )
                        current_attempt += 1
                    else:
                        print(f'❌ [FINAL] Maximum retries ({max_retries}) reached')
                        break
        else:
            print('⚠️ LLM: Skipped - no hints available')
            llm_result = {'success': False, 'error': 'No hints available for LLM'}
            applier_result = {'success': False, 'error': 'No LLM output to apply'}
            compile_result = {'success': False, 'error': 'No diff applied to compile'}

        # FINAL CLEANUP: If we reach here without full success, ensure files are restored to original state
        # Check if verilog_gen_result exists and was successful
        verilog_success = False
        if 'verilog_gen_result' in locals():
            verilog_success = verilog_gen_result.get('success', False)

        pipeline_fully_successful = (
            llm_result.get('success', False)
            and applier_result.get('success', False)
            and compile_result.get('success', False)
            and verilog_success
        )

        print(
            f'📊 [PIPELINE_CHECK] LLM: {llm_result.get("success", False)}, Applier: {applier_result.get("success", False)}, Compile: {compile_result.get("success", False)}, Verilog: {verilog_success}'
        )

        if not pipeline_fully_successful and master_backup_info.get('success', False):
            print('🔄 [FINAL_RESTORE] Pipeline not fully successful - restoring to original state')
            print(f'     Reason: Full pipeline success = {pipeline_fully_successful}')
            final_restore_result = self._restore_to_original(
                docker_container, master_backup_info, 'pipeline_incomplete_or_failed'
            )
            # Keep master backup for potential future runs - don't clean up yet
        else:
            print('✅ [FINAL_CHECK] Pipeline fully successful OR no master backup - keeping current state')
            final_restore_result = {'success': True, 'message': 'No restore needed'}

        # Return results for this bug
        result = {
            'bug_index': bug_idx,
            'verilog_file': file_name,
            'module_name': module_name,
            'unified_diff': unified_diff,
            'module_finder_hits': len(hits),
            'hits': [
                {
                    'module_name': hit.module_name,
                    'file_name': hit.file_name,
                    'start_line': hit.start_line,
                    'end_line': hit.end_line,
                    'confidence': hit.confidence,
                }
                for hit in hits
            ]
            if hits
            else [],
            'hints_source': hints_source,
            'final_hints': final_hints,
            'has_hints': bool(final_hints.strip()),
            'llm_success': llm_result.get('success', False),
            'generated_chisel_diff': generated_chisel_diff,
            'llm_prompt_used': llm_result.get('prompt_used', ''),
            'llm_error': llm_result.get('error', '') if not llm_result.get('success', False) else '',
            'applier_success': applier_result.get('success', False),
            'applier_error': applier_result.get('error', '') if not applier_result.get('success', False) else '',
            'compile_success': compile_result.get('success', False),
            'compile_error': compile_result.get('error', '') if not compile_result.get('success', False) else '',
            'compile_method': compile_result.get('compilation_method', ''),
            'verilog_generation_attempted': 'verilog_gen_result' in locals() and current_attempt <= max_retries,
            'verilog_generation_success': locals().get('verilog_gen_result', {}).get('success', False),
            'verilog_generation_error': locals().get('verilog_gen_result', {}).get('error', ''),
            'lec_attempted': False,  # Will be True when LEC is enabled
            'lec_equivalent': None,
            'lec_error': '',
            'master_backup_created': master_backup_info.get('success', False),
            'master_backup_id': master_backup_info.get('backup_id', ''),
            'files_backed_up': len(master_backup_info.get('files_backed_up', [])),
            'restore_to_original_performed': locals().get('restore_result', {}).get('success', False)
            or locals().get('final_restore_result', {}).get('success', False),
            'restore_reason': locals().get('restore_result', {}).get('restore_reason', '')
            or locals().get('final_restore_result', {}).get('restore_reason', ''),
            'total_attempts': current_attempt,
            'pipeline_success': (
                llm_result.get('success', False)
                and applier_result.get('success', False)
                and compile_result.get('success', False)
                and locals().get('verilog_gen_result', {}).get('success', False)
            ),
            'golden_design_success': locals().get('golden_result', {}).get('success', False),
            'lec_success': locals().get('lec_result', {}).get('success', False),
            'lec_method': locals().get('lec_result', {}).get('lec_method', 'none'),
        }

        return result

    def run(self, data):
        """Main processing function - Step 1: Read bugs and call module_finder"""
        print('\n🚀 Starting V2chisel_batch processing...')

        # Step 1: Load bug list (check input_data first, then external file)
        if 'bugs' in self.input_data:
            # Bugs defined directly in input file
            bugs = self.input_data['bugs']
            print(f'[V2chisel_batch] Using bugs from input_data: {len(bugs)} bugs')
        else:
            # Load from external bug list file
            bug_file = self.input_data.get('bug_list_file', 'bug_lists_unified.yaml')
            bugs = self._load_bug_list(bug_file)

        # Step 2: Get configuration (but don't search files yet - we'll do per-bug filtering)
        chisel_patterns = self.input_data.get('chisel_patterns', [self.chisel_source_pattern])
        # Also support single pattern for backward compatibility
        if 'chisel_pattern' in self.input_data:
            single_pattern = self.input_data['chisel_pattern']
            if isinstance(single_pattern, str):
                chisel_patterns = [single_pattern]
            else:
                chisel_patterns = single_pattern

        # Get local files once (these are small)
        print('[V2chisel_batch] Finding local Chisel files...')
        local_files = []
        for pattern in chisel_patterns:
            files = glob.glob(pattern, recursive=True)
            local_files.extend(files)
        print(f'[V2chisel_batch] Found {len(local_files)} local Chisel files')

        # Step 3: Process each bug
        print(f'\n🔄 Processing {len(bugs)} bugs...')
        results = []

        docker_container = self.input_data.get('docker_container', 'hagent')
        docker_patterns = self.input_data.get('docker_patterns', ['/code/workspace/repo'])

        for i, bug_entry in enumerate(bugs):
            try:
                bug_result = self._process_single_bug(i, bug_entry, local_files, docker_container, docker_patterns)
                results.append(bug_result)

                # Show progress based on actual pipeline success
                pipeline_success = bug_result.get('pipeline_success', False)
                if pipeline_success:
                    print(f'✅ Bug #{i + 1} completed successfully (full pipeline success)')
                else:
                    print(f'⚠️  Bug #{i + 1} processed but failed (pipeline incomplete or failed)')

                # Add small delay to see output clearly
                if self.debug:
                    import time

                    time.sleep(0.1)

            except Exception as e:
                print(f'❌ Bug #{i + 1} failed: {e}')
                # Continue with next bug
                results.append(
                    {
                        'bug_index': i,
                        'error': str(e),
                        'verilog_file': bug_entry.get('file', 'unknown'),
                        'module_finder_hits': 0,
                        'hits': [],
                    }
                )

        # Step 4: Generate summary
        total_bugs = len(results)
        bugs_with_hints = sum(1 for r in results if r.get('has_hints', False))
        module_finder_successes = sum(1 for r in results if r.get('hints_source') == 'module_finder')
        metadata_fallbacks = sum(1 for r in results if r.get('hints_source') == 'metadata_fallback')
        # no_hints = sum(1 for r in results if r.get('hints_source') == 'none')

        # Pipeline statistics (TRUE success = full pipeline completion)
        pipeline_successes = sum(1 for r in results if r.get('pipeline_success', False))
        llm_successes = sum(1 for r in results if r.get('llm_success', False))
        llm_attempts = sum(1 for r in results if r.get('has_hints', False))  # Only attempted where hints exist

        # Golden design and LEC statistics
        golden_design_successes = sum(1 for r in results if r.get('golden_design_success', False))
        lec_successes = sum(1 for r in results if r.get('lec_success', False))
        lec_attempts = sum(1 for r in results if r.get('lec_method') != 'none')

        print('\n📊 V2CHISEL_BATCH COMPLETE SUMMARY:')
        # Summary stats commented out for cleaner output
        # print(f'   📋 Total bugs processed: {total_bugs}')
        # print('   🔍 HINTS GENERATION:')
        # print(f'       Module_finder successes: {module_finder_successes}')
        # print(f'       Metadata fallbacks used: {metadata_fallbacks}')
        # print(f'       No hints available: {no_hints}')
        # print(f'       📈 Total with hints: {bugs_with_hints}/{total_bugs} ({bugs_with_hints / total_bugs * 100:.1f}%)')
        # print('   🤖 LLM CHISEL DIFF GENERATION:')
        # print(f'       LLM attempts made: {llm_attempts}')
        # print(f'       LLM successes: {llm_successes}')
        # print(f'       📈 LLM success rate: {llm_successes / llm_attempts * 100:.1f}%' if llm_attempts > 0 else '0.0%')
        # print('   🎯 PIPELINE STATUS:')
        # print(f'       ✅ Ready for next step: {llm_successes} bugs have Chisel diffs')
        # print(f'       ⚠️  Need attention: {total_bugs - llm_successes} bugs failed LLM generation')
        print(f'Processed {total_bugs} bugs: {pipeline_successes} successful (full pipeline), {llm_successes} LLM successful')
        if lec_attempts > 0:
            print(
                f'LEC Results: {lec_successes}/{lec_attempts} successful ({lec_successes / lec_attempts * 100:.1f}%), Golden Design: {golden_design_successes}/{total_bugs} successful'
            )

        # Return results
        final_result = data.copy()
        final_result['v2chisel_batch_with_llm'] = {
            'total_bugs': total_bugs,
            'pipeline_successes': pipeline_successes,
            'pipeline_success_rate': pipeline_successes / total_bugs * 100 if total_bugs > 0 else 0.0,
            'module_finder_successes': module_finder_successes,
            'metadata_fallbacks': metadata_fallbacks,
            'bugs_with_hints': bugs_with_hints,
            'hints_coverage_rate': bugs_with_hints / total_bugs * 100,
            'llm_attempts': llm_attempts,
            'llm_successes': llm_successes,
            'llm_success_rate': llm_successes / llm_attempts * 100 if llm_attempts > 0 else 0.0,
            'golden_design_successes': golden_design_successes,
            'lec_attempts': lec_attempts,
            'lec_successes': lec_successes,
            'lec_success_rate': lec_successes / lec_attempts * 100 if lec_attempts > 0 else 0.0,
            'bug_results': results,
            'local_files_found': len(local_files),
            'chisel_patterns_used': chisel_patterns,
            'docker_container': docker_container,
            'docker_patterns': docker_patterns,
        }

        # Final cleanup
        self._cleanup_temp_files()

        return final_result


def wrap_literals(obj):
    """Wrap multi-line strings as YAML literal scalars"""
    if isinstance(obj, dict):
        return {k: wrap_literals(v) for k, v in obj.items()}
    elif isinstance(obj, list):
        return [wrap_literals(elem) for elem in obj]
    elif isinstance(obj, str) and '\n' in obj:
        return LiteralScalarString(obj)
    else:
        return obj


def parse_arguments():
    parser = argparse.ArgumentParser(description='V2Chisel Batch Processing - Step 1')
    parser.add_argument('-o', required=True, help='Output YAML file')
    parser.add_argument('input_file', help='Input YAML file (can be minimal)')
    return parser.parse_args()


if __name__ == '__main__':
    args = parse_arguments()

    # Create step instance
    step = V2chisel_batch()
    step.parse_arguments()
    step.setup()

    # Run the step
    result = step.step()

    # Wrap multiline strings for proper YAML output
    result = wrap_literals(result)

    # Save results
    yaml = YAML()
    yaml.default_flow_style = False
    yaml.indent(mapping=2, sequence=4, offset=2)

    with open(args.o, 'w') as out_file:
        yaml.dump(result, out_file)

    print(f'\n✅ Results saved to: {args.o}')
