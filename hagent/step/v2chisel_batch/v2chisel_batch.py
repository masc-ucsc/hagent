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

        self.lw = LLM_wrap(
            name='v2chisel_batch', log_file='v2chisel_batch.log', conf_file=conf_file, overwrite_conf={'llm': final_llm_config}
        )

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

        print(f'[V2chisel_batch] Searching inside Docker container: {container_name}')
        docker_files = []

        for pattern in docker_patterns:
            print(f'  🐳 Docker pattern: {pattern}')
            try:
                # OPTIMIZATION: Search for files containing the module name first
                if module_name:
                    print(f'  🔍 Pre-filtering for module: {module_name}')
                    # Use grep to find files containing the module name (much faster)
                    grep_cmd = [
                        'docker',
                        'exec',
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

                    print(f'     Pre-filtered to: {len(files)} files matching "{module_name}"')

                    # If no matches with exact name, try broader search
                    if not files and len(module_name) > 3:
                        print('  🔍 Trying broader search with partial name...')
                        partial_name = module_name[:4] if len(module_name) > 4 else module_name
                        grep_cmd = [
                            'docker',
                            'exec',
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
                        print(f'     Broader search found: {len(files)} files')
                else:
                    # Fallback: get all files (but limit to reasonable number)
                    cmd = ['docker', 'exec', container_name, 'find', pattern, '-name', '*.scala', '-type', 'f']
                    result = subprocess.run(cmd, capture_output=True, text=True, check=True)
                    all_files = [f.strip() for f in result.stdout.split('\n') if f.strip()]
                    # Limit to first 100 files to avoid performance issues
                    files = all_files[:100]
                    print(f'     Found: {len(all_files)} files, limited to: {len(files)} for performance')

                if files:
                    for f in files[:3]:  # Show first 3
                        print(f'     - {f}')
                    if len(files) > 3:
                        print(f'     ... and {len(files) - 3} more')

                # Add docker: prefix to distinguish from local files
                docker_files.extend([f'docker:{container_name}:{f}' for f in files])

            except subprocess.CalledProcessError as e:
                print(f'     ❌ Docker command failed: {e}')
            except Exception as e:
                print(f'     ❌ Error: {e}')

        return docker_files

    def _find_chisel_files_docker(self, container_name: str, docker_patterns: list) -> list:
        """Legacy method - use filtered version instead"""
        return self._find_chisel_files_docker_filtered(container_name, docker_patterns)

    def _find_chisel_files(self, patterns=None) -> list:
        """Find Chisel source files using glob patterns (supports multiple patterns and Docker)"""
        import glob

        if patterns is None:
            patterns = [self.chisel_source_pattern]
        elif isinstance(patterns, str):
            patterns = [patterns]

        print(f'[V2chisel_batch] Searching for Chisel files with {len(patterns)} pattern(s):')

        all_chisel_files = []

        # Check if Docker container specified
        docker_container = self.input_data.get('docker_container', 'musing_sammet')
        docker_patterns = self.input_data.get('docker_patterns', ['/code/workspace/repo'])

        # Search in Docker first
        if docker_container:
            docker_files = self._find_chisel_files_docker(docker_container, docker_patterns)
            all_chisel_files.extend(docker_files)

        # Then search local patterns
        for pattern in patterns:
            if pattern.startswith('docker:'):
                continue  # Skip docker patterns in local search

            print(f'  📁 Local pattern: {pattern}')
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

                except Exception as e:
                    print(f'     ⚠️  Failed to read Docker file {file_path}: {e}')
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
                except:
                    pass
            self.temp_files = []

    def _parse_metadata_from_rtl(self, docker_container: str, verilog_file: str, verilog_diff: str) -> dict:
        """Parse metadata from RTL files to extract Chisel file:line mappings"""
        import subprocess
        import re

        print(f'🔍 [METADATA FALLBACK] Parsing RTL metadata for: {verilog_file}')

        # Find the RTL file in build_debug
        rtl_path = f'/code/workspace/build/build_dbg/rtl/{verilog_file}'

        try:
            # Check if RTL file exists
            check_cmd = ['docker', 'exec', docker_container, 'test', '-f', rtl_path]
            result = subprocess.run(check_cmd, capture_output=True)

            if result.returncode != 0:
                print(f'     ❌ RTL file not found: {rtl_path}')
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
            print(f'     📁 Mapped to {len(file_mappings)} Chisel files:')
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

        print(f'🔧 [METADATA FALLBACK] Extracting hints from {len(file_mappings)} files...')

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
        print(f'     📝 Generated {len(hints_text)} characters of hints')

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
            print('     ✅ [METADATA FALLBACK] Generated hints successfully')
            return hints
        else:
            print('     ❌ [METADATA FALLBACK] No hints generated')
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
        print(f'🤖 [LLM] Calling LLM (attempt {attempt})...')

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

            print(f'     🎯 Using prompt: {prompt_key}')
            print(f'     📝 Template data keys: {list(template_data.keys())}')

            # Call LLM
            response_list = self.lw.inference(template_data, prompt_index=prompt_key, n=1)

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

            print(f'     ✅ LLM generated diff: {len(generated_diff)} characters')
            if self.debug:
                print('     📋 Generated diff preview (first 200 chars):')
                print(f'        {generated_diff[:200]}...')

            return {'success': True, 'chisel_diff': generated_diff, 'prompt_used': prompt_key, 'attempt': attempt}

        except Exception as e:
            print(f'     ❌ LLM call failed: {e}')
            return {'success': False, 'error': str(e)}

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

        print(f'📁 Verilog file: {file_name}')
        print('📝 Diff preview (first 3 lines):')

        diff_lines = unified_diff.strip().split('\n')
        for i, line in enumerate(diff_lines[:3]):
            print(f'   {line}')
        if len(diff_lines) > 3:
            print(f'   ... ({len(diff_lines) - 3} more lines)')

        # Extract module name from file name (remove .sv extension)
        module_name = os.path.splitext(file_name)[0] if file_name else None

        print(f'🔍 Extracted module name: {module_name}')

        # OPTIMIZATION: Search Docker files specific to this module
        print(f'🐳 Searching Docker for module: {module_name}')
        docker_files = self._find_chisel_files_docker_filtered(docker_container, docker_patterns, module_name)

        # Combine local and filtered Docker files
        all_files = local_files + docker_files
        print(f'📁 Total files for this bug: {len(all_files)} (local: {len(local_files)}, docker: {len(docker_files)})')

        # Prepare files for module_finder (handle Docker files)
        print('🔧 Preparing files for module_finder...')
        prepared_files = self._prepare_files_for_module_finder(all_files)
        print(f'✅ Prepared {len(prepared_files)} files (including {len(getattr(self, "temp_files", []))} temp files)')

        # Call module_finder
        print('🚀 Calling module_finder...')
        try:
            hits = self.module_finder.find_modules(
                scala_files=prepared_files, verilog_module=module_name, verilog_diff=unified_diff
            )

            print(f'✅ Module_finder returned {len(hits)} hits')

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
                print('📋 Module finder results:')
                for i, hit in enumerate(mapped_hits[:3]):  # Show top 3 hits
                    confidence_bar = '█' * int(hit.confidence * 10) + '░' * (10 - int(hit.confidence * 10))
                    confidence_emoji = '🟢' if hit.confidence >= 0.8 else '🟡' if hit.confidence >= 0.5 else '🔴'
                    print(f'  [{i + 1}] {confidence_emoji} {hit.module_name} ({hit.confidence:.2f}) [{confidence_bar}]')

                    # Show if it's a Docker file
                    if hit.file_name.startswith('docker:'):
                        container_info = hit.file_name.split(':')[1]
                        file_path = hit.file_name.split(':', 2)[2]
                        print(f'      🐳 Container: {container_info}')
                        print(f'      📁 File: {file_path}')
                    else:
                        print(f'      📁 File: {hit.file_name}')

                    print(f'      📍 Lines: {hit.start_line}-{hit.end_line}')

                if len(mapped_hits) > 3:
                    print(f'      ... and {len(mapped_hits) - 3} more hits')
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
            # Use module_finder results
            hints_source = 'module_finder'
            # Format module_finder hits as hints (you can customize this format)
            final_hints = f'// Module finder results for {module_name}\n'
            for i, hit in enumerate(hits[:3]):  # Top 3 hits
                final_hints += f'// Hit {i + 1}: {hit.module_name} in {hit.file_name} (lines {hit.start_line}-{hit.end_line}, confidence: {hit.confidence:.2f})\n'
            print(f'✅ Using module_finder hints: {len(hits)} hits')

        elif metadata_hints.strip():
            # Use metadata fallback
            hints_source = 'metadata_fallback'
            final_hints = metadata_hints
            print(f'✅ Using metadata fallback hints: {len(metadata_hints)} characters')

        else:
            # No hints available
            hints_source = 'none'
            final_hints = f'// No hints found for {module_name} via module_finder or metadata fallback'
            print(f'❌ No hints available for {module_name}')

        print(f'📝 Final hints source: {hints_source}')

        # STEP 3: Call LLM to generate Chisel diff
        llm_result = {}
        generated_chisel_diff = ''

        if final_hints.strip():
            print('🤖 [LLM] Starting LLM call for Chisel diff generation...')
            llm_result = self._call_llm_for_chisel_diff(verilog_diff=unified_diff, chisel_hints=final_hints, attempt=1)

            if llm_result['success']:
                generated_chisel_diff = llm_result['chisel_diff']
                print('✅ [LLM] Successfully generated Chisel diff')
            else:
                print(f'❌ [LLM] Failed to generate Chisel diff: {llm_result.get("error", "Unknown error")}')
        else:
            print('⚠️ [LLM] Skipping LLM call - no hints available')
            llm_result = {'success': False, 'error': 'No hints available for LLM'}

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
        }

        return result

    def run(self, data):
        """Main processing function - Step 1: Read bugs and call module_finder"""
        print('\n🚀 Starting V2chisel_batch processing...')

        # Step 1: Load bug list (assume it's provided in input_data or use default)
        bug_file = self.input_data.get('bug_list_file', '/home/farzaneh/hagent/bug_lists_unified.yaml')
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

        docker_container = self.input_data.get('docker_container', 'musing_sammet')
        docker_patterns = self.input_data.get('docker_patterns', ['/code/workspace/repo'])

        for i, bug_entry in enumerate(bugs):
            try:
                bug_result = self._process_single_bug(i, bug_entry, local_files, docker_container, docker_patterns)
                results.append(bug_result)

                # Show progress
                print(f'✅ Bug #{i + 1} processed successfully')

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
        successful_hits = sum(1 for r in results if r.get('module_finder_hits', 0) > 0)
        bugs_with_hints = sum(1 for r in results if r.get('has_hints', False))
        module_finder_successes = sum(1 for r in results if r.get('hints_source') == 'module_finder')
        metadata_fallbacks = sum(1 for r in results if r.get('hints_source') == 'metadata_fallback')
        no_hints = sum(1 for r in results if r.get('hints_source') == 'none')

        # LLM statistics
        llm_successes = sum(1 for r in results if r.get('llm_success', False))
        llm_attempts = sum(1 for r in results if r.get('has_hints', False))  # Only attempted where hints exist

        print('\n📊 V2CHISEL_BATCH COMPLETE SUMMARY:')
        print(f'   📋 Total bugs processed: {total_bugs}')
        print('   🔍 HINTS GENERATION:')
        print(f'       Module_finder successes: {module_finder_successes}')
        print(f'       Metadata fallbacks used: {metadata_fallbacks}')
        print(f'       No hints available: {no_hints}')
        print(f'       📈 Total with hints: {bugs_with_hints}/{total_bugs} ({bugs_with_hints / total_bugs * 100:.1f}%)')
        print('   🤖 LLM CHISEL DIFF GENERATION:')
        print(f'       LLM attempts made: {llm_attempts}')
        print(f'       LLM successes: {llm_successes}')
        print(f'       📈 LLM success rate: {llm_successes / llm_attempts * 100:.1f}%' if llm_attempts > 0 else '0.0%')
        print('   🎯 PIPELINE STATUS:')
        print(f'       ✅ Ready for next step: {llm_successes} bugs have Chisel diffs')
        print(f'       ⚠️  Need attention: {total_bugs - llm_successes} bugs failed LLM generation')

        # Return results
        final_result = data.copy()
        final_result['v2chisel_batch_with_llm'] = {
            'total_bugs': total_bugs,
            'module_finder_successes': module_finder_successes,
            'metadata_fallbacks': metadata_fallbacks,
            'bugs_with_hints': bugs_with_hints,
            'hints_coverage_rate': bugs_with_hints / total_bugs * 100,
            'llm_attempts': llm_attempts,
            'llm_successes': llm_successes,
            'llm_success_rate': llm_successes / llm_attempts * 100 if llm_attempts > 0 else 0.0,
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
