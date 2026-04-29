#!/usr/bin/env python3
"""
V2chisel_batch - Clean refactored version using MCP profile system

This is a complete rewrite that:
1. Uses MCP profiles for compilation/Verilog generation (no hardcoded SBT commands)
2. Keeps all existing components (BaselineVerilogGenerator, VerilogGenerator, etc.)
3. Simple, clean flow that's easy to debug and maintain
"""

import argparse
import os
import shutil
import subprocess
import sys
import uuid
import yaml
from pathlib import Path

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent.parent))

from hagent.core.step import Step
from hagent.inou.builder import Builder
from hagent.tool.module_finder import Module_finder
from hagent.tool.docker_diff_applier import DockerDiffApplier
from hagent.tool.equiv_check import Equiv_check
from hagent.tool.chisel_diff_corrector import ChiselDiffCorrector

# Import components
try:
    from .components.baseline_verilog_generator import BaselineVerilogGenerator
    from .components.verilog_generator import VerilogGenerator
    from .components.hints_generator_v2 import HintsGeneratorV2
    from .components.chisel_diff_generator import ChiselDiffGenerator
    from .components.backup_manager import BackupManager
    from .components.golden_design_builder import GoldenDesignBuilder
    from .components.pipeline_reporter import PipelineReporter
except ImportError:
    from components.baseline_verilog_generator import BaselineVerilogGenerator
    from components.verilog_generator import VerilogGenerator
    from components.hints_generator_v2 import HintsGeneratorV2
    from components.chisel_diff_generator import ChiselDiffGenerator
    from components.backup_manager import BackupManager
    from components.golden_design_builder import GoldenDesignBuilder
    from components.pipeline_reporter import PipelineReporter


class V2chisel_batch(Step):
    """Clean V2chisel_batch implementation using MCP profiles"""

    def __init__(self):
        """Initialize V2chisel_batch with Builder and components"""
        super().__init__()

        self.debug = True
        self.input_data = {}

        # Builder is deferred — created in run() AFTER workspace env vars are set
        self.builder = None

        # Initialize Module_finder for hints generation
        self.module_finder = Module_finder()

        # Initialize components (will be initialized in run() after input_data is loaded)
        self.baseline_verilog_generator = None
        self.verilog_generator = None
        self.hints_generator_v2 = None
        self.chisel_diff_generator = None
        self.docker_diff_applier = None
        self.backup_manager = None

        # Backup tracking
        self.master_backup_info = None

        print('✅ [V2chisel_batch] Initialized')

    def _setup_workspace(self):
        """
        Auto-create a temporary workspace by running setup_mcp.sh simplechisel,
        then read the generated env vars from hagent_server.sh (same approach as
        run_v2chisel_manual.py).  Sets HAGENT_* env vars in the current process.

        Returns the tmp_dir path (caller must pass to _cleanup_workspace).
        """
        scripts_dir = Path(__file__).parent.parent.parent.parent / 'scripts'
        setup_script = scripts_dir / 'setup_mcp.sh'
        if not setup_script.exists():
            raise FileNotFoundError(f'setup_mcp.sh not found at {setup_script}')

        tmp_dir = Path('/tmp') / f'v2chisel_batch_{uuid.uuid4().hex[:8]}'
        tmp_dir.mkdir(parents=True, exist_ok=True)
        print(f'\n🗂️  Auto-workspace: {tmp_dir}')

        project = self.input_data.get('project', 'simplechisel')
        print(f'🐳 Setting up workspace for project: {project}')
        result = subprocess.run(
            ['bash', str(setup_script), project, str(tmp_dir)],
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            raise RuntimeError(
                f'setup_mcp.sh failed (exit {result.returncode}):\nSTDOUT: {result.stdout}\nSTDERR: {result.stderr}'
            )

        # Read env vars from the generated hagent_server.sh.
        # setup_mcp.sh writes exactly these variables (one per line):
        #   UV_PROJECT, HAGENT_ROOT,
        #   HAGENT_DOCKER  -or-  HAGENT_EXECUTION_MODE  (only one, mode-dependent),
        #   HAGENT_REPO_DIR, HAGENT_BUILD_DIR, HAGENT_CACHE_DIR, HAGENT_TECH_DIR
        #
        # We only import the HAGENT_* vars (skip UV_PROJECT / HAGENT_ROOT so we
        # don't clobber the host process's own project-root settings).
        _WANTED_PREFIXES = ('HAGENT_',)

        server_sh = tmp_dir / 'hagent_server.sh'
        if not server_sh.exists():
            raise RuntimeError(f'setup_mcp.sh succeeded but hagent_server.sh was not created at {server_sh}')

        extracted: dict[str, str] = {}
        with open(server_sh) as f:
            for raw_line in f:
                line = raw_line.strip()
                if not line.startswith('export '):
                    continue
                var_part = line[len('export ') :]
                if '=' not in var_part:
                    continue
                key, raw_value = var_part.split('=', 1)
                key = key.strip()
                # Strip a single layer of wrapping quotes (" or ') without
                # eating embedded quotes (unlike str.strip which removes all
                # leading/trailing chars in the set).
                if len(raw_value) >= 2 and raw_value[0] in ('"', "'") and raw_value[-1] == raw_value[0]:
                    value = raw_value[1:-1]
                else:
                    value = raw_value
                if any(key.startswith(p) for p in _WANTED_PREFIXES):
                    extracted[key] = value

        # Apply extracted vars
        for key, value in extracted.items():
            os.environ[key] = value
        print(f'✅ Env vars loaded from hagent_server.sh ({len(extracted)} vars)')

        # Ensure HAGENT_TECH_DIR is set (setup_mcp.sh always writes it, but
        # fall back gracefully if it arrived empty/unset).
        if not os.environ.get('HAGENT_TECH_DIR'):
            default_tech = '/home/farzaneh/open_pdks/sky130/sky130B/libs.ref/sky130_fd_sc_hd/lib'
            os.environ['HAGENT_TECH_DIR'] = default_tech
            print(f'⚠️  HAGENT_TECH_DIR missing from server.sh — falling back to: {default_tech}')

        # Reset PathManager singleton + recreate Runner so they re-read the
        # freshly exported HAGENT_* env vars (including HAGENT_TECH_DIR).
        self._reset_path_manager_and_runner()

        # Verify workspace setup: check that repo and build dirs exist
        repo_dir = tmp_dir / 'repo'
        build_dir = tmp_dir / 'build'
        if repo_dir.exists() and build_dir.exists():
            print(f'✅ Workspace verified: repo and build dirs exist in {tmp_dir}')
        else:
            raise RuntimeError(f'Workspace setup incomplete: missing repo or build dir in {tmp_dir}')

        return tmp_dir

    def _cleanup_workspace(self, tmp_dir):
        """Delete the auto-created workspace directory to free disk space."""
        if tmp_dir and tmp_dir.exists():
            shutil.rmtree(tmp_dir, ignore_errors=True)
            print(f'🗑️  Cleaned up workspace: {tmp_dir}')

    def run(self, data):
        """Main processing function"""
        print('\n' + '=' * 80)
        print('🚀 V2chisel_batch - Clean MCP-based Pipeline')
        print('=' * 80)

        # Update input_data with any runtime data
        self.input_data.update(data)

        # Auto-setup workspace if any required env var is missing
        tmp_dir = None
        required_vars = ['HAGENT_REPO_DIR', 'HAGENT_BUILD_DIR', 'HAGENT_CACHE_DIR', 'HAGENT_TECH_DIR']
        if not all(os.environ.get(v) for v in required_vars):
            print('\n🔧 HAGENT env vars not fully set — auto-creating workspace via setup_mcp.sh...')
            try:
                tmp_dir = self._setup_workspace()
            except Exception as exc:
                error_msg = f'Workspace auto-setup failed: {exc}'
                print(f'❌ {error_msg}')
                return {'success': False, 'error': error_msg}

        # Create Builder now that env vars are guaranteed to be set
        self._reset_path_manager_and_runner()
        self.builder = Builder()

        try:
            return self._run_pipeline(data)
        finally:
            self._cleanup_workspace(tmp_dir)

    def _reset_path_manager_and_runner(self):
        """Reset the PathManager singleton so it re-reads the current env vars on next use."""
        from hagent.inou.path_manager import PathManager as _PM

        _PM._instance = None
        _PM._initialized = False
        if self.builder is not None:
            self.builder.runner = type(self.builder.runner)()

    def _run_pipeline(self, _data=None):
        """Internal pipeline — called after workspace is ready."""
        # Print env vars so the user can verify they are set correctly
        print('\n🔧 Environment variables:')
        for var in [
            'HAGENT_REPO_DIR',
            'HAGENT_BUILD_DIR',
            'HAGENT_CACHE_DIR',
            'HAGENT_TECH_DIR',
            'HAGENT_DOCKER',
            'HAGENT_EXECUTION_MODE',
        ]:
            print(f'   {var} = {os.environ.get(var, "(not set)")}')

        # Setup Builder (initialize filesystem and load hagent.yaml configuration)
        if not self.builder.setup():
            error_msg = f'Builder setup failed: {self.builder.get_error()}'
            print(f'❌ {error_msg}')
            return {'success': False, 'error': error_msg}

        # Initialize components now that we have input_data
        self.debug = self.input_data.get('debug', True)
        self.baseline_verilog_generator = BaselineVerilogGenerator(self.builder, debug=self.debug)
        self.verilog_generator = VerilogGenerator(self.builder, debug=self.debug)
        self.hints_generator_v2 = HintsGeneratorV2(self.module_finder, self.builder, debug=self.debug)

        # Initialize LLM component for Chisel diff generation
        # Default to v2chisel_batch_conf.yaml in the same directory
        default_config = str(Path(__file__).parent / 'v2chisel_batch_conf.yaml')
        llm_config_file = self.input_data.get('llm_config_file', default_config)
        llm_name = self.input_data.get('llm_name', 'v2chisel_batch')

        # Read LLM overrides from input YAML's v2chisel_batch.llm section
        llm_overrides = dict(self.input_data.get('v2chisel_batch', {}).get('llm', {}))

        # CLI --llm flag takes highest priority
        if self.input_data.get('llm_model'):
            llm_overrides['model'] = self.input_data['llm_model']

        # Auto-add bedrock/converse/ prefix when aws_region_name is set and model has no provider prefix
        if llm_overrides.get('aws_region_name') and '/' not in llm_overrides.get('model', ''):
            llm_overrides['model'] = 'bedrock/converse/' + llm_overrides['model']

        self.chisel_diff_generator = ChiselDiffGenerator(llm_config_file, llm_name, debug=self.debug, llm_overrides=llm_overrides)

        # Initialize DockerDiffApplier for applying Chisel diffs in Docker
        self.docker_diff_applier = DockerDiffApplier(self.builder)

        # Initialize BackupManager for handling Chisel file backups during retries
        self.backup_manager = BackupManager(self.builder, debug=self.debug)

        # Initialize GoldenDesignBuilder for creating golden design for LEC
        self.golden_design_builder = GoldenDesignBuilder(self.builder, debug=self.debug)

        # Initialize ChiselDiffCorrector for auto-correcting LLM-generated diffs
        # Confidence threshold: 0.90 = moderate (0.85 aggressive, 0.95 conservative)
        self.diff_corrector = ChiselDiffCorrector(confidence_threshold=0.90)

        # Initialize PipelineReporter for DAC metrics tracking
        self.pipeline_reporter = PipelineReporter()

        # Initialize Equiv_check for LEC verification
        self.equiv_check = Equiv_check()
        if not self.equiv_check.setup():
            print(f'⚠️  Warning: LEC setup failed: {self.equiv_check.get_error()}')

        # Step 1: Load bugs from input
        # Support xiangshan-style format: {verilog_diffs: [{filename, verilog_diff}, ...]}
        # All verilog_diffs in one record come from a SINGLE chisel mutation, so we
        # combine them into ONE bug with a multi-file unified diff.
        bugs = self.input_data.get('bugs', [])
        if not bugs and 'verilog_diffs' in self.input_data:
            verilog_diffs_list = self.input_data['verilog_diffs']
            description = self.input_data.get('mutation_type', '')
            scala_file = self.input_data.get('scala_file', '')
            if scala_file:
                description = f'{description} in {scala_file}'

            # Concatenate all per-file diffs into one multi-file unified diff
            combined_diff = '\n'.join(entry['verilog_diff'] for entry in verilog_diffs_list)
            verilog_files = [entry['filename'] for entry in verilog_diffs_list]

            bugs.append(
                {
                    'verilog_file': scala_file or verilog_files[0],
                    'unified_diff': combined_diff,
                    'description': description,
                    'verilog_files': verilog_files,  # all SV files for multi-hint lookup
                }
            )
            print(f'📦 Converted xiangshan format: {len(verilog_diffs_list)} verilog diffs → 1 combined bug')

        if not bugs:
            print('❌ No bugs found in input')
            return {'success': False, 'error': 'No bugs provided'}

        print(f'\n📋 Loaded {len(bugs)} bug(s) to process')

        # Step 2: Determine CPU profile
        cpu_profile = self._determine_cpu_profile(bugs)
        if cpu_profile is not None:
            print(f'🔧 Using CPU profile: {cpu_profile}')
        else:
            project = self.input_data.get('project', 'simplechisel')
            print(f'🔧 CPU profile: not applicable for project "{project}"')

        chisel_diff_only = self.input_data.get('chisel_diff_only', True)

        # Step 3: Generate fresh baseline Verilog
        # Skipped in chisel_diff_only mode or when the project has no CPU-profile system.
        baseline_result = {}
        if not chisel_diff_only and cpu_profile is not None:
            print('\n' + '=' * 80)
            print('STEP 1: Generate Fresh Baseline Verilog')
            print('=' * 80)

            baseline_result = self._generate_baseline_verilog(cpu_profile)

            if not baseline_result['success']:
                print(f'❌ Baseline generation failed: {baseline_result.get("error")}')
                return {'success': False, 'error': f'Baseline generation failed: {baseline_result.get("error")}'}

            print(f'✅ Baseline Verilog generation complete (profile: {baseline_result.get("profile")})')
        elif chisel_diff_only:
            print('\n⏭️  Skipping baseline generation (chisel_diff_only mode)')
        else:
            print('\n⏭️  Skipping baseline generation (no CPU profile for this project)')

        # Step 2: Process each bug with retry loops
        print('\n' + '=' * 80)
        print('STEP 2: Process Bugs' + (' (chisel_diff_only)' if chisel_diff_only else ' with Retry Loops'))
        print('=' * 80)

        bug_results = []
        for idx, bug in enumerate(bugs, 1):
            print(f'\n--- Processing Bug {idx}/{len(bugs)} ---')

            # Process bug with retry logic (pass baseline_result for golden design)
            bug_result = self._process_single_bug_with_retries(
                bug=bug, bug_number=idx, cpu_profile=cpu_profile, baseline_result=baseline_result
            )

            bug_results.append(bug_result)

        # Summary
        successful_bugs = sum(1 for r in bug_results if r.get('success'))
        total_cost = sum(r.get('llm_cost', 0) for r in bug_results)
        total_tokens = sum(r.get('llm_tokens', 0) for r in bug_results)

        if chisel_diff_only:
            print(f'\n✅ Generated chisel_diff for {successful_bugs}/{len(bugs)} bugs')
            print(f'💰 Total LLM cost: ${total_cost:.4f}')
            print(f'🔢 Total tokens used: {total_tokens}')

            if self.builder:
                self.builder.cleanup()
                print('🗑️  Docker container cleaned up')

            return {
                'success': True,
                'cpu_profile': cpu_profile,
                'bugs_processed': len(bugs),
                'bug_results': bug_results,
                'bugs_successful': successful_bugs,
                'total_llm_cost': total_cost,
                'total_llm_tokens': total_tokens,
            }

        diffs_applied = sum(1 for r in bug_results if r.get('diff_applied', False))
        compilations_successful = sum(1 for r in bug_results if r.get('compilation_success', False))
        verilog_generated = sum(1 for r in bug_results if r.get('verilog_generated', False))
        lec_passed = sum(1 for r in bug_results if r.get('lec_passed', False))
        total_files_modified = sum(r.get('files_modified', 0) for r in bug_results)

        print(f'\n✅ Successfully processed {successful_bugs}/{len(bugs)} bugs')
        print(f'📝 Diffs applied: {diffs_applied}/{len(bugs)}')
        print(f'🔨 Compilations successful: {compilations_successful}/{len(bugs)}')
        print(f'📄 Verilog generated: {verilog_generated}/{len(bugs)}')
        print(f'🔍 LEC passed: {lec_passed}/{len(bugs)}')
        print(f'📁 Chisel files modified: {total_files_modified}')
        print(f'💰 Total LLM cost: ${total_cost:.4f}')
        print(f'🔢 Total tokens used: {total_tokens}')

        # Print final DAC metrics summary
        self.pipeline_reporter.print_all_summaries()

        return {
            'success': True,
            'baseline_result': baseline_result,
            'cpu_profile': cpu_profile,
            'bugs_processed': len(bugs),
            'bug_results': bug_results,
            'bugs_successful': successful_bugs,
            'diffs_applied': diffs_applied,
            'compilations_successful': compilations_successful,
            'verilog_generated': verilog_generated,
            'lec_passed': lec_passed,
            'files_modified': total_files_modified,
            'total_llm_cost': total_cost,
            'total_llm_tokens': total_tokens,
        }

    def _determine_cpu_profile(self, bugs):
        """
        Determine which CPU profile to use for compilation/Verilog generation.

        CPU profiles are a simplechisel/dinocpu-specific concept.  Projects like
        xiangshan, soomrv, and cva6 do not have multiple CPU variants, so this
        function returns None for them and the caller skips profile-dependent steps.

        Priority for simplechisel:
        1. --cpu argument (from input_data['cpu_type'])
        2. Auto-detect from bug Verilog filenames
        3. Default to singlecyclecpu_d
        """
        project = self.input_data.get('project', 'simplechisel')

        # Projects with their own compile profiles (not dinocpu CPU-profile system)
        _PROJECT_COMPILE_PROFILES = {
            'xiangshan': {'dbg': 'xiangshan_rtl_dbg', 'opt': 'xiangshan_rtl_opt'},
            'soomrv': None,
            'cva6': None,
        }
        if project in _PROJECT_COMPILE_PROFILES:
            profiles = _PROJECT_COMPILE_PROFILES[project]
            if not profiles:
                print(f'ℹ️  Project "{project}" has no compile profile — skipping cpu_type detection')
                return None
            # Use --xiangshan-profile arg if provided, default to dbg
            xiangshan_profile = self.input_data.get('xiangshan_profile', 'dbg')
            profile = profiles.get(xiangshan_profile, profiles['dbg'])
            print(f'ℹ️  Project "{project}" using compile profile "{profile}"')
            return profile

        # Check for explicit override via --cpu argument
        cpu_override = self.input_data.get('cpu_type')
        if cpu_override:
            print(f'🎯 CPU profile override from --cpu argument: {cpu_override}')
            return cpu_override

        # Auto-detect from verilog filenames in bugs (support both 'file' and 'verilog_file')
        verilog_files = [
            bug.get('file') or bug.get('verilog_file', '') for bug in bugs if bug.get('file') or bug.get('verilog_file')
        ]

        if not verilog_files:
            print('⚠️  No verilog files found in bugs, defaulting to singlecyclecpu_d')
            return 'singlecyclecpu_d'

        # Check for pipelined or dual-issue CPU indicators
        verilog_files_str = ' '.join(verilog_files).lower()

        if 'pipelined' in verilog_files_str and 'dual' in verilog_files_str:
            profile = 'dualissue_d'
        elif 'pipelined' in verilog_files_str:
            profile = 'pipelined_d'
        else:
            profile = 'singlecyclecpu_d'

        print(f'🔍 Auto-detected CPU profile from files {verilog_files}: {profile}')
        return profile

    def _run_mcp_build(self, cpu_profile: str, api: str, extra_opts: dict | None = None) -> tuple[int, str, str]:
        """
        Run mcp_build.py as a subprocess.

        Invokes:
            uv run --python 3.13 python <HAGENT_ROOT>/hagent/mcp/mcp_build.py
                --name <cpu_profile> --api <api> [extra options]

        Returns:
            (returncode, stdout, stderr)
        """
        hagent_root = os.environ.get('HAGENT_ROOT', str(Path(__file__).parent.parent.parent.parent))
        mcp_build = Path(hagent_root) / 'hagent' / 'mcp' / 'mcp_build.py'

        cmd = ['uv', 'run', '--python', '3.13', 'python', str(mcp_build), '--name', cpu_profile, '--api', api]
        if extra_opts:
            for k, v in extra_opts.items():
                cmd += [f'-o{k}={v}']

        if self.debug:
            print(f'   $ {" ".join(cmd)}')

        proc = subprocess.run(cmd, capture_output=True, text=True)
        return proc.returncode, proc.stdout, proc.stderr

    def _generate_baseline_verilog(self, cpu_profile):
        """
        Generate fresh baseline Verilog by calling mcp_build.py --api compile
        and backup files for golden design.

        Args:
            cpu_profile: MCP profile name (e.g., 'pipelined_d')

        Returns:
            Dict with success status, file information, and backed up Verilog files
        """
        print(f'\n🏭 Generating baseline Verilog using MCP profile: {cpu_profile}')

        # Compile Chisel → Verilog via mcp_build.py
        returncode, stdout, stderr = self._run_mcp_build(cpu_profile, 'compile')

        if returncode != 0:
            error_msg = f'mcp_build compile failed (exit {returncode}):\n{stderr}'
            print(f'❌ [BASELINE] {error_msg}')
            return {'success': False, 'error': error_msg}

        result = {'success': True, 'profile': cpu_profile, 'stdout': stdout, 'file_count': 0}

        # Backup the generated baseline Verilog files for golden design creation
        backup_id = f'baseline_{cpu_profile}'
        backup_result = self.golden_design_builder.backup_existing_original_verilog(
            docker_container=None,  # Builder handles this
            backup_id=backup_id,
        )

        if backup_result['success']:
            result['original_verilog_files'] = backup_result['files']
            result['baseline_verilog_success'] = True
            result['backup_id'] = backup_id
        else:
            result['original_verilog_files'] = {}
            result['baseline_verilog_success'] = False

        return result

    def _process_single_bug_with_retries(self, bug, bug_number, cpu_profile, baseline_result):
        """
        Process a single bug with retry loops for different error types.

        Retry strategy:
        - Ambiguous removal errors: 1 retry with prompt_ambiguous_removal
        - Compilation errors: 3 retries with prompt_compile_error
        - LEC failures: 1 retry with prompt_lec_error

        Args:
            bug: Bug dictionary with file, description, unified_diff
            bug_number: Bug number for display
            cpu_profile: CPU profile to use for compilation
            baseline_result: Baseline generation result with backed up Verilog files

        Returns:
            Dict with bug processing result and all metadata
        """
        bug_file = bug.get('file') or bug.get('verilog_file', 'unknown')
        bug_description = bug.get('description', '')
        unified_diff = bug.get('unified_diff', bug.get('patch', ''))
        verilog_files = bug.get('verilog_files')  # set for xiangshan multi-file bugs

        # Create report for this bug for DAC metrics tracking
        report = self.pipeline_reporter.create_report(bug_file)

        print(f'📄 File: {bug_file}')
        print(
            f'📝 Description: {bug_description[:100]}...' if len(bug_description) > 100 else f'📝 Description: {bug_description}'
        )

        if not unified_diff:
            print(f'⚠️  Bug {bug_number}: No Verilog diff found, skipping')
            return {'bug_number': bug_number, 'file': bug_file, 'success': False, 'error': 'No Verilog diff provided'}

        # Generate hints using HintsGeneratorV2 (3 strategies combined)
        print('🔍 Generating hints using multi-strategy approach...')
        hints_result = self._generate_hints_for_bug(unified_diff, bug_description, bug_file, verilog_files=verilog_files)

        if not hints_result['success']:
            print(f'❌ Hints generation failed: {hints_result.get("error", "Unknown error")}')
            report.finalize_dac_metrics(
                verilog_diff=unified_diff, has_hints=False, golden_design_success=False, lec_files_compared=[bug_file]
            )
            return {
                'bug_number': bug_number,
                'file': bug_file,
                'success': False,
                'error': hints_result.get('error', 'Hints generation failed'),
                'dac_metrics': report.get_dac_report_dict(),
            }

        hints = hints_result.get('hints', '')
        chisel_files_found = hints_result.get('chisel_files_found', [])
        print(f'✅ Hints generated ({len(hints)} chars, {len(chisel_files_found)} Chisel files found)')

        # Initial LLM call to generate Chisel diff
        # Use prompt_xiangshan for multi-file bugs (xiangshan-style mutations)
        initial_prompt = 'prompt_xiangshan' if verilog_files else 'prompt_initial'
        print(f'🤖 Calling LLM to generate Chisel diff (initial attempt, prompt: {initial_prompt})...')

        # Start iteration 1 for DAC metrics
        iter1 = report.add_iteration(1)

        llm_result = self.chisel_diff_generator.generate_chisel_diff(
            verilog_diff=unified_diff, chisel_hints=hints, bug_description=bug_description, prompt_name=initial_prompt
        )

        if not llm_result['success']:
            print(f'❌ LLM failed to generate Chisel diff: {llm_result.get("error", "Unknown error")}')
            iter1.error_stage = 'llm'
            iter1.error_message = llm_result.get('error', 'Unknown error')
            report.finalize_dac_metrics(
                verilog_diff=unified_diff, has_hints=True, golden_design_success=False, lec_files_compared=[bug_file]
            )
            return {
                'bug_number': bug_number,
                'file': bug_file,
                'success': False,
                'error': f'LLM generation failed: {llm_result.get("error", "Unknown")}',
                'hints': hints,
                'hints_success': True,
                'dac_metrics': report.get_dac_report_dict(),
            }

        chisel_diff = llm_result.get('chisel_diff', '')
        print(f'✅ LLM generated Chisel diff ({len(chisel_diff)} chars, {llm_result.get("attempts", 1)} attempt(s))')
        print('=' * 60)
        print('📋 Generated Chisel diff:')
        print(chisel_diff)
        print('=' * 60)
        report.mark_llm_success(generated_diff=chisel_diff)
        total_llm_cost = llm_result.get('cost', 0)
        total_llm_tokens = llm_result.get('tokens', 0)
        total_llm_attempts = llm_result.get('attempts', 0)

        # Auto-correct diff removal lines to match hints exactly
        print('🔧 [CORRECTOR] Auto-correcting diff removal lines...')
        correction_result = self.diff_corrector.correct_diff(generated_diff=chisel_diff, hints=hints, verilog_diff=unified_diff)

        if correction_result['corrections_made'] > 0:
            print(f'✅ [CORRECTOR] Auto-corrected {correction_result["corrections_made"]} removal line(s)')
            # Use corrected diff if valid
            corrected = correction_result['corrected_diff']
            if corrected and corrected.strip():
                chisel_diff = corrected
            else:
                print('⚠️  [CORRECTOR] Corrected diff is empty, using original')

        if correction_result['is_ambiguous']:
            print(f'⚠️  [CORRECTOR] Found {len(correction_result["ambiguous_lines"])} ambiguous line(s)')
            for amb in correction_result['ambiguous_lines'][:3]:  # Show first 3
                print(f'     Line: {amb["original"][:60]}...')
                print(f'     Matches: {len(amb["matches"])} possible locations')
            print('   Proceeding with best guess, may need LLM retry if diff fails...')

        # If chisel_diff_only mode, return after generating the diff (skip apply/compile/LEC)
        if self.input_data.get('chisel_diff_only', False):
            print('✅ [chisel_diff_only] Returning chisel_diff without apply/compile/LEC')
            return {
                'bug_number': bug_number,
                'file': bug_file,
                'success': True,
                'hints': hints,
                'chisel_files_found': chisel_files_found,
                'unified_diff': unified_diff,
                'description': bug_description,
                'chisel_diff': chisel_diff,
                'llm_attempts': total_llm_attempts,
                'llm_cost': total_llm_cost,
                'llm_tokens': total_llm_tokens,
            }

        module_name = os.path.splitext(os.path.basename(bug_file))[0]

        # Create golden design BEFORE modifying Chisel files (only for projects with cpu_profile):
        # 1. Apply verilog_diff to .sv file in build/build_<cpu>/
        # 2. Run mcp_build.py --api elab -o tag=gold
        golden_result = {'success': False}
        if cpu_profile is not None:
            print('🎯 [GOLDEN] Creating golden design for LEC comparison...')
            golden_result = self._create_golden_design_with_elab(
                verilog_diff=unified_diff,
                cpu_profile=cpu_profile,
                module_name=module_name,
            )
            if not golden_result['success']:
                print(f'⚠️  [GOLDEN] Golden design failed (LEC may be incorrect): {golden_result.get("error")}')
            else:
                print('✅ [GOLDEN] Golden design created (elab tag=gold)')
        else:
            print('⏭️  [GOLDEN] Skipping golden design (no CPU profile for this project)')

        # Create master backup before any modifications
        print('💾 Creating master backup of original Chisel files...')
        self.master_backup_info = self.backup_manager.create_master_backup(
            docker_container=None,  # Builder handles this
            chisel_diff=chisel_diff,
        )

        # Retry loop for ambiguous removal errors (1 iteration max)
        ambiguous_retries = 0
        max_ambiguous_retries = 1

        while ambiguous_retries <= max_ambiguous_retries:
            # Apply Chisel diff to source files in Docker
            print('📝 Applying Chisel diff to source files...')
            apply_result = self._apply_chisel_diff(chisel_diff=chisel_diff, chisel_files_found=chisel_files_found)

            if not apply_result['success']:
                error_msg = apply_result.get('error', '')
                report.set_error('applier', error_msg)

                # Check if it's an ambiguous removal error
                if 'ambiguous' in error_msg.lower() and ambiguous_retries < max_ambiguous_retries:
                    ambiguous_retries += 1
                    print(
                        f'⚠️  Ambiguous removal error detected, retrying with specialized prompt ({ambiguous_retries}/{max_ambiguous_retries})...'
                    )

                    # Retry with prompt_ambiguous_removal
                    llm_result = self.chisel_diff_generator.generate_chisel_diff(
                        verilog_diff=unified_diff,
                        chisel_hints=hints,
                        bug_description=bug_description,
                        prompt_name='prompt_ambiguous_removal',
                        previous_chisel_diff=chisel_diff,
                        error_message=error_msg,
                    )

                    if llm_result['success']:
                        chisel_diff = llm_result.get('chisel_diff', '')
                        total_llm_cost += llm_result.get('cost', 0)
                        total_llm_tokens += llm_result.get('tokens', 0)
                        total_llm_attempts += llm_result.get('attempts', 0)

                        # Auto-correct the retry diff
                        print('🔧 [CORRECTOR] Auto-correcting ambiguous retry diff...')
                        correction_result = self.diff_corrector.correct_diff(
                            generated_diff=chisel_diff, hints=hints, verilog_diff=unified_diff
                        )
                        if correction_result['corrections_made'] > 0:
                            print(f'✅ [CORRECTOR] Auto-corrected {correction_result["corrections_made"]} line(s)')
                            corrected = correction_result['corrected_diff']
                            if corrected and corrected.strip():
                                chisel_diff = corrected

                        continue  # Try applying again
                    else:
                        print('❌ LLM retry for ambiguous removal failed')
                        report.finalize_dac_metrics(
                            verilog_diff=unified_diff, has_hints=True, golden_design_success=False, lec_files_compared=[bug_file]
                        )
                        return {
                            'bug_number': bug_number,
                            'file': bug_file,
                            'success': False,
                            'error': f'Ambiguous removal retry failed: {llm_result.get("error")}',
                            'hints': hints,
                            'chisel_diff': chisel_diff,
                            'ambiguous_retries': ambiguous_retries,
                            'dac_metrics': report.get_dac_report_dict(),
                        }
                else:
                    # Not ambiguous or max retries reached
                    print(f'❌ Failed to apply Chisel diff: {error_msg}')
                    report.finalize_dac_metrics(
                        verilog_diff=unified_diff, has_hints=True, golden_design_success=False, lec_files_compared=[bug_file]
                    )
                    return {
                        'bug_number': bug_number,
                        'file': bug_file,
                        'success': False,
                        'error': f'Diff application failed: {error_msg}',
                        'hints': hints,
                        'chisel_diff': chisel_diff,
                        'llm_success': True,
                        'diff_applied': False,
                        'ambiguous_retries': ambiguous_retries,
                        'dac_metrics': report.get_dac_report_dict(),
                    }

            # Diff applied successfully, break out of ambiguous retry loop
            print(f'✅ Chisel diff applied ({apply_result.get("files_modified", 0)} file(s) modified)')
            report.mark_applier_success()
            break

        # For projects without a CPU profile (soomrv, cva6):
        # applying the chisel diff is the final step — no compile or LEC available.
        if cpu_profile is None:
            print('✅ Done (no compile/LEC for this project)')
            report.finalize_dac_metrics(
                verilog_diff=unified_diff, has_hints=True, golden_design_success=False, lec_files_compared=[bug_file]
            )
            return {
                'bug_number': bug_number,
                'file': bug_file,
                'success': True,
                'hints': hints,
                'chisel_files_found': chisel_files_found,
                'unified_diff': unified_diff,
                'description': bug_description,
                'chisel_diff': chisel_diff,
                'llm_attempts': total_llm_attempts,
                'llm_cost': total_llm_cost,
                'llm_tokens': total_llm_tokens,
                'diff_applied': True,
                'files_modified': apply_result.get('files_modified', 0),
                'compilation_success': False,
                'lec_passed': False,
                'dac_metrics': report.get_dac_report_dict(),
            }

        # Retry loop for compilation errors (3 iterations max)
        compile_retries = 0
        max_compile_retries = 0

        while compile_retries <= max_compile_retries:
            compile_result = self._compile_and_generate_verilog(cpu_profile, module_name=module_name)

            if not compile_result['success']:
                error_msg = compile_result.get('error', '')
                report.set_error('compilation', error_msg)
                print(f'❌ Compile error:\n{error_msg}')

                if compile_retries < max_compile_retries:
                    compile_retries += 1
                    print(
                        f'⚠️  Compilation error detected, retrying with specialized prompt ({compile_retries}/{max_compile_retries})...'
                    )

                    # Restore original Chisel files from master backup before retrying
                    restore_result = self.backup_manager.restore_to_original(
                        docker_container=None,  # Builder handles this
                        master_backup_info=self.master_backup_info,
                        reason=f'compilation_error_retry_{compile_retries}',
                    )

                    if not restore_result.get('success'):
                        print(f'❌ Failed to restore from backup: {restore_result.get("error")}')
                        report.finalize_dac_metrics(
                            verilog_diff=unified_diff, has_hints=True, golden_design_success=False, lec_files_compared=[bug_file]
                        )
                        return {
                            'bug_number': bug_number,
                            'file': bug_file,
                            'success': False,
                            'error': f'Backup restoration failed during compile retry {compile_retries}',
                            'compile_retries': compile_retries,
                            'dac_metrics': report.get_dac_report_dict(),
                        }

                    # Create new iteration for retry
                    report.add_iteration(compile_retries + 1)

                    # Retry with prompt_compile_error
                    llm_result = self.chisel_diff_generator.generate_chisel_diff(
                        verilog_diff=unified_diff,
                        chisel_hints=hints,
                        bug_description=bug_description,
                        prompt_name='prompt_compile_error',
                        previous_chisel_diff=chisel_diff,
                        error_message=error_msg,
                    )

                    if llm_result['success']:
                        chisel_diff = llm_result.get('chisel_diff', '')
                        total_llm_cost += llm_result.get('cost', 0)
                        total_llm_tokens += llm_result.get('tokens', 0)
                        total_llm_attempts += llm_result.get('attempts', 0)
                        report.mark_llm_success(generated_diff=chisel_diff)

                        # Auto-correct the retry diff
                        print('🔧 [CORRECTOR] Auto-correcting compilation retry diff...')
                        correction_result = self.diff_corrector.correct_diff(
                            generated_diff=chisel_diff, hints=hints, verilog_diff=unified_diff
                        )
                        if correction_result['corrections_made'] > 0:
                            print(f'✅ [CORRECTOR] Auto-corrected {correction_result["corrections_made"]} line(s)')
                            corrected = correction_result['corrected_diff']
                            if corrected and corrected.strip():
                                chisel_diff = corrected

                        # Apply new diff
                        apply_result = self._apply_chisel_diff(chisel_diff=chisel_diff, chisel_files_found=chisel_files_found)

                        if not apply_result['success']:
                            print(f'❌ Failed to apply retry diff: {apply_result.get("error")}')
                            report.finalize_dac_metrics(
                                verilog_diff=unified_diff,
                                has_hints=True,
                                golden_design_success=False,
                                lec_files_compared=[bug_file],
                            )
                            return {
                                'bug_number': bug_number,
                                'file': bug_file,
                                'success': False,
                                'error': f'Retry diff application failed: {apply_result.get("error")}',
                                'hints': hints,
                                'chisel_diff': chisel_diff,
                                'compile_retries': compile_retries,
                                'dac_metrics': report.get_dac_report_dict(),
                            }

                        continue  # Try compiling again
                    else:
                        print('❌ LLM retry for compilation error failed')
                        report.finalize_dac_metrics(
                            verilog_diff=unified_diff, has_hints=True, golden_design_success=False, lec_files_compared=[bug_file]
                        )
                        return {
                            'bug_number': bug_number,
                            'file': bug_file,
                            'success': False,
                            'error': f'Compilation retry {compile_retries} failed: {llm_result.get("error")}',
                            'hints': hints,
                            'chisel_diff': chisel_diff,
                            'compile_retries': compile_retries,
                            'dac_metrics': report.get_dac_report_dict(),
                        }
                else:
                    # Max retries reached
                    print(f'❌ Compilation failed after {max_compile_retries} retries: {error_msg}')
                    report.finalize_dac_metrics(
                        verilog_diff=unified_diff, has_hints=True, golden_design_success=False, lec_files_compared=[bug_file]
                    )
                    return {
                        'bug_number': bug_number,
                        'file': bug_file,
                        'success': False,
                        'error': f'Compilation failed after {max_compile_retries} retries: {error_msg}',
                        'hints': hints,
                        'chisel_diff': chisel_diff,
                        'diff_applied': True,
                        'compilation_success': False,
                        'compile_retries': compile_retries,
                        'dac_metrics': report.get_dac_report_dict(),
                    }

            # Compilation successful, break out of compile retry loop
            print(
                f'✅ Compile + elab gate done (profile: {compile_result.get("profile")}, {compile_result.get("verilog_count", 0)} Verilog file(s))'
            )
            report.mark_compilation_success()
            report.mark_verilog_success()
            break

        # Retry loop for LEC failures (1 iteration max)
        lec_retries = 0
        max_lec_retries = 0

        while lec_retries <= max_lec_retries:
            lec_result = self._run_lec_verification(
                bug_file=bug_file, cpu_profile=cpu_profile, unified_diff=unified_diff, golden_result=golden_result
            )

            if not lec_result['success']:
                error_msg = lec_result.get('error', '')
                report.set_error('lec', error_msg)

                if lec_retries < max_lec_retries:
                    lec_retries += 1
                    print(f'⚠️  LEC verification failed, retrying with specialized prompt ({lec_retries}/{max_lec_retries})...')

                    # Restore original Chisel files from master backup before retrying
                    restore_result = self.backup_manager.restore_to_original(
                        docker_container=None,  # Builder handles this
                        master_backup_info=self.master_backup_info,
                        reason=f'lec_error_retry_{lec_retries}',
                    )

                    if not restore_result.get('success'):
                        print(f'❌ Failed to restore from backup: {restore_result.get("error")}')
                        golden_dir = golden_result.get('golden_directory', '/code/workspace/repo/lec_golden')
                        modified_dir = f'/code/workspace/build/build_{cpu_profile}'
                        profile_to_verilog = {
                            'singlecyclecpu_d': 'SingleCycleCPU.sv',
                            'pipelined_d': 'PipelinedCPU.sv',
                            'dualissue_d': 'PipelinedDualIssueCPU.sv',
                        }
                        verilog_filename = profile_to_verilog.get(cpu_profile, 'SingleCycleCPU.sv')
                        report.finalize_dac_metrics(
                            verilog_diff=unified_diff,
                            has_hints=True,
                            golden_design_success=golden_result.get('success', False),
                            lec_golden_file=f'{golden_dir}/{verilog_filename}',
                            lec_generated_file=f'{modified_dir}/{verilog_filename}',
                            lec_files_compared=[bug_file],
                        )
                        return {
                            'bug_number': bug_number,
                            'file': bug_file,
                            'success': False,
                            'error': f'Backup restoration failed during LEC retry {lec_retries}',
                            'lec_retries': lec_retries,
                            'dac_metrics': report.get_dac_report_dict(),
                        }

                    # Create new iteration for LEC retry
                    # Note: LEC retries happen after successful compilation, so we might be on iteration 2, 3, or 4
                    current_iteration = len(report.iterations) + 1
                    report.add_iteration(current_iteration)

                    # Retry with prompt_lec_error
                    llm_result = self.chisel_diff_generator.generate_chisel_diff(
                        verilog_diff=unified_diff,
                        chisel_hints=hints,
                        bug_description=bug_description,
                        prompt_name='prompt_lec_error',
                        previous_chisel_diff=chisel_diff,
                        error_message=error_msg,
                    )

                    if llm_result['success']:
                        chisel_diff = llm_result.get('chisel_diff', '')
                        total_llm_cost += llm_result.get('cost', 0)
                        total_llm_tokens += llm_result.get('tokens', 0)
                        total_llm_attempts += llm_result.get('attempts', 0)
                        report.mark_llm_success(generated_diff=chisel_diff)

                        # Auto-correct the retry diff
                        print('🔧 [CORRECTOR] Auto-correcting LEC retry diff...')
                        correction_result = self.diff_corrector.correct_diff(
                            generated_diff=chisel_diff, hints=hints, verilog_diff=unified_diff
                        )
                        if correction_result['corrections_made'] > 0:
                            print(f'✅ [CORRECTOR] Auto-corrected {correction_result["corrections_made"]} line(s)')
                            corrected = correction_result['corrected_diff']
                            if corrected and corrected.strip():
                                chisel_diff = corrected

                        # Apply new diff
                        apply_result = self._apply_chisel_diff(chisel_diff=chisel_diff, chisel_files_found=chisel_files_found)

                        if not apply_result['success']:
                            print(f'❌ Failed to apply LEC retry diff: {apply_result.get("error")}')
                            golden_dir = golden_result.get('golden_directory', '/code/workspace/repo/lec_golden')
                            modified_dir = f'/code/workspace/build/build_{cpu_profile}'
                            profile_to_verilog = {
                                'singlecyclecpu_d': 'SingleCycleCPU.sv',
                                'pipelined_d': 'PipelinedCPU.sv',
                                'dualissue_d': 'PipelinedDualIssueCPU.sv',
                            }
                            verilog_filename = profile_to_verilog.get(cpu_profile, 'SingleCycleCPU.sv')
                            report.finalize_dac_metrics(
                                verilog_diff=unified_diff,
                                has_hints=True,
                                golden_design_success=golden_result.get('success', False),
                                lec_golden_file=f'{golden_dir}/{verilog_filename}',
                                lec_generated_file=f'{modified_dir}/{verilog_filename}',
                                lec_files_compared=[bug_file],
                            )
                            return {
                                'bug_number': bug_number,
                                'file': bug_file,
                                'success': False,
                                'error': f'LEC retry diff application failed: {apply_result.get("error")}',
                                'hints': hints,
                                'chisel_diff': chisel_diff,
                                'lec_retries': lec_retries,
                                'dac_metrics': report.get_dac_report_dict(),
                            }

                        # Recompile with new diff
                        compile_result = self._compile_and_generate_verilog(cpu_profile, module_name=module_name)
                        if not compile_result['success']:
                            print(f'❌ LEC retry compilation failed: {compile_result.get("error")}')
                            golden_dir = golden_result.get('golden_directory', '/code/workspace/repo/lec_golden')
                            modified_dir = f'/code/workspace/build/build_{cpu_profile}'
                            profile_to_verilog = {
                                'singlecyclecpu_d': 'SingleCycleCPU.sv',
                                'pipelined_d': 'PipelinedCPU.sv',
                                'dualissue_d': 'PipelinedDualIssueCPU.sv',
                            }
                            verilog_filename = profile_to_verilog.get(cpu_profile, 'SingleCycleCPU.sv')
                            report.finalize_dac_metrics(
                                verilog_diff=unified_diff,
                                has_hints=True,
                                golden_design_success=golden_result.get('success', False),
                                lec_golden_file=f'{golden_dir}/{verilog_filename}',
                                lec_generated_file=f'{modified_dir}/{verilog_filename}',
                                lec_files_compared=[bug_file],
                            )
                            return {
                                'bug_number': bug_number,
                                'file': bug_file,
                                'success': False,
                                'error': f'LEC retry compilation failed: {compile_result.get("error")}',
                                'hints': hints,
                                'chisel_diff': chisel_diff,
                                'lec_retries': lec_retries,
                                'dac_metrics': report.get_dac_report_dict(),
                            }

                        # Recreate golden design with new diff
                        print('🎯 [GOLDEN] Recreating golden design for LEC retry...')
                        golden_result = self._create_golden_design_with_elab(
                            verilog_diff=unified_diff, cpu_profile=cpu_profile, module_name=module_name
                        )

                        if not golden_result['success']:
                            print(f'❌ [GOLDEN] Golden design recreation failed: {golden_result.get("error")}')

                        continue  # Try LEC again
                    else:
                        print('❌ LLM retry for LEC error failed')
                        golden_dir = golden_result.get('golden_directory', '/code/workspace/repo/lec_golden')
                        modified_dir = f'/code/workspace/build/build_{cpu_profile}'
                        profile_to_verilog = {
                            'singlecyclecpu_d': 'SingleCycleCPU.sv',
                            'pipelined_d': 'PipelinedCPU.sv',
                            'dualissue_d': 'PipelinedDualIssueCPU.sv',
                        }
                        verilog_filename = profile_to_verilog.get(cpu_profile, 'SingleCycleCPU.sv')
                        report.finalize_dac_metrics(
                            verilog_diff=unified_diff,
                            has_hints=True,
                            golden_design_success=golden_result.get('success', False),
                            lec_golden_file=f'{golden_dir}/{verilog_filename}',
                            lec_generated_file=f'{modified_dir}/{verilog_filename}',
                            lec_files_compared=[bug_file],
                        )
                        return {
                            'bug_number': bug_number,
                            'file': bug_file,
                            'success': False,
                            'error': f'LEC retry failed: {llm_result.get("error")}',
                            'hints': hints,
                            'chisel_diff': chisel_diff,
                            'diff_applied': True,
                            'compilation_success': True,
                            'verilog_generated': True,
                            'lec_passed': False,
                            'lec_retries': lec_retries,
                            'dac_metrics': report.get_dac_report_dict(),
                        }
                else:
                    # Max retries reached
                    print(f'❌ LEC verification failed after {max_lec_retries} retries: {error_msg}')
                    if lec_result.get('counterexample'):
                        print(f'   Counterexample:\n{lec_result["counterexample"]}')

                    golden_dir = golden_result.get('golden_directory', '/code/workspace/repo/lec_golden')
                    modified_dir = f'/code/workspace/build/build_{cpu_profile}'
                    profile_to_verilog = {
                        'singlecyclecpu_d': 'SingleCycleCPU.sv',
                        'pipelined_d': 'PipelinedCPU.sv',
                        'dualissue_d': 'PipelinedDualIssueCPU.sv',
                    }
                    verilog_filename = profile_to_verilog.get(cpu_profile, 'SingleCycleCPU.sv')
                    report.finalize_dac_metrics(
                        verilog_diff=unified_diff,
                        has_hints=True,
                        golden_design_success=golden_result.get('success', False),
                        lec_golden_file=f'{golden_dir}/{verilog_filename}',
                        lec_generated_file=f'{modified_dir}/{verilog_filename}',
                        lec_files_compared=[bug_file],
                    )

                    return {
                        'bug_number': bug_number,
                        'file': bug_file,
                        'success': False,
                        'error': f'LEC failed: {error_msg}',
                        'hints': hints,
                        'chisel_diff': chisel_diff,
                        'diff_applied': True,
                        'compilation_success': True,
                        'verilog_generated': True,
                        'lec_passed': False,
                        'lec_error': error_msg,
                        'lec_counterexample': lec_result.get('counterexample', ''),
                        'lec_retries': lec_retries,
                        'llm_cost': total_llm_cost,
                        'llm_tokens': total_llm_tokens,
                        'llm_attempts': total_llm_attempts,
                        'dac_metrics': report.get_dac_report_dict(),
                    }

            # LEC passed!
            print('✅ LEC verification passed!')
            print('   Result: Designs are logically equivalent')
            report.mark_lec_success()
            break

        # Success! All steps passed
        # Clean up master backup
        if self.master_backup_info:
            self.backup_manager.cleanup_master_backup(
                docker_container=None,  # Builder handles this
                master_backup_info=self.master_backup_info,
            )

        # Finalize DAC metrics
        golden_dir = golden_result.get('golden_directory', '/code/workspace/repo/lec_golden')
        modified_dir = f'/code/workspace/build/build_{cpu_profile}'
        profile_to_verilog = {
            'singlecyclecpu_d': 'SingleCycleCPU.sv',
            'pipelined_d': 'PipelinedCPU.sv',
            'dualissue_d': 'PipelinedDualIssueCPU.sv',
        }
        verilog_filename = profile_to_verilog.get(cpu_profile, 'SingleCycleCPU.sv')
        golden_file = f'{golden_dir}/{verilog_filename}'
        modified_file = f'{modified_dir}/{verilog_filename}'

        report.finalize_dac_metrics(
            verilog_diff=unified_diff,
            has_hints=True,
            golden_design_success=golden_result.get('success', False),
            lec_golden_file=golden_file,
            lec_generated_file=modified_file,
            lec_files_compared=[bug_file],
        )

        return {
            'bug_number': bug_number,
            'file': bug_file,
            'success': True,
            'hints': hints,
            'chisel_files_found': chisel_files_found,
            'unified_diff': unified_diff,
            'description': bug_description,
            'chisel_diff': chisel_diff,
            'llm_attempts': total_llm_attempts,
            'llm_cost': total_llm_cost,
            'llm_tokens': total_llm_tokens,
            'diff_applied': True,
            'files_modified': apply_result.get('files_modified', 0),
            'compilation_success': True,
            'verilog_generated': True,
            'verilog_count': compile_result.get('verilog_count', 0),
            'lec_passed': True,
            'lec_command': lec_result.get('command', ''),
            'ambiguous_retries': ambiguous_retries,
            'compile_retries': compile_retries,
            'lec_retries': lec_retries,
            'dac_metrics': report.get_dac_report_dict(),
        }

    def _generate_hints_for_bug(self, verilog_diff, bug_description, bug_file='unknown', verilog_files=None):
        """
        Generate Chisel hints from Verilog diff using multi-strategy approach.

        For multi-file bugs (xiangshan), verilog_files contains all SV filenames.
        Hints are run per file and aggregated into one combined block.

        Args:
            verilog_diff: Unified diff of Verilog changes (may span multiple files)
            bug_description: Description of the bug
            bug_file: Primary Verilog/Scala file name
            verilog_files: Optional list of all SV files changed (for multi-file hints)

        Returns:
            Dict with success status, hints, and metadata
        """
        try:
            if self.debug:
                print('🔍 [HINTS] Running multi-strategy hints generation...')

            # Import BugInfo for constructing bug_info object
            from hagent.step.v2chisel_batch.components.bug_info import BugInfo

            # Get all Chisel files from the repository (using Builder's filesystem)
            all_files = []
            try:
                exit_code, stdout, stderr = self.builder.run_cmd(
                    'find /code/workspace/repo/src/main/scala -name "*.scala" -type f 2>/dev/null || find . -name "*.scala" -type f 2>/dev/null || true'
                )
                if exit_code == 0 and stdout:
                    raw_files = [f.strip() for f in stdout.strip().split('\n') if f.strip()]
                    for f in raw_files:
                        all_files.append(f'docker:hagent:{f}')
            except Exception as e:
                if self.debug:
                    print(f'⚠️  Could not find Scala files: {e}')

            if self.debug:
                print(f'   Found {len(all_files)} Scala files')

            # For multi-file bugs (xiangshan): if we already know the scala file, read it
            # directly from Docker — this is more accurate than per-SV-file strategy lookups
            # which are indirect (verilog module name → chisel class) and often miss the
            # actual mutation site inside nested sub-modules.
            if verilog_files and bug_file.endswith('.scala'):
                if self.debug:
                    print(f'   Multi-file xiangshan mode: using scala file directly: {bug_file}')
                return self._hints_from_scala_file(bug_file, verilog_diff, all_files)

            # For multi-file bugs: run hints per SV file and aggregate results
            files_to_search = verilog_files if verilog_files else [bug_file]

            if len(files_to_search) > 1:
                if self.debug:
                    print(f'   Multi-file mode: running hints for {len(files_to_search)} SV files')
                return self._aggregate_hints_for_files(files_to_search, verilog_diff, bug_description, all_files)

            # Single-file: standard path
            bug_entry = {'file': bug_file, 'unified_diff': verilog_diff, 'description': bug_description}
            bug_info = BugInfo(bug_entry, 0)
            hints_result = self.hints_generator_v2.find_hints(bug_info=bug_info, all_files=all_files, docker_container='hagent')

            if hints_result.get('success'):
                chisel_files = [
                    getattr(h, 'file_name', None) or (h.get('file_name') if isinstance(h, dict) else None)
                    for h in hints_result.get('hits', [])
                    if getattr(h, 'file_name', None) or (isinstance(h, dict) and h.get('file_name'))
                ]
                return {
                    'success': True,
                    'hints': hints_result.get('hints', ''),
                    'chisel_files_found': chisel_files,
                    'source': hints_result.get('source', 'unknown'),
                }
            else:
                return {'success': False, 'error': hints_result.get('error', 'No candidates found')}

        except Exception as e:
            error_msg = f'Exception during hints generation: {str(e)}'
            if self.debug:
                import traceback

                traceback.print_exc()
            return {'success': False, 'error': error_msg}

    def _hints_from_scala_file(self, scala_file: str, verilog_diff: str, all_files) -> dict:
        """
        Generate hints by reading the known Chisel scala file directly from Docker.

        Used for xiangshan mutations where the YAML already specifies the scala_file.
        Reading the file directly avoids the verilog→chisel name-lookup that often
        finds the wrapper instead of the implementation, and ensures sub-modules (like
        SubModule inside AluDataModule) are included without truncation.
        """
        import re

        MAX_TOTAL_HINTS = 16000

        # Try both workspace and cache-based paths inside the container
        candidate_paths = [
            f'/code/workspace/repo/{scala_file}',
            f'/code/workspace/repo/src/main/scala/{scala_file}',
            scala_file,
        ]

        file_content = None
        used_path = None
        for docker_path in candidate_paths:
            try:
                file_content = self.builder.filesystem.read_text(docker_path)
                used_path = docker_path
                break
            except Exception:
                continue

        if file_content is None:
            if self.debug:
                print(f'   ⚠️  Could not read scala file {scala_file} from Docker, falling back to aggregate mode')
            from hagent.step.v2chisel_batch.components.bug_info import BugInfo

            # Extract module name from scala_file for single-file fallback
            module_name = os.path.splitext(os.path.basename(scala_file))[0]
            bug_entry = {'file': module_name + '.sv', 'unified_diff': verilog_diff, 'description': scala_file}
            bug_info = BugInfo(bug_entry, 0)
            result = self.hints_generator_v2.find_hints(bug_info=bug_info, all_files=all_files, docker_container='hagent')
            if result.get('success'):
                return {
                    'success': True,
                    'hints': result.get('hints', ''),
                    'chisel_files_found': [scala_file],
                    'source': 'fallback',
                }
            return {'success': False, 'error': f'Could not read {scala_file} and fallback also failed'}

        if self.debug:
            print(f'   📖 Read {len(file_content)} chars from {used_path}')

        # Build hints: full scala file content + sub-module following
        hints_parts = [
            f'// ========== DIRECT SCALA FILE: {scala_file} ==========',
            f'// Source: {used_path}',
            '',
            file_content.strip(),
            '',
        ]

        # Sub-module following: find Module(new ClassName) patterns and append those classes too
        if self.hints_generator_v2.span_index is not None:
            already_included: set = set()
            sub_pattern = re.compile(r'Module\s*\(\s*new\s+(\w+)')
            queue = [file_content]
            seen_code: list = []

            while queue:
                code_block = queue.pop(0)
                if code_block in seen_code:
                    continue
                seen_code.append(code_block)

                for match in sub_pattern.finditer(code_block):
                    class_name = match.group(1)
                    if class_name in already_included:
                        continue
                    already_included.add(class_name)

                    span = next(
                        (s for s in self.hints_generator_v2.span_index.get_all_modules() if s.name == class_name),
                        None,
                    )
                    if span is None:
                        continue

                    sub_code = self.hints_generator_v2._extract_code_from_span(span)
                    if not sub_code:
                        continue

                    display_file = span.file
                    if display_file.startswith('docker:'):
                        parts = display_file.split(':', 2)
                        if len(parts) == 3:
                            display_file = parts[2]

                    hints_parts.append(f'// ========== SUB-MODULE: {class_name} ==========')
                    hints_parts.append(f'// File: {display_file} lines {span.start_line}-{span.end_line}')
                    hints_parts.append('')
                    hints_parts.append(sub_code.strip())
                    hints_parts.append('')

                    if self.debug:
                        print(f'   ➕ Sub-module: {class_name} ({display_file}:{span.start_line}-{span.end_line})')

                    # Recurse into this sub-module to follow nested instantiations
                    queue.append(sub_code)

                    # Safety: stop if we've already hit the hint size budget
                    current_size = sum(len(p) for p in hints_parts)
                    if current_size > MAX_TOTAL_HINTS:
                        if self.debug:
                            print(f'   ⚠️  Sub-module hint budget reached, stopping at {class_name}')
                        break

        combined = '\n'.join(hints_parts)
        if len(combined) > MAX_TOTAL_HINTS:
            combined = combined[:MAX_TOTAL_HINTS] + '\n// ... (truncated)'

        if self.debug:
            print(f'   📏 Direct scala hints: {len(combined)} chars')

        return {
            'success': True,
            'hints': combined,
            'chisel_files_found': [scala_file],
            'source': 'direct_scala',
        }

    def _aggregate_hints_for_files(self, verilog_files, verilog_diff, bug_description, all_files):
        """
        Run hints for each SV file and combine into one hints block.
        Used for xiangshan-style mutations where one chisel change produces N SV changes.
        """
        from hagent.step.v2chisel_batch.components.bug_info import BugInfo

        MAX_HINTS_PER_FILE = 4000  # chars — cap each file's hints block
        MAX_TOTAL_HINTS = 16000  # chars — cap the combined hints sent to LLM

        combined_hints_parts = []
        all_chisel_files = []
        any_success = False

        for sv_file in verilog_files:
            # Stop adding more file hints if we've already hit the total cap
            current_total = sum(len(p) for p in combined_hints_parts)
            if current_total >= MAX_TOTAL_HINTS:
                if self.debug:
                    print(f'   ⚠️  Total hints cap reached ({MAX_TOTAL_HINTS} chars), skipping {sv_file}')
                break

            bug_entry = {'file': sv_file, 'unified_diff': verilog_diff, 'description': bug_description}
            bug_info = BugInfo(bug_entry, 0)

            result = self.hints_generator_v2.find_hints(bug_info=bug_info, all_files=all_files, docker_container='hagent')

            if result.get('success'):
                any_success = True
                file_hints = result.get('hints', '')
                # Truncate this file's hints if too large
                if len(file_hints) > MAX_HINTS_PER_FILE:
                    file_hints = file_hints[:MAX_HINTS_PER_FILE] + '\n// ... (truncated)'
                    if self.debug:
                        print(f'   ✂️  Hints for {sv_file} truncated to {MAX_HINTS_PER_FILE} chars')
                combined_hints_parts.append(f'// === Hints for {sv_file} ===')
                combined_hints_parts.append(file_hints)
                for h in result.get('hits', []):
                    fp = getattr(h, 'file_name', None) or (h.get('file_name') if isinstance(h, dict) else None)
                    if fp and fp not in all_chisel_files:
                        all_chisel_files.append(fp)
            else:
                if self.debug:
                    print(f'   ⚠️  No hints for {sv_file}: {result.get("error")}')

        if not any_success:
            return {'success': False, 'error': 'No hints found for any of the SV files'}

        combined = '\n'.join(combined_hints_parts)
        # Final safety truncation
        if len(combined) > MAX_TOTAL_HINTS:
            combined = combined[:MAX_TOTAL_HINTS] + '\n// ... (total hints truncated)'

        if self.debug:
            print(f'   📏 Combined hints: {len(combined)} chars from {len(all_chisel_files)} Chisel file(s)')

        return {
            'success': True,
            'hints': combined,
            'chisel_files_found': all_chisel_files,
            'source': 'multi_file',
        }

    def _generate_chisel_diff_with_llm(self, verilog_diff, chisel_hints, bug_description):
        """
        Generate Chisel diff using LLM with Verilog diff and hints.

        Uses ChiselDiffGenerator component to call LLM with structured prompts.

        Args:
            verilog_diff: Unified diff of Verilog changes
            chisel_hints: Generated hints about relevant Chisel files
            bug_description: Description of the bug

        Returns:
            Dict with success status, chisel_diff, and metadata
        """
        try:
            if self.debug:
                print('🤖 [LLM] Calling LLM to generate Chisel diff...')

            # Call ChiselDiffGenerator component
            llm_result = self.chisel_diff_generator.generate_chisel_diff(
                verilog_diff=verilog_diff, chisel_hints=chisel_hints, bug_description=bug_description, max_retries=3
            )

            if llm_result.get('success'):
                if self.debug:
                    print('✅ [LLM] Chisel diff generation successful')
                    print(f'   Cost: ${llm_result.get("cost", 0):.4f}')
                    print(f'   Tokens: {llm_result.get("tokens", 0)}')

                return llm_result
            else:
                error_msg = llm_result.get('error', 'Unknown LLM error')
                if self.debug:
                    print(f'❌ [LLM] Chisel diff generation failed: {error_msg}')
                return llm_result

        except Exception as e:
            error_msg = f'Exception during LLM call: {str(e)}'
            if self.debug:
                print(f'❌ [LLM] {error_msg}')
            return {'success': False, 'error': error_msg}

    def _apply_chisel_diff(self, chisel_diff, chisel_files_found):
        """
        Apply generated Chisel diff to source files in Docker container.

        Uses DockerDiffApplier to apply the diff to files in the Docker environment.

        Args:
            chisel_diff: Generated Chisel diff (unified diff format)
            chisel_files_found: List of relevant Chisel files from hints

        Returns:
            Dict with success status and files modified count
        """
        try:
            if not chisel_diff:
                return {'success': False, 'error': 'Empty Chisel diff provided'}

            target_file = chisel_files_found[0] if chisel_files_found else None

            success = self.docker_diff_applier.apply_diff_to_container(
                diff_content=chisel_diff, target_file_path=target_file, dry_run=False
            )

            if success:
                return {
                    'success': True,
                    'files_modified': len(chisel_files_found) if chisel_files_found else 1,
                    'target_file': target_file,
                }
            return {'success': False, 'error': 'DockerDiffApplier returned failure'}

        except Exception as e:
            return {'success': False, 'error': f'Exception during diff application: {str(e)}'}

    def _compile_and_generate_verilog(self, cpu_profile, module_name: str = ''):
        """
        Compile modified Chisel code and generate Verilog using MCP profile.

        This uses Builder.run_api() with the 'compile' command, which does BOTH:
        1. Compiles the Chisel/Scala code
        2. Generates Verilog output (via sbt runMain)

        Args:
            cpu_profile: MCP profile name (e.g., 'pipelined_d', 'singlecyclecpu_d')

        Returns:
            Dict with success status, profile info, and Verilog file count
        """
        _COMPILE_ONLY_PROFILES = ('xiangshan_rtl_dbg', 'xiangshan_rtl_opt')

        try:
            # Step 1: compile (Chisel → Verilog)
            exit_code, stdout, stderr = self._run_mcp_build(cpu_profile, 'compile')
            if exit_code != 0:
                return {
                    'success': False,
                    'error': f'compile failed (exit {exit_code}):\n{stderr}',
                    'exit_code': exit_code,
                    'stderr': stderr,
                }

            # Step 2: elab --tag gate (skipped for xiangshan which has no elab API)
            if cpu_profile not in _COMPILE_ONLY_PROFILES:
                elab_opts = {'tag': 'gate'}
                if module_name:
                    elab_opts['top_synth'] = module_name
                elab_exit_code, _, elab_stderr = self._run_mcp_build(cpu_profile, 'elab', elab_opts)
                if elab_exit_code != 0:
                    return {
                        'success': False,
                        'error': f'elab gate failed (exit {elab_exit_code}):\n{elab_stderr}',
                        'exit_code': elab_exit_code,
                        'stderr': elab_stderr,
                    }

            verilog_count = self._count_verilog_files(cpu_profile)
            return {
                'success': True,
                'profile': cpu_profile,
                'exit_code': exit_code,
                'stdout': stdout,
                'verilog_count': verilog_count,
            }

        except Exception as e:
            return {'success': False, 'error': f'Exception during compilation: {str(e)}'}

    def _count_verilog_files(self, cpu_profile):
        """
        Count generated Verilog files for a CPU profile.

        Args:
            cpu_profile: MCP profile name

        Returns:
            Number of .sv files found
        """
        try:
            # Map profile to build directory
            profile_to_build_dir = {
                'singlecyclecpu_d': 'build_singlecyclecpu_d',
                'pipelined_d': 'build_pipelined_d',
                'dualissue_d': 'build_dualissue_d',
            }

            build_dir = profile_to_build_dir.get(cpu_profile, 'build_singlecyclecpu_d')
            build_path = f'/code/workspace/build/{build_dir}'

            # Count .sv files in build directory
            exit_code, stdout, stderr = self.builder.run_cmd(f'find {build_path} -name "*.sv" -type f 2>/dev/null | wc -l')

            if exit_code == 0 and stdout.strip():
                return int(stdout.strip())
            return 0

        except Exception:
            return 0

    def _create_golden_design_with_elab(self, verilog_diff: str, cpu_profile: str, module_name: str = ''):
        """
        Create golden design by:
        1. Applying verilog_diff directly to .sv file in build/build_<cpu_profile>/
        2. Running mcp_build.py --api elab -o tag=gold

        This matches the manual pipeline in run_v2chisel_manual.py / run_lec_benchmark.py.

        Args:
            verilog_diff: Unified diff to apply to the baseline Verilog file
            cpu_profile: MCP profile name (e.g., 'singlecyclecpu_d')

        Returns:
            Dict with success status and elab details
        """
        try:
            # Step 1: Apply verilog_diff to the .sv file in build/build_<cpu_profile>/
            apply_success = self.docker_diff_applier.apply_diff_to_container(diff_content=verilog_diff, dry_run=False)

            if not apply_success:
                return {'success': False, 'error': 'Failed to apply verilog_diff to build directory'}

            # Step 2: Run elab with tag=gold via mcp_build.py
            elab_opts = {'tag': 'gold'}
            if module_name:
                elab_opts['top_synth'] = module_name
            exit_code, stdout, stderr = self._run_mcp_build(cpu_profile, 'elab', elab_opts)

            if exit_code != 0:
                return {'success': False, 'error': f'elab gold failed (exit {exit_code}):\n{stderr}'}

            return {
                'success': True,
                'elab_tag': 'gold',
                'cpu_profile': cpu_profile,
                'golden_directory': f'/code/workspace/build/build_{cpu_profile}',
            }

        except Exception as e:
            return {'success': False, 'error': f'Golden design creation failed: {str(e)}'}

    def _run_lec_verification(self, bug_file, cpu_profile, unified_diff, golden_result):
        """
        Run Logic Equivalence Check via cli_equiv_check.py subprocess.

        Invokes:
            uv run --python 3.13 python <HAGENT_ROOT>/hagent/tool/tests/cli_equiv_check.py
                --dir <HAGENT_BUILD_DIR>/build_<cpu_profile>
                --ref-tag gold --impl-tag gate

        Exit codes from cli_equiv_check.py:
            0 = equivalent (pass)
            1 = not equivalent or error (fail)
            2 = inconclusive

        Args:
            bug_file: Verilog file name (display only)
            cpu_profile: MCP profile name (determines build subdirectory)
            unified_diff: unused, kept for interface compatibility
            golden_result: unused, kept for interface compatibility
        """
        try:
            hagent_root = os.environ.get('HAGENT_ROOT', str(Path(__file__).parent.parent.parent.parent))
            cli_script = Path(hagent_root) / 'hagent' / 'tool' / 'tests' / 'cli_equiv_check.py'

            build_base = os.environ.get('HAGENT_BUILD_DIR', '/code/workspace/build')
            build_dir = str(Path(build_base) / f'build_{cpu_profile}')

            cmd = [
                'uv',
                'run',
                '--python',
                '3.13',
                'python',
                str(cli_script),
                '--dir',
                build_dir,
                '--ref-tag',
                'gold',
                '--impl-tag',
                'gate',
            ]

            if self.debug:
                print(f'   $ {" ".join(cmd)}')

            proc = subprocess.run(cmd, capture_output=True, text=True)

            if proc.returncode == 0:
                return {'success': True, 'result': 'equivalent', 'stdout': proc.stdout}
            elif proc.returncode == 2:
                return {'success': False, 'error': f'LEC inconclusive: {proc.stdout}', 'result': 'inconclusive'}
            else:
                # returncode == 1: not equivalent or setup error
                return {
                    'success': False,
                    'error': 'Designs are NOT logically equivalent',
                    'counterexample': proc.stdout,
                    'result': 'not_equivalent',
                }

        except Exception as e:
            return {'success': False, 'error': f'Exception during LEC: {str(e)}'}


def main():
    """Command-line interface"""
    parser = argparse.ArgumentParser(description='V2chisel_batch - Clean MCP-based pipeline')

    # Required arguments
    parser.add_argument('input_file', help='Input YAML file with bugs')
    parser.add_argument('-o', '--output', required=True, help='Output directory')

    # Optional arguments
    parser.add_argument(
        '--cpu',
        choices=['singlecyclecpu_d', 'singlecyclecpu_nd', 'pipelined_d', 'pipelined_nd', 'dualissue_d', 'dualissue_nd'],
        help='CPU profile override (default: auto-detect from bugs)',
    )
    parser.add_argument('--bugs', help='Bug numbers to process (e.g., "1,2,3" or "1-5")')
    parser.add_argument('--llm', help='LLM model to use (e.g., "openai/gpt-4o", "anthropic/claude-sonnet-4-5-20250929")')
    parser.add_argument('--chisel-diff-only', action='store_true', default=True, help='Only generate chisel_diff, skip compile/LEC (default: True)')
    parser.add_argument('--full-pipeline', action='store_true', help='Run full pipeline including compile and LEC')
    parser.add_argument('--compile-error', help='Compile error from previous attempt (triggers prompt_compile_error)')
    parser.add_argument('--previous-diff-file', help='Path to file containing previous chisel_diff that failed')
    parser.add_argument('--project', help='Project name (e.g., xiangshan, soomrv, cva6, simplechisel)')
    parser.add_argument(
        '--xiangshan-profile',
        choices=['dbg', 'opt'],
        default='dbg',
        help='XiangShan compile profile: dbg (xiangshan_rtl_dbg) or opt (xiangshan_rtl_opt)',
    )
    parser.add_argument('--debug', action='store_true', default=True, help='Enable debug output')

    args = parser.parse_args()

    # Load input YAML
    print(f'📂 Loading input from: {args.input_file}')
    with open(args.input_file, 'r') as f:
        input_data = yaml.safe_load(f)

    # Add command-line arguments to input_data
    if args.project:
        input_data['project'] = args.project
        print(f'🔧 Project override from --project: {args.project}')

    if args.cpu:
        input_data['cpu_type'] = args.cpu
        print(f'🔧 CPU type override from --cpu: {args.cpu}')

    if args.llm:
        input_data['llm_model'] = args.llm
        print(f'🔧 LLM model override from --llm: {args.llm}')

    input_data['debug'] = args.debug
    input_data['output_dir'] = args.output
    input_data['chisel_diff_only'] = not args.full_pipeline

    # Wire --xiangshan-profile into input_data
    input_data['xiangshan_profile'] = args.xiangshan_profile

    if args.compile_error:
        input_data['compile_error'] = args.compile_error
    if args.previous_diff_file:
        prev_diff_path = Path(args.previous_diff_file)
        if prev_diff_path.exists():
            input_data['previous_chisel_diff'] = prev_diff_path.read_text()
        else:
            print(f'WARNING: previous-diff-file not found: {prev_diff_path}')

    # Filter bugs if --bugs specified
    if args.bugs and 'bugs' in input_data:
        all_bugs = input_data['bugs']
        selected_bugs = []

        # Parse bug selection (e.g., "1,2,3" or "1-5")
        for part in args.bugs.split(','):
            if '-' in part:
                start, end = map(int, part.split('-'))
                for i in range(start - 1, end):
                    if i < len(all_bugs):
                        selected_bugs.append(all_bugs[i])
            else:
                idx = int(part) - 1
                if idx < len(all_bugs):
                    selected_bugs.append(all_bugs[idx])

        input_data['bugs'] = selected_bugs
        print(f'🎯 Processing {len(selected_bugs)} selected bug(s)')

    # Create output directory (args.output is a file path, so use its parent dir)
    output_dir = os.path.dirname(os.path.abspath(args.output))
    os.makedirs(output_dir, exist_ok=True)

    # Run pipeline using Step pattern
    processor = V2chisel_batch()
    result = processor.run(input_data)

    # Print summary (minimal for chisel_diff_only)
    if not args.chisel_diff_only:
        print('\n' + '=' * 80)
        print('📊 PIPELINE SUMMARY')
        print('=' * 80)
        if result['success']:
            print('✅ Pipeline completed successfully')
            print(f'   CPU Profile: {result.get("cpu_profile")}')
            print(f'   Bugs Loaded: {result.get("bugs_processed")}')
            print(f'   Bugs Successful: {result.get("bugs_successful")}/{result.get("bugs_processed")}')
            print(f'   Diffs Applied: {result.get("diffs_applied")}/{result.get("bugs_processed")}')
            print(f'   Compilations: {result.get("compilations_successful")}/{result.get("bugs_processed")}')
            print(f'   Verilog Generated: {result.get("verilog_generated")}/{result.get("bugs_processed")}')
            print(f'   LEC Passed: {result.get("lec_passed")}/{result.get("bugs_processed")}')
            print(f'   Chisel Files Modified: {result.get("files_modified", 0)}')
            print(f'   Total LLM Cost: ${result.get("total_llm_cost", 0):.4f}')
            print(f'   Total LLM Tokens: {result.get("total_llm_tokens", 0)}')
            print('\n📋 Status by Bug:')
            for bug_result in result.get('bug_results', []):
                status = '✅' if bug_result.get('success') else '❌'
                applied = '✓' if bug_result.get('diff_applied', False) else '✗'
                compiled = '✓' if bug_result.get('compilation_success', False) else '✗'
                lec = '✓' if bug_result.get('lec_passed', False) else '✗'
                print(
                    f'   {status} Bug {bug_result.get("bug_number")}: {bug_result.get("file")} [Diff: {applied}, Compile: {compiled}, LEC: {lec}]'
                )
                if bug_result.get('success'):
                    print(f'      LLM: ${bug_result.get("llm_cost", 0):.4f}, {bug_result.get("llm_tokens", 0)} tokens')
                    print(
                        f'      Modified: {bug_result.get("files_modified", 0)} Chisel file(s), Generated: {bug_result.get("verilog_count", 0)} Verilog file(s)'
                    )
                    print('      LEC: Passed')
                else:
                    print(f'      Error: {bug_result.get("error")}')
                    if bug_result.get('lec_counterexample'):
                        print(f'      Counterexample: {bug_result.get("lec_counterexample")}')
        else:
            print(f'❌ Pipeline failed: {result.get("error")}')
        print('=' * 80)

    # Write output YAML with block scalar style for multiline strings
    from ruamel.yaml import YAML as _YAML
    from ruamel.yaml.scalarstring import LiteralScalarString as _LSS

    def _make_literal(obj):
        if isinstance(obj, dict):
            return {k: _make_literal(v) for k, v in obj.items()}
        if isinstance(obj, list):
            return [_make_literal(v) for v in obj]
        if isinstance(obj, str) and '\n' in obj:
            return _LSS(obj)
        return obj

    output_path = Path(args.output)
    if output_path.suffix in ('.yaml', '.yml'):
        output_file = str(output_path)
        output_path.parent.mkdir(parents=True, exist_ok=True)
    else:
        output_path.mkdir(parents=True, exist_ok=True)
        output_file = str(output_path / 'output.yaml')
    _ry = _YAML()
    _ry.default_flow_style = False
    _ry.width = 120
    with open(output_file, 'w') as f:
        _ry.dump(_make_literal(result), f)
    print(f'\n💾 Output written to: {output_file}')

    return 0 if result['success'] else 1


if __name__ == '__main__':
    sys.exit(main())
