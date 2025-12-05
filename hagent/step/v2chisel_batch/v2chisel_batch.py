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
import sys
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

        # Initialize Builder (handles Docker/local execution)
        self.builder = Builder()

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

    def run(self, data):
        """Main processing function"""
        print('\n' + '=' * 80)
        print('🚀 V2chisel_batch - Clean MCP-based Pipeline')
        print('=' * 80)

        # Update input_data with any runtime data
        self.input_data.update(data)

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
        self.chisel_diff_generator = ChiselDiffGenerator(llm_config_file, llm_name, debug=self.debug)

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
        bugs = self.input_data.get('bugs', [])
        if not bugs:
            print('❌ No bugs found in input')
            return {'success': False, 'error': 'No bugs provided'}

        print(f'\n📋 Loaded {len(bugs)} bug(s) to process')

        # Step 2: Determine CPU profile
        cpu_profile = self._determine_cpu_profile(bugs)
        print(f'🔧 Using CPU profile: {cpu_profile}')

        # Step 3: Generate fresh baseline Verilog
        print('\n' + '=' * 80)
        print('STEP 1: Generate Fresh Baseline Verilog')
        print('=' * 80)

        baseline_result = self._generate_baseline_verilog(cpu_profile)

        if not baseline_result['success']:
            print(f'❌ Baseline generation failed: {baseline_result.get("error")}')
            return {'success': False, 'error': f'Baseline generation failed: {baseline_result.get("error")}'}

        print('✅ Baseline Verilog generation complete!')
        print(f'   Profile: {baseline_result.get("profile")}')
        print(f'   Files: {baseline_result.get("file_count", 0)}')

        # Step 2: Process each bug with retry loops
        print('\n' + '=' * 80)
        print('STEP 2: Process Bugs with Retry Loops')
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
        diffs_applied = sum(1 for r in bug_results if r.get('diff_applied', False))
        compilations_successful = sum(1 for r in bug_results if r.get('compilation_success', False))
        verilog_generated = sum(1 for r in bug_results if r.get('verilog_generated', False))
        lec_passed = sum(1 for r in bug_results if r.get('lec_passed', False))
        total_cost = sum(r.get('llm_cost', 0) for r in bug_results)
        total_tokens = sum(r.get('llm_tokens', 0) for r in bug_results)
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

        Priority:
        1. --cpu argument (from input_data['cpu_type'])
        2. Auto-detect from bug Verilog filenames
        3. Default to singlecyclecpu_d
        """
        # Check for explicit override via --cpu argument
        cpu_override = self.input_data.get('cpu_type')
        if cpu_override:
            print(f'🎯 CPU profile override from --cpu argument: {cpu_override}')
            return cpu_override

        # Auto-detect from verilog filenames in bugs
        verilog_files = [bug.get('file', '') for bug in bugs if bug.get('file')]

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

    def _generate_baseline_verilog(self, cpu_profile):
        """
        Generate fresh baseline Verilog using MCP profile system and backup files for golden design.

        Args:
            cpu_profile: MCP profile name (e.g., 'pipelined_d')

        Returns:
            Dict with success status, file information, and backed up Verilog files
        """
        print(f'\n🏭 Generating baseline Verilog using MCP profile: {cpu_profile}')

        # Convert profile to verilog filename for BaselineVerilogGenerator
        profile_to_verilog = {
            'singlecyclecpu_d': ['SingleCycleCPU.sv'],
            'pipelined_d': ['PipelinedCPU.sv'],
            'dualissue_d': ['PipelinedDualIssueCPU.sv'],
        }
        verilog_files = profile_to_verilog.get(cpu_profile, ['SingleCycleCPU.sv'])

        # Generate baseline using BaselineVerilogGenerator (uses MCP internally)
        result = self.baseline_verilog_generator.generate_fresh_baseline(
            docker_container=None,  # Builder handles this
            verilog_files=verilog_files,
        )

        if not result['success']:
            return result

        # Backup the generated baseline Verilog files for golden design creation
        print('💾 [BASELINE] Backing up baseline Verilog files for golden design...')
        backup_id = f'baseline_{cpu_profile}'
        backup_result = self.golden_design_builder.backup_existing_original_verilog(
            docker_container=None,  # Builder handles this
            backup_id=backup_id,
        )

        if backup_result['success']:
            print(f'✅ [BASELINE] Backed up {backup_result["total_files"]} baseline Verilog files')
            # Add backup info to result
            result['original_verilog_files'] = backup_result['files']
            result['baseline_verilog_success'] = True
            result['backup_id'] = backup_id
        else:
            print(f'⚠️  [BASELINE] Backup failed: {backup_result.get("error")}, continuing anyway')
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
        bug_file = bug.get('file', 'unknown')
        bug_description = bug.get('description', '')
        unified_diff = bug.get('unified_diff', bug.get('patch', ''))

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
        hints_result = self._generate_hints_for_bug(unified_diff, bug_description)

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

        print('✅ Hints generated successfully')
        print('   Strategies used: 3 (Direct Module, Signal-Based, Context-Aware)')
        print(f'   Chisel files found: {len(hints_result.get("chisel_files_found", []))}')
        if hints_result.get('chisel_files_found'):
            for f in hints_result['chisel_files_found'][:3]:  # Show first 3
                print(f'     - {f}')

        hints = hints_result.get('hints', '')
        chisel_files_found = hints_result.get('chisel_files_found', [])

        # Initial LLM call to generate Chisel diff
        print('🤖 Calling LLM to generate Chisel diff (initial attempt)...')

        # Start iteration 1 for DAC metrics
        iter1 = report.add_iteration(1)

        llm_result = self.chisel_diff_generator.generate_chisel_diff(
            verilog_diff=unified_diff, chisel_hints=hints, bug_description=bug_description, prompt_name='prompt_initial'
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

        print('✅ LLM generated Chisel diff successfully')
        print(f'   Attempts: {llm_result.get("attempts", 1)}')
        print(f'   Cost: ${llm_result.get("cost", 0):.4f}')
        print(f'   Tokens: {llm_result.get("tokens", 0)}')

        chisel_diff = llm_result.get('chisel_diff', '')
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
            print('✅ Successfully applied Chisel diff')
            print(f'   Files modified: {apply_result.get("files_modified", 0)}')
            report.mark_applier_success()
            break

        # Retry loop for compilation errors (3 iterations max)
        compile_retries = 0
        max_compile_retries = 3

        while compile_retries <= max_compile_retries:
            # Compile modified Chisel and generate new Verilog using MCP
            print('🔨 Compiling modified Chisel and generating Verilog...')
            compile_result = self._compile_and_generate_verilog(cpu_profile)

            if not compile_result['success']:
                error_msg = compile_result.get('error', '')
                report.set_error('compilation', error_msg)

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
            print('✅ Successfully compiled and generated Verilog')
            print(f'   Profile: {compile_result.get("profile")}')
            print(f'   Verilog files: {compile_result.get("verilog_count", 0)}')
            report.mark_compilation_success()
            report.mark_verilog_success()
            break

        # Create golden design before LEC (apply verilog_diff to baseline)
        print('🎯 [GOLDEN] Creating golden design for LEC comparison...')
        golden_result = self.golden_design_builder.create_golden_design(
            verilog_diff=unified_diff,
            master_backup=baseline_result,
            docker_container=None,  # Builder handles this
        )

        if not golden_result['success']:
            print(f'❌ [GOLDEN] Golden design creation failed: {golden_result.get("error")}')
            print('⚠️  [GOLDEN] Continuing with LEC anyway, but results may be incorrect')
        else:
            print('✅ [GOLDEN] Golden design created successfully')
            print(f'   Files modified: {len(golden_result.get("files_modified", []))}')
            print(f'   Golden directory: {golden_result.get("golden_directory")}')

        # Retry loop for LEC failures (1 iteration max)
        lec_retries = 0
        max_lec_retries = 1

        while lec_retries <= max_lec_retries:
            # Run LEC verification (compares golden design vs modified Verilog)
            print('🔍 Running LEC verification...')
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
                        compile_result = self._compile_and_generate_verilog(cpu_profile)
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
                        golden_result = self.golden_design_builder.create_golden_design(
                            verilog_diff=unified_diff, master_backup=baseline_result, docker_container=None
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

    def _generate_hints_for_bug(self, verilog_diff, bug_description):
        """
        Generate Chisel hints from Verilog diff using multi-strategy approach.

        This method uses HintsGeneratorV2 which combines 3 strategies:
        1. Direct Module Mapping - Maps Verilog module names to Chisel classes
        2. Signal-Based Search - Searches for signals mentioned in the diff
        3. Context-Aware Analysis - Analyzes logic patterns and context

        Args:
            verilog_diff: Unified diff of Verilog changes
            bug_description: Description of the bug

        Returns:
            Dict with success status, hints, and metadata
        """
        try:
            if self.debug:
                print('🔍 [HINTS] Running multi-strategy hints generation...')

            # Call HintsGeneratorV2 to run all 3 strategies
            hints_result = self.hints_generator_v2.generate_hints_v2(verilog_diff=verilog_diff, bug_description=bug_description)

            if hints_result.get('success'):
                if self.debug:
                    print('✅ [HINTS] Multi-strategy hints generation successful')
                    print(f'   Combined hints length: {len(hints_result.get("hints", ""))} chars')

                return {
                    'success': True,
                    'hints': hints_result.get('hints', ''),
                    'chisel_files_found': hints_result.get('chisel_files_found', []),
                    'strategy_1_hints': hints_result.get('strategy_1_hints', ''),
                    'strategy_2_hints': hints_result.get('strategy_2_hints', ''),
                    'strategy_3_hints': hints_result.get('strategy_3_hints', ''),
                    'confidence': hints_result.get('confidence', 0.0),
                }
            else:
                error_msg = hints_result.get('error', 'Unknown error in hints generation')
                if self.debug:
                    print(f'❌ [HINTS] Hints generation failed: {error_msg}')
                return {'success': False, 'error': error_msg}

        except Exception as e:
            error_msg = f'Exception during hints generation: {str(e)}'
            if self.debug:
                print(f'❌ [HINTS] {error_msg}')
            return {'success': False, 'error': error_msg}

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
            if self.debug:
                print('📝 [APPLIER] Applying Chisel diff to Docker files...')

            if not chisel_diff:
                return {'success': False, 'error': 'Empty Chisel diff provided'}

            # Determine target file path if available from hints
            target_file = chisel_files_found[0] if chisel_files_found else None

            # Apply diff using DockerDiffApplier
            success = self.docker_diff_applier.apply_diff_to_container(
                diff_content=chisel_diff, target_file_path=target_file, dry_run=False
            )

            if success:
                if self.debug:
                    print('✅ [APPLIER] Diff applied successfully')

                return {
                    'success': True,
                    'files_modified': len(chisel_files_found) if chisel_files_found else 1,
                    'target_file': target_file,
                }
            else:
                error_msg = 'DockerDiffApplier returned failure'
                if self.debug:
                    print(f'❌ [APPLIER] {error_msg}')
                return {'success': False, 'error': error_msg}

        except Exception as e:
            error_msg = f'Exception during diff application: {str(e)}'
            if self.debug:
                print(f'❌ [APPLIER] {error_msg}')
            return {'success': False, 'error': error_msg}

    def _compile_and_generate_verilog(self, cpu_profile):
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
        try:
            if self.debug:
                print(f'🔨 [COMPILE] Compiling Chisel and generating Verilog using MCP profile: {cpu_profile}')

            # Use Builder's run_api to call MCP compile command
            # This executes: sbt "runMain dinocpu.PipelinedDualIssueDebug" (or similar based on profile)
            exit_code, stdout, stderr = self.builder.run_api(exact_name=cpu_profile, command_name='compile')

            if exit_code == 0:
                if self.debug:
                    print('✅ [COMPILE] Compilation and Verilog generation successful')

                # Count generated Verilog files
                verilog_count = self._count_verilog_files(cpu_profile)

                return {
                    'success': True,
                    'profile': cpu_profile,
                    'exit_code': exit_code,
                    'stdout': stdout,
                    'verilog_count': verilog_count,
                }
            else:
                error_msg = f'Compilation failed with exit code {exit_code}: {stderr}'
                if self.debug:
                    print(f'❌ [COMPILE] {error_msg}')

                return {'success': False, 'error': error_msg, 'exit_code': exit_code, 'stderr': stderr}

        except Exception as e:
            error_msg = f'Exception during compilation: {str(e)}'
            if self.debug:
                print(f'❌ [COMPILE] {error_msg}')
            return {'success': False, 'error': error_msg}

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

    def _run_lec_verification(self, bug_file, cpu_profile, unified_diff, golden_result):
        """
        Run Logic Equivalence Check (LEC) between golden design and modified Verilog.

        This compares:
        - Golden Verilog (baseline + verilog_diff): CORRECT fixed design
        - Modified Verilog (from Chisel compilation): Design after applying Chisel fix

        Args:
            bug_file: Name of the buggy Verilog file
            cpu_profile: MCP profile name (determines which Verilog files to compare)
            unified_diff: Original Verilog diff for reference
            golden_result: Golden design creation result with file paths

        Returns:
            Dict with success status, LEC command, and any counterexample
        """
        try:
            if self.debug:
                print('🔍 [LEC] Starting Logic Equivalence Check...')
                print(f'   Bug file: {bug_file}')
                print(f'   CPU profile: {cpu_profile}')

            # Map profile to Verilog files
            profile_to_verilog = {
                'singlecyclecpu_d': 'SingleCycleCPU.sv',
                'pipelined_d': 'PipelinedCPU.sv',
                'dualissue_d': 'PipelinedDualIssueCPU.sv',
            }

            verilog_filename = profile_to_verilog.get(cpu_profile, 'SingleCycleCPU.sv')

            # Paths to golden and modified Verilog
            golden_dir = golden_result.get('golden_directory', '/code/workspace/repo/lec_golden')
            modified_dir = f'/code/workspace/build/build_{cpu_profile}'

            golden_file = f'{golden_dir}/{verilog_filename}'
            modified_file = f'{modified_dir}/{verilog_filename}'

            # Read both Verilog files
            print(f'📄 [LEC] Reading GOLDEN Verilog: {golden_file}')
            golden_verilog = self.builder.filesystem.read_text(golden_file)

            print(f'📄 [LEC] Reading MODIFIED Verilog: {modified_file}')
            modified_verilog = self.builder.filesystem.read_text(modified_file)

            # Extract module name from bug_file (e.g., "ALU.sv" -> "ALU")
            module_name = bug_file.replace('.sv', '').replace('.v', '')

            print(f'🎯 [LEC] Comparing module: {module_name}')
            print(f'   Golden (correct): {golden_file}')
            print(f'   Modified (from LLM): {modified_file}')

            # Run LEC using Equiv_check
            # This will print the exact command and files involved
            lec_result = self.equiv_check.check_equivalence(
                gold_code=golden_verilog, gate_code=modified_verilog, desired_top=module_name if module_name else ''
            )

            if lec_result is True:
                if self.debug:
                    print('✅ [LEC] Designs are logically equivalent')

                return {'success': True, 'result': 'equivalent', 'command': 'Printed above by Equiv_check'}
            elif lec_result is False:
                counterexample = self.equiv_check.get_counterexample()
                error_msg = 'Designs are NOT logically equivalent'

                if self.debug:
                    print(f'❌ [LEC] {error_msg}')
                    if counterexample:
                        print(f'   Counterexample:\n{counterexample}')

                return {'success': False, 'error': error_msg, 'counterexample': counterexample, 'result': 'not_equivalent'}
            else:
                # None = inconclusive
                error_msg = f'LEC result inconclusive: {self.equiv_check.get_error()}'
                if self.debug:
                    print(f'⚠️  [LEC] {error_msg}')

                return {'success': False, 'error': error_msg, 'result': 'inconclusive'}

        except Exception as e:
            error_msg = f'Exception during LEC verification: {str(e)}'
            if self.debug:
                print(f'❌ [LEC] {error_msg}')
            return {'success': False, 'error': error_msg}


def main():
    """Command-line interface"""
    parser = argparse.ArgumentParser(description='V2chisel_batch - Clean MCP-based pipeline')

    # Required arguments
    parser.add_argument('input_file', help='Input YAML file with bugs')
    parser.add_argument('-o', '--output', required=True, help='Output directory')

    # Optional arguments
    parser.add_argument(
        '--cpu',
        choices=['singlecyclecpu_d', 'pipelined_d', 'dualissue_d'],
        help='CPU profile override (default: auto-detect from bugs)',
    )
    parser.add_argument('--bugs', help='Bug numbers to process (e.g., "1,2,3" or "1-5")')
    parser.add_argument('--debug', action='store_true', default=True, help='Enable debug output')

    args = parser.parse_args()

    # Load input YAML
    print(f'📂 Loading input from: {args.input_file}')
    with open(args.input_file, 'r') as f:
        input_data = yaml.safe_load(f)

    # Add command-line arguments to input_data
    if args.cpu:
        input_data['cpu_type'] = args.cpu
        print(f'🔧 CPU type override from --cpu: {args.cpu}')

    input_data['debug'] = args.debug
    input_data['output_dir'] = args.output

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

    # Create output directory
    os.makedirs(args.output, exist_ok=True)

    # Run pipeline using Step pattern
    processor = V2chisel_batch()
    result = processor.run(input_data)

    # Print summary
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

    # Write output YAML
    output_file = os.path.join(args.output, 'output.yaml')
    with open(output_file, 'w') as f:
        yaml.dump(result, f, default_flow_style=False)
    print(f'\n💾 Output written to: {output_file}')

    return 0 if result['success'] else 1


if __name__ == '__main__':
    sys.exit(main())
