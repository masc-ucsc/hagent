#!/usr/bin/env python3
# hagent/step/v2chisel_batch/components/pipeline_reporter.py
# See LICENSE file for details

import re
from typing import Optional, List, Dict, Any
from dataclasses import dataclass, field


@dataclass
class IterationResult:
    """Track results for a single iteration"""

    iteration: int
    llm_success: bool = False
    applier_success: bool = False
    compilation_success: bool = False
    verilog_gen_success: bool = False
    lec_success: bool = False
    error_stage: Optional[str] = None  # 'llm', 'applier', 'compilation', 'verilog_gen', 'lec'
    error_message: Optional[str] = None
    generated_chisel_diff: Optional[str] = None


@dataclass
class DACMetrics:
    """DAC Paper Reporting Metrics - all the metrics needed for DAC paper analysis"""

    # Core metrics
    failure_stage: str = 'unknown'  # First failure point: hints_generation, llm_generation, diff_application, compilation, verilog_generation, lec, success
    success_at_iteration: Optional[int] = None  # Which iteration succeeded (1-3 for compile, 1-2 for LEC)

    # Verilog diff statistics
    verilog_diff_stats: Dict[str, int] = field(
        default_factory=lambda: {'added_lines': 0, 'removed_lines': 0, 'total_changed_lines': 0}
    )

    # Chisel files affected by LLM-generated diff
    chisel_files_affected: List[str] = field(default_factory=list)

    # LEC file details
    lec_files: Dict[str, Any] = field(default_factory=lambda: {'golden_file': None, 'generated_file': None, 'files_compared': []})

    # Detailed iteration history
    iteration_history: List[Dict[str, Any]] = field(default_factory=list)

    @staticmethod
    def count_diff_lines(unified_diff: str) -> Dict[str, int]:
        """Count changed lines in unified diff"""
        if not unified_diff:
            return {'added_lines': 0, 'removed_lines': 0, 'total_changed_lines': 0}

        lines = unified_diff.split('\n')
        added = sum(1 for line in lines if line.startswith('+') and not line.startswith('+++'))
        removed = sum(1 for line in lines if line.startswith('-') and not line.startswith('---'))

        return {'added_lines': added, 'removed_lines': removed, 'total_changed_lines': added + removed}

    @staticmethod
    def extract_affected_chisel_files(chisel_diff: str) -> List[str]:
        """Extract list of files modified in Chisel diff"""
        if not chisel_diff:
            return []

        files = []
        for line in chisel_diff.split('\n'):
            # Match both "--- a/path/file.scala" and "+++ b/path/file.scala"
            if line.startswith('---') or line.startswith('+++'):
                # Extract filename from "--- a/path/to/file.scala" or "+++ b/path/to/file.scala"
                match = re.search(r'[ab]/(.*\.scala)', line)
                if match:
                    filename = match.group(1)
                    if filename not in files:
                        files.append(filename)

        return files

    @staticmethod
    def determine_failure_stage(
        has_hints: bool,
        llm_success: bool,
        applier_success: bool,
        compile_success: bool,
        verilog_gen_success: bool,
        golden_design_success: bool,
        lec_success: bool,
    ) -> str:
        """Determine exact failure stage in pipeline"""
        if not has_hints:
            return 'hints_generation'
        elif not llm_success:
            return 'llm_generation'
        elif not applier_success:
            return 'diff_application'
        elif not compile_success:
            return 'compilation'
        elif not verilog_gen_success:
            return 'verilog_generation'
        elif not golden_design_success:
            return 'golden_design'
        elif not lec_success:
            return 'lec'
        else:
            return 'success'

    @staticmethod
    def find_success_iteration(iterations: List[IterationResult]) -> Optional[int]:
        """Find which iteration succeeded (compile + verilog gen)"""
        for iter_result in iterations:
            if (
                iter_result.llm_success
                and iter_result.applier_success
                and iter_result.compilation_success
                and iter_result.verilog_gen_success
            ):
                return iter_result.iteration
        return None

    @staticmethod
    def build_iteration_history(iterations: List[IterationResult]) -> List[Dict[str, Any]]:
        """Build detailed iteration history for DAC reporting"""
        history = []
        for iter_result in iterations:
            history.append(
                {
                    'attempt': iter_result.iteration,
                    'llm_success': iter_result.llm_success,
                    'applier_success': iter_result.applier_success,
                    'compile_success': iter_result.compilation_success,
                    'verilog_gen_success': iter_result.verilog_gen_success,
                    'lec_success': iter_result.lec_success,
                    'error_stage': iter_result.error_stage,
                    'error_message': iter_result.error_message,
                    'generated_diff_preview': (
                        iter_result.generated_chisel_diff[:200] + '...'
                        if iter_result.generated_chisel_diff and len(iter_result.generated_chisel_diff) > 200
                        else iter_result.generated_chisel_diff
                    ),
                }
            )
        return history


@dataclass
class PipelineReport:
    """Generate concise pipeline status reports"""

    bug_id: str
    iterations: List[IterationResult] = field(default_factory=list)
    dac_metrics: DACMetrics = field(default_factory=DACMetrics)

    def add_iteration(self, iteration: int) -> IterationResult:
        """Add a new iteration to track"""
        result = IterationResult(iteration=iteration)
        self.iterations.append(result)
        return result

    def get_current_iteration(self) -> Optional[IterationResult]:
        """Get the current (last) iteration"""
        return self.iterations[-1] if self.iterations else None

    def mark_llm_success(self, generated_diff: str = None, iteration: int = None):
        """Mark LLM generation as successful"""
        if iteration is None and self.iterations:
            self.iterations[-1].llm_success = True
            if generated_diff:
                self.iterations[-1].generated_chisel_diff = generated_diff
        else:
            for iter_result in self.iterations:
                if iter_result.iteration == iteration:
                    iter_result.llm_success = True
                    if generated_diff:
                        iter_result.generated_chisel_diff = generated_diff
                    break

    def mark_applier_success(self, iteration: int = None):
        """Mark diff application as successful"""
        if iteration is None and self.iterations:
            self.iterations[-1].applier_success = True
        else:
            for iter_result in self.iterations:
                if iter_result.iteration == iteration:
                    iter_result.applier_success = True
                    break

    def mark_compilation_success(self, iteration: int = None):
        """Mark compilation as successful"""
        if iteration is None and self.iterations:
            self.iterations[-1].compilation_success = True
        else:
            for iter_result in self.iterations:
                if iter_result.iteration == iteration:
                    iter_result.compilation_success = True
                    break

    def mark_verilog_success(self, iteration: int = None):
        """Mark Verilog generation as successful"""
        if iteration is None and self.iterations:
            self.iterations[-1].verilog_gen_success = True
        else:
            for iter_result in self.iterations:
                if iter_result.iteration == iteration:
                    iter_result.verilog_gen_success = True
                    break

    def mark_lec_success(self, iteration: int = None):
        """Mark LEC as successful"""
        if iteration is None and self.iterations:
            self.iterations[-1].lec_success = True
        else:
            for iter_result in self.iterations:
                if iter_result.iteration == iteration:
                    iter_result.lec_success = True
                    break

    def set_error(self, error_stage: str, error_message: str, iteration: int = None):
        """Set error stage and message for iteration"""
        if iteration is None and self.iterations:
            self.iterations[-1].error_stage = error_stage
            self.iterations[-1].error_message = error_message
        else:
            for iter_result in self.iterations:
                if iter_result.iteration == iteration:
                    iter_result.error_stage = error_stage
                    iter_result.error_message = error_message
                    break

    def finalize_dac_metrics(
        self,
        verilog_diff: str,
        has_hints: bool,
        golden_design_success: bool,
        lec_golden_file: str = None,
        lec_generated_file: str = None,
        lec_files_compared: List[str] = None,
    ):
        """Finalize all DAC metrics after pipeline completes"""
        # Get final successful chisel diff for file extraction
        final_chisel_diff = None
        for iter_result in self.iterations:
            if iter_result.llm_success and iter_result.generated_chisel_diff:
                final_chisel_diff = iter_result.generated_chisel_diff

        # Calculate verilog diff stats
        self.dac_metrics.verilog_diff_stats = DACMetrics.count_diff_lines(verilog_diff)

        # Extract chisel files affected
        if final_chisel_diff:
            self.dac_metrics.chisel_files_affected = DACMetrics.extract_affected_chisel_files(final_chisel_diff)

        # Determine failure stage
        llm_success = any(iter_result.llm_success for iter_result in self.iterations)
        applier_success = any(iter_result.applier_success for iter_result in self.iterations)
        compile_success = any(iter_result.compilation_success for iter_result in self.iterations)
        verilog_gen_success = any(iter_result.verilog_gen_success for iter_result in self.iterations)
        lec_success = any(iter_result.lec_success for iter_result in self.iterations)

        self.dac_metrics.failure_stage = DACMetrics.determine_failure_stage(
            has_hints=has_hints,
            llm_success=llm_success,
            applier_success=applier_success,
            compile_success=compile_success,
            verilog_gen_success=verilog_gen_success,
            golden_design_success=golden_design_success,
            lec_success=lec_success,
        )

        # Find success iteration
        self.dac_metrics.success_at_iteration = DACMetrics.find_success_iteration(self.iterations)

        # Build iteration history
        self.dac_metrics.iteration_history = DACMetrics.build_iteration_history(self.iterations)

        # Store LEC file details
        if lec_golden_file or lec_generated_file or lec_files_compared:
            self.dac_metrics.lec_files = {
                'golden_file': lec_golden_file,
                'generated_file': lec_generated_file,
                'files_compared': lec_files_compared or [],
            }

    def get_dac_report_dict(self) -> Dict[str, Any]:
        """Get DAC metrics as dictionary for YAML output"""
        return {
            'failure_stage': self.dac_metrics.failure_stage,
            'success_at_iteration': self.dac_metrics.success_at_iteration,
            'verilog_diff_stats': self.dac_metrics.verilog_diff_stats,
            'chisel_files_affected': self.dac_metrics.chisel_files_affected,
            'lec_files': self.dac_metrics.lec_files,
            'iteration_history': self.dac_metrics.iteration_history,
        }

    def get_compilation_status(self) -> str:
        """Get one-line compilation status"""
        for iter_result in self.iterations:
            if iter_result.compilation_success:
                return f'COMPILATION: SUCCESS (iteration {iter_result.iteration})'

        # Find last compilation attempt
        for iter_result in reversed(self.iterations):
            if iter_result.llm_success:  # Only count iterations where LLM generated code
                return f'COMPILATION: FAILED (last attempt: iteration {iter_result.iteration})'

        return 'COMPILATION: NO ATTEMPTS'

    def get_lec_status(self) -> str:
        """Get one-line LEC status"""
        for iter_result in self.iterations:
            if iter_result.lec_success:
                return f'LEC: SUCCESS (iteration {iter_result.iteration})'

        # Find last LEC attempt (needs successful compilation + verilog)
        for iter_result in reversed(self.iterations):
            if iter_result.compilation_success and iter_result.verilog_gen_success:
                return f'LEC: FAILED (last attempt: iteration {iter_result.iteration})'

        return 'LEC: NO ATTEMPTS (compilation/verilog failed)'

    def get_summary_line(self) -> str:
        """Get one-line summary"""
        comp_status = self.get_compilation_status()
        lec_status = self.get_lec_status()
        return f'📊 PIPELINE SUMMARY [{self.bug_id}]: {comp_status} | {lec_status}'

    def print_summary(self):
        """Print the one-line summary"""
        print(self.get_summary_line())


class PipelineReporter:
    """Manages pipeline reports for multiple bugs"""

    def __init__(self):
        self.reports: Dict[str, PipelineReport] = {}

    def create_report(self, bug_id: str) -> PipelineReport:
        """Create a new report for a bug"""
        report = PipelineReport(bug_id=bug_id)
        self.reports[bug_id] = report
        return report

    def get_report(self, bug_id: str) -> Optional[PipelineReport]:
        """Get existing report for a bug"""
        return self.reports.get(bug_id)

    def print_all_summaries(self):
        """Print summary for all bugs"""
        print('=' * 80)
        print('🎯 FINAL PIPELINE SUMMARY')
        print('=' * 80)
        for bug_id, report in self.reports.items():
            report.print_summary()
        print('=' * 80)


# Example usage:
if __name__ == '__main__':
    # Demo usage with DAC metrics
    reporter = PipelineReporter()

    # Bug 1: Success case
    report1 = reporter.create_report('NextPC.sv')
    iter1 = report1.add_iteration(1)
    report1.mark_llm_success(generated_diff='--- a/NextPC.scala\n+++ b/NextPC.scala\n...')
    report1.mark_applier_success()
    report1.mark_compilation_success()
    report1.mark_verilog_success()
    report1.mark_lec_success()

    # Finalize DAC metrics
    verilog_diff = '--- a/NextPC.sv\n+++ b/NextPC.sv\n@@ -10,3 +10,3 @@\n- assign x = y;\n+ assign x = z;\n'
    report1.finalize_dac_metrics(
        verilog_diff=verilog_diff,
        has_hints=True,
        golden_design_success=True,
        lec_golden_file='/path/to/golden/NextPC.sv',
        lec_generated_file='/path/to/generated/NextPC.sv',
        lec_files_compared=['NextPC.sv'],
    )

    print('DAC Metrics for Bug 1:')
    print(report1.get_dac_report_dict())

    # Bug 2: Compilation failure case
    report2 = reporter.create_report('ALU.sv')
    iter2a = report2.add_iteration(1)
    report2.mark_llm_success(generated_diff='--- a/ALU.scala\n...')
    report2.mark_applier_success()
    report2.set_error('compilation', 'Type mismatch error')

    iter2b = report2.add_iteration(2)
    report2.mark_llm_success(generated_diff='--- a/ALU.scala\n...')
    report2.mark_applier_success()
    report2.set_error('compilation', 'Syntax error')

    report2.finalize_dac_metrics(
        verilog_diff='--- a/ALU.sv\n+++ b/ALU.sv\n@@ -5,2 +5,2 @@\n- wire [3:0] x;\n+ wire [7:0] x;\n',
        has_hints=True,
        golden_design_success=False,
    )

    print('\nDAC Metrics for Bug 2:')
    print(report2.get_dac_report_dict())

    # Print summaries
    reporter.print_all_summaries()
