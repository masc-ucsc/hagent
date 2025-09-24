#!/usr/bin/env python3
# hagent/step/v2chisel_batch/components/pipeline_reporter.py
# See LICENSE file for details

from typing import Optional, List, Dict
from dataclasses import dataclass, field


@dataclass
class IterationResult:
    """Track results for a single iteration"""

    iteration: int
    llm_success: bool = False
    compilation_success: bool = False
    verilog_gen_success: bool = False
    lec_success: bool = False
    error_message: Optional[str] = None


@dataclass
class PipelineReport:
    """Generate concise pipeline status reports"""

    bug_id: str
    iterations: List[IterationResult] = field(default_factory=list)

    def add_iteration(self, iteration: int) -> IterationResult:
        """Add a new iteration to track"""
        result = IterationResult(iteration=iteration)
        self.iterations.append(result)
        return result

    def get_current_iteration(self) -> Optional[IterationResult]:
        """Get the current (last) iteration"""
        return self.iterations[-1] if self.iterations else None

    def mark_llm_success(self, iteration: int = None):
        """Mark LLM generation as successful"""
        if iteration is None and self.iterations:
            self.iterations[-1].llm_success = True
        else:
            for iter_result in self.iterations:
                if iter_result.iteration == iteration:
                    iter_result.llm_success = True
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

    def set_error(self, error_message: str, iteration: int = None):
        """Set error message for iteration"""
        if iteration is None and self.iterations:
            self.iterations[-1].error_message = error_message
        else:
            for iter_result in self.iterations:
                if iter_result.iteration == iteration:
                    iter_result.error_message = error_message
                    break

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
    # Demo usage
    reporter = PipelineReporter()

    # Bug 1: Success case
    report1 = reporter.create_report('NextPC.sv')
    iter1 = report1.add_iteration(1)
    report1.mark_llm_success()
    report1.mark_compilation_success()
    report1.mark_verilog_success()
    report1.mark_lec_success()

    # Bug 2: Compilation failure case
    report2 = reporter.create_report('ALU.sv')
    iter2a = report2.add_iteration(1)
    report2.mark_llm_success()
    # compilation fails
    iter2b = report2.add_iteration(2)
    report2.mark_llm_success()
    # compilation fails again

    # Bug 3: LEC failure case
    report3 = reporter.create_report('Control.sv')
    iter3 = report3.add_iteration(1)
    report3.mark_llm_success()
    report3.mark_compilation_success()
    report3.mark_verilog_success()
    # LEC fails

    # Print summaries
    reporter.print_all_summaries()
