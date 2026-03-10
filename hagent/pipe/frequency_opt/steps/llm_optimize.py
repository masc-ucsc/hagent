"""
LLM Optimization step with four-phase pipeline.

This step optimizes RTL modules for timing improvement using an LLM-driven
pipeline with compilation/LEC verification and frequency evaluation.

Pipeline per module:
  1. Generate Candidates: LLM generates N optimized candidates
  2. Verify Candidates:   Compile + LEC each candidate (fix-agent on failure)
  3. Evaluate Timing:   Synth + STA on all verified candidates
  4. Refine Candidates:   Deep-dive frequency feedback loop (only if no improvement)
"""

import os
import re
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from hagent.core.step import Step
from hagent.core.llm_wrap import LLM_wrap
from hagent.tool.verilog_patch_applier import VerilogPatchApplier
from hagent.tool.parse_tool_result import get_tool_result_parser
from hagent.tool.memory import CompilationFixMemory, DesignWareMemory, OptimizationMemory, Memory_shot
from hagent.pipe.frequency_opt.steps.common_utilities import get_clock_signal
from hagent.pipe.frequency_opt.schema import (
    BenchmarkConfig,
    RTLSourceConfig,
    ToolsConfig,
    ThresholdsConfig,
    LLMConfig,
    StorageConfig,
    require_field,
    set_field,
)
from hagent.pipe.frequency_opt.llm_session import LLMSession


# ─── Data structures ──────────────────────────────────────────────────────────


@dataclass
class CandidateState:
    """Tracks a single candidate through the optimization pipeline."""

    code: str = ''
    module_name: str = ''
    candidate_strat: str = ''
    compile_ok: bool = False
    lec_ok: bool = False
    frequency: Optional[float] = None
    attempt_dir: Optional[Path] = None
    gate_elab_path: Optional[Path] = None


@dataclass(frozen=True)
class ElabResult:
    patch: Optional[str]  # present on success
    elab_path: Optional[Path]  # present on success
    error_msg: Optional[str]  # present on failure

    @property
    def ok(self) -> bool:
        return self.elab_path is not None

    def assert_valid(self) -> None:
        # exactly one of (success payload) vs error
        # We could just return `fixed_patch` without `res_elab_path` but it could save time to re-elab.
        assert (self.elab_path is None) == (self.patch is None)  # both set or both None
        assert (self.elab_path is None) != (self.error_msg is None)  # xor with error


# ─── Step implementation ──────────────────────────────────────────────────────
_CRITICAL_HINT = (
    'We marked the signals/procedures that the critical path traverses through with "// CRITICAL:" markers in the source code. '
    'The critical signal should be found directly adjacent to the marked lines '
    'or live in the adjacent "begin, end" blocks, or always blocks of the marked line.'
)

PATCH_FORMAT_CONTRACT = (
    'You MUST use exactly this format for each change:\n\n'
    '<<<<<<< SEARCH\n'
    '<exact lines from original code>\n'
    '=======\n'
    '<replacement lines>\n'
    '>>>>>>> REPLACE\n\n'
    'Rules:\n'
    '- The closing marker MUST be ">>>>>>> REPLACE" (not END, DONE, or anything else)\n'
    '- The separator MUST be "=======" (at least 3 equals signs)\n'
    '- The opening marker MUST be "<<<<<<< SEARCH"\n'
    '- Output ONLY these blocks. No prose, no code fences, no commentary.\n'
)


class LLMOptimizeWithLECStep(Step):
    """
    Four-phase LLM optimization with compilation, LEC, and timing evaluation.

    1. Generate Candidates — LLM produces N optimized RTL candidates
    2. Verify Candidates   — Compile + LEC each (disposable fix-agent on failure)
    3. Evaluate Timing   — Synth + STA on all verified candidates
    4. Refine Candidates   — Frequency feedback loop

    Required YAML sections:
      - thresholds: compile_fix_max, freq_refine_max
      - llm: conf_file
      - storage: output_dir, memory_db_dir
      - benchmark: top_module
      - rtl: source_dir, manifest_file
      - tools: liberty_file, elab_method

    Required YAML fields (from previous steps):
      - sta.frequency_mhz (baseline frequency)
      - critical_path_info.dir
      - critical_path_info.module_names
      - critical_path_info.critical_path

    Writes to YAML:
      - optimized.rtl_dir
      - optimized.modules
      - optimized.failed_modules
      - should_continue
    """

    def setup(self):
        super().setup()
        self.patch_applier = VerilogPatchApplier()

        # Parse configuration from input YAML
        data = self.input_data
        self.thresholds = ThresholdsConfig.from_data(data, 'thresholds')
        self.llm_config = LLMConfig.from_data(data, 'llm')
        self.storage = StorageConfig.from_data(data, 'storage')
        self.benchmark = BenchmarkConfig.from_data(data, 'benchmark')
        self.rtl = RTLSourceConfig.from_data(data, 'rtl')
        self.tools = ToolsConfig.from_data(data, 'tools')
        self.baseline_freq: float = require_field(data, 'sta.frequency_mhz')

        # Initialize RAG memory databases
        self._init_rag_db()

        # Setup output directory
        self.output_dir = Path(self.storage.output_dir) / 'llm_generated'
        self.output_dir.mkdir(parents=True, exist_ok=True)

        # Get critical modules info
        self.critical_dir = require_field(data, 'critical_path_info.commented_rtl_dir')
        assert Path(self.critical_dir).is_dir() and any(Path(self.critical_dir).iterdir())
        self.critical_module_names = require_field(data, 'critical_path_info.module_names')

        # Get design hierarchy
        self.hierarchy_file = require_field(data, 'rtl.hierarchy_file')

        # Create shared LLM instances
        self.arch_llm = LLM_wrap(
            name='architecture_timing_optimizer', log_file='arch_agent.log', conf_file=self.llm_config.conf_file
        )
        self.opt_llm = LLM_wrap(name='module_timing_optimizer', log_file='module_opt.log', conf_file=self.llm_config.conf_file)
        self.syntax_fix_llm = LLM_wrap(name='syntax_fixer', log_file='syntax_fix.log', conf_file=self.llm_config.conf_file)
        self.lec_fix_llm = LLM_wrap(name='lec_fixer', log_file='lec_fix.log', conf_file=self.llm_config.conf_file)

        for llm in [self.arch_llm, self.opt_llm, self.syntax_fix_llm, self.lec_fix_llm]:
            if llm.last_error:
                self.error(f'LLM setup failed for {llm.name}: {llm.last_error}')

    def run(self, data: Dict) -> Dict:
        print(f'  Baseline frequency: {self.baseline_freq:.2f} MHz')

        opt_dir = self.output_dir / 'optimize'
        opt_dir.mkdir(parents=True, exist_ok=True)
        opt_result = self._run_optimize_workflow(opt_dir)

        # Re-run STA with all optimized modules combined
        combined_freq = None
        if opt_result['optimized_modules']:
            replacements = {m['name']: Path(m['file']) for m in opt_result['optimized_modules']}
            try:
                combined_flist = self._create_gate_flist(
                    original_flist=self.rtl.manifest_file,
                    replacements=replacements,
                    output_path=opt_dir / 'combined_flist.f',
                )
                combined_freq = self._run_candidate_synth_sta(flist_path=combined_flist, output_dir=opt_dir, tag='combined_sta')
            except ValueError as e:
                print(f'  Combined STA flist error: {e}')

            if combined_freq is not None:
                print(f'\n  Combined frequency: {combined_freq:.2f} MHz (baseline: {self.baseline_freq:.2f} MHz)')
            else:
                print('\n  Combined STA failed or returned no frequency')

        output = data.copy()
        set_field(output, 'optimized.rtl_dir', str(self.output_dir))
        set_field(output, 'optimized.modules', opt_result['optimized_modules'])
        set_field(output, 'optimized.failed_modules', opt_result['failed_modules'])
        if combined_freq is not None:
            set_field(output, 'optimized.combined_frequency_mhz', combined_freq)

        print('\nOptimization summary:')
        print(f'  Successful: {len(opt_result["optimized_modules"])}')
        print(f'  Failed: {len(opt_result["failed_modules"])}')

        return output

    # Core orchestration flow
    def _run_optimize_workflow(self, output_dir: Path) -> Dict:
        """Core optimization workflow for all critical modules.

        Steps:
        1. Arch agent proposes per-module strategies.
        2. Optimize each module (strategy loop inside _optimize_single_module).

        Args:
            output_dir: Directory for all optimization artifacts.

        Returns:
            {'optimized_modules': [...], 'failed_modules': [...]}
        """
        # Arch agent proposes strategies per module
        prompt_per_module = self._craft_prompt_for_each_module(self.arch_llm, self.hierarchy_file)

        # Optimize each module with different strategies
        optimized_modules = []
        failed_modules = []
        for module_name, strategies in prompt_per_module.items():
            print(f'\n  Optimizing module: {module_name}')
            original_code = self._read_module_code(self.critical_dir, module_name)

            result = self._optimize_single_module(self.opt_llm, module_name, original_code, strategies)

            if result['success']:
                optimized_dir = output_dir / 'optimized'
                optimized_dir.mkdir(parents=True, exist_ok=True)
                opt_file = optimized_dir / f'{module_name}.sv'
                opt_file.write_text(result['code'])
                optimized_modules.append(
                    {
                        'name': module_name,
                        'file': str(opt_file),
                        'achieved_freq': result['frequency'],
                    }
                )
                print(f'    Success: saved to {opt_file}')
            else:
                failed_modules.append({'name': module_name, 'reason': result['reason']})
                print(f'    Failed: {result["reason"]}')

        return {'optimized_modules': optimized_modules, 'failed_modules': failed_modules}

    def _craft_prompt_for_each_module(
        self,
        arch_llm: LLM_wrap,
        hierarchy_file: str,
    ) -> Dict[str, Dict[str, str]]:
        """Craft customized optimization prompt for each module.

        Uses arch_llm to reason about the design hierarchy and
        propose per-module strategies.

        Returns:
            {'module_name': {'strategy_name': 'prompt text', ...}}
        """
        with open(hierarchy_file, 'r') as f:
            hier_content = f.read()

        if not hier_content:
            raise ValueError(f'{hierarchy_file} is empty')

        parts = []
        for i, module_name in enumerate(self.critical_module_names, 1):
            code = self._read_module_code(self.critical_dir, module_name)
            print(f'    Architecture agent reading {module_name} source code')
            parts.append(f'--- Module {i}: {module_name} ---\n```verilog\n{code}\n```')
        modules_detail = '\n\n'.join(parts)

        prompt_dict = {
            'hierarchy_content': hier_content,
            'modules_detail': modules_detail,
            'critical_hint': _CRITICAL_HINT,
        }

        responses = arch_llm.inference(prompt_dict, 'arch_optimize_prompt')
        if not responses:
            self.error('Architecture agent returned no response')

        strat_prompt_per_module = self._parse_arch_agent_response(responses[0])
        for module_name in self.critical_module_names:
            if module_name not in strat_prompt_per_module:
                print(f'  Warning: no strategy for {module_name}, using default')
                strat_prompt_per_module[module_name] = {'default': _CRITICAL_HINT}
            else:
                for name in strat_prompt_per_module[module_name]:
                    strat_prompt_per_module[module_name][name] += '\n' + _CRITICAL_HINT

        return strat_prompt_per_module

    def _parse_arch_agent_response(self, response: str) -> Dict[str, Dict[str, str]]:
        """Parse architecture agent response into per-module strategy-prompt map.

        Returns:
            {'module_name': {'strategy_name': 'detailed prompt', ...}}
        """
        module_pattern = r'=== MODULE:\s*(\S+)\s*===\s*\n(.*?)\n=== END MODULE ==='
        strategy_pattern = r'--- STRATEGY:\s*(.+?)\s*---\s*\n(.*?)\n--- END STRATEGY ---'

        result = {}
        for module_name, module_body in re.findall(module_pattern, response, re.DOTALL):
            strategies = {}
            for strat_name, strat_prompt in re.findall(strategy_pattern, module_body, re.DOTALL):
                strategies[strat_name.strip()] = strat_prompt.strip()
            if strategies:
                result[module_name.strip()] = strategies

        return result

    # Keywords that indicate a strategy could benefit from DesignWare retrieval
    _DW_KEYWORDS = frozenset(
        {
            'adder',
            'carry',
            'lookahead',
            'prefix',
            'multiplier',
            'arithmetic',
            'operator',
            'divider',
            'shifter',
        }
    )

    def _augment_with_rag(self, critical_hint: str, original_code: str, strat_name: str) -> str:
        """Conditionally append RAG examples based on strategy relevance.

        DesignWare examples are only retrieved when the strategy name
        contains arithmetic/operator keywords.
        """
        strat_lower = strat_name.lower()
        if self.dw_memory and any(kw in strat_lower for kw in self._DW_KEYWORDS):
            try:
                dw_entries = self.dw_memory.find_for_code(query_code=original_code, n_results=3)
                if dw_entries:
                    parts = [critical_hint, '', 'Open design ware optimized implementations available:']
                    for dw in dw_entries:
                        parts.append(f'When you see this pattern:\n```verilog\n{dw.pattern}\n```')
                        if dw.description:
                            parts.append(f'Reason to replace: {dw.description}')
                        parts.append(f'Use this optimized implementation instead:\n```verilog\n{dw.replacement}\n```')
                        parts.append('')
                    critical_hint = '\n'.join(parts)
                    print(f'      Injected {len(dw_entries)} DesignWare implementation(s) for strategy "{strat_name}"')
            except Exception as e:
                print(f'      Warning: DesignWare lookup failed: {e}')

        return critical_hint

    def _optimize_single_module(
        self,
        opt_llm: LLM_wrap,
        module_name: str,
        original_code: str,
        strategies: Dict[str, str],
    ) -> Dict:
        """Optimize a single module by trying each strategy (1 candidate each).

        For each strategy proposed by the arch agent:
          1. Build prompt with strategy hint + conditional RAG
          2. Generate code candidate via opt_llm
          3. Verify (compile + LEC with fix loops)
        Then evaluate timing on all verified candidates and pick the best.

        Returns:
            {'success': bool, 'code': str, 'reason': str, 'frequency': float}
        """
        print(f'    Optimizing {module_name} ({len(strategies)} strategies)')

        module_dir = self.output_dir / module_name
        module_dir.mkdir(parents=True, exist_ok=True)

        # Elaborate gold design once (for LEC comparisons)
        lec_dir = module_dir / 'lec'
        lec_dir.mkdir(parents=True, exist_ok=True)
        gold_error, gold_elab_path = self._elaborate_design(
            flist_path=Path(self.rtl.manifest_file),
            standalone_files=self.rtl.standalone_files or [],
            elab_top=self.benchmark.top_module,
            synth_top=module_name,
            elab_method=self.tools.elab_method,
            output_dir=lec_dir,
            tag='gold',
        )
        if not gold_elab_path:
            self.error(f'{gold_error}')

        # Try each strategy: generate 1 candidate, verify, collect
        best_candidate = CandidateState()
        improving: List[CandidateState] = []
        for strat_name, strat_prompt in strategies.items():
            print(f'    Strategy: {strat_name}')
            normed_strat = strat_name.replace(' ', '_')
            strat_dir = module_dir / f'{normed_strat}'

            # Fresh session per strategy
            opt_session = LLMSession.create(opt_llm)

            # Build prompt with strategy hint + conditional RAG augmentation
            strategy_hint = self._augment_with_rag(strat_prompt, original_code, strat_name)

            prompt_dict = {
                'module_name': module_name,
                'original_code': original_code,
                'strategy_hint': strategy_hint,
            }

            # Generate strategy candidate
            try:
                responses = opt_session.call_with_history(
                    prompt_dict,
                    'optimize_timing_prompt',
                    n=1,
                    max_history=8,
                )
            except Exception as e:
                print(f'      LLM call failed: {e}')
                continue

            # Pre-check: ensure optimizer response contains valid patch format
            ok_patch, fmt_err = self._ensure_search_replace_patch(
                opt_session,
                code_to_patch=original_code,
                patch=responses[0],
                prompt_dict=prompt_dict,
                prompt_index='optimize_timing_prompt',
                max_format_rounds=2,
            )
            if ok_patch is None:
                print(f'      Strategy "{strat_name}" failed format check: {fmt_err}')
                continue
            response_patch = ok_patch

            # Verify (compile + LEC with fix loops)
            candidate = self._verify_and_fix(
                proposed_patch=response_patch,
                original_code=original_code,
                output_dir=strat_dir,
                module_name=module_name,
                strat_name=strat_name,
                gold_elab_path=gold_elab_path,
            )

            if not candidate.compile_ok or not candidate.lec_ok:
                print(f'      Strategy "{strat_name}" candidate failed verification')
                continue

            candidate_freq = self._evaluate_timing(candidate, module_name, strat_dir)

            if candidate_freq > self.baseline_freq:
                if not best_candidate.frequency:
                    best_candidate = candidate
                    continue

                improving.append(candidate)
                if candidate_freq > best_candidate.frequency:
                    best_candidate = candidate

        if len(improving) > 0:
            self._store_candidates(module_name, improving, module_dir / 'improved_candidates')

        if best_candidate.frequency:
            print(f'    Best candidate: {best_candidate.frequency:.2f} MHz (baseline: {self.baseline_freq:.2f} MHz)')
            return {'success': True, 'code': best_candidate.code, 'frequency': best_candidate.frequency, 'reason': ''}

        print(f'    Warning: No candidate improved frequency for {module_name}')

        return {'success': False, 'code': '', 'reason': 'no improvement after refinement'}

    def _verify_and_fix(
        self,
        proposed_patch: str,
        original_code: str,
        output_dir: Path,
        module_name: str,
        strat_name: str,
        gold_elab_path: Path,
    ) -> CandidateState:
        """
        Verify a proposed strategy patch by checking syntax and logical equivalence,
        with separate fix-agents if either fails.

        Applies `proposed_patch` to `original_code`.
        Syntax checking as phase 1 - fix with syntax-fixer if needed;
        LEC as phase 2 - fix with lec-fixer if needed.

        Each phase uses its own disposable fix-agent, feedback builder, and
        RAG memory to avoid contaminating the optimizer's conversation.
        """
        output_dir.mkdir(parents=True, exist_ok=True)

        # Phase 1: Compile and fix potential issues
        elab_res = self._elab_react(proposed_patch, original_code, module_name, output_dir / 'syntax_check')

        if not elab_res.ok:
            print(f'    {module_name} with strategy {strat_name} failed compilation with {elab_res.error_msg}')

            return CandidateState(
                code=original_code,
                module_name=module_name,
                candidate_strat=strat_name,
                compile_ok=False,
                lec_ok=False,
                gate_elab_path=None,
                attempt_dir=output_dir,
            )

        print('    Compilation success')

        # Phase 2: LEC and fix potential issues
        assert elab_res.patch is not None
        assert elab_res.elab_path is not None
        lec_ok, lec_patch, lec_result = self._lec_react(
            elab_res.patch,
            original_code,
            elab_res.elab_path,
            gold_elab_path,
            module_name,
            output_dir=output_dir / 'lec',
        )

        if lec_ok:
            assert lec_patch is not None
            candidate_code = None
            try:
                candidate_code = self.patch_applier.try_apply(original_code, lec_patch)
            except RuntimeError as e:
                print(f'      Patch application failed: {e}')

            if candidate_code is None:
                print('      Could not apply LEC-validated patch, returning failed candidate')
                return CandidateState(
                    code=original_code,
                    module_name=module_name,
                    candidate_strat=strat_name,
                    compile_ok=True,
                    lec_ok=False,
                    attempt_dir=output_dir,
                )

            return CandidateState(
                code=candidate_code,
                module_name=module_name,
                candidate_strat=strat_name,
                compile_ok=True,
                lec_ok=True,
                gate_elab_path=elab_res.elab_path,
                attempt_dir=output_dir,
            )

        print(f'   LEC failed {lec_result}')
        return CandidateState(
            code=original_code,
            module_name=module_name,
            candidate_strat=strat_name,
            compile_ok=True,
            lec_ok=False,
            attempt_dir=output_dir,
        )

    def _elab_react(
        self,
        proposed_patch: str,
        original_code: str,
        module_name: str,
        output_dir: Path,
    ) -> ElabResult:
        """
        Run the elaboration ReAct loop on a proposed candidate patch;
        fix the proposed patch if it fails to compile.
        Returns:
            (elab_ok, fixed_patch, error_msg, res_elab_path)
        """
        if not self.rtl.manifest_file:
            res = ElabResult(patch=None, elab_path=None, error_msg='No manifest file specified in the input config file')
            res.assert_valid()
            return res

        # The final working patch
        fixed_patch: Optional[str] = None
        # The path that stores the elaboration result of `fixed_patch` applied to `original_code`
        res_elab_path: Optional[Path] = None
        # The error message if the ReAct loop could not elaborate
        error_msg: Optional[str] = None
        # Prepare output directory and SyntaxFixer that will potentially be used
        output_dir.mkdir(parents=True, exist_ok=True)
        fix_session = LLMSession.create(self.syntax_fix_llm)

        num_compile_attempts = (
                    self.thresholds.compile_fix_max 
                    if self.thresholds.compile_fix_max is not None 
                    else 1
                )

        current_patch = proposed_patch
        for i in range(num_compile_attempts):
            print(f'    Compile attempt {i}/{num_compile_attempts}')

            # Format or SEARCH-not-found issue — ask the fix LLM for a corrected patch
            ok_patch, fmt_err = self._ensure_search_replace_patch(
                fix_session,
                code_to_patch=original_code,
                patch=current_patch,
                prompt_dict={
                    'original_code': original_code,
                    'failed_patch': current_patch,
                    'error_feedback': 'The previous response could not be applied as a patch.',
                },
                prompt_index='compile_fix_prompt',
            )
            if ok_patch is None:
                error_msg = fmt_err
                break
            current_patch = ok_patch
            # it's guaranteed to apply successfully
            candidate_code = self.patch_applier.try_apply(
                    original_code, 
                    ok_patch
                )
            assert candidate_code is not None

            # Assume module naming and its file naming are the same
            candidate_module_file = output_dir / f'{module_name}.sv'
            candidate_module_file.write_text(candidate_code)

            curr_attempt_dir = output_dir / f'attempt_{i}'
            # Create gate design's filelist and then elaborate
            try:
                gate_flist = self._create_gate_flist(
                    original_flist=self.rtl.manifest_file,
                    replacements={module_name: candidate_module_file},
                    output_path=curr_attempt_dir / 'gate_flist.f',
                )
            except ValueError as e:
                error_msg = str(e)
                # `break` instead of `continue` because this is not an elab issue anymore
                break

            gate_tag = 'gate'
            elab_error, gate_elab_path = self._elaborate_design(
                flist_path=gate_flist,
                standalone_files=self.rtl.standalone_files or [],
                elab_top=self.benchmark.top_module,
                synth_top=module_name,
                elab_method=self.tools.elab_method,
                output_dir=curr_attempt_dir,
                tag=gate_tag,
            )

            if gate_elab_path:
                res_elab_path = gate_elab_path
                fixed_patch = current_patch
                break

            # Candidate code elab failed, run syntax fixing loop
            feedback = self._build_compile_feedback(
                elab_error,
                elab_log_dir=curr_attempt_dir / gate_tag,
                target_module=module_name,
                memory=self.compile_memory,
                candidate_code=candidate_code,
            )

            prompt_dict = {
                'original_code': original_code,
                'failed_patch': current_patch,
                'error_feedback': feedback,
            }

            try:
                responses = fix_session.call_with_history(
                    prompt_dict, 
                    'compile_fix_prompt', 
                    n=1, 
                    max_history=8
                )
            except Exception as e:
                print(f'      Fix LLM call failed: {e}')
                continue

            if not responses:
                print(f'      Fix LLM returned no response')
                continue
            current_patch = responses[0]

        if fixed_patch is not None:
            res = ElabResult(patch=fixed_patch, elab_path=res_elab_path, error_msg=None)
        else:
            res = ElabResult(
                patch=None,
                elab_path=None,
                error_msg=error_msg or 'Elaboration failed: no successful candidate within attempt budget',
            )

        res.assert_valid()
        return res

    # LEC ReAct loop (miter + SAT)
    def _lec_react(
        self,
        proposed_patch: str,
        original_code: str,
        gate_elab_path: Optional[Path],
        gold_elab_path: Path,
        module_name: str,
        output_dir: Path,
    ) -> Tuple[bool, Optional[str], Optional[str]]:
        """
        Run logical equivalence check ReAct loop on the elaborated result of
        `original_code` patched with `proposed_patch` against
        `gold_elab_path`, use elaborated `gate_elab_path` to
        avoid re-elab in the first run.
        Fix the proposed patch if LEC fails.

        Returns:
            (lec_ok, patch, error_msg)
        """
        # Prepare output directory and SyntaxFixer that will potentially be used
        output_dir.mkdir(parents=True, exist_ok=True)
        fix_session = LLMSession.create(self.lec_fix_llm)

        num_lec_attempts = self.thresholds.lec_fix_max if self.thresholds.lec_fix_max is not None else 1

        current_patch = proposed_patch
        curr_gate_elab_path = gate_elab_path
        for i in range(num_lec_attempts):
            print(f'    LEC attempt {i}/{num_lec_attempts}')

            curr_attempt_dir = output_dir / f'attempt_{i}'
            curr_attempt_dir.mkdir(parents=True, exist_ok=True)

            should_compile = i > 0 or (i == 0 and curr_gate_elab_path is None)
            if should_compile:
                ok_patch, fmt_err = self._ensure_search_replace_patch(
                    fix_session,
                    code_to_patch=original_code,
                    patch=current_patch,
                    prompt_dict={
                        'original_code': original_code,
                        'failed_patch': current_patch,
                        'error_feedback': 'The previous response could not be applied as a patch.',
                    },
                    prompt_index='lec_fix_prompt',
                )
                if ok_patch is None:
                    return (False, None, fmt_err)
                
                current_patch = ok_patch

                elab_res = self._elab_react(
                    current_patch,
                    original_code,
                    module_name, 
                    curr_attempt_dir / 'syntax_check'
                )

                if not elab_res.ok:
                    return (False, None, f'{module_name} failed to compile at LEC attempt {i} with error {elab_res.error_msg}')

                assert elab_res.patch is not None
                assert elab_res.elab_path is not None
                current_patch = elab_res.patch
                curr_gate_elab_path = elab_res.elab_path
            else:
                assert curr_gate_elab_path is not None

            lec_tcl = curr_attempt_dir / 'lec.tcl'
            script = self._build_lec_script(module_name, curr_gate_elab_path, gold_elab_path)

            lec_tcl.write_text(script)

            start_time = time.perf_counter()
            try:
                result = subprocess.run(
                    ['yosys', '-s', str(lec_tcl)],
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    text=True,
                    timeout=120,
                    cwd=str(curr_attempt_dir),
                )
                with open(curr_attempt_dir / 'lec.log', 'w') as f:
                    f.write('==== STDOUT ====\n')
                    f.write(result.stdout)
                    f.write('\n\n==== STDERR ====\n')
                    f.write(result.stderr)
            except subprocess.TimeoutExpired:
                # LEC timed out after 300s (assumed equivalent as it cannot prove not equal)
                end_time = time.perf_counter()
                dur = end_time - start_time
                print(f'    LEC took {dur}')
                return (True, current_patch, None)
            except Exception as e:
                end_time = time.perf_counter()
                dur = end_time - start_time
                print(f'    LEC took {dur}')

                return (False, None, f'{e}')
                
            end_time = time.perf_counter()
            dur = end_time - start_time
            print(f'    LEC took {dur}')

            stdout = result.stdout
            stderr = result.stderr

            if re.search(r'SAT.*PASS', stdout) or re.search(r'proven', stdout, re.IGNORECASE):
                print('    LEC success')
                return (True, current_patch, None)

            if re.search(r'ERROR', stderr):
                error_lines = [ln for ln in stderr.splitlines() if 'ERROR' in ln]
                return (False, None, '\n'.join(error_lines[:10]))

            if i == num_lec_attempts - 1:
                break

            if re.search(r'SAT.*FAIL!', stdout):
                cex = self._parse_counterexample(stdout)
            
            candidate_code = self.patch_applier.try_apply(
                    original_code, 
                    current_patch
                )
            assert candidate_code is not None
            feedback = self._build_lec_feedback(
                stderr,
                cex,
                memory=self.lec_memory,
                candidate_code=candidate_code,
            )

            prompt_dict = {
                'original_code': original_code,
                'failed_patch': current_patch,
                'error_feedback': feedback,
            }

            try:
                responses = fix_session.call_with_history(
                        prompt_dict, 
                        'lec_fix_prompt', 
                        n=1, 
                        max_history=8
                    )
                current_patch = responses[0]
            except Exception as e:
                print(f'      Fix LLM call failed: {e}')
                continue
            
        return (False, None, f'Could not parse LEC result (rc={result.returncode})')

    def _build_lec_script(self, top_module: str, gate_elab_path: Path, gold_elab_path: Path) -> str:
        script = f"""\
read_verilog {gold_elab_path}
prep -top {top_module} -flatten
rename {top_module} gold
design -stash gold

read_verilog {gate_elab_path}
prep -top {top_module} -flatten
rename {top_module} gate
design -stash gate

design -copy-from gold -as gold gold
design -copy-from gate -as gate gate

miter -equiv -flatten -make_outputs -ignore_gold_x gold gate miter
hierarchy -top miter

proc
opt
flatten
async2sync
memory
opt_clean

sat -tempinduct -prove trigger 0 -set-init-undef -enable_undef -set-def-inputs -show-ports miter
"""

        return script

    # Evaluate Timing
    def _evaluate_timing(self, candidate: CandidateState, module_name: str, output_dir: Path) -> float:
        """Run synth + STA on a single verified candidate to measure frequency."""
        print(f'    Evaluating timing for candidate strategy {candidate.candidate_strat}')
        sta_dir = output_dir / 'sta'
        sta_dir.mkdir(parents=True, exist_ok=True)

        candidate_file = sta_dir / f'{module_name}.sv'
        candidate_file.write_text(candidate.code)

        try:
            flist_path = self._create_gate_flist(
                original_flist=self.rtl.manifest_file,
                replacements={module_name: candidate_file},
                output_path=sta_dir / 'candidate_flist.f',
            )
        except ValueError as e:
            print(f'    STA flist error: {e}')
            self.error(f'    STA failed for this candidate: {e}')

        freq = self._run_candidate_synth_sta(flist_path, sta_dir, tag='candidate')
        candidate.frequency = freq
        if freq is not None:
            print(f'    Frequency: {freq:.2f} MHz (vs baseline {self.baseline_freq:.2f} MHz)')
            return freq
        else:
            self.error('    STA failed for this candidate')

    def _run_candidate_synth_sta(
        self,
        flist_path: Path,
        output_dir: Path,
        tag: str,
    ) -> Optional[float]:
        """Run synth + STA using a pre-built flist. Returns frequency_mhz or None."""
        output_dir.mkdir(parents=True, exist_ok=True)

        if not self.rtl.manifest_file:
            print('    Warning: no manifest file, cannot run synth+STA')
            return None

        synth_script = self._find_synth_script()
        cmd = [
            sys.executable, str(synth_script),
            '--dir', str(output_dir),
            '--elab-method', self.tools.elab_method,
            '--top-synthesis', self.benchmark.effective_synth_top,
            '--run-sta',
            '--liberty', self.tools.liberty_file,
            '--tag', tag,
        ]

        if self.benchmark.output_module is not None:
            cmd.extend(['--output-module', self.benchmark.output_module])

        cmd.extend(['--', '--top', self.benchmark.top_module, '--allow-use-before-declare'])

        if self.rtl.standalone_files:
            cmd.extend(self.rtl.standalone_files)

        cmd.extend(['-f', str(flist_path)])

        try:
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=1800)
        except subprocess.TimeoutExpired:
            print('    STA timed out after 1800s')
            return None

        if result.returncode != 0:
            print(f'    STA failed (rc={result.returncode})')
            return None

        # Parse timing report
        sta_report = output_dir / tag / 'sta.log'
        netlist = output_dir / tag / 'synth.v'

        if not sta_report.exists() or not netlist.exists():
            print('    STA output files not found')
            return None

        clock_signal = get_clock_signal(netlist)
        assert clock_signal is not None
        return self._parse_timing_log(sta_report, clock_signal)

    def _parse_timing_log(self, timing_rpt_path: Path, clock_signal: str) -> Optional[float]:
        """Parse timing report for frequency (MHz)."""
        try:
            content = timing_rpt_path.read_text()
            sections = re.split(r'(?=Startpoint:)', content)

            for section in sections:
                if not section.strip():
                    continue
                path_group_match = re.search(r'Path Group:\s*\**(\S+)\**', section)
                if not path_group_match:
                    continue
                if path_group_match.group(1) == clock_signal:
                    arrival_match = re.search(r'([+-]?\d+(?:\.\d+)?)\s+data arrival time\s+', section, re.IGNORECASE)
                    if arrival_match:
                        arrival_time = float(arrival_match.group(1))
                        if arrival_time > 0:
                            return 1000.0 / arrival_time
        except Exception as e:
            print(f'    Warning: Failed to parse timing log: {e}')

        return None

    # Compilation-related (flist + elaboration)
    def _create_gate_flist(
        self,
        original_flist: str,
        replacements: Dict[str, Path],
        output_path: Path,
    ) -> Path:
        """
        Create a modified flist for the gate design.

        Reads the original flist and replaces lines matching module filenames
        with paths to the LLM-generated replacement files.

        Args:
            original_flist: Path to the original flist file.
            replacements: Dict mapping module_name -> replacement file path.
            output_path: Where to write the modified flist.
        """
        flist_path = Path(original_flist)
        lines = flist_path.read_text().splitlines()

        patterns = {name: re.compile(rf'(^|/){re.escape(name)}\.(sv|v)\s*$') for name in replacements}
        match_counts: Dict[str, int] = {name: 0 for name in replacements}

        modified_lines = []

        for line in lines:
            stripped = line.strip()

            if not stripped or stripped.startswith('//'):
                modified_lines.append(line)
                continue

            if stripped.startswith('+incdir+'):
                modified_lines.append(line)
                continue

            if stripped.startswith('-f ') or stripped.startswith('-f\t'):
                modified_lines.append(line)
                continue

            expanded = os.path.expandvars(stripped)
            matched = False
            for name, pattern in patterns.items():
                if pattern.search(expanded):
                    modified_lines.append(str(replacements[name]))
                    match_counts[name] += 1
                    matched = True
                    break
            if not matched:
                modified_lines.append(line)

        for name, count in match_counts.items():
            if count == 0:
                raise ValueError(f'No file matching {name}.(sv|v) found in flist {original_flist}')
            if count > 1:
                raise ValueError(f'Multiple files ({count}) matching {name}.(sv|v) found in flist {original_flist}')

        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text('\n'.join(modified_lines) + '\n')
        return output_path

    def _elaborate_design(
        self,
        flist_path: Path,
        standalone_files: List[str],
        elab_top: str,
        synth_top: str,
        elab_method: str,
        output_dir: Path,
        tag: str,
    ) -> Tuple[str, Optional[Path]]:
        """
        Elaborate a full design and returns error message (if any) and the path to elaborated design.

        Returns:
            (error_message, elab_path)
        """
        synth_script = self._find_synth_script()

        elab_cmd = [
            sys.executable,
            str(synth_script),
            '--dir',
            str(output_dir),
            '--elab-method',
            elab_method,
            '--top-synthesis',
            synth_top,
            '--run-elab',
            '--tag',
            tag,
        ]

        elab_cmd.extend(['--', '--top', elab_top])
        elab_cmd.extend(['--allow-use-before-declare'])

        if standalone_files:
            elab_cmd.extend(standalone_files)

        elab_cmd.extend(['-f', str(flist_path)])

        try:
            result = subprocess.run(elab_cmd, capture_output=True, text=True, timeout=600)
        except subprocess.TimeoutExpired:
            return ('Elaboration timed out after 600s', None)

        elab_path = output_dir / tag / 'elab.v'

        if result.returncode == 0 and elab_path.exists():
            return ('', elab_path)

        raw = result.stderr + result.stdout
        lines = [re.sub(r'\s+', ' ', ln) for ln in raw.splitlines() if ln.strip()]
        error_msg = '\n'.join(lines[:100]) if lines else f'Elaboration failed (rc={result.returncode})'

        return (error_msg, None)

    def _find_synth_script(self) -> Path:
        """Find the synth.py script in the hagent repository."""
        this_file = Path(__file__).resolve()
        hagent_root = this_file.parent.parent.parent.parent.parent
        synth_script = hagent_root / 'scripts' / 'synth.py'

        if synth_script.exists():
            return synth_script

        repo_dir = os.environ.get('HAGENT_ROOT_DIR')
        if repo_dir:
            synth_script = Path(repo_dir) / 'scripts' / 'synth.py'
            if synth_script.exists():
                return synth_script

        self.error('Cannot find scripts/synth.py. Set HAGENT_ROOT_DIR or run from hagent directory.')

    def _resolve_synth_top(self, hierarchy_path: Path, module_name: str) -> str:
        """
        Look up the yosys-internal module name from hierarchy.txt.

        Returns the full yosys name. Raises ValueError if zero or more than one match.
        """
        lines = hierarchy_path.read_text().splitlines()

        module_lines = []
        for line in lines:
            stripped = line.strip()
            if not stripped:
                continue
            if stripped.endswith(':'):
                continue
            module_lines.append(stripped)

        for entry in module_lines:
            if entry == module_name:
                return module_name

        matches = [entry for entry in module_lines if entry.startswith(f'{module_name}$')]

        if len(matches) == 1:
            return f'"{matches[0]}"'
        if len(matches) == 0:
            raise ValueError(f"Module '{module_name}' not found in {hierarchy_path}")
        raise ValueError(f"Multiple matches ({len(matches)}) for '{module_name}' in {hierarchy_path}: " + ', '.join(matches[:5]))

    # Feedback builders
    def _build_compile_feedback(
        self,
        error_msg: str,
        elab_log_dir: Optional[Path] = None,
        target_module: str = '',
        memory: Optional[CompilationFixMemory] = None,
        candidate_code: str = '',
    ) -> str:
        """Build LLM feedback for compilation errors.

        Tries to parse elab.log / elab_sv2v.log via ParseToolResultForLLM for
        structured feedback. Falls back to filtering the raw error_msg.

        Returns:
            feedback_text
        """
        error_summary = None
        error_type = 'unknown'

        if not elab_log_dir:
            self.error('   Cannot find elaboration log directory')
        for log_name in ['elab.log', 'elab_sv2v.log']:
            log_path = elab_log_dir / log_name
            if not log_path.exists():
                breakpoint()
            if log_path.exists():
                parser = get_tool_result_parser(log_path)
                if parser:
                    parser.parse()
                    error_summary = parser.format_for_llm(target_module=target_module)
                    error_type = parser.get_primary_error_type()
                    break

        if not error_summary:
            relevant = []
            for line in error_msg.splitlines():
                lower = line.lower()
                if 'error:' in lower or 'warning' in lower:
                    relevant.append(line.strip())
            error_summary = '\n'.join(relevant[:15]) if relevant else error_msg[:500]

        lines = [
            'The previous optimization failed to compile in the full design context.',
            'Compilation errors:',
            error_summary,
            '',
            'Please fix these compilation errors while maintaining the timing optimization.',
        ]

        # RAG: look up similar past fixes from memory
        if memory and error_type != 'unknown' and candidate_code:
            try:
                examples = memory.find(error_type=error_type, fix_question=candidate_code, n_results=2)
                if examples:
                    lines.append('')
                    lines.append('Here are examples of how similar errors were fixed before:')
                    for i, ex in enumerate(examples):
                        lines.append(f'--- Example {i + 1} ---')
                        q = ex.question[:1000] if len(ex.question) > 1000 else ex.question
                        a = ex.answer[:1000] if len(ex.answer) > 1000 else ex.answer
                        lines.append(f'Broken code snippet:\n{q}')
                        lines.append(f'Fixed code snippet:\n{a}')
            except Exception:
                pass  # Memory lookup is best-effort

        return '\n'.join(lines)

    _SAT_FAIL_MARKER = re.compile(r'SAT.*FAIL!')
    _TRYING_RE = re.compile(r'Trying induction with length\s+(\d+)')

    def _parse_counterexample(self, stdout: str) -> str:
        """Parse yosys SAT counterexample table into LLM-friendly text."""
        lines = stdout.splitlines(True)

        fail_idx = None
        for i, line in enumerate(lines):
            if self._SAT_FAIL_MARKER.search(line):
                fail_idx = i
                break

        if fail_idx is None:
            return ''

        trying_idx = None
        for j in range(fail_idx, -1, -1):
            if self._TRYING_RE.search(lines[j]):
                trying_idx = j
                break

        if trying_idx is None:
            return ''

        relevant_failing_text = lines[trying_idx:]

        lec_result_lines = []
        for line in relevant_failing_text:
            stripped = line.strip()
            if (
                not stripped
                or stripped.startswith('----')
                or stripped.startswith('(')
                or stripped.startswith(')')
                or stripped.startswith('|')
                or stripped.startswith('_')
            ):
                continue

            if stripped.startswith('init'):
                continue

            cleaned = re.sub(r'\s+', ' ', stripped)
            lec_result_lines.append(cleaned)

        if not lec_result_lines:
            return ''

        return ''.join(lec_result_lines)

    def _build_lec_feedback(
        self,
        error: str,
        counterexample: str,
        memory: Optional[CompilationFixMemory] = None,
        candidate_code: str = '',
    ) -> str:
        """Build feedback message for LEC failure, with optional RAG."""
        lines = [
            'The previous optimization failed logical equivalence checking (LEC).',
            'The SAT solver found a counterexample proving the optimized module',
            'produces different outputs than the original for the following input sequence:',
            '',
        ]

        if error:
            lines.append(error)

        if counterexample:
            lines.append(counterexample)

        lines.append('Please fix the logical errors while maintaining the timing optimization intent.')
        lines.append('Ensure the optimized module produces identical outputs for all inputs.')

        # RAG: look up similar past LEC fixes
        if memory and candidate_code:
            try:
                examples = memory.find(error_type='lec_mismatch', fix_question=candidate_code, n_results=2)
                if examples:
                    lines.append('')
                    lines.append('Here are examples of how similar LEC errors were fixed before:')
                    for i, ex in enumerate(examples):
                        lines.append(f'--- Example {i + 1} ---')
                        q = ex.question[:1000] if len(ex.question) > 1000 else ex.question
                        a = ex.answer[:1000] if len(ex.answer) > 1000 else ex.answer
                        lines.append(f'Broken code snippet:\n{q}')
                        lines.append(f'Fixed code snippet:\n{a}')
            except Exception:
                pass  # Memory lookup is best-effort

        return '\n'.join(lines)

    # Helpers
    def _ensure_search_replace_patch(
        self,
        session,
        *,
        code_to_patch: str,
        patch: str,
        prompt_dict: Dict,
        prompt_index: str,
        max_format_rounds: int = 3,
    ) -> Tuple[Optional[str], Optional[str]]:
        """Validate that *patch* parses and applies to *code_to_patch*.

        On failure, diagnoses the format issue via
        ``VerilogPatchApplier.diagnose_format``, injects feedback into the
        *session* history, and retries up to *max_format_rounds* times.

        Args:
            session: LLMSession to use for retries.
            code_to_patch: The code the patch should apply to.
            patch: The potentially failing patch that the LLM produces.
            prompt_dict: Template variables for the retry call.
            prompt_index: Prompt template name for the retry call.
            max_format_rounds: Max retry attempts for format issues.

        Returns:
            ``(ok_patch, None)`` on success, or ``(None, error_msg)`` on failure.
        """
        for r in range(max_format_rounds):
            apply_err: Optional[str] = None
            try:
                applied = self.patch_applier.try_apply(
                        code_to_patch, 
                        patch
                    )
            except RuntimeError as e:
                applied = None
                apply_err = str(e)
            except Exception as e:
                applied = None
                apply_err = str(e)

            if applied is not None:
                # successfully applied, meaning the patch is valid
                return patch, None

            if r == max_format_rounds - 1:
                break

            # Build feedback using diagnose_format for specific diagnostics
            diag = self.patch_applier.diagnose_format(patch)
            feedback = apply_err or diag or 'Response contained no search-and-replace patch blocks.'
            feedback += '\n' + PATCH_FORMAT_CONTRACT

            print(f'      Patch format/apply issue (round {r + 1}/{max_format_rounds}): {feedback}')
            prompt_dict['error_feedback'] = feedback
            prompt_dict['failed_patch'] = patch
            try:
                responses = session.call_with_history(
                        prompt_dict, 
                        prompt_index, 
                        n=1, 
                        max_history=8
                    )
                if not responses:
                    print(f'      Format LLM returned no response')
                    continue
                # potentially failing patch
                patch = responses[0]
            except Exception as e:
                print(f'      Format fix LLM call failed: {e}')
                break

        return None, 'Could not obtain a valid SEARCH/REPLACE patch within format-fix rounds'

    def _init_rag_db(self):
        """Initialize RAG memory databases for:
        - Verilog compilation fixes;
        - Logical equivalence check fixes;
        - Optimization technique examples;
        - Open design ware for faster implementation.
        """
        try:
            db_path = str(self.storage.memory_db_dir)
            self.compile_memory = CompilationFixMemory(db_path=db_path, learn=True)
            # TODO: how to do LEC memory is still unclear, bottlenecked by
            # how to best present and interpret LEC's result to agents
            self.lec_memory = CompilationFixMemory(db_path=db_path, learn=False)
            self.opt_memory = OptimizationMemory(db_path=db_path, learn=False)
        except Exception as e:
            print(f'  Warning: Memory init failed (will proceed without): {e}')
            self.compile_memory = None
            self.lec_memory = None
            self.opt_memory = None

        # Open design ware memory — load from YAML catalog on first use
        try:
            self.dw_memory = DesignWareMemory(db_path=db_path, learn=True)
            if self.tools.open_ware_path is None:
                if self.dw_memory.collection.count() == 0:
                    print('  Warning: DesignWare memory is empty and external resource is not provided')
                return
            open_ware_path = Path(self.tools.open_ware_path)
            if not open_ware_path.exists():
                print(f'  Warning: DesignWare catalog not found at {open_ware_path}')
            import yaml

            with open(open_ware_path) as f:
                open_ware = yaml.safe_load(f)
            count = 0
            for entry in open_ware.get('designware', []):
                pattern = entry.get('pattern', '')
                replacement = entry.get('replacement', '')
                if pattern and replacement:
                    if self.dw_memory.add(
                        category=entry.get('category', ''),
                        pattern=pattern,
                        replacement=replacement,
                        description=entry.get('description', ''),
                    ):
                        count += 1
            print(f'  Loaded DesignWare memory with {count} entries from catalog')
        except Exception as e:
            print(f'  Warning: DesignWare memory init failed (will proceed without): {e}')
            self.dw_memory = None

    def _pick_improving(self, candidates: List[CandidateState]) -> List[CandidateState]:
        """Filter candidates that improved over baseline frequency."""
        return [v for v in candidates if v.frequency is not None and v.frequency > self.baseline_freq]

    def _store_candidates(self, module_name: str, candidates: List[CandidateState], output_dir: Path):
        """Store all improving candidates to disk for reference."""
        output_dir.mkdir(parents=True, exist_ok=True)
        for v in candidates:
            path = output_dir / f'{module_name}_{v.candidate_strat}.sv'
            path.write_text(v.code)

    def _store_compile_fix(self, error_type: str, broken_code: str, fixed_code: str):
        """Store a successful compilation fix in RAG memory."""
        if self.compile_memory and error_type != 'unknown':
            try:
                fix = Memory_shot(question=broken_code, answer=fixed_code)
                self.compile_memory.add(error_type=error_type, fix=fix)
                print(f'      Stored compile fix in memory (error_type={error_type})')
            except Exception as e:
                print(f'      Warning: Failed to store compile fix: {e}')

    def _store_lec_fix(self, broken_code: str, fixed_code: str):
        """Store a successful LEC fix in RAG memory."""
        if self.lec_memory:
            try:
                fix = Memory_shot(question=broken_code, answer=fixed_code)
                self.lec_memory.add(error_type='lec_mismatch', fix=fix)
                print('      Stored LEC fix in memory')
            except Exception as e:
                print(f'      Warning: Failed to store LEC fix: {e}')

    def _read_module_code(self, rtl_dir: str, module_name: str) -> str:
        """Read RTL code for a module from the critical modules directory."""
        rtl_path = Path(rtl_dir)

        if not (rtl_path.is_dir()):
            raise NotADirectoryError(f'{rtl_dir} is not a directory')

        candidates = [
            rtl_path / f'{module_name}.sv',
            rtl_path / f'{module_name}.v',
            rtl_path / f'{module_name.lower()}.sv',
            rtl_path / f'{module_name.lower()}.v',
        ]

        for path in candidates:
            if path.exists():
                return path.read_text()

        raise FileNotFoundError(f'No RTL file found for module: {module_name} in {rtl_dir}')


if __name__ == '__main__':
    step = LLMOptimizeWithLECStep()
    step.parse_arguments()
    step.setup()
    step.step()
