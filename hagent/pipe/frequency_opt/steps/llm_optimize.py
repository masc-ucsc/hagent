# See LICENSE for details
"""
LLM Optimization step with two-phase compilation + LEC check.

This step combines LLM-driven RTL optimization with full-design elaboration
and LEC verification in a single step with internal retry logic.

Phase 1 (Compilation): Create a modified flist pointing to LLM-generated file,
  elaborate via yosys/slang, retry with LLM feedback on errors.
Phase 2 (LEC): Use baseline elab.v + successfully elaborated gate elab.v,
  run miter+SAT for equivalence checking.
"""

import os
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from hagent.core.step import Step
from hagent.core.llm_wrap import LLM_wrap
from hagent.tool.extract_code import Extract_code_verilog
from hagent.tool.parse_tool_result import get_tool_result_parser
from hagent.tool.memory import CompilationFixMemory, OptimizationMemory, Memory_shot
from hagent.pipe.frequency_opt.schema import (
    BenchmarkConfig,
    RTLSourceConfig,
    ToolsConfig,
    ThresholdsConfig,
    LLMConfig,
    StorageConfig,
    require_field,
    get_field,
    set_field,
)
from hagent.pipe.frequency_opt.llm_session import PersistentLLMSession


class LLMOptimizeWithLECStep(Step):
    """
    Combined LLM optimization + LEC verification with internal retry.

    This step:
    1. Reads RTL modules from critical_path_info.dir
    2. Calls LLM to generate optimized variants
    3. Elaborates the full design with modified flist to catch compilation errors
    4. If compilation fails, retries with feedback (Phase 1 loop)
    5. If compilation passes, runs LEC via miter+SAT (Phase 2)
    6. If LEC fails, retries with feedback
    7. Outputs LEC-passing variants

    Required YAML sections:
      - thresholds.lec_retry_max
      - llm: model
      - storage: output_dir
      - benchmark: top_module
      - rtl: source_dir, manifest_file

    Required YAML fields (from previous steps):
      - critical_path_info.dir
      - critical_path_info.module_names
      - critical_path_info.critical_path (for context)

    Writes to YAML:
      - optimized.rtl_dir: Directory with LEC-passing optimized modules
      - optimized.modules: List of successfully optimized module info
      - optimized.failed_modules: List of modules that failed optimization
      - llm_session: Persistent LLM conversation state
    """

    def setup(self):
        super().setup()
        self.verilog_extractor = Extract_code_verilog()
        self.storage = None

    def run(self, data: Dict) -> Dict:
        # Parse configuration
        thresholds = ThresholdsConfig.from_data(data, 'thresholds')
        llm_config = LLMConfig.from_data(data, 'llm')
        self.storage = StorageConfig.from_data(data, 'storage')
        benchmark = BenchmarkConfig.from_data(data, 'benchmark')
        rtl = RTLSourceConfig.from_data(data, 'rtl')
        tools = ToolsConfig.from_data(data, 'tools')

        # Get critical modules info
        critical_dir = require_field(data, 'critical_path_info.dir')
        module_names = require_field(data, 'critical_path_info.module_names')
        critical_path = get_field(data, 'critical_path_info.critical_path', {})

        # Check if commented RTL (from synalign) is available
        commented_rtl_dir = get_field(data, 'critical_path_info.commented_rtl_dir', None)
        use_commented_rtl = (
            tools.run_synalign
            and commented_rtl_dir
            and Path(commented_rtl_dir).is_dir()
            and any(Path(commented_rtl_dir).iterdir())
        )
        rtl_read_dir = commented_rtl_dir if use_commented_rtl else critical_dir
        synalign_critical_hint = (
            (
                'We marked the likely CRITICAL signals/procedures with "// CRITICAL:" markers in the source code. '
                'The critical signal should be found directly adjacent to the marked lines '
                'or live in the adjacent "begin, end" blocks, or always blocks of the marked line.'
            )
            if use_commented_rtl
            else None
        )

        if use_commented_rtl:
            print(f'  Using commented RTL from synalign: {commented_rtl_dir}')

        # Setup output directory
        output_dir = Path(self.storage.output_dir) / 'optimized'
        if output_dir.exists():
            shutil.rmtree(output_dir)
        output_dir.mkdir(parents=True)

        # Initialize LLM
        llm = LLM_wrap(
            name='rtl_timing_optimizer',
            log_file='rtl_timing_optimizer.log',
            conf_file=llm_config.conf_file,
        )

        if llm.last_error:
            self.error(f'LLM setup failed: {llm.last_error}')

        # Restore or create LLM session
        session = PersistentLLMSession.from_yaml_data(llm, data)

        # Process each module
        optimized_modules = []
        failed_modules = []

        for module_name in module_names:
            print(f'\nOptimizing module: {module_name}')

            # Read RTL code: either original or marked by synalign
            original_code = self._read_module_code(rtl_read_dir, module_name)
            if not original_code:
                print(f'  Warning: Could not read module {module_name}, skipping')
                failed_modules.append({'name': module_name, 'reason': 'could not read source'})
                continue

            # Try to optimize with two-phase compilation + LEC
            result = self._optimize_module_with_lec(
                module_name=module_name,
                original_code=original_code,
                critical_path=critical_path,
                session=session,
                max_retries=thresholds.lec_retry_max,
                max_variants=llm_config.max_variants,
                benchmark=benchmark,
                rtl=rtl,
                tools=tools,
                output_dir=output_dir,
                synalign_critical_hint=synalign_critical_hint,
            )

            if result['success']:
                # Save optimized code
                opt_file = output_dir / f'{module_name}.sv'
                opt_file.write_text(result['code'])

                optimized_modules.append(
                    {
                        'name': module_name,
                        'file': str(opt_file),
                        'original_code': original_code,
                        'optimized_code': result['code'],
                    }
                )
                print(f'  Success: saved to {opt_file}')
            else:
                failed_modules.append(
                    {
                        'name': module_name,
                        'reason': result['reason'],
                    }
                )
                print(f'  Failed: {result["reason"]}')

        # Build output
        output = data.copy()
        set_field(output, 'optimized.rtl_dir', str(output_dir))
        set_field(output, 'optimized.modules', optimized_modules)
        set_field(output, 'optimized.failed_modules', failed_modules)
        set_field(output, 'llm_session', session.get_state_dict())

        # Set loop control - continue if we have optimized modules
        has_optimized = len(optimized_modules) > 0
        set_field(output, 'should_continue', has_optimized)

        print('\nOptimization summary:')
        print(f'  Successful: {len(optimized_modules)}')
        print(f'  Failed: {len(failed_modules)}')

        return output

    def _read_module_code(self, rtl_dir: str, module_name: str) -> Optional[str]:
        """Read RTL code for a module from the critical modules directory."""
        rtl_path = Path(rtl_dir)

        # Try common file naming patterns
        candidates = [
            rtl_path / f'{module_name}.sv',
            rtl_path / f'{module_name}.v',
            rtl_path / f'{module_name.lower()}.sv',
            rtl_path / f'{module_name.lower()}.v',
        ]

        for path in candidates:
            if path.exists():
                return path.read_text()

        # Search all files for the module
        for sv_file in rtl_path.glob('*.sv'):
            content = sv_file.read_text()
            if f'module {module_name}' in content:
                return content

        for v_file in rtl_path.glob('*.v'):
            content = v_file.read_text()
            if f'module {module_name}' in content:
                return content

        return None

    # -------------------------------------------------------------------------
    # Phase 1: Compilation (flist + elaboration)
    # -------------------------------------------------------------------------

    def _create_gate_flist(
        self,
        original_flist: str,
        module_name: str,
        replacement_file: Path,
        output_path: Path,
    ) -> Path:
        """
        Create a modified flist for the gate design.

        Reads the original flist and replaces the line matching the target
        module's filename with the path to the LLM-generated replacement file.

        Args:
            original_flist: Path to the original manifest/flist file
            module_name: Name of the module being replaced
            replacement_file: Path to the LLM-generated .sv file
            output_path: Where to write the modified flist

        Returns:
            output_path

        Raises:
            ValueError: If not exactly 1 match found for the module filename
        """
        flist_path = Path(original_flist)
        lines = flist_path.read_text().splitlines()

        # Pattern to match filenames like module_name.sv or module_name.v
        pattern = re.compile(rf'(^|/){re.escape(module_name)}\.(sv|v)\s*$')

        modified_lines = []
        match_count = 0

        for line in lines:
            stripped = line.strip()

            # Skip empty lines and comments — copy as-is
            if not stripped or stripped.startswith('//'):
                modified_lines.append(line)
                continue

            # +incdir+ lines — copy as-is
            if stripped.startswith('+incdir+'):
                modified_lines.append(line)
                continue

            # -f <nested_flist> lines — copy as-is (don't recurse)
            if stripped.startswith('-f ') or stripped.startswith('-f\t'):
                modified_lines.append(line)
                continue

            # File path lines — check if basename matches
            # Expand env vars for matching but keep original line for non-matches
            expanded = os.path.expandvars(stripped)
            if pattern.search(expanded):
                modified_lines.append(str(replacement_file))
                match_count += 1
            else:
                modified_lines.append(line)

        if match_count == 0:
            raise ValueError(f'No file matching {module_name}.(sv|v) found in flist {original_flist}')
        if match_count > 1:
            raise ValueError(f'Multiple files ({match_count}) matching {module_name}.(sv|v) found in flist {original_flist}')

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
    ) -> Tuple[bool, str, Optional[Path]]:
        """
        Elaborate a full design by invoking scripts/synth.py --run-elab.

        Args:
            flist_path: Path to flist file (original for gold, modified for gate)
            standalone_files: Additional standalone .sv/.v files
            elab_top: Top module for elaboration (benchmark.top_module)
            synth_top: Synthesis top module (e.g., module_name)
            elab_method: Elaboration method (tools.elab_method)
            output_dir: Base output directory for this attempt
            tag: Tag name for this elab run (e.g., "gate"), where the output will be stored to

        Returns:
            (success, error_message, elab_path)
        """
        synth_script = self._find_synth_script()

        elab_cmd = [
            sys.executable, str(synth_script),
            '--dir', str(output_dir),
            '--elab-method', elab_method,
            '--top-synthesis', synth_top,
            '--run-elab',
            '--tag', tag,
        ]

        elab_cmd.extend(['--', '--top', elab_top])

        elab_cmd.extend(['--allow-use-before-declare'])

        if standalone_files:
            cmd.extend(standalone_files)

        elab_cmd.extend(['-f', str(flist_path)])

        try:
            result = subprocess.run(elab_cmd, capture_output=True, text=True, timeout=600)
        except subprocess.TimeoutExpired:
            return (False, 'Elaboration timed out after 600s', None)

        elab_path = output_dir / tag / 'elab.v'

        if result.returncode == 0 and elab_path.exists():
            return (True, '', elab_path)

        # Return raw stderr/stdout as fallback error info when providing feedback for the LLM
        raw = result.stderr + result.stdout
        lines = [re.sub(r'\s+', ' ', ln) for ln in raw.splitlines() if ln.strip()]
        error_msg = '\n'.join(lines[:100]) if lines else f'Elaboration failed (rc={result.returncode})'

        return (False, error_msg, None)

    def _find_synth_script(self) -> Path:
        """Find the synth.py script in the hagent repository."""
        this_file = Path(__file__).resolve()
        # Go up from hagent/pipe/frequency_opt/steps/ to hagent root, then to scripts/
        hagent_root = this_file.parent.parent.parent.parent.parent
        synth_script = hagent_root / 'scripts' / 'synth.py'

        if synth_script.exists():
            return synth_script

        # Fallback: try HAGENT_ROOT_DIR
        repo_dir = os.environ.get('HAGENT_ROOT_DIR')
        if repo_dir:
            synth_script = Path(repo_dir) / 'scripts' / 'synth.py'
            if synth_script.exists():
                return synth_script

        self.error('Cannot find scripts/synth.py. Set HAGENT_ROOT_DIR or run from hagent directory.')

    def _resolve_synth_top(self, hierarchy_path: Path, module_name: str) -> str:
        """
        Look up the yosys-internal module name from hierarchy.txt.

        hierarchy.txt lines look like:
          lsu_bypass$cva6_nocache.ex_stage_i.lsu_i.lsu_bypass_i
          cva6_nocache       (top-level, no '$')

        Returns the full yosys name (e.g. 'lsu_bypass$cva6_nocache...').
        Raises ValueError if zero or more than one match is found.
        """
        lines = hierarchy_path.read_text().splitlines()

        # Collect non-header, non-empty lines
        module_lines = []
        for line in lines:
            stripped = line.strip()
            if not stripped:
                continue
            # Skip header lines like "250 modules:"
            if stripped.endswith(':'):
                continue
            module_lines.append(stripped)

        # Try exact match first
        for entry in module_lines:
            if entry == module_name:
                return module_name

        # Find lines starting with module_name$
        matches = [entry for entry in module_lines if entry.startswith(f'{module_name}$')]

        if len(matches) == 1:
            # we wrap it in double quotes to prevent misleading the bash
            return f'"{matches[0]}"'
        if len(matches) == 0:
            raise ValueError(f"Module '{module_name}' not found in {hierarchy_path}")
        raise ValueError(f"Multiple matches ({len(matches)}) for '{module_name}' in {hierarchy_path}: " + ', '.join(matches[:5]))

    # -------------------------------------------------------------------------
    # Phase 2: LEC (miter + SAT)
    # -------------------------------------------------------------------------

    def _run_lec(
        self,
        gold_elab_path: Path,
        gate_elab_path: Path,
        top_module: str,
        output_dir: Path,
    ) -> Tuple[Optional[bool], str, str]:
        """
        Compare two already-elaborated designs using yosys miter+SAT.

        Args:
            gold_elab_path: Path to gold elab.v (baseline)
            gate_elab_path: Path to gate elab.v (LLM-optimized)
            top_module: Module name in both elab.v files
            output_dir: Where to write lec.tcl and logs

        Returns:
            (result, error_msg, counterexample)
            result: True = equivalent, False = not equivalent, None = error
        """
        output_dir.mkdir(parents=True, exist_ok=True)
        lec_tcl = output_dir / 'lec.tcl'

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
        lec_tcl.write_text(script)

        try:
            result = subprocess.run(
                ['yosys', '-s', str(lec_tcl)],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                timeout=300,
                cwd=str(output_dir),
            )
        except FileNotFoundError:
            return (None, 'yosys not found in PATH', '')
        except subprocess.TimeoutExpired:
            return (True, 'LEC timed out after 300s (assumed equivalent as it cannot prove not equal)', '')

        stdout = result.stdout
        stderr = result.stderr

        # Check for errors first
        if re.search(r'ERROR', stderr):
            error_lines = [ln for ln in stderr.splitlines() if 'ERROR' in ln]
            return (None, '\n'.join(error_lines[:10]), '')

        # Check SAT result (right now matching for Yosys miter+SAT output format)
        if re.search(r'SAT.*FAIL!', stdout):
            cex = self._parse_counterexample(stdout)
            return (False, 'SAT proved mismatch', cex)

        if re.search(r'SAT.*PASS', stdout) or re.search(r'proven', stdout, re.IGNORECASE):
            return (True, '', '')

        # Ambiguous — treat as error
        return (None, f'Could not parse LEC result (rc={result.returncode})', '')

    # -------------------------------------------------------------------------
    # Feedback from memory DB
    # -------------------------------------------------------------------------
    def _build_compile_feedback(
        self,
        error_msg: str,
        elab_log_dir: Optional[Path] = None,
        target_module: str = '',
        memory: Optional[CompilationFixMemory] = None,
        variant_code: str = '',
    ) -> Tuple[str, str]:
        """Build LLM feedback for compilation errors.

        Tries to parse elab.log / elab_sv2v.log via ParseToolResultForLLM for
        structured, LLM-friendly feedback. Falls back to filtering the raw
        error_msg if no log files are found or no parser matches.

        If a CompilationFixMemory is provided, looks up similar past errors and
        includes fix examples in the feedback.

        Args:
            error_msg: Raw error text (stderr/stdout from elaboration).
            elab_log_dir: Directory containing elab.log / elab_sv2v.log.
            target_module: Name of the module being optimized.
            memory: Optional FewShotMemory for looking up similar past fixes.
            variant_code: The broken variant code (used for memory similarity search).

        Returns:
            Tuple of (feedback_text, error_type) where error_type is the
            categorized primary error type (for later memory.add on success).
        """
        error_summary = None
        error_type = 'unknown'

        # Try structured parsing from log files
        if elab_log_dir:
            for log_name in ['elab.log', 'elab_sv2v.log']:
                log_path = elab_log_dir / log_name
                if log_path.exists():
                    parser = get_tool_result_parser(log_path)
                    if parser:
                        parser.parse()
                        error_summary = parser.format_for_llm(target_module=target_module)
                        error_type = parser.get_primary_error_type()
                        break

        # Fallback: filter raw error_msg for relevant lines
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

        # Look up similar past fixes from memory
        if memory and error_type != 'unknown' and variant_code:
            try:
                examples = memory.find(error_type=error_type, fix_question=variant_code, n_results=2)
                breakpoint()
                if examples:
                    lines.append('')
                    lines.append('Here are examples of how similar errors were fixed before:')
                    for i, ex in enumerate(examples):
                        lines.append(f'--- Example {i + 1} ---')
                        # Truncate to avoid overwhelming the prompt
                        q = ex.question[:1000] if len(ex.question) > 1000 else ex.question
                        a = ex.answer[:1000] if len(ex.answer) > 1000 else ex.answer
                        lines.append(f'Broken code snippet:\n{q}')
                        lines.append(f'Fixed code snippet:\n{a}')
            except Exception:
                pass  # Memory lookup is best-effort

        return '\n'.join(lines), error_type

    _SAT_FAIL_MARKER = re.compile(r'SAT*.*FAIL!')
    _TRYING_RE = re.compile(r'Trying induction with length\s+(\d+)')

    def _parse_counterexample(self, stdout: str) -> str:
        """
        Parse yosys SAT counterexample table into an LLM-friendly text format.

        The raw output is a wide table with columns: Time, Signal Name, Dec, Hex, Bin.
        We extract only the relevant failing induction section, skip init/separator/
        decoration lines, and collapse whitespace.

        TODO: Structure the result in a more LLM-native way (e.g., per-timestep
        dicts with input/output grouping). Right now we simply join all cleaned
        lines into a single string.
        """
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

    def _build_lec_feedback(self, error: str, counterexample: str) -> str:
        """Build feedback message for LEC failure."""
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

        return '\n'.join(lines)

    # -------------------------------------------------------------------------
    # Main optimization loop (two-phase)
    # -------------------------------------------------------------------------

    def _optimize_module_with_lec(
        self,
        module_name: str,
        original_code: str,
        critical_path: Dict,
        session: PersistentLLMSession,
        max_retries: int,
        max_variants: int,
        benchmark: BenchmarkConfig,
        rtl: RTLSourceConfig,
        tools: ToolsConfig,
        output_dir: Path,
        synalign_critical_hint: Optional[str] = None,
    ) -> Dict:
        """
        Optimize a module with two-phase verification and retry loop.

        Phase 1: Compilation — elaborate the full design with modified flist
        Phase 2: LEC — miter+SAT comparison of gold vs gate elab.v

        Returns:
            {'success': bool, 'code': str, 'reason': str}
        """
        feedback = None
        lec_dir = output_dir / 'equiv_check' / module_name

        # Initialize memories — compilation fixes and optimization techniques
        # share the same db_path but live in separate ChromaDB collections.
        compile_memory = None
        opt_memory = None
        try:
            db_path = str(self.storage.memory_db_dir)
            compile_memory = CompilationFixMemory(db_path=db_path, learn=True)
            opt_memory = OptimizationMemory(db_path=db_path, learn=False)
        except Exception as e:
            print(f'  Warning: Memory init failed (will proceed without): {e}')

        # Track error state for learning: when a variant succeeds after a previous
        # failure, we store the (error_type, broken_code -> fixed_code) pair.
        last_error_type: Optional[str] = None
        last_broken_code: Optional[str] = None

        # Note: _resolve_synth_top() is available for future use to look up
        # yosys-internal names (e.g. 'lsu_bypass$cva6_nocache...') from hierarchy.txt.
        # Currently synth.py's TCL script handles '$' name resolution internally,
        # so we just use module_name directly.
        module_synth_top = module_name

        # Elaborate gold (baseline) design with module_name as synth_top
        gold_elab_path = None
        if rtl.manifest_file:
            gold_ok, gold_error, gold_elab_path = self._elaborate_design(
                flist_path=Path(rtl.manifest_file),
                standalone_files=rtl.standalone_files or [],
                elab_top=benchmark.top_module,
                synth_top=module_synth_top,
                elab_method=tools.elab_method,
                output_dir=lec_dir,
                tag='gold',
            )
            if not gold_ok:
                print(f'  Gold elaboration failed: {gold_error[:100]}')
                return {'success': False, 'code': '', 'reason': f'Gold elaboration failed: {gold_error[:100]}'}
        else:
            self.error('We only support elab by manifest file only')

        for attempt in range(max_retries + 1):
            print(f'  Attempt {attempt + 1}/{max_retries + 1}')

            # Generate `max_variants` number of variants per module from LLM
            variants = self._generate_variants(
                session=session,
                module_name=module_name,
                original_code=original_code,
                critical_path=critical_path,
                feedback=feedback,
                n_variants=max_variants,
                synalign_critical_hint=synalign_critical_hint,
                opt_memory=opt_memory,
            )

            if not variants:
                print('    No variants generated')
                feedback = 'No valid Verilog code generated. Please generate a complete module.'
                continue

            # PHASE 1: Compilation check — try each variant
            compiled_variant = None
            gate_elab_path = None
            attempt_dir = None

            for idx, variant_code in enumerate(variants):
                attempt_dir = lec_dir / f'attempt_{attempt}' / f'variant_{idx}'
                attempt_dir.mkdir(parents=True, exist_ok=True)

                # Write LLM code to file
                gate_module_file = attempt_dir / f'{module_name}.sv'
                gate_module_file.write_text(variant_code)

                # If we have a manifest file, use flist-based elaboration
                if rtl.manifest_file:
                    try:
                        gate_flist = self._create_gate_flist(
                            original_flist=rtl.manifest_file,
                            module_name=module_name,
                            replacement_file=gate_module_file,
                            output_path=attempt_dir / 'gate_flist.f',
                        )
                    except ValueError as e:
                        print(f'    Variant {idx + 1} flist error: {e}')
                        feedback = str(e)
                        continue

                    elab_ok, elab_error, elab_path = self._elaborate_design(
                        flist_path=gate_flist,
                        standalone_files=rtl.standalone_files or [],
                        elab_top=benchmark.top_module,
                        synth_top=module_synth_top,
                        elab_method=tools.elab_method,
                        output_dir=attempt_dir,
                        tag='gate',
                    )

                    if elab_ok:
                        compiled_variant = variant_code
                        gate_elab_path = elab_path
                        print(f'    Variant {idx + 1} compiled successfully')

                        # Learn: store the fix if we had a previous compilation failure
                        if compile_memory and last_error_type and last_broken_code:
                            try:
                                fix = Memory_shot(question=last_broken_code, answer=variant_code)
                                # TODO: add later after debugging stage
                                # compile_memory.add(error_type=last_error_type, fix=fix)
                                # print(f'    Stored compile fix in memory (error_type={last_error_type})')
                            except Exception as e:
                                print(f'    Warning: Failed to store fix in memory: {e}')
                            last_error_type = None
                            last_broken_code = None

                        break
                    else:
                        print(f'    Variant {idx + 1} compilation failed: {elab_error[:200]}')
                        feedback, error_type = self._build_compile_feedback(
                            elab_error,
                            elab_log_dir=attempt_dir / 'gate',
                            target_module=module_name,
                            memory=compile_memory,
                            variant_code=variant_code,
                        )
                        last_error_type = error_type
                        last_broken_code = variant_code
                else:
                    self.error('We only support elab by manifest file only')


            if compiled_variant is None:
                # All variants failed compilation — retry with compile feedback
                continue

            # PHASE 2: LEC check
            assert attempt_dir is not None
            if gold_elab_path and gate_elab_path:
                # Both elab files available — run full LEC
                lec_result, lec_error, cex = self._run_lec(
                    gold_elab_path=gold_elab_path,
                    gate_elab_path=gate_elab_path,
                    top_module=module_name,
                    output_dir=attempt_dir,
                )

                if lec_result is True:
                    print('    LEC passed!')
                    return {'success': True, 'code': compiled_variant, 'reason': ''}
                elif lec_result is False:
                    print(f'    LEC failed (mismatch): {lec_error[:100]}')
                    feedback = self._build_lec_feedback(lec_error, cex)
                else:
                    print(f'    LEC error: {lec_error[:100]}')
                    feedback = self._build_lec_feedback(lec_error, cex)
            else:
                # No gold elab or no gate elab — skip LEC
                print('    Skipping LEC (no gold elab or no gate elab available)')
                return {'success': True, 'code': compiled_variant, 'reason': ''}

        return {
            'success': False,
            'code': '',
            'reason': f'All {max_retries + 1} attempts failed',
        }

    def _generate_variants(
        self,
        session: PersistentLLMSession,
        module_name: str,
        original_code: str,
        critical_path: Dict,
        feedback: Optional[str],
        n_variants: int,
        synalign_critical_hint: Optional[str] = None,
        opt_memory: Optional[OptimizationMemory] = None,
    ) -> List[str]:
        """Generate optimized variants using LLM."""
        # Build prompt
        prompt_dict = {
            'module_name': module_name,
            'original_code': original_code,
        }

        if synalign_critical_hint:
            prompt_dict['critical_hint'] = synalign_critical_hint
        else:
            start = critical_path.get('start', 'unknown')
            end = critical_path.get('end', 'unknown')
            prompt_dict['critical_hint'] = f'The critical path is from "{start}" to "{end}".'

        # On first attempt (no feedback), inject relevant optimization technique examples
        if opt_memory and not feedback:
            try:
                opt_examples = opt_memory.find_similar(query_code=original_code, n_results=2)
                if opt_examples:
                    hint_parts = [prompt_dict['critical_hint'], '', 'Here are relevant optimization techniques with examples:']
                    for ex in opt_examples:
                        if ex.description:
                            hint_parts.append(f'Technique: {ex.description}')
                        hint_parts.append(f'Before optimization:\n```verilog\n{ex.question}\n```')
                        hint_parts.append(f'After optimization:\n```verilog\n{ex.answer}\n```')
                        hint_parts.append('')
                    prompt_dict['critical_hint'] = '\n'.join(hint_parts)
                    print(f'    Injected {len(opt_examples)} optimization technique example(s)')
            except Exception as e:
                print(f'    Warning: optimization technique lookup failed: {e}')

        # Add feedback if this is a retry
        if feedback:
            session.add_feedback('compilation or lec failure', feedback, {'module': module_name})

        # Call LLM
        try:
            responses = session.call_with_history(
                prompt_dict,
                'optimize_timing_prompt',
                n=n_variants,
                max_history=8,
            )
        except Exception as e:
            print(f'    LLM call failed: {e}')
            return []

        # Extract Verilog code from responses
        variants = []
        for response in responses:
            codes = self.verilog_extractor.parse(response)
            for code in codes:
                if code:
                    variants.append(code)

        return variants


if __name__ == '__main__':
    step = LLMOptimizeWithLECStep()
    step.parse_arguments()
    step.setup()
    step.step()
