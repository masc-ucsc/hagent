# See LICENSE for details

"""ArchAgent step: proposes RTL optimization strategies for critical-path modules.

Sits in the outer frequency optimization Workflow cycle:
  SynthSTA → Locator → **ArchAgent** → ModuleOptDispatcher → Evaluate → cycle back

Uses ReactLoop for format-retry on MODULE/STRATEGY block parsing.
Fresh Conversation per iteration to avoid context bloat from stale RTL.
"""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Optional

from hagent.inou.locator import Locator
from hagent.core.llm.conversation import Conversation
from hagent.core.llm.llm_wrap import LLM_wrap
from hagent.core.llm.models import ChatOutput, LLMParams, Message
from hagent.core.llm.template_registry import TemplateRegistry
from hagent.core.react import Observation, ReactLoop
from hagent.core.step import Step
from hagent.workflow.frequency_opt.config import (
    DesignConfig,
    get_field,
    set_field,
)
from hagent.workflow.frequency_opt.common_utils import resolve_instance_signal

_MODULE_RE = re.compile(r'=== MODULE:\s*(\S+)\s*===\s*\n(.*?)\n=== END MODULE ===', re.DOTALL)
_STRATEGY_RE = re.compile(r'--- STRATEGY:\s*(.+?)\s*---\s*\n(.*?)\n--- END STRATEGY ---', re.DOTALL)


def read_rtl_files(rtl_dir: Path) -> dict[str, str]:
    """Read all Verilog/SystemVerilog files from a directory.

    Returns a dict mapping file stem (module name) to file contents.
    """
    files = {}
    for pat in ('*.sv', '*.v'):
        for p in sorted(rtl_dir.glob(pat)):
            files[p.stem] = p.read_text()
    return files


def parse_arch_response(response: str) -> dict[str, dict[str, str]]:
    """Parse MODULE/STRATEGY blocks from an LLM response.

    Returns nested dict: {module_name: {strategy_name: strategy_description}}.
    """
    result = {}
    for mod, body in _MODULE_RE.findall(response):
        strats = {}
        for sname, sprompt in _STRATEGY_RE.findall(body):
            strats[sname.strip()] = sprompt.strip()
        if strats:
            result[mod.strip()] = strats
    return result


# ---------------------------------------------------------------------------
# Pure helper functions (testable independently)
# ---------------------------------------------------------------------------


def _format_hierarchy(hierarchy_dict: dict, synth_top: str) -> str:
    """Format raw Locator hierarchy as a natural-language tree rooted at synth_top.

    Args:
        hierarchy_dict: From Locator.get_hierarchy(). Maps instance_path -> {module, file}.
        synth_top: Module name (or Top$instance.path) to use as root.

    Returns:
        Human-readable hierarchy tree string.
    """
    instances = {k: v for k, v in hierarchy_dict.items() if not k.startswith('_')}
    if not instances:
        return '(no hierarchy available)'

    root_instance: Optional[str] = None

    if '$' in synth_top:
        inst_path = synth_top.split('$', 1)[1]
        if inst_path in instances:
            root_instance = inst_path

    if root_instance is None and synth_top in instances:
        root_instance = synth_top

    if root_instance is None:
        for ip, info in instances.items():
            if info.get('module') == synth_top:
                root_instance = ip
                break

    if root_instance is None:
        return f'(hierarchy root "{synth_top}" not found)'

    root_module = instances[root_instance].get('module', synth_top)

    children: dict[str, list[tuple[str, str, str]]] = {}
    prefix = root_instance + '.'
    for ip, info in instances.items():
        if ip == root_instance or not ip.startswith(prefix):
            continue
        parent = ip.rsplit('.', 1)[0]
        rel_name = ip.rsplit('.', 1)[1]
        children.setdefault(parent, []).append((ip, info.get('module', ''), rel_name))

    lines: list[str] = [f'The top-level module is {root_module}.']

    def _render(inst_path: str, module_name: str, indent: int) -> None:
        kids = children.get(inst_path, [])
        if not kids:
            return
        pad = '  ' * indent
        lines.append(f'{pad}{module_name} instantiates:')
        for child_path, child_mod, child_rel in sorted(kids, key=lambda x: x[2]):
            lines.append(f'{pad}  - {child_mod} (instance: {child_rel})')
            _render(child_path, child_mod, indent + 2)

    _render(root_instance, root_module, indent=0)
    return '\n'.join(lines)


def _format_signal_description(signal: str, hierarchy_dict: dict, synth_top: str) -> str:
    """Format a signal with its module/instance/parent context using hierarchy resolution.

    Example output: "ALU's result signal (instance alu in CPU)"
    Falls back to the raw signal string when resolution fails.
    """
    inst_key, leaf, _file = resolve_instance_signal(signal, hierarchy_dict, synth_top)
    if not inst_key:
        return signal

    info = hierarchy_dict.get(inst_key, {})
    module_name = info.get('module', '')
    inst_name = inst_key.rsplit('.', 1)[-1]

    # Find parent module
    parent_module = None
    if '.' in inst_key:
        parent_path = inst_key.rsplit('.', 1)[0]
        parent_info = hierarchy_dict.get(parent_path)
        if parent_info:
            parent_module = parent_info.get('module', '')

    if module_name and parent_module:
        return f"{module_name}'s {leaf} signal (instance {inst_name} in {parent_module})"
    elif module_name:
        return f"{module_name}'s {leaf} signal (instance {inst_name})"
    return signal


def _format_critical_path_info(
    modules: list[str],
    start: str,
    end: str,
    freq: float,
    hierarchy_dict: Optional[dict] = None,
    synth_top: Optional[str] = None,
) -> str:
    """Build the critical path information text block.

    When hierarchy_dict and synth_top are provided, resolves start/end flop
    signals to their module/instance context for richer descriptions.
    """
    if hierarchy_dict and synth_top:
        start_desc = _format_signal_description(start, hierarchy_dict, synth_top)
        end_desc = _format_signal_description(end, hierarchy_dict, synth_top)
    else:
        start_desc = start
        end_desc = end

    module_list = ', '.join(modules) if modules else '(none)'
    lines = [
        f'The critical path starts from {start_desc} and ends at {end_desc}.',
        f'The critical path includes {len(module_list)} modules: {module_list}.',
        f'Current frequency: {freq:.1f} MHz',
    ]
    return '\n'.join(lines)


def _order_modules_bottom_up(names: list[str], hierarchy_dict: dict) -> list[str]:
    """Sort module names by hierarchy depth descending (deepest first).

    Modules not found in hierarchy are placed at the end.
    """
    if not hierarchy_dict:
        return list(names)

    instances = {k: v for k, v in hierarchy_dict.items() if not k.startswith('_')}
    module_depth: dict[str, int] = {}
    for ip, info in instances.items():
        mod = info.get('module', '')
        depth = ip.count('.')
        if mod in module_depth:
            module_depth[mod] = max(module_depth[mod], depth)
        else:
            module_depth[mod] = depth

    def sort_key(name: str) -> tuple[int, str]:
        d = module_depth.get(name, -1)
        return (-d, name)

    return sorted(names, key=sort_key)


def _build_rtl_sections(ordered_modules: list[str], file_contents: dict[str, str]) -> str:
    """Build numbered RTL code blocks for the prompt."""
    parts: list[str] = []
    for i, name in enumerate(ordered_modules, 1):
        code = file_contents.get(name)
        if code is not None:
            parts.append(f'--- Module {i}: {name} ---\n```verilog\n{code}\n```')
        else:
            parts.append(f'--- Module {i}: {name} ---\n(source not available)')
    return '\n\n'.join(parts)


def _build_prior_summaries(iteration_history: list[dict], current_modules: list[str]) -> str:
    """Build prior-iteration summaries for refinement prompt.

    For modules recurring on the current critical path, includes exact patches.
    For other modules, includes only high-level result summary.
    """
    if not iteration_history:
        return '(first iteration \u2014 no prior history)'

    current_set = set(current_modules)
    parts: list[str] = []

    for entry in iteration_history:
        it = entry.get('iteration', '?')
        freq_before = entry.get('frequency_before', 0.0)
        freq_after = entry.get('frequency_after', 0.0)
        mods = entry.get('critical_path_modules', [])
        start = entry.get('critical_path_start', '?')
        end = entry.get('critical_path_end', '?')
        results = entry.get('results', [])

        header = f'### Iteration {it} ({freq_before:.1f} \u2192 {freq_after:.1f} MHz)'
        path_chain = ' \u2192 '.join([start] + mods + [end])
        lines = [header, f'Critical path: {path_chain}']

        for r in results:
            mod = r.get('module', '?')
            strat = r.get('strategy', '?')
            success = r.get('success', False)
            if success:
                freq = r.get('frequency_mhz', 0.0)
                line = f'- {mod}/{strat}: SUCCEEDED ({freq:.1f} MHz)'
                patch = r.get('patch', '')
                if patch and mod in current_set:
                    line += f'\n  Applied patch:\n  ```\n{patch}\n  ```'
            else:
                error = r.get('error', 'unknown')
                line = f'- {mod}/{strat}: FAILED ({error})'
            lines.append(line)

        parts.append('\n'.join(lines))

    return '\n\n'.join(parts)


# ---------------------------------------------------------------------------
# ArchAgentStep
# ---------------------------------------------------------------------------


class ArchAgentStep(Step, ReactLoop[dict]):
    """Proposes optimization strategies by analyzing annotated RTL on the critical path.

    State persists across Workflow cycle iterations (created once):
      - _llm, _system_prompt, _params, _registry: LLM infrastructure
      - _locator: hierarchy access
      - _first_call: distinguishes initial vs refinement
      - _iteration_history: lightweight per-iteration summary dicts
    """

    def __init__(self):
        super().__init__()

    def setup(self):
        super().setup()

        data = self.input_data
        assert data is not None

        conf_file = get_field(data, 'llm.conf_file')
        if not conf_file:
            raise RuntimeError('ArchAgent: llm_config not set (pass via constructor or input YAML)')
        self._llm = LLM_wrap(name='arch_agent', conf_file=conf_file, log_file='arch_agent.log')
        if self._llm.last_error:
            raise RuntimeError(f'ArchAgent LLM init failed: {self._llm.last_error}')

        self._registry = TemplateRegistry(self._llm.config)
        system_content = self._registry.get_system('arch_initial')
        if system_content:
            self._system_prompt = Message(role='system', content=system_content)
        self._params = LLMParams.from_llm_args(self._llm.llm_args)

        self._max_format_retries = int(data.get('max_format_retries', 3))

        self._first_call = True
        self._iteration_history: list[dict] = []

        self.design = DesignConfig.from_data(data, 'design_info')
        self.locator = Locator(
            config_path=self.design.hagent_config_yaml,
            profile_name=self.design.hagent_profile_name,
        )
        if not self.locator.setup():
            self.error(f'Locator setup failed: {self.locator.get_error()}')

    def run(self, data: dict) -> dict:
        cp_info = data.get('critical_path_info', {})
        rtl_dir = cp_info.get('dir', '')
        module_names = cp_info.get('module_names', [])
        cp = cp_info.get('critical_path', {})
        start_flop = cp.get('start', '?')
        end_flop = cp.get('end', '?')
        current_freq = get_field(data, 'synth_sta.frequency_mhz')

        file_contents = read_rtl_files(Path(rtl_dir)) if rtl_dir else {}
        hierarchy = self.locator.get_hierarchy()

        synth_top = self.design.effective_synth_top

        ordered = _order_modules_bottom_up(module_names, hierarchy)
        hierarchy_text = _format_hierarchy(hierarchy, synth_top) if hierarchy and synth_top else '(not available)'
        critical_path_text = _format_critical_path_info(
            module_names,
            start_flop,
            end_flop,
            current_freq,
            hierarchy_dict=hierarchy,
            synth_top=synth_top,
        )
        rtl_sections = _build_rtl_sections(ordered, file_contents)
        prior_summaries = _build_prior_summaries(self._iteration_history, module_names)

        template_name = 'arch_initial' if self._first_call else 'arch_refinement'
        variables = {
            'hierarchy_text': hierarchy_text,
            'critical_path_info': critical_path_text,
            'rtl_sections': rtl_sections,
            'prior_summaries': prior_summaries,
        }
        user_content = self._registry.format(template_name, variables)

        # Fresh Conversation for this iteration (avoids context bloat from stale RTL)
        self.conversation = Conversation(
            llm=self._llm,
            system_prompt=self._system_prompt,
            default_params=self._params,
        )

        observation = self.react(user_content, max_retries=self._max_format_retries)

        output = data.copy()
        if observation.success:
            output['strategies'] = json.loads(observation.value)
        else:
            output['strategies'] = {}
            output['arch_agent_error'] = observation.feedback
            print(f'ArchAgent: all format retries exhausted: {observation.feedback}')

        self._iteration_history.append(
            {
                'iteration': len(self._iteration_history),
                'critical_path_modules': list(module_names),
                'critical_path_start': start_flop,
                'critical_path_end': end_flop,
                'frequency_before': data.get('previous_frequency_mhz', current_freq),
                'frequency_after': current_freq,
                'results': data.get('module_opt_results', []),
            }
        )
        self._first_call = False
        return output

    # -- ReactLoop overrides --

    def action(self, chat_output: ChatOutput) -> dict:
        return parse_arch_response(chat_output.content)

    def observe(self, action_result: dict) -> Observation:
        if not action_result:
            return Observation(
                success=False,
                feedback=(
                    'Your response could not be parsed. Please use the exact format:\n'
                    '=== MODULE: <module_name> ===\n'
                    '--- STRATEGY: <short_strategy_name> ---\n'
                    '<description>\n'
                    '--- END STRATEGY ---\n'
                    '=== END MODULE ==='
                ),
            )
        return Observation(success=True, value=json.dumps(action_result))


if __name__ == '__main__':  # pragma: no cover
    step = ArchAgentStep()
    step.parse_arguments()
    step.setup()
    step.step()
