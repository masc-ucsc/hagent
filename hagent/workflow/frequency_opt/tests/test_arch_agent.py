# See LICENSE for details

"""Tests for ArchAgentStep and its helper functions."""

from __future__ import annotations

from pathlib import Path
from types import SimpleNamespace
from unittest.mock import MagicMock

from ruamel.yaml import YAML

from hagent.core.llm.models import LLMParams, Message
from hagent.core.llm.template_registry import TemplateRegistry
from hagent.workflow.frequency_opt.experiment_sr import parse_arch_response
from hagent.workflow.frequency_opt.common_utils import resolve_instance_signal
from hagent.workflow.frequency_opt.steps.arch_agent import (
    ArchAgentStep,
    _build_prior_summaries,
    _build_rtl_sections,
    _format_critical_path_info,
    _format_hierarchy,
    _format_signal_description,
    _order_modules_bottom_up,
)


# ---------------------------------------------------------------------------
# Fixtures / helpers
# ---------------------------------------------------------------------------

SAMPLE_HIERARCHY = {
    'CPU': {'module': 'CPU', 'file': '/src/CPU.sv'},
    'CPU.alu': {'module': 'ALU', 'file': '/src/ALU.sv'},
    'CPU.alu.adder': {'module': 'Adder', 'file': '/src/Adder.sv'},
    'CPU.regFile': {'module': 'RegFile', 'file': '/src/RegFile.sv'},
    'CPU.decoder': {'module': 'Decoder', 'file': '/src/Decoder.sv'},
    'CPU.decoder.rom': {'module': 'DecodeROM', 'file': '/src/DecodeROM.sv'},
    '_metadata': {'slang_hier_command': 'test'},
    '_top_modules': ['CPU'],
}

GOOD_RESPONSE = """\
=== MODULE: ALU ===
--- STRATEGY: flatten_mux ---
Restructure the priority-encoded mux tree in the ALU to use a parallel case.
--- END STRATEGY ---
--- STRATEGY: lookahead_add ---
Replace the ripple-carry adder with a carry-lookahead adder.
--- END STRATEGY ---
=== END MODULE ===

=== MODULE: Decoder ===
--- STRATEGY: simplify_decode ---
Move the critical signal out of the nested if-else chain.
--- END STRATEGY ---
=== END MODULE ===
"""

BAD_RESPONSE = 'Here are some optimization ideas for the ALU module...'


def _load_prompts_config():
    """Load the arch_agent config section from the real YAML file."""
    yaml_path = Path(__file__).parent.parent / 'steps' / 'arch_agent_prompts.yaml'
    yaml_obj = YAML(typ='safe')
    with open(yaml_path) as f:
        data = yaml_obj.load(f)
    return data['arch_agent']


def _make_arch_agent_step(responses, hierarchy=None):
    """Create an ArchAgentStep with mocked LLM returning scripted responses."""
    step = ArchAgentStep()

    config = _load_prompts_config()
    llm = MagicMock()
    llm.last_error = ''
    llm.config = config
    llm.llm_args = config['llm']
    llm.total_cost = 0.0
    llm.total_tokens = 0
    llm.responses = []

    response_iter = iter(responses)

    def mock_call_impl(messages, params=None):
        return [next(response_iter)]

    llm.call = MagicMock(side_effect=mock_call_impl)

    step._llm = llm
    step._registry = TemplateRegistry(config)
    system_content = step._registry.get_system('arch_initial')
    if system_content:
        step._system_prompt = Message(role='system', content=system_content)
    step._params = LLMParams(model='test')
    step._max_format_retries = 3
    step._first_call = True
    step._iteration_history = []

    if hierarchy is not None:
        step.locator = SimpleNamespace(get_hierarchy=lambda: hierarchy)

    step.design = SimpleNamespace(effective_synth_top='CPU')
    step.setup_called = True
    step.output_file = '/dev/null'
    step.input_data = {}

    return step


def _make_base_data(module_names=None, freq=500.0, rtl_dir=''):
    """Build a minimal data dict for testing run()."""
    return {
        'critical_path_info': {
            'dir': rtl_dir,
            'module_names': module_names or ['ALU'],
            'critical_path': {'start': 'reg_a', 'end': 'reg_b'},
        },
        'synth_sta': {'frequency_mhz': freq},
        'design_info': {'top_module': 'CPU', 'synth_top_module': 'CPU'},
    }


# ---------------------------------------------------------------------------
# Unit tests: parse_arch_response
# ---------------------------------------------------------------------------


class TestParseArchResponse:
    def test_valid_multi_module(self):
        result = parse_arch_response(GOOD_RESPONSE)
        assert 'ALU' in result
        assert 'Decoder' in result
        assert len(result['ALU']) == 2
        assert 'flatten_mux' in result['ALU']
        assert 'lookahead_add' in result['ALU']
        assert len(result['Decoder']) == 1

    def test_bad_format(self):
        assert parse_arch_response(BAD_RESPONSE) == {}

    def test_empty(self):
        assert parse_arch_response('') == {}

    def test_module_without_strategies(self):
        text = '=== MODULE: ALU ===\nSome text without strategy markers\n=== END MODULE ==='
        assert parse_arch_response(text) == {}


# ---------------------------------------------------------------------------
# Unit tests: _format_hierarchy
# ---------------------------------------------------------------------------


class TestFormatHierarchy:
    def test_basic_tree(self):
        result = _format_hierarchy(SAMPLE_HIERARCHY, 'CPU')
        assert 'The top-level module is CPU.' in result
        assert 'ALU (instance: alu)' in result
        assert 'Adder (instance: adder)' in result
        assert 'RegFile (instance: regFile)' in result
        assert 'Decoder (instance: decoder)' in result
        assert 'DecodeROM (instance: rom)' in result
        assert '/src/' not in result

    def test_skips_metadata_keys(self):
        result = _format_hierarchy(SAMPLE_HIERARCHY, 'CPU')
        assert '_metadata' not in result
        assert '_top_modules' not in result

    def test_empty_hierarchy(self):
        result = _format_hierarchy({}, 'CPU')
        assert 'no hierarchy available' in result

    def test_missing_root(self):
        result = _format_hierarchy(SAMPLE_HIERARCHY, 'NonExistent')
        assert 'not found' in result

    def test_dollar_synth_top(self):
        result = _format_hierarchy(SAMPLE_HIERARCHY, 'TopChip$CPU')
        assert 'The top-level module is CPU.' in result
        assert 'ALU' in result

    def test_module_name_match(self):
        hier = {
            'top_inst': {'module': 'MyTop', 'file': 'MyTop.sv'},
            'top_inst.sub': {'module': 'SubMod', 'file': 'Sub.sv'},
        }
        result = _format_hierarchy(hier, 'MyTop')
        assert 'The top-level module is MyTop.' in result
        assert 'SubMod' in result


# ---------------------------------------------------------------------------
# Unit tests: _order_modules_bottom_up
# ---------------------------------------------------------------------------


class TestOrderModulesBottomUp:
    def test_deepest_first(self):
        result = _order_modules_bottom_up(['CPU', 'ALU', 'Adder', 'Decoder'], SAMPLE_HIERARCHY)
        assert result.index('Adder') < result.index('CPU')
        assert result.index('ALU') < result.index('CPU')

    def test_unknown_modules_at_end(self):
        result = _order_modules_bottom_up(['ALU', 'Unknown'], SAMPLE_HIERARCHY)
        assert result[-1] == 'Unknown'

    def test_empty_hierarchy(self):
        result = _order_modules_bottom_up(['A', 'B'], {})
        assert set(result) == {'A', 'B'}


# ---------------------------------------------------------------------------
# Unit tests: _build_rtl_sections
# ---------------------------------------------------------------------------


class TestBuildRtlSections:
    def test_numbered_blocks(self):
        contents = {'ALU': 'module ALU(...);', 'RegFile': 'module RegFile(...);'}
        result = _build_rtl_sections(['ALU', 'RegFile'], contents)
        assert '--- Module 1: ALU ---' in result
        assert '--- Module 2: RegFile ---' in result
        assert '```verilog' in result

    def test_missing_source(self):
        result = _build_rtl_sections(['Missing'], {})
        assert 'source not available' in result


# ---------------------------------------------------------------------------
# Unit tests: _format_critical_path_info
# ---------------------------------------------------------------------------


class TestFormatCriticalPathInfo:
    def test_contains_info_without_hierarchy(self):
        result = _format_critical_path_info(['ALU', 'Decoder'], 'reg_a', 'reg_b', 500.0)
        assert 'reg_a' in result
        assert 'reg_b' in result
        assert 'ALU' in result
        assert 'Decoder' in result
        assert '500.0 MHz' in result

    def test_with_hierarchy_resolves_signals(self):
        result = _format_critical_path_info(
            ['ALU', 'Decoder'],
            'alu.result',
            'decoder.rom.data_out',
            500.0,
            hierarchy_dict=SAMPLE_HIERARCHY,
            synth_top='CPU',
        )
        assert "ALU's result signal" in result
        assert 'instance alu in CPU' in result
        assert "DecodeROM's data_out signal" in result
        assert 'instance rom in Decoder' in result
        assert 'ALU' in result
        assert 'Decoder' in result
        assert '500.0 MHz' in result

    def test_with_hierarchy_unresolvable_signal(self):
        result = _format_critical_path_info(
            ['ALU'],
            'nonexistent_signal',
            'alu.result',
            500.0,
            hierarchy_dict=SAMPLE_HIERARCHY,
            synth_top='CPU',
        )
        # Unresolvable signal falls back to raw string
        assert 'nonexistent_signal' in result
        assert "ALU's result signal" in result


# ---------------------------------------------------------------------------
# Unit tests: _format_signal_description
# ---------------------------------------------------------------------------


class TestFormatSignalDescription:
    def test_resolves_instance_to_module(self):
        result = _format_signal_description('alu.result', SAMPLE_HIERARCHY, 'CPU')
        assert "ALU's result signal" in result
        assert 'instance alu in CPU' in result

    def test_nested_instance(self):
        result = _format_signal_description('decoder.rom.data_out', SAMPLE_HIERARCHY, 'CPU')
        assert "DecodeROM's data_out signal" in result
        assert 'instance rom in Decoder' in result

    def test_no_dot_signal_resolves_to_top(self):
        # 'nonexistent' with synth_top='CPU' forms 'CPU.nonexistent' → matches 'CPU' key
        result = _format_signal_description('nonexistent', SAMPLE_HIERARCHY, 'CPU')
        assert "CPU's nonexistent signal" in result

    def test_unresolvable_returns_raw(self):
        result = _format_signal_description('alu.result', {}, 'CPU')
        assert result == 'alu.result'

    def test_dollar_synth_top(self):
        result = _format_signal_description('alu.result', SAMPLE_HIERARCHY, 'TopChip$CPU')
        assert "ALU's result signal" in result


# ---------------------------------------------------------------------------
# Unit tests: resolve_instance_signal
# ---------------------------------------------------------------------------


class TestResolveInstanceSignal:
    def test_basic_resolution(self):
        inst_key, leaf, _file = resolve_instance_signal('alu.result', SAMPLE_HIERARCHY, 'CPU')
        assert inst_key == 'CPU.alu'
        assert leaf == 'result'

    def test_deep_resolution(self):
        inst_key, leaf, _file = resolve_instance_signal('decoder.rom.data_out', SAMPLE_HIERARCHY, 'CPU')
        assert inst_key == 'CPU.decoder.rom'
        assert leaf == 'data_out'

    def test_dollar_synth_top(self):
        inst_key, leaf, _file = resolve_instance_signal('alu.result', SAMPLE_HIERARCHY, 'TopChip$CPU')
        assert inst_key == 'CPU.alu'
        assert leaf == 'result'

    def test_no_dot_resolves_to_top(self):
        # 'nonexistent' with synth_top='CPU' forms 'CPU.nonexistent' → matches 'CPU' key
        inst_key, leaf, _file = resolve_instance_signal('nonexistent', SAMPLE_HIERARCHY, 'CPU')
        assert inst_key == 'CPU'
        assert leaf == 'nonexistent'

    def test_truly_unresolvable(self):
        inst_key, leaf, _file = resolve_instance_signal('x.y', SAMPLE_HIERARCHY, 'WrongTop')
        # 'WrongTop.x.y' — no prefix matches and suffix 'x' doesn't match any instance
        assert inst_key is None
        assert leaf == 'x.y'

    def test_empty_hierarchy(self):
        inst_key, leaf, _file = resolve_instance_signal('alu.result', {}, 'CPU')
        assert inst_key is None

    def test_suffix_fallback(self):
        inst_key, leaf, _file = resolve_instance_signal('alu.result', SAMPLE_HIERARCHY, 'WrongTop')
        # Falls back to suffix matching: 'alu' matches 'CPU.alu'
        assert inst_key == 'CPU.alu'
        assert leaf == 'result'


# ---------------------------------------------------------------------------
# Unit tests: _build_prior_summaries
# ---------------------------------------------------------------------------


class TestBuildPriorSummaries:
    def test_no_history(self):
        result = _build_prior_summaries([], ['ALU'])
        assert 'first iteration' in result

    def test_basic_summary(self):
        history = [
            {
                'iteration': 0,
                'critical_path_modules': ['ALU'],
                'critical_path_start': 'reg_a',
                'critical_path_end': 'reg_b',
                'frequency_before': 500.0,
                'frequency_after': 520.0,
                'results': [
                    {'module': 'ALU', 'strategy': 'flatten_mux', 'success': True, 'frequency_mhz': 520.0},
                    {'module': 'ALU', 'strategy': 'pipeline', 'success': False, 'error': 'LEC mismatch'},
                ],
            }
        ]
        result = _build_prior_summaries(history, ['ALU'])
        assert 'Iteration 0' in result
        assert '500.0' in result
        assert '520.0' in result
        assert 'SUCCEEDED' in result
        assert 'FAILED' in result
        assert 'LEC mismatch' in result

    def test_recurring_module_includes_patches(self):
        history = [
            {
                'iteration': 0,
                'critical_path_modules': ['ALU'],
                'critical_path_start': 'r1',
                'critical_path_end': 'r2',
                'frequency_before': 500.0,
                'frequency_after': 520.0,
                'results': [
                    {
                        'module': 'ALU',
                        'strategy': 'flatten_mux',
                        'success': True,
                        'frequency_mhz': 520.0,
                        'patch': '<<<<<<< SEARCH\nold code\n=======\nnew code\n>>>>>>> REPLACE',
                    },
                ],
            }
        ]
        result = _build_prior_summaries(history, ['ALU'])
        assert '<<<<<<< SEARCH' in result
        assert 'old code' in result

    def test_non_recurring_module_no_patch(self):
        history = [
            {
                'iteration': 0,
                'critical_path_modules': ['ALU'],
                'critical_path_start': 'r1',
                'critical_path_end': 'r2',
                'frequency_before': 500.0,
                'frequency_after': 520.0,
                'results': [
                    {
                        'module': 'ALU',
                        'strategy': 'flatten_mux',
                        'success': True,
                        'frequency_mhz': 520.0,
                        'patch': 'some patch content',
                    },
                ],
            }
        ]
        result = _build_prior_summaries(history, ['Decoder'])
        assert 'SUCCEEDED' in result
        assert 'some patch content' not in result

    def test_multi_iteration_patches_accumulated(self):
        history = [
            {
                'iteration': 0,
                'critical_path_modules': ['ALU'],
                'critical_path_start': 'r1',
                'critical_path_end': 'r2',
                'frequency_before': 500.0,
                'frequency_after': 520.0,
                'results': [
                    {'module': 'ALU', 'strategy': 's1', 'success': True, 'frequency_mhz': 520.0, 'patch': 'patch_iter0'},
                ],
            },
            {
                'iteration': 1,
                'critical_path_modules': ['ALU'],
                'critical_path_start': 'r1',
                'critical_path_end': 'r2',
                'frequency_before': 520.0,
                'frequency_after': 540.0,
                'results': [
                    {'module': 'ALU', 'strategy': 's2', 'success': True, 'frequency_mhz': 540.0, 'patch': 'patch_iter1'},
                ],
            },
        ]
        result = _build_prior_summaries(history, ['ALU'])
        assert 'patch_iter0' in result
        assert 'patch_iter1' in result


# ---------------------------------------------------------------------------
# Integration tests: ArchAgentStep.run() with mocked LLM
# ---------------------------------------------------------------------------


class TestInitialCallParsesStrategies:
    def test_good_response_first_try(self):
        step = _make_arch_agent_step([GOOD_RESPONSE], hierarchy=SAMPLE_HIERARCHY)
        data = _make_base_data(module_names=['ALU', 'Decoder'])
        result = step.run(data)

        assert 'strategies' in result
        assert 'ALU' in result['strategies']
        assert 'Decoder' in result['strategies']
        assert 'arch_agent_error' not in result


class TestFormatRetrySucceeds:
    def test_bad_then_good(self):
        step = _make_arch_agent_step([BAD_RESPONSE, GOOD_RESPONSE], hierarchy=SAMPLE_HIERARCHY)
        data = _make_base_data(module_names=['ALU', 'Decoder'])
        result = step.run(data)

        assert 'ALU' in result['strategies']
        assert step.react_iterations == 2


class TestAllRetriesExhausted:
    def test_all_bad(self):
        step = _make_arch_agent_step(
            [BAD_RESPONSE, BAD_RESPONSE, BAD_RESPONSE],
            hierarchy=SAMPLE_HIERARCHY,
        )
        data = _make_base_data()
        result = step.run(data)

        assert result['strategies'] == {}
        assert 'arch_agent_error' in result


class TestRefinementUsesPreviousResults:
    def test_second_run_uses_refinement(self):
        step = _make_arch_agent_step(
            [GOOD_RESPONSE, GOOD_RESPONSE],
            hierarchy=SAMPLE_HIERARCHY,
        )

        data1 = _make_base_data(module_names=['ALU'], freq=500.0)
        step.run(data1)
        assert step._first_call is False

        data2 = _make_base_data(module_names=['ALU', 'Decoder'], freq=520.0)
        data2['module_opt_results'] = [
            {'module': 'ALU', 'strategy': 'flatten_mux', 'success': True, 'frequency_mhz': 520.0},
        ]
        data2['previous_frequency_mhz'] = 500.0
        result = step.run(data2)

        assert 'strategies' in result
        calls = step._llm.call.call_args_list
        assert len(calls) == 2
        second_call_messages = calls[1][0][0]
        user_msg = second_call_messages[-1]
        assert 'Prior Iteration Summaries' in user_msg.content


class TestBottomUpOrderingInPrompt:
    def test_deeper_modules_first_in_prompt(self):
        step = _make_arch_agent_step([GOOD_RESPONSE], hierarchy=SAMPLE_HIERARCHY)
        data = _make_base_data(module_names=['CPU', 'ALU', 'Adder'])
        step.run(data)

        calls = step._llm.call.call_args_list
        user_msg = calls[0][0][0][-1].content
        assert 'Module 1: Adder' in user_msg


class TestIterationHistoryAccumulates:
    def test_three_iterations(self):
        step = _make_arch_agent_step(
            [GOOD_RESPONSE, GOOD_RESPONSE, GOOD_RESPONSE],
            hierarchy=SAMPLE_HIERARCHY,
        )

        for i in range(3):
            data = _make_base_data(freq=500.0 + i * 10)
            step.run(data)

        assert len(step._iteration_history) == 3
        assert step._iteration_history[0]['iteration'] == 0
        assert step._iteration_history[1]['iteration'] == 1
        assert step._iteration_history[2]['iteration'] == 2


class TestRecurringModuleIncludesPatches:
    def test_patches_in_refinement_message(self):
        step = _make_arch_agent_step(
            [GOOD_RESPONSE, GOOD_RESPONSE],
            hierarchy=SAMPLE_HIERARCHY,
        )

        data1 = _make_base_data(module_names=['ALU'], freq=500.0)
        data1['module_opt_results'] = [
            {
                'module': 'ALU',
                'strategy': 'flatten_mux',
                'success': True,
                'frequency_mhz': 520.0,
                'patch': 'SEARCH_REPLACE_PATCH_CONTENT',
            },
        ]
        step.run(data1)

        data2 = _make_base_data(module_names=['ALU'], freq=520.0)
        step.run(data2)

        calls = step._llm.call.call_args_list
        second_msg = calls[1][0][0][-1].content
        assert 'SEARCH_REPLACE_PATCH_CONTENT' in second_msg


class TestNonRecurringModuleExcludesPatchInPrompt:
    def test_patch_excluded_when_module_leaves_critical_path(self):
        """Module optimized in iter 0 but NOT on critical path in iter 1 → no patch in prompt."""
        step = _make_arch_agent_step(
            [GOOD_RESPONSE, GOOD_RESPONSE],
            hierarchy=SAMPLE_HIERARCHY,
        )

        data1 = _make_base_data(module_names=['ALU'], freq=500.0)
        data1['module_opt_results'] = [
            {
                'module': 'ALU',
                'strategy': 'flatten_mux',
                'success': True,
                'frequency_mhz': 520.0,
                'patch': 'SHOULD_NOT_APPEAR_IN_PROMPT',
            },
        ]
        step.run(data1)

        # Iter 1: critical path shifted to Decoder only (ALU no longer on path)
        data2 = _make_base_data(module_names=['Decoder'], freq=520.0)
        step.run(data2)

        calls = step._llm.call.call_args_list
        second_msg = calls[1][0][0][-1].content
        assert 'SUCCEEDED' in second_msg
        assert 'SHOULD_NOT_APPEAR_IN_PROMPT' not in second_msg


class TestFailedStrategyInPrompt:
    def test_failed_strategy_shows_error_no_patch(self):
        """Failed strategies appear with error message but no patch in refinement prompt."""
        step = _make_arch_agent_step(
            [GOOD_RESPONSE, GOOD_RESPONSE],
            hierarchy=SAMPLE_HIERARCHY,
        )

        data1 = _make_base_data(module_names=['ALU'], freq=500.0)
        data1['module_opt_results'] = [
            {
                'module': 'ALU',
                'strategy': 'pipeline_add',
                'success': False,
                'error': 'LEC mismatch detected',
            },
        ]
        step.run(data1)

        data2 = _make_base_data(module_names=['ALU'], freq=500.0)
        step.run(data2)

        calls = step._llm.call.call_args_list
        second_msg = calls[1][0][0][-1].content
        assert 'FAILED' in second_msg
        assert 'LEC mismatch detected' in second_msg


class TestMultiIterationPatchAccumulationInPrompt:
    def test_patches_from_two_iterations_in_third_prompt(self):
        """Patches from iter 0 and iter 1 both appear in iter 2 refinement prompt."""
        step = _make_arch_agent_step(
            [GOOD_RESPONSE, GOOD_RESPONSE, GOOD_RESPONSE],
            hierarchy=SAMPLE_HIERARCHY,
        )

        # Iter 0: ALU optimized
        data0 = _make_base_data(module_names=['ALU'], freq=500.0)
        data0['module_opt_results'] = [
            {
                'module': 'ALU',
                'strategy': 's1',
                'success': True,
                'frequency_mhz': 520.0,
                'patch': 'PATCH_FROM_ITER_0',
            },
        ]
        step.run(data0)

        # Iter 1: ALU still on critical path, optimized again
        data1 = _make_base_data(module_names=['ALU'], freq=520.0)
        data1['module_opt_results'] = [
            {
                'module': 'ALU',
                'strategy': 's2',
                'success': True,
                'frequency_mhz': 540.0,
                'patch': 'PATCH_FROM_ITER_1',
            },
        ]
        step.run(data1)

        # Iter 2: ALU still on critical path → both patches should appear
        data2 = _make_base_data(module_names=['ALU'], freq=540.0)
        step.run(data2)

        calls = step._llm.call.call_args_list
        third_msg = calls[2][0][0][-1].content
        assert 'PATCH_FROM_ITER_0' in third_msg
        assert 'PATCH_FROM_ITER_1' in third_msg


class TestMixedSuccessFailureInPrompt:
    def test_mixed_results_in_refinement(self):
        """Both succeeded (with patch) and failed strategies from same iteration in prompt."""
        step = _make_arch_agent_step(
            [GOOD_RESPONSE, GOOD_RESPONSE],
            hierarchy=SAMPLE_HIERARCHY,
        )

        data1 = _make_base_data(module_names=['ALU'], freq=500.0)
        data1['module_opt_results'] = [
            {
                'module': 'ALU',
                'strategy': 'flatten_mux',
                'success': True,
                'frequency_mhz': 520.0,
                'patch': 'SUCCESSFUL_PATCH',
            },
            {
                'module': 'ALU',
                'strategy': 'bad_idea',
                'success': False,
                'error': 'synthesis timeout',
            },
        ]
        step.run(data1)

        data2 = _make_base_data(module_names=['ALU'], freq=520.0)
        step.run(data2)

        calls = step._llm.call.call_args_list
        second_msg = calls[1][0][0][-1].content
        assert 'SUCCESSFUL_PATCH' in second_msg
        assert 'SUCCEEDED' in second_msg
        assert 'FAILED' in second_msg
        assert 'synthesis timeout' in second_msg
