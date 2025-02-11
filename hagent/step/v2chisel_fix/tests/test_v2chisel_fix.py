# hagent/step/v2chisel_fix/tests/test_v2chisel_fix.py

import os
import pytest
from unittest.mock import patch, MagicMock

from hagent.step.v2chisel_fix.v2chisel_fix import V2ChiselFix


@pytest.fixture
def valid_input_file(tmp_path):
    """
    Creates a minimal valid YAML for V2ChiselFix:
      - 'chisel_pass1' with some snippet
      - 'verilog_fixed'
      - 'llm' if needed
    """
    content = """\
chisel_pass1:
  chisel_changed: |
    class MyModule extends Module {
      val io = IO(new Bundle {})
    }
  verilog_candidate: |
    module mymodule (input clk, rst);
    endmodule
  was_valid: true

verilog_fixed: |
  module mymodule (input clk, rst);
  // new changes
  endmodule

llm:
  model: "test-model"
"""
    fpath = tmp_path / 'input_fix.yaml'
    fpath.write_text(content)
    return str(fpath)


@pytest.fixture
def step_with_io(valid_input_file, tmp_path):
    """
    Returns a V2ChiselFix step with an input path and a temp output.
    We'll call .setup() and then use run(input_data) to get the result.
    """
    step_obj = V2ChiselFix()
    out_file = str(tmp_path / 'output_fix.yaml')
    step_obj.set_io(inp_file=valid_input_file, out_file=out_file)
    return step_obj


def test_missing_chisel_pass1(tmp_path):
    """
    If 'chisel_pass1' isn't in the YAML => raises ValueError
    """
    content = """\
verilog_fixed: |
  module foo();
  endmodule
llm:
  model: test-model
"""
    bad_file = tmp_path / 'input_bad.yaml'
    bad_file.write_text(content)

    step_obj = V2ChiselFix()
    out_file = tmp_path / 'output_bad.yaml'
    step_obj.set_io(inp_file=str(bad_file), out_file=str(out_file))

    with pytest.raises(ValueError, match="Missing 'chisel_pass1' in input YAML"):
        step_obj.setup()


def test_no_prompt3_file(step_with_io):
    """
    If prompt3.yaml doesn't exist => prints a warning, refine_llm=None.
    Run normally so no refinement occurs.
    """
    # Ensure there's NO prompt3.yaml in the directory
    step_dir = os.path.dirname(__file__)
    prompt3_path = os.path.join(step_dir, 'prompt3.yaml')
    if os.path.exists(prompt3_path):
        os.remove(prompt3_path)

    step_with_io.setup()
    with patch('hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check') as mock_eq:
        mock_eq_instance = MagicMock()
        mock_eq.return_value = mock_eq_instance
        # Let equivalence pass => no refine needed
        mock_eq_instance.setup.return_value = True
        mock_eq_instance.check_equivalence.return_value = True

        res = step_with_io.run(step_with_io.input_data)

    # verify 'chisel_fixed' in output
    assert 'chisel_fixed' in res
    cf = res['chisel_fixed']
    assert cf['equiv_passed'] is True
    # since code was equivalent, no refinement needed => refined_chisel = original (or chisel_changed)
    assert cf['refined_chisel'].strip().startswith('class MyModule')

    # Cleanup
    if os.path.exists(prompt3_path):
        os.remove(prompt3_path)


def test_prompt3_but_no_llm_config(tmp_path):
    """
    If prompt3.yaml exists but there's no 'llm' config => warn and refine_llm=None.
    Run normally so no refinement occurs.
    """
    # Create prompt3.yaml
    test_dir = os.path.dirname(__file__)
    prompt3_path = os.path.join(test_dir, 'prompt3.yaml')
    prompt3_contents = """\
messages:
  - role: system
    content: "This is prompt3 for refinement."
"""
    with open(prompt3_path, 'w') as f:
        f.write(prompt3_contents)

    # Create an input file with no 'llm' block
    content = """\
chisel_pass1:
  chisel_changed: |
    class MyModule extends Module { val io = IO(new Bundle {}) }
  verilog_candidate: |
    module mymodule();
    endmodule
  was_valid: true

verilog_fixed: |
  module mymodule();
  endmodule
"""
    bad_llm_file = tmp_path / 'input_no_llm.yaml'
    bad_llm_file.write_text(content)

    step_obj = V2ChiselFix()
    out_file = tmp_path / 'output_no_llm.yaml'
    step_obj.set_io(inp_file=str(bad_llm_file), out_file=str(out_file))

    # Now run
    step_obj.setup()
    # Force equivalence pass => no refine needed
    with patch('hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check') as mock_eq:
        mock_eq_inst = MagicMock()
        mock_eq.return_value = mock_eq_inst
        mock_eq_inst.setup.return_value = True
        mock_eq_inst.check_equivalence.return_value = True

        step_obj.run(step_obj.input_data)

    # Cleanup
    if os.path.exists(prompt3_path):
        os.remove(prompt3_path)


def test_already_equiv_no_refine(step_with_io):
    """
    LEC passes initially so no refinement is done.
    """
    step_with_io.setup()
    with patch('hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check') as mock_eq:
        mock_eq_inst = MagicMock()
        mock_eq.return_value = mock_eq_inst
        mock_eq_inst.setup.return_value = True
        mock_eq_inst.check_equivalence.return_value = True  # Already equivalent

        res = step_with_io.run(step_with_io.input_data)

    cf = res['chisel_fixed']
    assert cf['equiv_passed'] is True
    assert 'class MyModule' in cf['refined_chisel']


def test_lec_fails_refine_succeeds(step_with_io, tmp_path):
    """
    LEC fails initially, then a refinement produces a new snippet and verilog,
    so that equivalence passes on the second check.
    """
    import hagent.step.v2chisel_fix.v2chisel_fix as fix_mod
    module_dir = os.path.dirname(os.path.abspath(fix_mod.__file__))
    prompt3_path = os.path.join(module_dir, 'prompt3.yaml')

    with open(prompt3_path, 'w') as pf:
        pf.write("""\
- role: system
  content: "Refinement system message"
""")
    try:
        step_with_io.setup()
        # Ensure the pass has an "original_chisel" value; if missing, use chisel_changed.
        step_with_io.input_data['chisel_pass1'].setdefault(
            'original_chisel', step_with_io.input_data['chisel_pass1'].get('chisel_changed', '')
        )

        mock_eq_inst = MagicMock()
        mock_eq_inst.setup.return_value = True
        # First equivalence check fails, second passes.
        mock_eq_inst.check_equivalence.side_effect = [False, True]

        def mock_chat_side_effect(prompt_dict):
            # Use the current candidate from the prompt dictionary
            code_in = prompt_dict.get('chisel_subset', '')
            return '```chisel\n' + code_in + 'X\n```'

        def mock_generate_verilog(chisel_code, module_name):
            if 'attempt1' in chisel_code:
                return ('module refined_attempt1(); endmodule', None)
            return ('module original(); endmodule', None)

        with patch('hagent.core.step.yaml.dump', return_value=None), \
             patch('hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check', return_value=mock_eq_inst), \
             patch.object(step_with_io, '_generate_verilog', side_effect=mock_generate_verilog), \
             patch.object(step_with_io.refine_llm, 'chat', side_effect=mock_chat_side_effect):
            res = step_with_io.run(step_with_io.input_data)

        cf = res['chisel_fixed']
        assert cf['equiv_passed'] is True, 'Expected success after second equivalence check'
        assert 'X' in cf['refined_chisel']
    finally:
        if os.path.exists(prompt3_path):
            os.remove(prompt3_path)


def test_lec_fails_all_attempts(step_with_io, tmp_path):
    """
    LEC fails for all attempts; after reaching lec_limit the result has equiv_passed=False.
    """
    import hagent.step.v2chisel_fix.v2chisel_fix as fix_mod
    module_dir = os.path.dirname(os.path.abspath(fix_mod.__file__))
    prompt3_path = os.path.join(module_dir, 'prompt3.yaml')

    with open(prompt3_path, 'w') as f:
        f.write("""\
- role: system
  content: "Refine"
""")
    try:
        step_with_io.setup()
        step_with_io.lec_limit = 2  # shorten attempts

        mock_eq_inst = MagicMock()
        mock_eq_inst.setup.return_value = True
        # Always fails equivalence check.
        mock_eq_inst.check_equivalence.return_value = False

        def mock_chat_side_effect(prompt_dict):
            # Use the candidate from the prompt dictionary
            code_in = prompt_dict.get('chisel_subset', '')
            return '```chisel\n' + code_in + 'X\n```'

        def mock_gen_verilog(chisel_code, module_name):
            return ('module changed(); endmodule', None)

        with patch('hagent.core.step.yaml.dump', return_value=None), \
             patch('hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check', return_value=mock_eq_inst), \
             patch.object(step_with_io.refine_llm, 'chat', side_effect=mock_chat_side_effect), \
             patch.object(step_with_io, '_generate_verilog', side_effect=mock_gen_verilog):
            res = step_with_io.run(step_with_io.input_data)

        cf = res['chisel_fixed']
        assert cf['equiv_passed'] is False, 'Should remain false after max attempts'
        # Expect the refined snippet to have been appended with 'X' only once since the second refinement does not improve.
        assert cf['refined_chisel'].endswith('X')
    finally:
        if os.path.exists(prompt3_path):
            os.remove(prompt3_path)


def test_lec_fails_refine_cannot_improve(step_with_io, tmp_path):
    """
    LEC fails and the LLM returns the same code (no improvement) so refinement stops.
    """
    import hagent.step.v2chisel_fix.v2chisel_fix as fix_mod
    module_dir = os.path.dirname(os.path.abspath(fix_mod.__file__))
    prompt3_path = os.path.join(module_dir, 'prompt3.yaml')

    with open(prompt3_path, 'w') as f:
        f.write("""\
- role: system
  content: "Refinement prompt"
""")
    try:
        step_with_io.setup()
        mock_eq_inst = MagicMock()
        mock_eq_inst.setup.return_value = True
        mock_eq_inst.check_equivalence.return_value = False  # fails

        def mock_chat_side_effect(prompt_dict):
            # Return the same candidate => no improvement.
            return prompt_dict.get('chisel_subset', '')

        with patch('hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check', return_value=mock_eq_inst), \
             patch.object(step_with_io.refine_llm, 'chat', side_effect=mock_chat_side_effect), \
             patch.object(step_with_io, '_generate_verilog', return_value=('module x(); endmodule', None)):
            res = step_with_io.run(step_with_io.input_data)

        cf = res['chisel_fixed']
        assert cf['equiv_passed'] is False
    finally:
        if os.path.exists(prompt3_path):
            os.remove(prompt3_path)


def test_refine_llm_not_present(step_with_io):
    """
    If there's no prompt3.yaml then refine_llm is None so _refine_chisel_code returns the original code.
    """
    step_dir = os.path.dirname(__file__)
    prompt3_path = os.path.join(step_dir, 'prompt3.yaml')
    if os.path.exists(prompt3_path):
        os.remove(prompt3_path)

    step_with_io.setup()
    # Remove any LLM.
    step_with_io.refine_llm = None

    new_code = step_with_io._refine_chisel_code('class MyModule extends Module{}', 'some LEC error')
    assert 'MyModule' in new_code  # same code returned


def test_refine_chisel_code_empty_response(step_with_io):
    """
    If LLM returns an empty response, the original code is kept.
    """
    step_with_io.setup()
    # Ensure required attributes are set.
    step_with_io.chisel_original = 'class MyModule extends Module {}'
    step_with_io.chisel_subset = 'class MyModule extends Module {}'
    step_with_io.refine_llm = MagicMock()
    step_with_io.refine_llm.chat.return_value = '  '  # empty after strip

    old_code = 'class MyModule extends Module {}'
    result = step_with_io._refine_chisel_code(old_code, 'some error')
    assert result == old_code


def test_refine_chisel_code_no_fences(step_with_io):
    """
    When LLM returns triple backticks, they are stripped.
    """
    step_with_io.setup()
    step_with_io.chisel_original = 'class MyModule extends Module {}'
    step_with_io.chisel_subset = 'class MyModule extends Module {}'
    step_with_io.refine_llm = MagicMock()
    step_with_io.refine_llm.chat.return_value = """```chisel
class MyRefined extends Module {}
```"""

    old_code = 'class MyModule extends Module {}'
    result = step_with_io._refine_chisel_code(old_code, 'some error')
    assert 'MyRefined' in result
    # triple backticks are removed
    assert '```' not in result


def test_generate_verilog_missing_module(step_with_io):
    """
    Test _generate_verilog returns an error when generated Verilog lacks the 'module' keyword.
    """
    step_with_io.setup()
    with patch(
        'hagent.step.v2chisel_fix.v2chisel_fix.Chisel2v.setup', return_value=True
    ), patch(
        'hagent.step.v2chisel_fix.v2chisel_fix.Chisel2v.generate_verilog', return_value='// No mod keyword here'
    ):
        bad_out, bad_err = step_with_io._generate_verilog('some code', 'shared_dir')
        assert bad_out is None
        assert "missing 'module' keyword" in bad_err


def test_generate_verilog_exception(step_with_io):
    """
    Test _generate_verilog catches an exception from c2v.generate_verilog.
    """
    step_with_io.setup()

    with (
        patch('hagent.step.v2chisel_fix.v2chisel_fix.Chisel2v.setup', return_value=True),
        patch('hagent.step.v2chisel_fix.v2chisel_fix.Chisel2v.generate_verilog', side_effect=RuntimeError('some c2v error')),
    ):
        out, err = step_with_io._generate_verilog('class MyModule extends Module{}', 'shared')
        assert out is None
        assert 'some c2v error' in err


def test_check_equivalence_ok(step_with_io):
    """
    Test _check_equivalence when equivalence returns True.
    """
    step_with_io.setup()

    with patch('hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check') as meq:
        eqinst = MagicMock()
        meq.return_value = eqinst
        eqinst.setup.return_value = True
        eqinst.check_equivalence.return_value = True

        iseq, lec_err = step_with_io._check_equivalence('module gold(); endmodule', 'module ref(); endmodule')
        assert iseq is True
        assert lec_err is None


def test_check_equivalence_false(step_with_io):
    """
    Test _check_equivalence when equivalence returns False and a counterexample is provided.
    """
    step_with_io.setup()
    with patch('hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check') as meq:
        eqinst = MagicMock()
        meq.return_value = eqinst
        eqinst.setup.return_value = True
        eqinst.check_equivalence.return_value = False
        eqinst.get_counterexample.return_value = 'Counterexample found'

        iseq, lec_err = step_with_io._check_equivalence('module gold(); endmodule', 'module ref(); endmodule')
        assert iseq is False
        assert 'Counterexample found' in lec_err


def test_check_equivalence_none_result(step_with_io):
    """
    Test _check_equivalence when the equivalence check returns None.
    """
    step_with_io.setup()
    with patch('hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check') as meq:
        eqinst = MagicMock()
        meq.return_value = eqinst
        eqinst.setup.return_value = True
        eqinst.check_equivalence.return_value = None
        eqinst.get_error.return_value = 'LEC result is None'

        iseq, lec_err = step_with_io._check_equivalence('module gold();', 'module ref();')
        assert iseq is False
        assert 'LEC result is None' in lec_err


def test_check_equivalence_exception(step_with_io):
    """
    Test _check_equivalence when an exception is thrown.
    """
    step_with_io.setup()
    with patch('hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check') as meq:
        eqinst = MagicMock()
        meq.return_value = eqinst
        eqinst.setup.return_value = True
        eqinst.check_equivalence.side_effect = RuntimeError('Oops LEC')

        iseq, lec_err = step_with_io._check_equivalence('module gold();', 'module ref();')
        assert iseq is False
        assert 'Oops LEC' in lec_err


def test_check_equivalence_missing_code(step_with_io):
    """
    Test _check_equivalence when gold or reference code is missing.
    """
    step_with_io.setup()
    iseq, lec_err = step_with_io._check_equivalence('', 'module something();')
    assert iseq is False
    assert 'Missing code' in lec_err


def test_strip_markdown_fences(step_with_io):
    """
    Test that markdown fences (with optional language tags) are removed.
    """
    step_with_io.setup()
    text = """```scala
class Foo extends Module {}
```"""
    out = step_with_io._strip_markdown_fences(text)
    assert '```' not in out
    assert 'scala' not in out
    assert 'class Foo extends Module' in out


def test_setup_no_prompt3_warning(tmp_path):
    """
    Test that a warning is printed when 'prompt3.yaml' is not found,
    and that refine_llm remains None.
    """
    content = """\
chisel_pass1:
  chisel_changed: |
    class MyModule extends Module {
      val io = IO(new Bundle {})
    }
  verilog_candidate: |
    module mymodule();
    endmodule
  was_valid: true

verilog_fixed: |
  module mymodule();
  // new changes
  endmodule

llm:
  model: "test-model"
"""
    input_file = tmp_path / 'input_no_prompt3.yaml'
    input_file.write_text(content)

    step_obj = V2ChiselFix()
    out_file = tmp_path / 'output_no_prompt3.yaml'
    step_obj.set_io(inp_file=str(input_file), out_file=str(out_file))

    with patch('hagent.step.v2chisel_fix.v2chisel_fix.os.path.exists', return_value=False), \
         patch('builtins.print') as mock_print:
        step_obj.setup()
        mock_print.assert_any_call('[WARN] prompt3.yaml not found, cannot refine if LEC fails.')
        assert step_obj.refine_llm is None


def test_run_missing_verilog_fixed(step_with_io, tmp_path):
    """
    Test that if 'verilog_fixed' is missing the LEC check is skipped.
    """
    input_data = {
        'chisel_pass1': {
            'chisel_changed': 'class MyModule extends Module { val io = IO(new Bundle {}) }',
            'verilog_candidate': 'module mymodule(); endmodule',
            'was_valid': True,
        },
        # 'verilog_fixed' is missing
        'llm': {'model': 'test-model'},
    }

    with patch('hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check') as mock_eq, \
         patch('builtins.print') as mock_print:
        step_with_io.setup()
        res = step_with_io.run(input_data)
        mock_print.assert_any_call("[WARN] No 'verilog_fixed' in input. Skipping initial LEC check.")
        assert 'chisel_fixed' in res
        cf = res['chisel_fixed']
        assert cf['equiv_passed'] is False
        assert cf['refined_chisel'] == 'class MyModule extends Module { val io = IO(new Bundle {}) }'
        assert cf.get('verilog_candidate') is None
        mock_eq.assert_not_called()


def test_run_equiv_check_setup_failure(step_with_io):
    """
    Test that if Equiv_check.setup() fails, an error is printed and equivalence check fails.
    """
    import hagent.step.v2chisel_fix.v2chisel_fix as v2chisel_fix_module
    module_dir = os.path.dirname(os.path.abspath(v2chisel_fix_module.__file__))
    prompt3_path = os.path.join(module_dir, 'prompt3.yaml')

    with open(prompt3_path, 'w') as f:
        f.write("""\
- role: system
  content: "Refinement system message"
""")
    try:
        step_with_io.setup()
        with patch('hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check') as mock_eq, \
             patch('builtins.print') as mock_print:
            mock_eq_inst = MagicMock()
            mock_eq_inst.setup.return_value = False
            mock_eq_inst.get_error.return_value = 'Yosys not found'
            mock_eq.return_value = mock_eq_inst

            res = step_with_io.run({
                'chisel_pass1': {
                    'chisel_changed': 'class MyModule extends Module { val io = IO(new Bundle {}) }',
                    'verilog_candidate': 'module mymodule(); endmodule',
                    'was_valid': True,
                },
                'verilog_fixed': 'module mymodule(); // fixed changes endmodule',
                'llm': {'model': 'test-model'},
            })
            mock_print.assert_any_call('[ERROR] Equiv_check setup failed: Yosys not found')
            cf = res['chisel_fixed']
            assert cf['equiv_passed'] is False
            assert cf['refined_chisel'] == 'class MyModule extends Module { val io = IO(new Bundle {}) }'
            assert cf.get('verilog_candidate') is None
    finally:
        if os.path.exists(prompt3_path):
            os.remove(prompt3_path)


def test_refine_chisel_code_empty_after_strip(step_with_io):
    """
    Test that if LLM returns code that is empty after stripping markdown fences,
    the original code is kept.
    """
    import hagent.step.v2chisel_fix.v2chisel_fix as fix_mod
    module_dir = os.path.dirname(os.path.abspath(fix_mod.__file__))
    prompt3_path = os.path.join(module_dir, 'prompt3.yaml')

    with open(prompt3_path, 'w') as f:
        f.write("""\
- role: system
  content: "Refinement system message"
""")
    try:
        step_with_io.setup()
        # Set required attributes.
        step_with_io.chisel_original = 'class MyModule extends Module {}'
        step_with_io.chisel_subset = 'class MyModule extends Module {}'
        with patch.object(step_with_io.refine_llm, 'chat', return_value='```chisel\n\n```'), \
             patch('builtins.print') as mock_print:
            original_code = 'class MyModule extends Module { val io = IO(new Bundle {}) }'
            refined_code = step_with_io._refine_chisel_code(original_code, 'Some LEC error')
            mock_print.assert_any_call('[ERROR] After removing markdown fences, code is empty. Keeping old code.')
            assert refined_code == original_code
    finally:
        if os.path.exists(prompt3_path):
            os.remove(prompt3_path)


def test_generate_verilog_setup_failure(step_with_io):
    """
    Test that _generate_verilog returns (None, error_message) when Chisel2v.setup() fails.
    """
    step_with_io.setup()

    from hagent.tool.chisel2v import Chisel2v

    mock_c2v = MagicMock(spec=Chisel2v)
    mock_c2v.setup.return_value = False
    mock_c2v.error_message = 'Chisel2v setup failed due to missing dependencies.'

    with patch('hagent.step.v2chisel_fix.v2chisel_fix.Chisel2v', return_value=mock_c2v):
        verilog_output, error = step_with_io._generate_verilog('class MyModule extends Module {}', 'shared_dir')
        assert verilog_output is None
        assert error == 'Chisel2v setup failed due to missing dependencies.'


def test_generate_verilog_missing_module_keyword(step_with_io):
    """
    Test that _generate_verilog returns an error when generated Verilog lacks 'module' keyword.
    """
    step_with_io.setup()

    with (
        patch('hagent.step.v2chisel_fix.v2chisel_fix.Chisel2v.setup', return_value=True),
        patch('hagent.step.v2chisel_fix.v2chisel_fix.Chisel2v.generate_verilog', return_value='// No mod keyword here'),
        patch('builtins.print') as mock_print,
    ):
        verilog_output, error = step_with_io._generate_verilog('class MyModule extends Module {}', 'shared_dir')
        assert verilog_output is None
        assert error == "Generated Verilog missing 'module' keyword."


def test_refinement_with_verilog_generation_failure(step_with_io, tmp_path):
    """
    Test the case where Verilog generation fails during refinement.
    """
    step_with_io.setup()
    step_with_io.lec_limit = 3  # Allow multiple iterations

    step_with_io.refine_llm = MagicMock()
    step_with_io.refine_llm.chat.return_value = 'refined Chisel code'

    mock_eq_inst = MagicMock()
    mock_eq_inst.setup.return_value = True
    mock_eq_inst.check_equivalence.return_value = (False, 'LEC mismatch')  # Initial LEC failure

    def mock_generate_verilog(chisel_code, shared_dir):
        if 'refined' in chisel_code:
            return (None, 'Chisel2v failed')
        return ('module valid_verilog(); endmodule', None)

    with (
        patch('hagent.core.step.yaml.dump', return_value=None),
        patch('hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check', return_value=mock_eq_inst),
        patch.object(step_with_io.refine_llm, 'chat', side_effect=lambda pd: 'refined Chisel code'),
        patch.object(step_with_io, '_generate_verilog', side_effect=mock_generate_verilog),
        patch('builtins.print') as mock_print,
    ):
        input_data = {
            'chisel_pass1': {'chisel_changed': 'initial Chisel code', 'verilog_candidate': 'initial Verilog', 'was_valid': True},
            'verilog_fixed': 'module fixed_verilog(); endmodule',
        }
        res = step_with_io.run(input_data)
        mock_print.assert_any_call('[ERROR] Verilog generation failed on iteration 1: Chisel2v failed')
        cf = res['chisel_fixed']
        assert cf['equiv_passed'] is False
        assert 'refined Chisel code' in cf['refined_chisel']


def test_successful_verilog_generation_no_error(step_with_io):
    """
    Test that _generate_verilog returns (verilog_output, None) on a successful run.
    """
    step_with_io.setup()

    with (
        patch('hagent.step.v2chisel_fix.v2chisel_fix.Chisel2v.setup', return_value=True),
        patch('hagent.step.v2chisel_fix.v2chisel_fix.Chisel2v.generate_verilog', return_value='module successful_verilog(); endmodule'),
    ):
        verilog_output, error = step_with_io._generate_verilog('class MyModule extends Module {}', 'shared_dir')
        assert verilog_output == 'module successful_verilog(); endmodule'
        assert error is None


def test_setup_prompt3_exists_but_empty_llm_config(tmp_path):
    """
    If prompt3.yaml exists and the 'llm' config is empty, warn and set refine_llm to None.
    """
    import sys
    from hagent.step.v2chisel_fix.v2chisel_fix import V2ChiselFix

    module = sys.modules[V2ChiselFix.__module__]
    class_dir = os.path.dirname(os.path.abspath(module.__file__))
    prompt3_path = os.path.join(class_dir, 'prompt3.yaml')
    prompt3_contents = """\
messages:
  - role: system
    content: "This is prompt3 for refinement."
"""
    with open(prompt3_path, 'w') as f:
        f.write(prompt3_contents)

    try:
        content = """\
chisel_pass1:
  chisel_changed: |
    class MyModule extends Module { val io = IO(new Bundle {}) }
  verilog_candidate: |
    module mymodule();
    endmodule
  was_valid: true

verilog_fixed: |
  module mymodule();
  endmodule

llm: {}
"""
        input_file = tmp_path / 'input_empty_llm.yaml'
        input_file.write_text(content)

        step_obj = V2ChiselFix()
        out_file = tmp_path / 'output_empty_llm.yaml'
        step_obj.set_io(inp_file=str(input_file), out_file=str(out_file))

        with patch('builtins.print') as mock_print:
            step_obj.setup()
            mock_print.assert_any_call("[WARN] prompt3.yaml found but no 'llm' config. Can't refine automatically.")
            assert step_obj.refine_llm is None
    finally:
        if os.path.exists(prompt3_path):
            os.remove(prompt3_path)


def test_generate_verilog_success(step_with_io):
    """
    Test that _generate_verilog returns (verilog_output, None) on a successful run.
    """
    step_with_io.setup()

    with (
        patch('hagent.step.v2chisel_fix.v2chisel_fix.Chisel2v.setup', return_value=True),
        patch('hagent.step.v2chisel_fix.v2chisel_fix.Chisel2v.generate_verilog', return_value='module successful(); endmodule'),
    ):
        verilog_output, error = step_with_io._generate_verilog('class MyModule extends Module {}', 'shared_dir')
        assert verilog_output == 'module successful(); endmodule'
        assert error is None
