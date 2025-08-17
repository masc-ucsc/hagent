import pytest

# Monkeypatch LLM_template and LLM_wrap inside generate_diff module
import hagent.step.generate_diff.generate_diff as gen_mod
from hagent.step.generate_diff.generate_diff import Generate_diff


class DummyTemplate:
    def __init__(self, conf_file):
        # Simulate the loaded YAML structure
        self.template_dict = {
            'v2chisel_pass1': {
                'prompt0': [
                    {'role': 'system', 'content': 'System prompt'},
                    {'role': 'user', 'content': 'User prompt: {verilog_diff}, {chisel_original}, {hints}, {error_msg}'},
                ]
            }
        }


class DummyWrap:
    def __init__(self, name, log_file, conf_file, overwrite_conf):
        self.last_error = None
        self.chat_template = None
        self.prompt_dicts = []

    def inference(self, prompt_dict, prompt_index, n):
        # Record call for inspection
        self.prompt_dicts.append((prompt_dict, prompt_index, n))
        # Return a Markdown-fenced diff
        return [
            """
--- a/file.scala
+++ b/file.scala
@@ -1 +1 @@
-foo
+bar
"""
        ]


@pytest.fixture(autouse=True)
def patch_llm(monkeypatch):
    monkeypatch.setattr(gen_mod, 'LLM_template', DummyTemplate)
    monkeypatch.setattr(gen_mod, 'LLM_wrap', DummyWrap)


def test_generate_diff_success():
    data = {
        'verilog_diff': 'dummy diff',
        'chisel_original': 'dummy chisel code',
        'hints': 'dummy hints',
        'error_msg': 'previous error',
    }
    step = Generate_diff()
    # Provide dummy IO so setup() succeeds
    step.set_io('', 'dummy_out.yaml')
    step.input_data = {}
    step.setup()
    out = step.run(data.copy())
    assert 'generated_diff' in out
    # Should strip fences
    gen = out['generated_diff']
    assert gen.startswith('--- a/file.scala')
    # Ensure removed content present
    assert '-foo' in gen
    # Ensure added content present
    assert '+bar' in gen


def test_generate_diff_empty_response(monkeypatch):
    # Monkeypatch inference to return empty list
    def empty_inference(self, prompt_dict, prompt_index, n):
        return []

    monkeypatch.setattr(DummyWrap, 'inference', empty_inference)

    data = {'verilog_diff': 'diff', 'chisel_original': 'code', 'hints': 'hints', 'error_msg': ''}
    step = Generate_diff()
    step.set_io('', 'dummy_out.yaml')
    step.input_data = {}
    step.setup()
    out = step.run(data.copy())
    # generated_diff exists but is empty
    assert 'generated_diff' in out
    assert out['generated_diff'] == ''
