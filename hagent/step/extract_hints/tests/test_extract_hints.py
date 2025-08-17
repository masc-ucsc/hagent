import pytest
from hagent.step.extract_hints.extract_hints import Extract_hints

# Sample data for metadata test
DIFF_WITH_META = """
@@ -1 +1 @@
 // src/main/scala/Test.scala:3
"""
CHISEL_CODE = """
line1
line2
line3: important code
line4
line5
"""


# Fake classes for fuzzy fallback
class DummyFuzzy:
    def __init__(self):
        self.error_message = ''

    def setup(self, lang):
        return True

    def search(self, text, search_terms, threshold):
        return {'text': [(2, 'line3: important code')]}


class DummyCS:
    def __init__(self, code):
        pass

    def find_nearest_upper_scopes(self, lines):
        return [(2, 3)]

    def get_code(self, scope_pair, hint_list, marker):
        return 'SNIPPET'


@pytest.fixture(autouse=True)
def patch_tools(monkeypatch):
    # Monkeypatch Fuzzy_grep and Code_scope for fallback
    import hagent.step.extract_hints.extract_hints as mod

    monkeypatch.setattr(mod, 'Fuzzy_grep', DummyFuzzy)
    monkeypatch.setattr(mod, 'Code_scope', DummyCS)


def test_extract_hints_metadata():
    data = {'verilog_original': '', 'verilog_fixed': '', 'verilog_diff': DIFF_WITH_META, 'chisel_original': CHISEL_CODE}
    step = Extract_hints()
    step.set_io('', 'dummy_out.yaml')
    step.input_data = data.copy()
    step.setup()
    out = step.run(data.copy())
    hints = out.get('hints', '')
    # Should reference the Test.scala file
    assert 'Test.scala' in hints
    # Should include the important code line
    assert 'important code' in hints
    # Should mark at least one line with arrow
    assert '->' in hints


def test_extract_hints_fuzzy():
    data = {
        'verilog_original': '',
        'verilog_fixed': '',
        'verilog_diff': 'no metadata comments here',
        'chisel_original': CHISEL_CODE,
    }
    step = Extract_hints()
    step.set_io('', 'dummy_out.yaml')
    step.input_data = data.copy()
    step.setup()
    out = step.run(data.copy())
    hints = out.get('hints', '')
    # Should come from DummyCS.get_code output
    assert 'SNIPPET' in hints
