# hagent/step/apply_diff/tests/test_apply_diff.py
import pytest

from hagent.step.apply_diff.apply_diff import Apply_diff
from hagent.tool.chisel_diff_applier import ChiselDiffApplier

@pytest.fixture(autouse=True)
def dummy_setup_and_error(monkeypatch):
    # Replace setup() so it only initializes the applier
    def fake_setup(self):
        self.applier = ChiselDiffApplier()
        self.setup_called = True
    monkeypatch.setattr(Apply_diff, "setup", fake_setup)
    # Replace error() to raise instead of exiting
    def fake_error(self, msg):
        raise ValueError(msg)
    monkeypatch.setattr(Apply_diff, "error", fake_error)

def test_apply_diff_success(monkeypatch):
    orig = "foo\nbar\n"
    # simple unified diff: remove "foo", add "baz"
    diff_text = """---
+++ 
@@ -1,2 +1,2 @@
-foo
+baz
 bar
"""
    # stub actual apply_diff to replace foo→baz
    monkeypatch.setattr(
        ChiselDiffApplier, "apply_diff",
        lambda self, diff, original: original.replace("foo", "baz")
    )

    step = Apply_diff()
    step.setup()
    data = {
        "chisel_original": orig,
        "generated_diff": diff_text
    }
    out = step.run(data)

    # candidate should have baz instead of foo
    assert out["chisel_candidate"] == "baz\nbar\n"
    assert out["apply_diff_ok"] is True

def test_apply_diff_fails_on_missing_removal(monkeypatch):
    orig = "foo\nbar\n"
    # removal "qux" not in original
    diff_text = "-qux\n+new\n"
    # stub apply_diff to just return original
    monkeypatch.setattr(
        ChiselDiffApplier, "apply_diff",
        lambda self, diff, original: original
    )

    step = Apply_diff()
    step.setup()
    data = {
        "chisel_original": orig,
        "generated_diff": diff_text
    }
    with pytest.raises(ValueError) as exc:
        step.run(data)
    assert "removal not in original: 'qux'" in str(exc.value)

def test_apply_diff_fails_on_missing_addition(monkeypatch):
    orig = "foo\nbar\n"
    # removal foo is in original, addition "new" but we stub apply_diff to leave it out
    diff_text = "-foo\n+new\n"
    monkeypatch.setattr(
        ChiselDiffApplier, "apply_diff",
        lambda self, diff, original: original.replace("foo", "")  # removes foo, but never adds "new"
    )

    step = Apply_diff()
    step.setup()
    data = {
        "chisel_original": orig,
        "generated_diff": diff_text
    }
    with pytest.raises(ValueError) as exc:
        step.run(data)
    assert "addition not in candidate: 'new'" in str(exc.value)
