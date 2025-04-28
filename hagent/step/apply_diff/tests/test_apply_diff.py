import pytest
from hagent.step.apply_diff.apply_diff import Apply_diff

# A simple unified diff that replaces a single line
SIMPLE_DIFF = '''@@ -1,2 +1,2 @@
- val a = 1
+ val a = 42
'''

# Original Chisel code snippet
ORIGINAL_CODE = '''val a = 1
val b = 2
'''


def test_apply_diff_replaces_line():
    data = {
        'chisel_original': ORIGINAL_CODE,
        'generated_diff': SIMPLE_DIFF
    }
    step = Apply_diff()
    # Provide dummy IO so setup() succeeds but skip file reading
    step.set_io('', 'dummy_output.yaml')
    step.input_data = data.copy()
    step.setup()
    out = step.run(data.copy())
    candidate = out.get('chisel_candidate')
    # Check that the replacement occurred
    assert 'val a = 42' in candidate
    # Ensure unchanged lines still present
    assert 'val b = 2' in candidate


def test_apply_diff_empty_diff():
    data = {
        'chisel_original': ORIGINAL_CODE,
        'generated_diff': ''
    }
    step = Apply_diff()
    step.set_io('', 'dummy_output.yaml')
    step.input_data = data.copy()
    step.setup()
    out = step.run(data.copy())
    candidate = out.get('chisel_candidate')
    # No diff → original code unchanged
    assert candidate == ORIGINAL_CODE.strip()


def test_apply_diff_invalid_diff():
    invalid_diff = '''@@ -10,2 +10,2 @@
- non_existent_line
+ new_line
'''
    data = {
        'chisel_original': ORIGINAL_CODE,
        'generated_diff': invalid_diff
    }
    step = Apply_diff()
    step.set_io('', 'dummy_output.yaml')
    step.input_data = data.copy()
    step.setup()
    out = step.run(data.copy())
    candidate = out.get('chisel_candidate')
    # Invalid diff → original code unchanged
    assert candidate == ORIGINAL_CODE.strip()

