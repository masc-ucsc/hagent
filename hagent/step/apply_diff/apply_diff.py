from hagent.core.step import Step
from hagent.tool.chisel_diff_applier import ChiselDiffApplier

class Apply_diff(Step):
    """
    Applies a unified diff to Chisel source code.

    Reads from:
      - chisel_original: str
      - generated_diff: str
    Emits:
      - chisel_candidate: str
    """
    def setup(self):
        super().setup()
        self.applier = ChiselDiffApplier()
        self.setup_called = True

    def run(self, data):
        original = data.get('chisel_original', '')
        diff_text = data.get('generated_diff', '')
        # Apply the diff to produce updated candidate
        candidate = self.applier.apply_diff(diff_text, original)
        data['chisel_candidate'] = candidate
        return data
