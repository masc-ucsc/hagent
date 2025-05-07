from hagent.core.step import Step
from hagent.tool.chisel_diff_applier import ChiselDiffApplier

class Apply_diff(Step):
    """
    Applies a unified diff to Chisel source code and verifies by checking removal/addition lines.

    Reads:
      - chisel_original: str
      - generated_diff:  str
    Emits:
      - chisel_candidate: str
      - apply_diff_ok:    bool
    """
    def setup(self):
        super().setup()
        self.applier = ChiselDiffApplier()
        self.setup_called = True

    def run(self, data):
        original  = data.get('chisel_original', '')
        diff_text = data.get('generated_diff', '')

        # Apply the diff
        candidate = self.applier.apply_diff(diff_text, original)
        data['chisel_candidate'] = candidate

        # Parse removal (+) and addition (-) lines from the diff
        removals, additions = [], []
        for line in diff_text.splitlines():
            if line.startswith('---') or line.startswith('+++') or line.startswith('@@'):
                continue
            if line.startswith('-'):
                removals.append(line[1:].strip())
            elif line.startswith('+'):
                additions.append(line[1:].strip())
        
        # DEBUG: print both diffs for inspection
        print("=== apply_diff: input diff ===")
        print(diff_text)
        print("=== apply_diff: recomputed diff ===")
        print(diff_text)

        # Verify each removal existed in original, and each addition appears in candidate
        for rem in removals:
            if rem not in original:
                self.error(f"apply_diff verification failed: removal not in original: '{rem}'")
        for add in additions:
            if add not in candidate:
                self.error(f"apply_diff verification failed: addition not in candidate: '{add}'")

        # If we reach here, verification passed
        data['apply_diff_ok'] = True
        return data
