from hagent.core.step import Step
from hagent.tool.metadata_mapper import MetadataMapper
from hagent.tool.extract_verilog_diff_keywords import Extract_verilog_diff_keywords
from hagent.tool.fuzzy_grep import Fuzzy_grep
from hagent.tool.code_scope import Code_scope
from typing import Optional


class Extract_hints(Step):
    """
    Step to extract Chisel hint snippets using metadata comments or fuzzy-grep.

    Reads from:
      - verilog_diff
      - chisel_original
      - optional: threshold (int)
    Emits:
      - hints: str
    """

    def __init__(self, metadata_context: Optional[int] = None):
        super().__init__()
        # optional override from agent
        self._meta = metadata_context

    def setup(self):
        super().setup()
        # Initialize metadata mapper with original/fixed Verilog
        self.metadata_mapper = MetadataMapper(
            self.input_data.get('verilog_original', ''), self.input_data.get('verilog_fixed', '')
        )
        # Default fuzzy-grep threshold
        self.threshold = self.input_data.get('threshold', 80)
        self.metadata_context = self._meta if self._meta is not None else self.input_data.get('metadata_context', 10)
        self.setup_called = True

    def run(self, data):
        verilog_diff = data.get('verilog_diff', '')
        chisel_original = data.get('chisel_original', '')

        # First try metadata-driven hints (with before/after context)
        pointers = self.metadata_mapper.pointers_for_diff(verilog_diff)
        if pointers:
            # same defaults as your monolithic version
            before = 5
            # after  = data.get('metadata_context', 10)
            after = self.metadata_context
            snippet = self.metadata_mapper.slice_chisel_by_pointers(chisel_original, pointers, before=before, after=after)
            # if metadata snippet actually has “→” lines, use it:
            if any(line.startswith('->') and line.split(':', 1)[1].strip() for line in snippet.splitlines()):
                hints = snippet
            else:
                # fallback to fuzzy
                hints = ''
        else:
            # Fallback to fuzzy-grep
            keywords = Extract_verilog_diff_keywords.get_user_variables(verilog_diff)
            fg = Fuzzy_grep()
            fg.setup('chisel')
            results = fg.search(text=chisel_original, search_terms=keywords, threshold=self.threshold)
            hints = ''
            if 'text' in results:
                lines = [pair[0] for pair in results['text']]
                cs = Code_scope(chisel_original)
                scopes = cs.find_nearest_upper_scopes(lines)
                for start, end in scopes:
                    hints += f'Code snippet from {start} to {end}:\n'
                    hints += cs.get_code((start, end), lines, '->')
                    hints += '\n\n'

        data['hints'] = hints
        return data
