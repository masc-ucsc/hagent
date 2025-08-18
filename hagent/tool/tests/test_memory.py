# test/test_memory.py

import unittest
import uuid
import datetime
from pathlib import Path
from hagent.tool.memory import FewShotMemory, Memory_shot


class TestFewShotMemory(unittest.TestCase):
    def setUp(self):
        # Use a unique directory to avoid polluting the real DB
        test_id = f'{datetime.datetime.now().strftime("%Y%m%d_%H%M%S")}_{uuid.uuid4().hex[:8]}'
        self.temp_dir = Path('output') / 'test_memory' / test_id
        self.temp_dir.mkdir(parents=True, exist_ok=True)
        self.memory = FewShotMemory(learn=True, db_path=str(self.temp_dir))

        # Add related Verilog snippets
        self.memory.add(
            error_type='syntax_error',
            fix=Memory_shot(
                question='always @(posedge clk) begin if (rst) q <= 0; else q <= d; end', answer='Flip1-flop with async reset'
            ),
        )
        self.memory.add(
            error_type='syntax_error2',
            fix=Memory_shot(
                question='always @(posedge clk) begin if (!rst_n) q <= 0; else q <= d; end',
                answer='Flip2-flop with active-low reset',
            ),
        )
        self.memory.add(
            error_type='syntax_error', fix=Memory_shot(question='assign q = d;', answer='Simple combinational assignment')
        )
        self.memory.add(error_type='syntax_error3', fix=Memory_shot(question='potato;', answer='Anything match'))

    def tearDown(self):
        # Leave directories for inspection - they will be in output/
        pass

    def test_similar_snippet_retrieval(self):
        query_snippet = 'always @(posedge clk) begin if (!rst_n) q <= 0; else q <= d_in; end'
        results = self.memory.find(error_type='syntax_error', fix_question=query_snippet, n_results=4)
        self.assertTrue(any('Flip1-flop' in r.answer for r in results), 'Expected flip-flop related sample')

    def test_match_anything_if_needed(self):
        query_snippet = 'always @(posedge clk) begin if (!rst_n) q <= 0; else q <= d_in; end'
        results = self.memory.find(error_type='syntax_error3', fix_question=query_snippet, n_results=2)
        self.assertEqual(len(results), 1)
        self.assertTrue('Anything' in results[0].answer, 'Expected nothing but Anything')


if __name__ == '__main__':
    unittest.main()
