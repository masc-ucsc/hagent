#!/usr/bin/env python3
"""Unit tests for ChiselDiffCorrector"""

import unittest
from hagent.tool.chisel_diff_corrector import ChiselDiffCorrector


class TestChiselDiffCorrector(unittest.TestCase):
    def setUp(self):
        self.corrector = ChiselDiffCorrector(confidence_threshold=0.90)

    def test_no_removal_lines(self):
        """Test diff with only additions (no corrections needed)"""
        diff = """--- a/test.scala
+++ b/test.scala
@@ -1,3 +1,4 @@
 val x = 5
+val y = 10
 val z = 15
"""
        hints = 'val x = 5\nval z = 15'

        result = self.corrector.correct_diff(diff, hints)

        self.assertTrue(result['success'])
        self.assertEqual(result['corrections_made'], 0)
        self.assertFalse(result['is_ambiguous'])
        # Corrected diff should be semantically the same (minor formatting differences ok)
        self.assertIn('val x = 5', result['corrected_diff'])
        self.assertIn('+val y = 10', result['corrected_diff'])

    def test_exact_match_no_correction_needed(self):
        """Test diff where removal lines already match hints exactly"""
        diff = """--- a/test.scala
+++ b/test.scala
@@ -1,4 +1,4 @@
 val x = 5
-val y = 10
+val y = 20
 val z = 15
"""
        hints = 'val x = 5\nval y = 10\nval z = 15'

        result = self.corrector.correct_diff(diff, hints)

        self.assertTrue(result['success'])
        # Even exact matches are "corrected" (confirmed to use exact hint line)
        self.assertEqual(result['corrections_made'], 1)
        self.assertFalse(result['is_ambiguous'])
        # The removal line should still be the exact hint line
        self.assertIn('-val y = 10', result['corrected_diff'])

    def test_whitespace_normalization(self):
        """Test correction with different whitespace"""
        diff = """--- a/test.scala
+++ b/test.scala
@@ -1,4 +1,4 @@
 val x = 5
-val y=10
+val y = 20
 val z = 15
"""
        hints = 'val x = 5\nval y  =  10\nval z = 15'

        result = self.corrector.correct_diff(diff, hints)

        self.assertTrue(result['success'])
        self.assertEqual(result['corrections_made'], 1)
        self.assertIn('val y  =  10', result['corrected_diff'])  # Should use exact hint line

    def test_operator_normalization(self):
        """Test correction with normalized operators"""
        diff = """--- a/test.scala
+++ b/test.scala
@@ -1,4 +1,4 @@
 when (cond) {
-  io.out:=5.U
+  io.out := 10.U
 }
"""
        hints = 'when (cond) {\n  io.out  :=  5.U\n}'

        result = self.corrector.correct_diff(diff, hints)

        self.assertTrue(result['success'])
        self.assertEqual(result['corrections_made'], 1)
        self.assertIn('io.out  :=  5.U', result['corrected_diff'])

    def test_comment_handling(self):
        """Test that comments are ignored in matching"""
        diff = """--- a/test.scala
+++ b/test.scala
@@ -1,4 +1,4 @@
 val x = 5
-val y = 10
+val y = 20
 val z = 15
"""
        hints = 'val x = 5\nval y = 10  // old value\nval z = 15'

        result = self.corrector.correct_diff(diff, hints)

        self.assertTrue(result['success'])
        self.assertEqual(result['corrections_made'], 1)
        self.assertIn('val y = 10  // old value', result['corrected_diff'])

    def test_ambiguous_identical_lines(self):
        """Test detection of ambiguous removal lines (multiple identical matches)"""
        diff = """--- a/test.scala
+++ b/test.scala
@@ -1,4 +1,4 @@
-io.result := 0.U
+io.result := 5.U
"""
        hints = """io.result := 0.U
when (cond) {
  io.result := 0.U
}
otherwise {
  io.result := 0.U
}"""

        result = self.corrector.correct_diff(diff, hints)

        self.assertFalse(result['success'])  # Ambiguous, needs clarification
        self.assertTrue(result['is_ambiguous'])
        self.assertEqual(len(result['ambiguous_lines']), 1)
        self.assertEqual(len(result['ambiguous_lines'][0]['matches']), 3)  # 3 matches

    def test_no_match_found(self):
        """Test when removal line doesn't exist in hints"""
        diff = """--- a/test.scala
+++ b/test.scala
@@ -1,4 +1,4 @@
-val nonexistent = 99
+val y = 20
"""
        hints = 'val x = 5\nval z = 15'

        result = self.corrector.correct_diff(diff, hints)

        self.assertFalse(result['success'])
        self.assertEqual(len(result['no_match_lines']), 1)
        self.assertIn('val nonexistent = 99', result['no_match_lines'])

    def test_unique_match_correction(self):
        """Test successful correction with unique fuzzy match"""
        diff = """--- a/test.scala
+++ b/test.scala
@@ -1,5 +1,5 @@
 when (io.funct7==="b0000000".U) {
-  io.result:=io.operand1+io.operand2
+  io.result := io.operand1 - io.operand2
 }
"""
        hints = """when (io.funct7 === "b0000000".U) {
  io.result  :=  io.operand1  +  io.operand2  // ADD operation
}"""

        result = self.corrector.correct_diff(diff, hints)

        self.assertTrue(result['success'])
        self.assertEqual(result['corrections_made'], 1)
        # Should preserve exact hint formatting
        self.assertIn('io.result  :=  io.operand1  +  io.operand2  // ADD operation', result['corrected_diff'])

    def test_multiple_hunks(self):
        """Test diff with multiple hunks"""
        diff = """--- a/test.scala
+++ b/test.scala
@@ -1,4 +1,4 @@
 val x = 5
-val y=10
+val y = 20
 val z = 15
@@ -10,4 +10,4 @@
 when (cond) {
-  io.out:=5.U
+  io.out := 10.U
 }
"""
        hints = 'val x = 5\nval y  =  10\nval z = 15\nwhen (cond) {\n  io.out  :=  5.U\n}'

        result = self.corrector.correct_diff(diff, hints)

        self.assertTrue(result['success'])
        self.assertEqual(result['corrections_made'], 2)
        self.assertIn('val y  =  10', result['corrected_diff'])
        self.assertIn('io.out  :=  5.U', result['corrected_diff'])

    def test_confidence_threshold(self):
        """Test that confidence threshold affects matching"""
        diff = """--- a/test.scala
+++ b/test.scala
@@ -1,4 +1,4 @@
-completely different line xyz
+new line
"""
        hints = 'val x = 5\nval y = 10'

        # High threshold should not match
        corrector_high = ChiselDiffCorrector(confidence_threshold=0.95)
        result = corrector_high.correct_diff(diff, hints)

        self.assertFalse(result['success'])
        self.assertEqual(len(result['no_match_lines']), 1)

    def test_normalize_for_matching(self):
        """Test the normalization function directly"""
        # Test whitespace normalization
        normalized = self.corrector._normalize_for_matching('val   x   =   5')
        self.assertEqual(normalized, 'val x = 5')

        # Test operator normalization
        normalized = self.corrector._normalize_for_matching('io.out:=5.U')
        self.assertEqual(normalized, 'io.out := 5.U')

        # Test comment removal
        normalized = self.corrector._normalize_for_matching('val x = 5 // comment')
        self.assertNotIn('comment', normalized)

        # Test punctuation normalization (spaces collapse)
        normalized = self.corrector._normalize_for_matching('when ( cond ) { }')
        self.assertEqual(normalized, 'when(cond){}')  # Spaces inside braces are collapsed

    def test_extract_signature(self):
        """Test signature extraction for similarity calculation"""
        sig = self.corrector._extract_signature('when (io.funct7 === "b0000000".U) {')

        # Should extract meaningful tokens
        self.assertIn('when', sig)
        self.assertIn('io', sig)
        self.assertIn('funct7', sig)
        self.assertIn('===', sig)
        self.assertIn('b0000000', sig)

        # Should not extract very short tokens
        self.assertNotIn('U', sig)

    def test_calculate_similarity(self):
        """Test similarity calculation"""
        line1 = 'io.result := io.operand1 + io.operand2'
        line2 = 'io.result  :=  io.operand1  +  io.operand2  // comment'

        similarity = self.corrector._calculate_similarity(
            self.corrector._normalize_for_matching(line1), self.corrector._normalize_for_matching(line2)
        )

        # Should be very high (almost 1.0) for same semantic content
        self.assertGreater(similarity, 0.9)

    def test_real_world_chisel_example(self):
        """Test with realistic Chisel code example"""
        diff = """--- a/src/main/scala/ALU.scala
+++ b/src/main/scala/ALU.scala
@@ -15,7 +15,7 @@
   when (io.funct7 === "b0000000".U) {
     when (io.funct3 === "b000".U) {
-      io.result:=io.operand1+io.operand2
+      io.result := io.operand1 - io.operand2  // Change ADD to SUB
     }
   }
"""
        hints = """  when (io.funct7 === "b0000000".U) {
    when (io.funct3 === "b000".U) {
      io.result  :=  io.operand1  +  io.operand2  // ADD
    }
  }"""

        result = self.corrector.correct_diff(diff, hints)

        self.assertTrue(result['success'])
        self.assertEqual(result['corrections_made'], 1)
        # Should preserve exact hint formatting including comment
        self.assertIn('io.result  :=  io.operand1  +  io.operand2  // ADD', result['corrected_diff'])


if __name__ == '__main__':
    unittest.main()
