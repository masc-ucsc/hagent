#!/usr/bin/env python3
"""Integration test for ChiselDiffCorrector with real bug data"""

import unittest
from hagent.tool.chisel_diff_corrector import ChiselDiffCorrector


class TestChiselDiffCorrectorIntegration(unittest.TestCase):
    """
    Integration tests using realistic Chisel code patterns similar to the
    bugs in the dino folder (ALUControl, SingleCycleCPU, etc.)
    """

    def setUp(self):
        self.corrector = ChiselDiffCorrector(confidence_threshold=0.90)

    def test_alu_control_scenario(self):
        """Test with realistic ALUControl-like Chisel code"""

        # Simulated hints from actual Chisel code (with exact formatting)
        hints = """  when (io.funct7 === "b0000000".U) {
    when (io.funct3 === "b000".U) {
      io.result  :=  io.operand1  +  io.operand2  // ADD
    } .elsewhen (io.funct3 === "b101".U) {
      io.result  :=  io.operand1  >>  io.operand2(4,0)  // SRL
    }
  }"""

        # LLM-generated diff with formatting errors (recreated instead of copied)
        llm_generated_diff = """--- a/src/main/scala/ALUControl.scala
+++ b/src/main/scala/ALUControl.scala
@@ -15,7 +15,7 @@
   when (io.funct7 === "b0000000".U) {
     when (io.funct3 === "b000".U) {
-      io.result:=io.operand1+io.operand2
+      io.result := io.operand1 - io.operand2  // Change ADD to SUB
     } .elsewhen (io.funct3 === "b101".U) {
       io.result := io.operand1 >> io.operand2(4,0)
     }
"""

        # Apply corrector
        result = self.corrector.correct_diff(llm_generated_diff, hints)

        # Verify correction
        self.assertTrue(result['success'])
        self.assertEqual(result['corrections_made'], 1)
        self.assertFalse(result['is_ambiguous'])

        # Check that the corrected diff uses exact hint formatting
        self.assertIn('io.result  :=  io.operand1  +  io.operand2  // ADD', result['corrected_diff'])
        # Should NOT contain the poorly formatted version
        self.assertNotIn('io.result:=io.operand1+io.operand2', result['corrected_diff'])

        print('\n✅ ALUControl scenario test passed!')
        print(f'   Corrections made: {result["corrections_made"]}')
        print('   Original removal line: io.result:=io.operand1+io.operand2')
        print('   Corrected to:          io.result  :=  io.operand1  +  io.operand2  // ADD')

    def test_when_statement_indentation(self):
        """Test correction of when statements with indentation mismatches"""

        hints = """  when (cond1) {
    io.out1  :=  5.U
  } .elsewhen (cond2) {
    io.out2  :=  10.U
  } .otherwise {
    io.out3  :=  15.U
  }"""

        # LLM recreated the code with different indentation
        llm_generated_diff = """--- a/test.scala
+++ b/test.scala
@@ -1,7 +1,7 @@
   when (cond1) {
-io.out1:=5.U
+    io.out1 := 0.U
   } .elsewhen (cond2) {
     io.out2 := 10.U
"""

        result = self.corrector.correct_diff(llm_generated_diff, hints)

        self.assertTrue(result['success'])
        self.assertEqual(result['corrections_made'], 1)
        # Should preserve exact indentation from hints
        self.assertIn('io.out1  :=  5.U', result['corrected_diff'])

    def test_multiple_identical_lines_ambiguity(self):
        """Test detection of ambiguous cases with identical lines"""

        # Code with repeated pattern (common in switch/case statements)
        hints = """  switch (io.operation) {
    is (0.U) {
      io.result := 0.U
    }
    is (1.U) {
      io.result := 0.U
    }
    is (2.U) {
      io.result := 0.U
    }
  }"""

        # LLM generates diff without enough context
        llm_generated_diff = """--- a/test.scala
+++ b/test.scala
@@ -1,7 +1,7 @@
-      io.result := 0.U
+      io.result := io.operand1
"""

        result = self.corrector.correct_diff(llm_generated_diff, hints)

        # Should detect ambiguity
        self.assertFalse(result['success'])
        self.assertTrue(result['is_ambiguous'])
        self.assertEqual(len(result['ambiguous_lines']), 1)
        self.assertEqual(len(result['ambiguous_lines'][0]['matches']), 3)  # 3 identical lines

        print('\n✅ Ambiguity detection test passed!')
        print(f'   Detected {len(result["ambiguous_lines"][0]["matches"])} ambiguous matches')
        print('   This would trigger clarification prompt in v2chisel_batch')

    def test_nested_when_with_operators(self):
        """Test with complex nested when statements and various operators"""

        # Use unique variables to avoid ambiguity
        hints = """  when (io.funct7 === "b0000000".U && io.funct3 === "b000".U) {
    addResult  :=  operand1  +  operand2
  } .elsewhen (io.funct7 === "b0100000".U && io.funct3 === "b000".U) {
    subResult  :=  operand1  -  operand2
  } .elsewhen (io.funct3 === "b111".U) {
    andResult  :=  operand1  &  operand2
  }"""

        # LLM generated diff with unique variable
        llm_generated_diff = """--- a/test.scala
+++ b/test.scala
@@ -1,5 +1,5 @@
   when (io.funct7 === "b0000000".U && io.funct3 === "b000".U) {
-    addResult:=operand1+operand2
+    addResult := operand1 * operand2  // Change to multiply
   }
"""

        result = self.corrector.correct_diff(llm_generated_diff, hints)

        self.assertTrue(result['success'])
        self.assertEqual(result['corrections_made'], 1)

        # Check correction
        self.assertIn('addResult  :=  operand1  +  operand2', result['corrected_diff'])

        print('\n✅ Nested when with operators test passed!')
        print(f'   Corrections made: {result["corrections_made"]}')

    def test_comment_preservation(self):
        """Test that comments in hints are preserved in corrections"""

        hints = """  when (condition) {
    io.result  :=  5.U  // Default value for safety
    io.status  :=  true.B  // Active high status
  }"""

        llm_generated_diff = """--- a/test.scala
+++ b/test.scala
@@ -1,4 +1,4 @@
   when (condition) {
-    io.result:=5.U
+    io.result := 10.U
-io.status:=true.B
+    io.status := false.B
   }
"""

        result = self.corrector.correct_diff(llm_generated_diff, hints)

        self.assertTrue(result['success'])
        self.assertEqual(result['corrections_made'], 2)

        # Comments should be preserved
        self.assertIn('// Default value for safety', result['corrected_diff'])
        self.assertIn('// Active high status', result['corrected_diff'])

        print('\n✅ Comment preservation test passed!')
        print('   Comments from hints successfully preserved in corrected diff')

    def test_correction_log_tracking(self):
        """Test that correction log tracks all changes"""

        hints = 'val x = 5\nval y  =  10'

        llm_generated_diff = """--- a/test.scala
+++ b/test.scala
@@ -1,2 +1,2 @@
-val x=5
+val x = 10
-val y=10
+val y = 20
"""

        result = self.corrector.correct_diff(llm_generated_diff, hints)

        self.assertTrue(result['success'])
        self.assertEqual(len(result['correction_log']), 2)

        # Check log entries
        log = result['correction_log']
        self.assertEqual(log[0]['original'], 'val x=5')
        self.assertEqual(log[0]['corrected'], 'val x = 5')
        self.assertGreater(log[0]['confidence'], 0.9)

        self.assertEqual(log[1]['original'], 'val y=10')
        self.assertEqual(log[1]['corrected'], 'val y  =  10')  # Preserves exact hint formatting
        self.assertGreater(log[1]['confidence'], 0.9)

        print('\n✅ Correction log tracking test passed!')
        print(f'   Tracked {len(result["correction_log"])} corrections with confidence scores')


if __name__ == '__main__':
    # Run tests with verbose output
    unittest.main(verbosity=2)
