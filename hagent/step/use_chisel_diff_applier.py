from hagent.tool.chisel_diff_applier import ChiselDiffApplier

# The diff to be applied:
chisel_diff = """diff --git a/chisel_code.scala b/chisel_code.scala
index 123456..789012 100644
--- a/chisel_code.scala
+++ b/chisel_code.scala
@@ -121,10 +121,10 @@
   io.out := io.in
-  val in = Input(UInt(8.W))
-  io.out := in
+  val in = Input(UInt(8.W))
+  io.out := ~in"""

# The original Chisel code snippet:
chisel_code = """
package example
  import chisel3._
  class Foo extends Module {
    val io = IO(new Bundle {
      val in  = Input(UInt(8.W))
      val out = Output(UInt(8.W))
    })
    io.out := io.in
  }
"""

applier = ChiselDiffApplier()
new_code = applier.apply_diff(chisel_diff, chisel_code)
print(new_code)
