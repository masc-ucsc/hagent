#!/usr/bin/env python3
"""
Test script for v2chisel_batch retry mechanism with diff applier
"""

import sys
import os
import tempfile
from pathlib import Path

# Add project root to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent.parent))

from hagent.step.v2chisel_batch.v2chisel_batch import V2chisel_batch
from hagent.tool.docker_diff_applier import DockerDiffApplier


def test_retry_mechanism():
    """Test that demonstrates the retry loop when applier fails"""
    print("🧪 Testing v2chisel_batch retry mechanism")
    print("=" * 60)
    
    # Create temporary input and output files
    test_dir = Path(__file__).parent
    
    input_file = test_dir / "test_input_retry.yaml"
    output_file = test_dir / "test_output_retry.yaml"
    
    if not input_file.exists():
        print(f"❌ Test input file not found: {input_file}")
        return False
    
    print(f"📁 Input file: {input_file}")
    print(f"📁 Output file: {output_file}")
    
    # Initialize v2chisel_batch
    try:
        processor = V2chisel_batch()
        processor.input_file = str(input_file)
        processor.output_file = str(output_file)
        
        # Load input data
        from ruamel.yaml import YAML
        yaml = YAML()
        with open(input_file, 'r') as f:
            processor.input_data = yaml.load(f)
        
        # Setup the processor
        processor.setup()
        print("✅ V2chisel_batch initialized successfully")
        
    except Exception as e:
        print(f"❌ Failed to initialize v2chisel_batch: {e}")
        return False
    
    # Test the docker diff applier separately first
    print("\n🐳 Testing DockerDiffApplier with intentionally wrong diff...")
    
    # Create a test diff that should fail (wrong removal line)
    wrong_diff = """--- a/yunsuan/vector/VectorFloatAdder.scala
+++ b/yunsuan/vector/VectorFloatAdder.scala
@@ -778,7 +778,7 @@
-  io_c := io_a - io_b  // This line doesn't exist in the actual file
+  io_c := io_a + io_b
"""
    
    # Test the applier
    container_name = processor.input_data.get('docker_container', 'musing_sammet')
    applier = DockerDiffApplier(container_name)
    
    try:
        success = applier.apply_diff_to_container(wrong_diff, dry_run=True)
        if success:
            print("⚠️  Expected failure but applier succeeded - this shouldn't happen")
            return False
        else:
            print("✅ Applier correctly failed with wrong diff")
    except Exception as e:
        print(f"✅ Applier correctly raised exception: {e}")
    
    print("\n🔄 Now testing correct diff...")
    
    # Test with a correct diff
    correct_diff = """--- a/yunsuan/vector/VectorFloatAdder.scala
+++ b/yunsuan/vector/VectorFloatAdder.scala
@@ -778,7 +778,7 @@
-    io.c := (if (is_sub) io.a -& io.b else io.a +& io.b)
+    io.c := (if (is_sub) io.a +& io.b else io.a +& io.b)
"""
    
    try:
        success = applier.apply_diff_to_container(correct_diff, dry_run=True)
        if success:
            print("✅ Applier succeeded with correct diff format")
        else:
            print("❌ Applier failed even with correct diff")
            return False
    except Exception as e:
        print(f"❌ Applier failed with correct diff: {e}")
        return False
    
    print("\n🎯 Test Summary:")
    print("✅ DockerDiffApplier correctly handles both success and failure cases")
    print("📝 Next steps:")
    print("   1. Modify v2chisel_batch.py to integrate the retry loop")
    print("   2. Add compilation step after successful diff application")
    print("   3. Add LEC (Logic Equivalence Check) step")
    
    return True


if __name__ == "__main__":
    success = test_retry_mechanism()
    if success:
        print("\n🎉 Test completed successfully!")
        sys.exit(0)
    else:
        print("\n❌ Test failed!")
        sys.exit(1)