#!/usr/bin/env python3
"""
Demo script showing GoldenDesignBuilder in action.

This demo shows how GoldenDesignBuilder takes a Verilog diff and creates
a golden design for LEC verification.

Usage:
    uv run python hagent/step/v2chisel_batch/tests/demo_golden_design_builder.py
"""

import os
import sys
from pathlib import Path
from unittest.mock import Mock, patch

# Set environment before importing
os.environ['HAGENT_EXECUTION_MODE'] = 'docker'

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent.parent))

from hagent.step.v2chisel_batch.components.golden_design_builder import GoldenDesignBuilder


def demo_golden_design_creation():
    """Demonstrate golden design creation process."""
    
    print("🎯 GOLDEN DESIGN BUILDER DEMO")
    print("=" * 60)
    print("This demo shows how to create a golden design for LEC verification")
    print()
    
    # Step 1: Show the problem
    print("📋 STEP 1: The Problem")
    print("-" * 30)
    print("You have a processor bug fix:")
    print("• Original code: wire _signals_T_132 = io_opcode == 7'h3B;")
    print("• Fixed code:    wire _signals_T_132 = io_opcode == 7'h3F;")
    print("• Need to verify: Does this fix work correctly?")
    print("• Solution: Create golden design for LEC comparison")
    print()
    
    # Step 2: Create the components
    print("📋 STEP 2: Setting Up")
    print("-" * 30)
    
    # Create builder and golden design builder
    mock_builder = Mock()
    golden_builder = GoldenDesignBuilder(mock_builder, debug=True)
    
    print(f"✅ Created GoldenDesignBuilder")
    print(f"   🎯 Purpose: Create reference design for LEC")
    print(f"   📂 Target: {golden_builder.golden_dir}")
    print()
    
    # Step 3: Show the inputs
    print("📋 STEP 3: Input Data")
    print("-" * 30)
    
    # Realistic Verilog diff (the fix we want to apply)
    verilog_diff = '''--- a/Control.sv
+++ b/Control.sv
@@ -7,1 +7,1 @@
-  wire _signals_T_132 = io_opcode == 7'h3B;  // Bug: wrong opcode
+  wire _signals_T_132 = io_opcode == 7'h3F;  // Fix: correct opcode'''
    
    print("🔧 Verilog Diff (the fix to apply):")
    for line in verilog_diff.strip().split('\n'):
        if line.startswith('-'):
            print(f"   ❌ {line}")
        elif line.startswith('+'):
            print(f"   ✅ {line}")
        else:
            print(f"   📄 {line}")
    print()
    
    # Master backup (simulates having baseline files)
    master_backup = {
        'success': True,
        'backup_id': 'backup_20241201_demo',
        'baseline_verilog_success': True,
        'original_verilog_files': {
            '/code/workspace/build/build_singlecyclecpu_nd/Control.sv': 
                '/code/workspace/cache/backups/backup_20241201_demo/original_verilog/Control.sv',
            '/code/workspace/build/build_singlecyclecpu_nd/ALU.sv':
                '/code/workspace/cache/backups/backup_20241201_demo/original_verilog/ALU.sv',
            '/code/workspace/build/build_singlecyclecpu_nd/SingleCycleCPU.sv':
                '/code/workspace/cache/backups/backup_20241201_demo/original_verilog/SingleCycleCPU.sv'
        }
    }
    
    print("📦 Master Backup (baseline files available):")
    print(f"   🆔 Backup ID: {master_backup['backup_id']}")
    print(f"   📁 Files: {len(master_backup['original_verilog_files'])}")
    for container_path in master_backup['original_verilog_files'].keys():
        filename = os.path.basename(container_path)
        print(f"      📄 {filename}")
    print()
    
    # Step 4: Mock Docker environment
    print("📋 STEP 4: Mocking Docker Environment")
    print("-" * 30)
    
    def mock_subprocess(*args, **kwargs):
        """Mock successful Docker operations."""
        return Mock(returncode=0, stdout='', stderr='')
    
    def mock_import_docker_applier(name, *args, **kwargs):
        """Mock successful DockerDiffApplier."""
        if name == 'hagent.tool.docker_diff_applier':
            mock_applier = Mock()
            mock_applier.apply_diff_to_container.return_value = True
            
            mock_module = Mock()
            mock_module.DockerDiffApplier = Mock(return_value=mock_applier)
            return mock_module
        else:
            return __import__(name, *args, **kwargs)
    
    print("🐳 Docker environment ready:")
    print("   ✅ Container operations: Mocked")
    print("   ✅ File operations: Mocked")
    print("   ✅ Diff applier: Mocked")
    print()
    
    # Step 5: Execute golden design creation
    print("📋 STEP 5: Creating Golden Design")
    print("-" * 30)
    print("🚀 Running the golden design creation workflow...")
    print()
    
    with patch('subprocess.run', side_effect=mock_subprocess), \
         patch('builtins.__import__', side_effect=mock_import_docker_applier):
        
        result = golden_builder.create_golden_design(
            verilog_diff=verilog_diff,
            master_backup=master_backup,
            docker_container='demo_container'
        )
    
    # Step 6: Show the results
    print("📋 STEP 6: Results")
    print("-" * 30)
    
    success = result.get('success', False)
    if success:
        print("🎉 GOLDEN DESIGN CREATION: SUCCESS!")
        print()
        print("✅ What was accomplished:")
        print(f"   📂 Created directory: {result.get('golden_directory')}")
        print(f"   📁 Golden files: {len(result.get('golden_files', []))}")
        print(f"   🔧 Applied diff: {result.get('diff_applied')}")
        
        print()
        print("📄 Golden files created:")
        for golden_file in result.get('golden_files', []):
            filename = os.path.basename(golden_file)
            print(f"   ✅ {filename} -> {golden_file}")
        
        print()
        print("🔍 What this means:")
        print("   1. 📋 Baseline files were copied to golden directory")
        print("   2. 🔧 Your Verilog diff was applied to create the 'golden' version")
        print("   3. 🎯 Golden design now contains your EXPECTED fixed design")
        print("   4. ⚖️  LEC can compare: Generated design vs Golden design")
        print("   5. ✅ If LEC passes: Your Chisel fix generates the expected Verilog")
        
    else:
        print("❌ GOLDEN DESIGN CREATION: FAILED")
        print(f"🚨 Error: {result.get('error', 'Unknown error')}")
    
    print()
    print("📋 STEP 7: How This Fits Into V2chisel_batch")
    print("-" * 30)
    print("In the complete V2chisel_batch workflow:")
    print("   1. 🐛 Bug is detected in generated Verilog")
    print("   2. 🤖 AI generates Chisel code hints")  
    print("   3. ✏️  Chisel code is modified based on hints")
    print("   4. 🔧 New Verilog is generated from modified Chisel")
    print("   5. 🎯 Golden design is created (this demo!)")
    print("   6. ⚖️  LEC compares generated vs golden")
    print("   7. ✅ Success: Fix verified by LEC equivalence")
    
    return success


def demo_backup_and_baseline():
    """Demo backup and baseline generation."""
    
    print("\n\n🎯 BACKUP & BASELINE GENERATION DEMO")
    print("=" * 60)
    print("This shows how GoldenDesignBuilder manages baseline files")
    print()
    
    mock_builder = Mock()
    golden_builder = GoldenDesignBuilder(mock_builder, debug=False)  # Less verbose for demo
    
    print("📋 Backup Process Demo")
    print("-" * 30)
    
    with patch('subprocess.run') as mock_subprocess:
        # Mock finding existing files
        mock_subprocess.return_value.returncode = 0
        mock_subprocess.return_value.stdout = '''
/code/workspace/build/build_singlecyclecpu_nd/Control.sv
/code/workspace/build/build_singlecyclecpu_nd/ALU.sv
/code/workspace/build/build_singlecyclecpu_nd/SingleCycleCPU.sv
        '''.strip()
        
        result = golden_builder.backup_existing_original_verilog('demo_container', 'demo_backup')
        
        print("🔍 What backup does:")
        print("   1. 📁 Searches for existing Verilog files in container")
        print("   2. 💾 Creates backup copies for golden design use")
        print("   3. 🗂️  Maps original → backup paths")
        
        print(f"\n📊 Backup result:")
        print(f"   ✅ Success: {result.get('success', False)}")
        print(f"   📁 Files backed up: {result.get('total_files', 0)}")
    
    print("\n📋 Baseline Generation Demo")
    print("-" * 30)
    
    # Mock SBT operations
    mock_builder.run.side_effect = [
        (0, 'SBT compilation successful', ''),  # SBT build
        (0, 'Files copied', '')                 # File copy
    ]
    
    with patch.object(golden_builder, 'backup_existing_original_verilog') as mock_backup:
        mock_backup.return_value = {
            'success': True,
            'files': {'/build/Control.sv': '/backup/Control.sv'},
            'total_files': 1
        }
        
        result = golden_builder.generate_baseline_verilog('demo_container', 'demo_backup')
        
        print("🔍 What baseline generation does:")
        print("   1. 🧹 Cleans build directories")
        print("   2. 🏗️  Runs SBT to generate fresh Verilog from Chisel")
        print("   3. 📁 Copies generated files to expected locations")
        print("   4. 💾 Backs up the fresh baseline files")
        
        print(f"\n📊 Generation result:")
        print(f"   ✅ Success: {result.get('success', False)}")
        print(f"   🔧 Generation OK: {result.get('generation_success', False)}")
        print(f"   💾 Backup OK: {result.get('backup_result', {}).get('success', False)}")


def main():
    """Run the demo."""
    print("Welcome to the GoldenDesignBuilder Demo!")
    print("This shows how golden design creation works in practice.")
    print()
    
    # Demo 1: Golden design creation
    success1 = demo_golden_design_creation()
    
    # Demo 2: Backup and baseline
    demo_backup_and_baseline()
    
    print("\n" + "=" * 60)
    print("🎉 DEMO COMPLETE!")
    
    if success1:
        print("✅ You've seen how GoldenDesignBuilder works!")
        print("✅ Ready to integrate with V2chisel_batch")
        print("✅ Golden design workflow is functioning")
    else:
        print("⚠️  Demo had issues, but that's expected with mocked data")
    
    print()
    print("🔧 Next steps:")
    print("   • Integrate GoldenDesignBuilder into V2chisel_batch")
    print("   • Replace monolithic golden design methods")
    print("   • Test with real Docker container")
    print("   • Verify LEC integration works")


if __name__ == '__main__':
    main()