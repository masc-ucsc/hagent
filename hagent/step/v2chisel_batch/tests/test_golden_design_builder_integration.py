#!/usr/bin/env python3
"""
Integration tests for GoldenDesignBuilder with V2chisel_batch.
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


def test_golden_design_builder_initialization():
    """Test that GoldenDesignBuilder can be initialized properly."""
    print("🧪 Testing GoldenDesignBuilder initialization...")
    
    mock_builder = Mock()
    golden_builder = GoldenDesignBuilder(mock_builder, debug=True)
    
    print(f"✅ GoldenDesignBuilder created with debug: {golden_builder.debug}")
    print(f"✅ Golden directory configured: {golden_builder.golden_dir}")
    print(f"✅ Baseline paths configured: {len(golden_builder.baseline_paths)} paths")
    
    assert golden_builder.builder == mock_builder
    assert golden_builder.debug == True
    print("✅ Initialization test passed")
    return True


def test_golden_design_builder_with_v2chisel_batch():
    """Test GoldenDesignBuilder integration with V2chisel_batch setup."""
    print("\n🧪 Testing GoldenDesignBuilder integration with V2chisel_batch...")
    
    try:
        # Test importing V2chisel_batch and GoldenDesignBuilder
        from hagent.step.v2chisel_batch.v2chisel_batch import V2chisel_batch
        from hagent.step.v2chisel_batch.components import GoldenDesignBuilder
        
        print("✅ Successfully imported V2chisel_batch and GoldenDesignBuilder")
        
        # Test creating V2chisel_batch instance
        processor = V2chisel_batch()
        print("✅ V2chisel_batch instance created successfully")
        
        # Test that we can create GoldenDesignBuilder with processor's builder
        golden_builder = GoldenDesignBuilder(processor.builder, debug=True)
        print("✅ GoldenDesignBuilder created with V2chisel_batch builder")
        
        # Test the interface matches what V2chisel_batch expects
        assert hasattr(golden_builder, 'create_golden_design')
        assert hasattr(golden_builder, 'backup_existing_original_verilog')
        assert hasattr(golden_builder, 'generate_baseline_verilog')
        print("✅ All required methods are available")
        
        return True
        
    except Exception as e:
        print(f"❌ Integration test failed: {e}")
        return False


def test_golden_design_builder_method_signatures():
    """Test that GoldenDesignBuilder methods have expected signatures."""
    print("\n🧪 Testing GoldenDesignBuilder method signatures...")
    
    mock_builder = Mock()
    golden_builder = GoldenDesignBuilder(mock_builder, debug=False)
    
    # Test create_golden_design signature
    try:
        # This should not raise an error even with invalid data
        result = golden_builder.create_golden_design(
            verilog_diff="test diff",
            master_backup={'baseline_verilog_success': False},  # Invalid to trigger early return
            docker_container="test_container"
        )
        assert 'success' in result
        assert 'error' in result
        print("✅ create_golden_design signature correct")
    except Exception as e:
        print(f"❌ create_golden_design signature test failed: {e}")
        return False
    
    # Test backup_existing_original_verilog signature
    try:
        with patch('subprocess.run') as mock_subprocess:
            mock_subprocess.return_value.returncode = 1  # Simulate failure to trigger early return
            mock_subprocess.return_value.stdout = ""
            
            result = golden_builder.backup_existing_original_verilog(
                docker_container="test_container",
                backup_id="test_backup"
            )
            assert 'success' in result
            assert 'files' in result
            print("✅ backup_existing_original_verilog signature correct")
    except Exception as e:
        print(f"❌ backup_existing_original_verilog signature test failed: {e}")
        return False
    
    # Test generate_baseline_verilog signature  
    try:
        mock_builder.run.return_value = (1, "", "Error")  # Simulate SBT failure
        
        result = golden_builder.generate_baseline_verilog(
            docker_container="test_container",
            backup_id="test_backup"
        )
        assert 'success' in result
        print("✅ generate_baseline_verilog signature correct")
    except Exception as e:
        print(f"❌ generate_baseline_verilog signature test failed: {e}")
        return False
    
    return True


def test_realistic_golden_design_workflow():
    """Test the complete golden design workflow with realistic data."""
    print("\n🧪 Testing realistic golden design workflow...")
    
    mock_builder = Mock()
    golden_builder = GoldenDesignBuilder(mock_builder, debug=True)
    
    # Create realistic master backup
    master_backup = {
        'success': True,
        'backup_id': 'backup_20241201_123456',
        'baseline_verilog_success': True,
        'original_verilog_files': {
            '/code/workspace/build/build_singlecyclecpu_nd/Control.sv': 
                '/code/workspace/cache/backups/backup_20241201_123456/original_verilog/Control.sv',
            '/code/workspace/build/build_singlecyclecpu_nd/ALU.sv': 
                '/code/workspace/cache/backups/backup_20241201_123456/original_verilog/ALU.sv'
        }
    }
    
    realistic_diff = '''--- a/Control.sv
+++ b/Control.sv
@@ -27,1 +27,1 @@
-  wire _signals_T_132 = io_opcode == 7'h3B;
+  wire _signals_T_132 = io_opcode == 7'h3F;'''
    
    # Mock all subprocess calls and DockerDiffApplier import
    with patch('subprocess.run') as mock_subprocess, \
         patch('builtins.__import__') as mock_import:
        
        # Mock successful operations
        mock_subprocess.return_value.returncode = 0
        
        # Mock DockerDiffApplier import and usage
        mock_applier = Mock()
        mock_applier.apply_diff_to_container.return_value = True
        mock_applier_class = Mock(return_value=mock_applier)
        
        def mock_import_side_effect(name, *args, **kwargs):
            if name == 'hagent.tool.docker_diff_applier':
                mock_module = Mock()
                mock_module.DockerDiffApplier = mock_applier_class
                return mock_module
            else:
                return __import__(name, *args, **kwargs)
        
        mock_import.side_effect = mock_import_side_effect
        
        result = golden_builder.create_golden_design(
            verilog_diff=realistic_diff,
            master_backup=master_backup,
            docker_container='test_container'
        )
        
        print(f"✅ Workflow result: {result.get('success', False)}")
        print(f"✅ Golden files created: {len(result.get('golden_files', []))}")
        print(f"✅ Diff applied: {result.get('diff_applied', False)}")
        
        assert result['success'] == True
        assert result['diff_applied'] == True
        assert len(result['golden_files']) > 0
        
        return True


def main():
    """Run all integration tests."""
    print("🎯 GoldenDesignBuilder Integration Tests")
    print("=" * 60)
    
    tests = [
        test_golden_design_builder_initialization,
        test_golden_design_builder_with_v2chisel_batch,
        test_golden_design_builder_method_signatures,
        test_realistic_golden_design_workflow
    ]
    
    passed = 0
    total = len(tests)
    
    for test in tests:
        try:
            if test():
                passed += 1
            else:
                print(f"❌ {test.__name__} failed")
        except Exception as e:
            print(f"❌ {test.__name__} failed with exception: {e}")
    
    print(f"\n📊 Integration Test Results: {passed}/{total} passed")
    
    if passed == total:
        print("🎉 All integration tests passed!")
        print("✅ GoldenDesignBuilder is ready for integration with V2chisel_batch")
        return True
    else:
        print("❌ Some integration tests failed")
        return False


if __name__ == '__main__':
    success = main()
    if not success:
        sys.exit(1)