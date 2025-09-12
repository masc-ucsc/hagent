#!/usr/bin/env python3
"""
Comprehensive unit tests for GoldenDesignBuilder class.
"""

import pytest
import sys
import tempfile
import os
from pathlib import Path
from unittest.mock import Mock, patch, MagicMock, call

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent.parent))

from hagent.step.v2chisel_batch.components.golden_design_builder import GoldenDesignBuilder


class TestGoldenDesignBuilder:
    """Comprehensive test cases for GoldenDesignBuilder class."""
    
    def test_basic_initialization(self):
        """Test basic GoldenDesignBuilder initialization."""
        mock_builder = Mock()
        golden_builder = GoldenDesignBuilder(mock_builder, debug=False)
        
        assert golden_builder.builder == mock_builder
        assert golden_builder.debug == False
        assert golden_builder.golden_dir == '/code/workspace/repo/lec_golden'
        assert len(golden_builder.baseline_paths) == 4
        assert '/code/workspace/build/build_singlecyclecpu_nd' in golden_builder.baseline_paths
    
    def test_validate_baseline_files_success(self):
        """Test successful baseline file validation."""
        mock_builder = Mock()
        golden_builder = GoldenDesignBuilder(mock_builder, debug=False)
        
        master_backup = {
            'baseline_verilog_success': True,
            'original_verilog_files': {
                '/code/workspace/build/Control.sv': '/code/workspace/cache/backup1/Control.sv',
                '/code/workspace/build/ALU.sv': '/code/workspace/cache/backup1/ALU.sv'
            }
        }
        
        result = golden_builder._validate_baseline_files(master_backup)
        
        assert result['success'] == True
        assert len(result['files']) == 2
        assert '/code/workspace/build/Control.sv' in result['files']
    
    def test_validate_baseline_files_no_files(self):
        """Test baseline validation failure when no files available."""
        mock_builder = Mock()
        golden_builder = GoldenDesignBuilder(mock_builder, debug=False)
        
        master_backup = {
            'baseline_verilog_success': True,
            'original_verilog_files': {}
        }
        
        result = golden_builder._validate_baseline_files(master_backup)
        
        assert result['success'] == False
        assert 'No baseline Verilog files available' in result['error']
    
    def test_validate_baseline_files_generation_failed(self):
        """Test baseline validation failure when generation was not successful."""
        mock_builder = Mock()
        golden_builder = GoldenDesignBuilder(mock_builder, debug=False)
        
        master_backup = {
            'baseline_verilog_success': False,
            'original_verilog_files': {
                '/code/workspace/build/Control.sv': '/code/workspace/cache/backup1/Control.sv'
            }
        }
        
        result = golden_builder._validate_baseline_files(master_backup)
        
        assert result['success'] == False
        assert 'Baseline Verilog generation was not successful' in result['error']
    
    @patch('subprocess.run')
    def test_create_golden_directory_success(self, mock_subprocess):
        """Test successful golden directory creation."""
        # Mock successful subprocess calls
        mock_subprocess.return_value.returncode = 0
        
        mock_builder = Mock()
        golden_builder = GoldenDesignBuilder(mock_builder, debug=False)
        
        result = golden_builder._create_golden_directory('test_container')
        
        assert result['success'] == True
        assert result['directory'] == '/code/workspace/repo/lec_golden'
        
        # Verify rm and mkdir commands were called
        assert mock_subprocess.call_count == 2
        
        # Check rm command
        rm_call = mock_subprocess.call_args_list[0]
        assert 'rm' in rm_call[0][0]
        assert '/code/workspace/repo/lec_golden' in rm_call[0][0]
        
        # Check mkdir command  
        mkdir_call = mock_subprocess.call_args_list[1]
        assert 'mkdir' in mkdir_call[0][0]
        assert '/code/workspace/repo/lec_golden' in mkdir_call[0][0]
    
    @patch('subprocess.run')
    def test_create_golden_directory_failure(self, mock_subprocess):
        """Test golden directory creation failure."""
        # Mock failed mkdir command
        mock_result = Mock()
        mock_result.returncode = 1
        mock_result.stderr = 'Permission denied'
        mock_subprocess.return_value = mock_result
        
        mock_builder = Mock()
        golden_builder = GoldenDesignBuilder(mock_builder, debug=False)
        
        result = golden_builder._create_golden_directory('test_container')
        
        assert result['success'] == False
        assert 'Failed to create golden directory' in result['error']
        assert 'Permission denied' in result['error']
    
    @patch('subprocess.run')
    def test_copy_baseline_to_golden_success(self, mock_subprocess):
        """Test successful copying of baseline files to golden directory."""
        # Mock successful cp commands
        mock_subprocess.return_value.returncode = 0
        
        mock_builder = Mock()
        golden_builder = GoldenDesignBuilder(mock_builder, debug=False)
        
        baseline_verilog = {
            '/code/workspace/build/Control.sv': '/code/workspace/cache/backup1/Control.sv',
            '/code/workspace/build/ALU.sv': '/code/workspace/cache/backup1/ALU.sv'
        }
        
        result = golden_builder._copy_baseline_to_golden(baseline_verilog, 'test_container')
        
        assert result['success'] == True
        assert len(result['copied_files']) == 2
        assert '/code/workspace/repo/lec_golden/Control.sv' in result['copied_files']
        assert '/code/workspace/repo/lec_golden/ALU.sv' in result['copied_files']
        assert len(result['failed_copies']) == 0
        assert result['total_copied'] == 2
        
        # Verify cp commands were called
        assert mock_subprocess.call_count == 2
    
    @patch('subprocess.run')
    def test_copy_baseline_to_golden_partial_failure(self, mock_subprocess):
        """Test copying with some failures."""
        # Mock mixed success/failure
        def mock_run_side_effect(*args, **kwargs):
            cmd = args[0]
            if 'Control.sv' in str(cmd):
                result = Mock()
                result.returncode = 0
                return result
            else:  # ALU.sv fails
                result = Mock()
                result.returncode = 1
                result.stderr = 'File not found'
                return result
        
        mock_subprocess.side_effect = mock_run_side_effect
        
        mock_builder = Mock()
        golden_builder = GoldenDesignBuilder(mock_builder, debug=False)
        
        baseline_verilog = {
            '/code/workspace/build/Control.sv': '/code/workspace/cache/backup1/Control.sv',
            '/code/workspace/build/ALU.sv': '/code/workspace/cache/backup1/ALU.sv'
        }
        
        result = golden_builder._copy_baseline_to_golden(baseline_verilog, 'test_container')
        
        assert result['success'] == True
        assert len(result['copied_files']) == 1
        assert '/code/workspace/repo/lec_golden/Control.sv' in result['copied_files']
        assert len(result['failed_copies']) == 1
        assert 'ALU.sv' in result['failed_copies']
    
    @patch('subprocess.run')
    def test_copy_baseline_to_golden_all_fail(self, mock_subprocess):
        """Test copying when all files fail."""
        # Mock all failures
        mock_result = Mock()
        mock_result.returncode = 1
        mock_result.stderr = 'Permission denied'
        mock_subprocess.return_value = mock_result
        
        mock_builder = Mock()
        golden_builder = GoldenDesignBuilder(mock_builder, debug=False)
        
        baseline_verilog = {
            '/code/workspace/build/Control.sv': '/code/workspace/cache/backup1/Control.sv'
        }
        
        result = golden_builder._copy_baseline_to_golden(baseline_verilog, 'test_container')
        
        assert result['success'] == False
        assert 'No baseline files were copied' in result['error']
    
    def test_apply_diff_to_golden_files_success(self):
        """Test successful diff application to golden files."""
        mock_builder = Mock()
        golden_builder = GoldenDesignBuilder(mock_builder, debug=False)
        
        with patch('builtins.__import__') as mock_import:
            # Mock successful DockerDiffApplier import and usage
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
            
            verilog_diff = '''--- a/Control.sv
+++ b/Control.sv
@@ -1,1 +1,1 @@
-wire test = 1'b0;
+wire test = 1'b1;'''
            
            result = golden_builder._apply_diff_to_golden_files(verilog_diff, 'test_container')
            
            assert result['success'] == True
            assert result['diff_applied'] == True
            assert 'Diff applied successfully' in result['output']
    
    def test_apply_diff_to_golden_files_failure(self):
        """Test failed diff application."""
        mock_builder = Mock()
        golden_builder = GoldenDesignBuilder(mock_builder, debug=False)
        
        with patch('builtins.__import__') as mock_import:
            # Mock failed DockerDiffApplier usage
            mock_applier = Mock()
            mock_applier.apply_diff_to_container.return_value = False
            
            mock_applier_class = Mock(return_value=mock_applier)
            
            def mock_import_side_effect(name, *args, **kwargs):
                if name == 'hagent.tool.docker_diff_applier':
                    mock_module = Mock()
                    mock_module.DockerDiffApplier = mock_applier_class
                    return mock_module
                else:
                    return __import__(name, *args, **kwargs)
            
            mock_import.side_effect = mock_import_side_effect
            
            verilog_diff = 'invalid diff'
            
            result = golden_builder._apply_diff_to_golden_files(verilog_diff, 'test_container')
            
            assert result['success'] == False
            assert 'Diff application failed' in result['error']
    
    def test_apply_diff_import_error(self):
        """Test diff application when DockerDiffApplier cannot be imported."""
        mock_builder = Mock()
        golden_builder = GoldenDesignBuilder(mock_builder, debug=False)
        
        with patch('builtins.__import__') as mock_import:
            def mock_import_side_effect(name, *args, **kwargs):
                if name == 'hagent.tool.docker_diff_applier':
                    raise ImportError('Module not found')
                else:
                    return __import__(name, *args, **kwargs)
            
            mock_import.side_effect = mock_import_side_effect
            
            result = golden_builder._apply_diff_to_golden_files('diff', 'test_container')
            
            assert result['success'] == False
            assert 'Could not import DockerDiffApplier' in result['error']
    
    @patch('subprocess.run')
    def test_find_verilog_files_in_path_success(self, mock_subprocess):
        """Test successful Verilog file discovery."""
        mock_subprocess.return_value.returncode = 0
        mock_subprocess.return_value.stdout = '/path/Control.sv\n/path/ALU.sv\n'
        
        mock_builder = Mock()
        golden_builder = GoldenDesignBuilder(mock_builder, debug=False)
        
        result = golden_builder._find_verilog_files_in_path('test_container', '/code/workspace/build')
        
        assert len(result) == 2
        assert '/path/Control.sv' in result
        assert '/path/ALU.sv' in result
    
    @patch('subprocess.run')
    def test_find_verilog_files_in_path_no_files(self, mock_subprocess):
        """Test Verilog file discovery when no files found."""
        mock_subprocess.return_value.returncode = 0
        mock_subprocess.return_value.stdout = ''
        
        mock_builder = Mock()
        golden_builder = GoldenDesignBuilder(mock_builder, debug=False)
        
        result = golden_builder._find_verilog_files_in_path('test_container', '/code/workspace/build')
        
        assert len(result) == 0
    
    @patch('subprocess.run')
    def test_find_verilog_files_in_path_command_failure(self, mock_subprocess):
        """Test Verilog file discovery when command fails."""
        mock_subprocess.return_value.returncode = 1
        
        mock_builder = Mock()
        golden_builder = GoldenDesignBuilder(mock_builder, debug=False)
        
        result = golden_builder._find_verilog_files_in_path('test_container', '/code/workspace/build')
        
        assert len(result) == 0
    
    def test_generate_baseline_verilog_integration(self):
        """Integration test for baseline Verilog generation."""
        mock_builder = Mock()
        
        # Mock builder.run calls - SBT first, then copy
        mock_builder.run.side_effect = [
            (0, 'SBT Success', ''),  # SBT generation
            (0, 'Copy Success', '')  # File copy
        ]
        
        golden_builder = GoldenDesignBuilder(mock_builder, debug=False)
        
        with patch.object(golden_builder, 'backup_existing_original_verilog') as mock_backup:
            mock_backup.return_value = {
                'success': True,
                'files': {'/path/Control.sv': '/backup/Control.sv'},
                'total_files': 1
            }
            
            result = golden_builder.generate_baseline_verilog('test_container', 'backup123')
            
            assert result['success'] == True
            assert result['generation_success'] == True
            assert 'backup_result' in result
            
            # Verify SBT command was called (should be first call)
            assert mock_builder.run.call_count >= 1
            first_call = mock_builder.run.call_args_list[0]
            sbt_call = first_call[0][0]
            assert 'sbt "runMain dinocpu.SingleCycleCPUNoDebug"' in sbt_call
    
    def test_create_golden_design_integration(self):
        """Integration test for complete golden design creation."""
        mock_builder = Mock()
        golden_builder = GoldenDesignBuilder(mock_builder, debug=False)
        
        # Mock all the sub-methods
        with patch.object(golden_builder, '_validate_baseline_files') as mock_validate, \
             patch.object(golden_builder, '_create_golden_directory') as mock_create_dir, \
             patch.object(golden_builder, '_copy_baseline_to_golden') as mock_copy, \
             patch.object(golden_builder, '_apply_diff_to_golden_files') as mock_apply:
            
            # Set up successful mocks
            mock_validate.return_value = {
                'success': True,
                'files': {'/path/Control.sv': '/backup/Control.sv'}
            }
            mock_create_dir.return_value = {'success': True, 'directory': '/golden'}
            mock_copy.return_value = {
                'success': True,
                'copied_files': ['/golden/Control.sv'],
                'failed_copies': [],
                'total_copied': 1
            }
            mock_apply.return_value = {
                'success': True,
                'diff_applied': True,
                'output': 'Success',
                'files_modified': []
            }
            
            master_backup = {
                'baseline_verilog_success': True,
                'original_verilog_files': {'/path/Control.sv': '/backup/Control.sv'}
            }
            verilog_diff = '--- a/Control.sv\n+++ b/Control.sv\n@@ -1,1 +1,1 @@\n-old\n+new'
            
            result = golden_builder.create_golden_design(verilog_diff, master_backup, 'test_container')
            
            assert result['success'] == True
            assert result['diff_applied'] == True
            assert '/golden/Control.sv' in result['golden_files']
            
            # Verify all steps were called
            mock_validate.assert_called_once_with(master_backup)
            mock_create_dir.assert_called_once_with('test_container')
            mock_copy.assert_called_once()
            mock_apply.assert_called_once_with(verilog_diff, 'test_container')
    
    def test_create_golden_design_validation_failure(self):
        """Test golden design creation when validation fails."""
        mock_builder = Mock()
        golden_builder = GoldenDesignBuilder(mock_builder, debug=False)
        
        with patch.object(golden_builder, '_validate_baseline_files') as mock_validate:
            mock_validate.return_value = {
                'success': False,
                'error': 'No baseline files'
            }
            
            master_backup = {}
            result = golden_builder.create_golden_design('diff', master_backup, 'test_container')
            
            assert result['success'] == False
            assert result['error'] == 'No baseline files'


def test_golden_design_builder_with_real_data():
    """Integration test with realistic data structures."""
    mock_builder = Mock()
    golden_builder = GoldenDesignBuilder(mock_builder, debug=False)
    
    # Create realistic master backup data
    master_backup = {
        'success': True,
        'backup_id': 'backup_20241201_123456',
        'baseline_verilog_success': True,
        'original_verilog_files': {
            '/code/workspace/build/build_singlecyclecpu_nd/Control.sv': '/code/workspace/cache/backups/backup_20241201_123456/original_verilog/Control.sv',
            '/code/workspace/build/build_singlecyclecpu_nd/ALU.sv': '/code/workspace/cache/backups/backup_20241201_123456/original_verilog/ALU.sv',
            '/code/workspace/build/build_singlecyclecpu_nd/SingleCycleCPU.sv': '/code/workspace/cache/backups/backup_20241201_123456/original_verilog/SingleCycleCPU.sv'
        },
        'is_master_backup': True
    }
    
    realistic_verilog_diff = '''--- a/Control.sv
+++ b/Control.sv
@@ -27,1 +27,1 @@
-  wire _signals_T_132 = io_opcode == 7'h3B;
+  wire _signals_T_132 = io_opcode == 7'h3F;'''
    
    # Test validation with realistic data
    result = golden_builder._validate_baseline_files(master_backup)
    assert result['success'] == True
    assert len(result['files']) == 3
    assert '/code/workspace/build/build_singlecyclecpu_nd/Control.sv' in result['files']


if __name__ == '__main__':
    pytest.main([__file__, '-v'])