#!/usr/bin/env python3
"""
Comprehensive unit tests for HintsGenerator class.
"""

import pytest
import sys
import tempfile
import os
from pathlib import Path
from unittest.mock import Mock, patch

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent.parent))

from hagent.step.v2chisel_batch.components.hints_generator import HintsGenerator
from hagent.step.v2chisel_batch.components.bug_info import BugInfo


class MockHit:
    """Mock class for module_finder hits."""

    def __init__(self, file_name, module_name, start_line, end_line, confidence):
        self.file_name = file_name
        self.module_name = module_name
        self.start_line = start_line
        self.end_line = end_line
        self.confidence = confidence


class TestHintsGenerator:
    """Comprehensive test cases for HintsGenerator class."""

    def test_basic_initialization(self):
        """Test basic HintsGenerator initialization."""
        mock_module_finder = Mock()
        hints_gen = HintsGenerator(mock_module_finder, debug=False)

        assert hints_gen.module_finder == mock_module_finder
        assert hints_gen.debug is False
        assert hints_gen.temp_files == []
        assert hints_gen.temp_to_original == {}

    def test_cleanup_temp_files(self):
        """Test temp file cleanup."""
        mock_module_finder = Mock()
        hints_gen = HintsGenerator(mock_module_finder)

        # Create a temp file to test cleanup
        temp_fd, temp_path = tempfile.mkstemp()
        os.close(temp_fd)

        hints_gen.temp_files = [temp_path]
        hints_gen.temp_to_original = {temp_path: 'docker:container:file'}

        # Should exist before cleanup
        assert os.path.exists(temp_path)

        # Cleanup
        hints_gen.cleanup_temp_files()

        # Should be gone after cleanup
        assert not os.path.exists(temp_path)
        assert hints_gen.temp_files == []
        assert hints_gen.temp_to_original == {}

    def test_find_hints_module_finder_success(self):
        """Test successful hints generation with module_finder."""
        mock_module_finder = Mock()

        # Create mock hits with good confidence
        mock_hits = [MockHit('test.scala', 'TestModule', 10, 20, 0.8), MockHit('another.scala', 'AnotherModule', 30, 40, 0.7)]
        mock_module_finder.find_modules.return_value = mock_hits

        hints_gen = HintsGenerator(mock_module_finder, debug=False)

        # Mock the code extraction
        with patch.object(hints_gen, '_extract_code_from_hits', return_value='mock code hints'):
            bug_info = BugInfo({'file': 'test.sv', 'unified_diff': 'diff'}, 0)
            result = hints_gen.find_hints(bug_info, ['test.scala'], 'test_container')

            assert result['source'] == 'module_finder'
            assert result['success']
            assert 'Module finder results for test' in result['hints']
            assert 'mock code hints' in result['hints']
            assert len(result['hits']) == 2
            assert result['hits'][0].confidence == 0.8

    def test_find_hints_low_confidence_fallback(self):
        """Test fallback to metadata when module_finder has low confidence."""
        mock_module_finder = Mock()

        # Create mock hits with low confidence
        mock_hits = [MockHit('test.scala', 'TestModule', 10, 20, 0.3)]
        mock_module_finder.find_modules.return_value = mock_hits

        hints_gen = HintsGenerator(mock_module_finder, debug=False)

        # Mock the fallback to return hints
        with patch.object(hints_gen, '_get_metadata_fallback_hints', return_value='fallback hints'):
            bug_info = BugInfo({'file': 'test.sv', 'unified_diff': 'diff'}, 0)
            result = hints_gen.find_hints(bug_info, ['test.scala'], 'test_container')

            assert result['source'] == 'metadata_fallback'
            assert result['success']
            assert result['hints'] == 'fallback hints'

    def test_find_hints_no_hits_no_fallback(self):
        """Test find_hints when both module_finder and fallback fail."""
        mock_module_finder = Mock()
        mock_module_finder.find_modules.return_value = []

        hints_gen = HintsGenerator(mock_module_finder, debug=False)

        # Mock the fallback to return empty
        with patch.object(hints_gen, '_get_metadata_fallback_hints', return_value=''):
            bug_info = BugInfo({'file': 'test.sv', 'unified_diff': 'diff'}, 0)
            result = hints_gen.find_hints(bug_info, ['test.scala'], 'test_container')

            assert result['source'] == 'none'
            assert result['success'] is False
            assert 'No hints found' in result['hints']

    def test_find_hints_exception_handling(self):
        """Test exception handling in find_hints."""
        mock_module_finder = Mock()
        mock_module_finder.find_modules.side_effect = Exception('Test error')

        hints_gen = HintsGenerator(mock_module_finder, debug=False)

        # Mock the fallback to return empty to trigger the 'none' path
        with patch.object(hints_gen, '_get_metadata_fallback_hints', return_value=''):
            bug_info = BugInfo({'file': 'test.sv', 'unified_diff': 'diff'}, 0)
            result = hints_gen.find_hints(bug_info, ['test.scala'], 'test_container')

            # When module_finder fails and fallback is empty, source should be 'none'
            assert result['source'] == 'none'
            assert result['success'] is False
            assert 'No hints found' in result['hints']

    def test_find_hints_file_prep_exception(self):
        """Test exception handling in file preparation."""
        mock_module_finder = Mock()
        hints_gen = HintsGenerator(mock_module_finder, debug=False)

        # Mock _prepare_files_for_module_finder to raise an exception
        with patch.object(hints_gen, '_prepare_files_for_module_finder', side_effect=Exception('File prep error')):
            bug_info = BugInfo({'file': 'test.sv', 'unified_diff': 'diff'}, 0)
            result = hints_gen.find_hints(bug_info, ['test.scala'], 'test_container')

            assert result['source'] == 'error'
            assert result['success'] is False
            assert 'HintsGenerator error' in result['hints']

    def test_prepare_files_local_only(self):
        """Test preparing files with only local files."""
        mock_module_finder = Mock()
        hints_gen = HintsGenerator(mock_module_finder)

        local_files = ['/path/to/local1.scala', '/path/to/local2.scala']
        result = hints_gen._prepare_files_for_module_finder(local_files)

        # Local files should be returned as-is
        assert result == local_files
        assert hints_gen.temp_files == []
        assert hints_gen.temp_to_original == {}

    @patch('subprocess.run')
    @patch('tempfile.mkstemp')
    @patch('os.fdopen')
    def test_prepare_files_with_docker(self, mock_fdopen, mock_mkstemp, mock_subprocess):
        """Test preparing files with Docker files."""
        # Setup mocks
        mock_subprocess.return_value.stdout = 'docker file content'
        mock_mkstemp.return_value = (123, '/tmp/tempfile.scala')
        mock_file = Mock()
        mock_fdopen.return_value.__enter__.return_value = mock_file

        mock_module_finder = Mock()
        hints_gen = HintsGenerator(mock_module_finder, debug=False)

        files = ['local.scala', 'docker:container:remote.scala']
        result = hints_gen._prepare_files_for_module_finder(files)

        # Should have both local and temp file
        assert 'local.scala' in result
        assert '/tmp/tempfile.scala' in result
        assert len(result) == 2

        # Should have created temp file mapping
        assert '/tmp/tempfile.scala' in hints_gen.temp_to_original
        assert hints_gen.temp_to_original['/tmp/tempfile.scala'] == 'docker:container:remote.scala'

    @patch('subprocess.run')
    def test_read_docker_file(self, mock_subprocess):
        """Test reading a file from Docker container."""
        mock_subprocess.return_value.stdout = 'file content'

        mock_module_finder = Mock()
        hints_gen = HintsGenerator(mock_module_finder)

        docker_path = 'docker:container:file.scala'
        result = hints_gen._read_docker_file(docker_path)

        assert result == 'file content'
        mock_subprocess.assert_called_once_with(
            ['docker', 'exec', 'container', 'cat', 'file.scala'], capture_output=True, text=True, check=True
        )

    def test_read_docker_file_invalid_format(self):
        """Test reading docker file with invalid format."""
        mock_module_finder = Mock()
        hints_gen = HintsGenerator(mock_module_finder)

        with pytest.raises(ValueError, match='Invalid docker path format'):
            hints_gen._read_docker_file('invalid:path')

    @patch('subprocess.run')
    def test_extract_code_from_hits_local_file(self, mock_subprocess):
        """Test extracting code from local file hits."""
        mock_module_finder = Mock()
        hints_gen = HintsGenerator(mock_module_finder, debug=False)

        # Create a temporary test file
        test_content = 'line 1\nline 2\nline 3\nline 4\nline 5\n'
        with tempfile.NamedTemporaryFile(mode='w', delete=False) as f:
            f.write(test_content)
            temp_file_path = f.name

        try:
            hit = MockHit(temp_file_path, 'TestModule', 2, 4, 0.8)
            result = hints_gen._extract_code_from_hits([hit], 'test_container')

            assert 'TestModule (confidence: 0.80)' in result
            assert 'line 2' in result
            assert 'line 3' in result
            assert 'line 4' in result
            assert 'line 1' not in result  # Should not include line before range

        finally:
            os.unlink(temp_file_path)

    @patch('subprocess.run')
    def test_extract_code_from_hits_docker_file(self, mock_subprocess):
        """Test extracting code from Docker file hits."""
        mock_subprocess.return_value.stdout = 'docker line 1\ndocker line 2\n'

        mock_module_finder = Mock()
        hints_gen = HintsGenerator(mock_module_finder, debug=False)

        hit = MockHit('docker:container:/code/workspace/repo/test.scala', 'TestModule', 10, 12, 0.9)
        result = hints_gen._extract_code_from_hits([hit], 'container')

        assert 'TestModule (confidence: 0.90)' in result
        assert 'test.scala' in result  # Should show relative path
        assert 'docker line 1' in result
        mock_subprocess.assert_called_with(
            ['docker', 'exec', 'container', 'sed', '-n', '10,12p', '/code/workspace/repo/test.scala'],
            capture_output=True,
            text=True,
            check=True,
        )

    def test_try_module_finder_success(self):
        """Test successful module_finder execution."""
        mock_module_finder = Mock()
        mock_hits = [MockHit('test.scala', 'TestModule', 10, 20, 0.8)]
        mock_module_finder.find_modules.return_value = mock_hits

        hints_gen = HintsGenerator(mock_module_finder, debug=False)
        result = hints_gen._try_module_finder(['test.scala'], 'TestModule', 'diff')

        assert result['success']
        assert len(result['hits']) == 1
        assert result['hits'][0].confidence == 0.8

    def test_try_module_finder_low_confidence(self):
        """Test module_finder with low confidence hits."""
        mock_module_finder = Mock()
        mock_hits = [MockHit('test.scala', 'TestModule', 10, 20, 0.3)]
        mock_module_finder.find_modules.return_value = mock_hits

        hints_gen = HintsGenerator(mock_module_finder, debug=False)
        result = hints_gen._try_module_finder(['test.scala'], 'TestModule', 'diff')

        assert result['success'] is False  # Low confidence should fail
        assert len(result['hits']) == 1
        assert result['hits'][0].confidence == 0.3


def test_hints_generator_with_real_bug_info():
    """Integration test with real BugInfo object."""
    mock_module_finder = Mock()
    mock_module_finder.find_modules.return_value = []

    hints_gen = HintsGenerator(mock_module_finder, debug=False)

    # Create a realistic bug
    bug_data = {
        'file': 'Control.sv',
        'unified_diff': """--- a/Control.sv
+++ b/Control.sv
@@ -27,1 +27,1 @@
-  wire _signals_T_132 = io_opcode == 7'h3B;
+  wire _signals_T_132 = io_opcode == 7'h3F;""",
    }

    bug_info = BugInfo(bug_data, 0)

    with patch.object(hints_gen, '_get_metadata_fallback_hints', return_value=''):
        result = hints_gen.find_hints(bug_info, ['control.scala'], 'test_container')

        assert result['source'] == 'none'
        assert 'Control' in result['hints']  # Should reference the module name


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
