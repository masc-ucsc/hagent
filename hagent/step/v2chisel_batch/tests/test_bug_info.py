#!/usr/bin/env python3
"""
Unit tests for BugInfo class.
"""

import pytest
import sys
from pathlib import Path

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent.parent))

from hagent.step.v2chisel_batch.components.bug_info import BugInfo


class TestBugInfo:
    """Test cases for BugInfo class."""

    def test_basic_initialization(self):
        """Test basic BugInfo initialization with valid data."""
        bug_entry = {
            'file': 'TestModule.sv',
            'unified_diff': '--- a/TestModule.sv\n+++ b/TestModule.sv\n@@ -1,3 +1,3 @@\n-  old_line\n+  new_line',
        }

        bug_info = BugInfo(bug_entry, 0)

        assert bug_info.file_name == 'TestModule.sv'
        assert bug_info.module_name == 'TestModule'
        assert bug_info.bug_index == 0
        assert bug_info.unified_diff.startswith('---')
        assert bug_info.has_verilog_diff()
        assert bug_info.get_display_name() == 'Bug #1: TestModule.sv'

    def test_missing_file_field(self):
        """Test BugInfo with missing 'file' field."""
        bug_entry = {'unified_diff': 'some diff content'}

        bug_info = BugInfo(bug_entry, 1)

        assert bug_info.file_name == 'unknown'
        assert bug_info.module_name == 'unknown'  # os.path.splitext('unknown')[0] = 'unknown'
        assert bug_info.get_display_name() == 'Bug #2: unknown'

    def test_missing_unified_diff_field(self):
        """Test BugInfo with missing 'unified_diff' field."""
        bug_entry = {'file': 'SomeModule.sv'}

        bug_info = BugInfo(bug_entry, 2)

        assert bug_info.file_name == 'SomeModule.sv'
        assert bug_info.module_name == 'SomeModule'
        assert bug_info.unified_diff == ''
        assert not bug_info.has_verilog_diff()

    def test_empty_unified_diff(self):
        """Test BugInfo with empty unified_diff."""
        bug_entry = {
            'file': 'EmptyModule.sv',
            'unified_diff': '   \n  \t  ',  # whitespace only
        }

        bug_info = BugInfo(bug_entry, 3)

        assert not bug_info.has_verilog_diff()

    def test_to_dict_conversion(self):
        """Test conversion to dictionary."""
        bug_entry = {'file': 'DictTest.sv', 'unified_diff': 'test diff'}

        bug_info = BugInfo(bug_entry, 4)
        result_dict = bug_info.to_dict()

        expected = {
            'bug_index': 4,
            'file_name': 'DictTest.sv',
            'module_name': 'DictTest',
            'unified_diff': 'test diff',
            'has_verilog_diff': True,
        }

        assert result_dict == expected

    def test_complex_file_extension(self):
        """Test module name extraction with complex file extensions."""
        test_cases = [
            ('simple.sv', 'simple'),
            ('Module.v', 'Module'),
            ('Complex.scala.sv', 'Complex.scala'),  # Should only remove last extension
            ('NoExtension', 'NoExtension'),
            ('', None),
        ]

        for file_name, expected_module in test_cases:
            bug_entry = {'file': file_name, 'unified_diff': 'test'}
            bug_info = BugInfo(bug_entry, 0)
            assert bug_info.module_name == expected_module, f'Failed for {file_name}'


if __name__ == '__main__':
    pytest.main([__file__])
