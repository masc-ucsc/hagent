#!/usr/bin/env python3
# hagent/step/v2chisel_batch/tests/test_bug_selector.py
# See LICENSE file for details

"""Tests for bug_selector module."""

import tempfile
from pathlib import Path

import pytest
from ruamel.yaml import YAML

from hagent.step.v2chisel_batch.bug_selector import BugSelector, load_successful_bugs, parse_bug_range


# Test fixtures
@pytest.fixture
def sample_bugs():
    """Create sample bug list for testing."""
    return [
        {'verilog_file': 'ALU.sv', 'module_name': 'ALU'},
        {'verilog_file': 'ALU.sv', 'module_name': 'ALU'},
        {'verilog_file': 'Control.sv', 'module_name': 'Control'},
        {'verilog_file': 'NextPC.sv', 'module_name': 'NextPC'},
        {'verilog_file': 'ALU.sv', 'module_name': 'ALU'},
        {'verilog_file': 'ALU.sv', 'module_name': 'ALU'},
        {'verilog_file': 'Control.sv', 'module_name': 'Control'},
        {'verilog_file': 'NextPC.sv', 'module_name': 'NextPC'},
        {'verilog_file': 'ALU.sv', 'module_name': 'ALU'},
        {'verilog_file': 'ALU.sv', 'module_name': 'ALU'},
    ]


@pytest.fixture
def sample_output_yaml():
    """Create a sample output YAML file with some successful bugs."""
    data = {
        'v2chisel_batch_with_llm': {
            'total_bugs': 10,
            'bug_results': [
                {'bug_index': 0, 'lec_success': True, 'lec_equivalent': True},  # Bug #1 - SUCCESS
                {'bug_index': 1, 'lec_success': False, 'lec_equivalent': False},  # Bug #2 - FAIL
                {'bug_index': 2, 'lec_success': True, 'lec_equivalent': True},  # Bug #3 - SUCCESS
                {'bug_index': 3, 'lec_success': False, 'lec_equivalent': False},  # Bug #4 - FAIL
                {'bug_index': 4, 'lec_success': True, 'lec_equivalent': True},  # Bug #5 - SUCCESS
                {'bug_index': 5, 'lec_success': False, 'lec_equivalent': False},  # Bug #6 - FAIL
                {'bug_index': 6, 'lec_success': False, 'lec_equivalent': False},  # Bug #7 - FAIL
                {'bug_index': 7, 'lec_success': True, 'lec_equivalent': True},  # Bug #8 - SUCCESS
                {'bug_index': 8, 'lec_success': False, 'lec_equivalent': False},  # Bug #9 - FAIL
                {'bug_index': 9, 'lec_success': True, 'lec_equivalent': True},  # Bug #10 - SUCCESS
            ],
        }
    }

    # Write to temporary file
    with tempfile.NamedTemporaryFile(mode='w', suffix='.yaml', delete=False) as f:
        yaml = YAML()
        yaml.dump(data, f)
        return f.name


class TestBugSelector:
    """Tests for BugSelector class."""

    def test_no_filters(self, sample_bugs):
        """Test that no filters returns all bugs."""
        selector = BugSelector(sample_bugs)
        selected = selector.get_bugs()

        assert len(selected) == 10
        assert selected == sample_bugs

    def test_select_single_bug(self, sample_bugs):
        """Test selecting a single bug."""
        selector = BugSelector(sample_bugs)
        selected = selector.select_by_range('5').get_bugs()

        assert len(selected) == 1
        assert selected[0] == sample_bugs[4]  # Bug #5 (0-based index 4)

    def test_select_range(self, sample_bugs):
        """Test selecting a range of bugs."""
        selector = BugSelector(sample_bugs)
        selected = selector.select_by_range('3-7').get_bugs()

        assert len(selected) == 5
        assert selected == sample_bugs[2:7]  # Bugs 3-7

    def test_select_list(self, sample_bugs):
        """Test selecting a list of bugs."""
        selector = BugSelector(sample_bugs)
        selected = selector.select_by_range('1,3,5,7').get_bugs()

        assert len(selected) == 4
        assert selected[0] == sample_bugs[0]  # Bug #1
        assert selected[1] == sample_bugs[2]  # Bug #3
        assert selected[2] == sample_bugs[4]  # Bug #5
        assert selected[3] == sample_bugs[6]  # Bug #7

    def test_select_combined(self, sample_bugs):
        """Test selecting with combined range specification."""
        selector = BugSelector(sample_bugs)
        selected = selector.select_by_range('1-3,5,8-10').get_bugs()

        assert len(selected) == 7
        # Bugs: 1, 2, 3, 5, 8, 9, 10
        expected_indices = [0, 1, 2, 4, 7, 8, 9]
        for i, idx in enumerate(expected_indices):
            assert selected[i] == sample_bugs[idx]

    def test_skip_successful(self, sample_bugs, sample_output_yaml):
        """Test skipping bugs that passed LEC."""
        selector = BugSelector(sample_bugs)
        selected = selector.skip_successful(sample_output_yaml).get_bugs()

        # Successful bugs: 1, 3, 5, 8, 10 (5 bugs)
        # Should have 5 remaining bugs: 2, 4, 6, 7, 9
        assert len(selected) == 5

        # Check that we have the right bugs
        expected_indices = [1, 3, 5, 6, 8]  # 0-based indices for bugs 2, 4, 6, 7, 9
        for i, idx in enumerate(expected_indices):
            assert selected[i] == sample_bugs[idx]

        # Clean up
        Path(sample_output_yaml).unlink()

    def test_chained_filters(self, sample_bugs, sample_output_yaml):
        """Test chaining multiple filters."""
        # Skip successful (removes bugs 1, 3, 5, 8, 10), then select range 2-7
        # After skip_successful: remaining bugs are 2, 4, 6, 7, 9
        # After select_by_range('2-7'): intersection of (not successful) AND (in range 2-7)
        #   - Not successful: 2, 4, 6, 7, 9
        #   - In range 2-7: 2, 3, 4, 5, 6, 7
        #   - Intersection: 2, 4, 6, 7
        selector = BugSelector(sample_bugs)
        selected = selector.skip_successful(sample_output_yaml).select_by_range('2-7').get_bugs()

        assert len(selected) == 4
        # Should be bugs 2, 4, 6, 7 (0-based indices: 1, 3, 5, 6)
        expected_indices = [1, 3, 5, 6]
        for i, idx in enumerate(expected_indices):
            assert selected[i] == sample_bugs[idx]

        # Clean up
        Path(sample_output_yaml).unlink()

    def test_get_selected_indices(self, sample_bugs):
        """Test getting selected bug indices."""
        selector = BugSelector(sample_bugs)
        selector.select_by_range('1,3,5,7,9')

        indices = selector.get_selected_indices()
        assert indices == [1, 3, 5, 7, 9]

    def test_get_selection_summary(self, sample_bugs):
        """Test getting selection summary."""
        selector = BugSelector(sample_bugs)
        selector.select_by_range('1-5')

        summary = selector.get_selection_summary()
        assert '5 of 10 bugs' in summary
        assert 'range=1-5' in summary


class TestParseRangeSpec:
    """Tests for range specification parsing."""

    def test_single_number(self):
        """Test parsing a single number."""
        indices = BugSelector._parse_range_spec('5')
        assert indices == {5}

    def test_simple_range(self):
        """Test parsing a simple range."""
        indices = BugSelector._parse_range_spec('1-5')
        assert indices == {1, 2, 3, 4, 5}

    def test_list(self):
        """Test parsing a list."""
        indices = BugSelector._parse_range_spec('1,3,5,7')
        assert indices == {1, 3, 5, 7}

    def test_combined(self):
        """Test parsing combined specification."""
        indices = BugSelector._parse_range_spec('1-3,5,8-10,15')
        assert indices == {1, 2, 3, 5, 8, 9, 10, 15}

    def test_with_spaces(self):
        """Test parsing with spaces."""
        indices = BugSelector._parse_range_spec('1 - 5, 8, 10 - 12')
        assert indices == {1, 2, 3, 4, 5, 8, 10, 11, 12}

    def test_invalid_range_format(self):
        """Test that invalid range format raises error."""
        with pytest.raises(ValueError, match='Invalid range format'):
            BugSelector._parse_range_spec('1-2-3')

    def test_invalid_number(self):
        """Test that invalid number raises error."""
        with pytest.raises(ValueError, match='Invalid bug index'):
            BugSelector._parse_range_spec('abc')

    def test_negative_index(self):
        """Test that negative index raises error."""
        with pytest.raises(ValueError, match='empty start or end'):
            BugSelector._parse_range_spec('-5')

    def test_zero_index(self):
        """Test that zero index raises error."""
        with pytest.raises(ValueError, match='must be >= 1'):
            BugSelector._parse_range_spec('0')

    def test_reversed_range(self):
        """Test that reversed range raises error."""
        with pytest.raises(ValueError, match='start must be <= end'):
            BugSelector._parse_range_spec('10-5')


class TestLoadSuccessfulBugs:
    """Tests for loading successful bugs from output file."""

    def test_load_successful(self, sample_output_yaml):
        """Test loading successful bugs."""
        successful = BugSelector._load_successful_bugs(sample_output_yaml)

        # Bugs 1, 3, 5, 8, 10 passed (1-based)
        assert successful == {1, 3, 5, 8, 10}

        # Clean up
        Path(sample_output_yaml).unlink()

    def test_nonexistent_file(self):
        """Test loading from nonexistent file."""
        successful = BugSelector._load_successful_bugs('/nonexistent/file.yaml')
        assert successful == set()

    def test_empty_file(self):
        """Test loading from empty file."""
        with tempfile.NamedTemporaryFile(mode='w', suffix='.yaml', delete=False) as f:
            f.write('')
            temp_file = f.name

        successful = BugSelector._load_successful_bugs(temp_file)
        assert successful == set()

        Path(temp_file).unlink()


class TestConvenienceFunctions:
    """Tests for convenience functions."""

    def test_parse_bug_range(self):
        """Test parse_bug_range convenience function."""
        indices = parse_bug_range('1-5,8,10-12')
        assert indices == [1, 2, 3, 4, 5, 8, 10, 11, 12]

    def test_load_successful_bugs(self, sample_output_yaml):
        """Test load_successful_bugs convenience function."""
        successful = load_successful_bugs(sample_output_yaml)
        assert successful == [1, 3, 5, 8, 10]

        Path(sample_output_yaml).unlink()
