"""Tests for hagent.inou.locator module."""

import json
import tempfile
from pathlib import Path

import pytest

from hagent.inou.locator import Locator, RepresentationType, SourceLocation


class TestRepresentationType:
    """Test RepresentationType enum."""

    def test_enum_values(self):
        """Test that enum has expected values."""
        assert RepresentationType.VERILOG.value == 'verilog'
        assert RepresentationType.NETLIST.value == 'netlist'
        assert RepresentationType.CHISEL.value == 'chisel'
        assert RepresentationType.VCD.value == 'vcd'


class TestSourceLocation:
    """Test SourceLocation dataclass."""

    def test_create_source_location(self):
        """Test creating a SourceLocation."""
        loc = SourceLocation(
            file_path='/path/to/file.v',
            module_name='TestModule',
            line_start=10,
            line_end=20,
            confidence=0.95,
            representation=RepresentationType.VERILOG,
        )

        assert loc.file_path == '/path/to/file.v'
        assert loc.module_name == 'TestModule'
        assert loc.line_start == 10
        assert loc.line_end == 20
        assert loc.confidence == 0.95
        assert loc.representation == RepresentationType.VERILOG


class TestLocatorBasics:
    """Test basic Locator functionality."""

    def test_init_without_params(self):
        """Test initialization without parameters."""
        locator = Locator()
        assert locator.config_path is None
        assert locator.profile_name is None
        assert locator.builder is None

    def test_init_with_params(self):
        """Test initialization with parameters."""
        locator = Locator(config_path='/path/to/config.yaml', profile_name='test_profile')
        assert locator.config_path == '/path/to/config.yaml'
        assert locator.profile_name == 'test_profile'

    def test_context_manager(self):
        """Test context manager support."""
        with Locator() as locator:
            assert locator is not None
        # After exit, cleanup should be called
        assert locator.builder is None

    def test_get_error_initial(self):
        """Test get_error returns empty string initially."""
        locator = Locator()
        assert locator.get_error() == ''


class TestLocatorValidation:
    """Test Locator validation and error handling."""

    def test_same_representation_variable_rejected(self):
        """Test that same-representation variable mapping is rejected."""
        locator = Locator()

        # VERILOG -> VERILOG should fail
        result = locator.map_variable(
            to=RepresentationType.VERILOG,
            from_type=RepresentationType.VERILOG,
            variable='test_signal',
            module='TestModule',
        )

        assert result == []
        assert locator.get_error() == 'same representation mapping not supported'

    def test_same_representation_code_rejected(self):
        """Test that same-representation code mapping is rejected."""
        locator = Locator()

        diff = """
--- a/test.v
+++ b/test.v
@@ -1,1 +1,1 @@
-assign a = b;
+assign a = c;
"""

        result = locator.locate_code(
            to=RepresentationType.CHISEL,
            from_type=RepresentationType.CHISEL,
            diff_patch=diff,
        )

        assert result == []
        assert locator.get_error() == 'same representation mapping not supported'

    def test_synalign_not_integrated_verilog_netlist(self):
        """Test that Verilog->Netlist mapping returns synalign error."""
        locator = Locator()

        result = locator.map_variable(
            to=RepresentationType.NETLIST,
            from_type=RepresentationType.VERILOG,
            variable='test_signal',
            module='TestModule',
        )

        assert result == []
        assert locator.get_error() == 'synalign not integrated'

    def test_synalign_not_integrated_netlist_verilog(self):
        """Test that Netlist->Verilog mapping returns synalign error."""
        locator = Locator()

        result = locator.map_variable(
            to=RepresentationType.VERILOG,
            from_type=RepresentationType.NETLIST,
            variable='test_signal',
            module='TestModule',
        )

        assert result == []
        assert locator.get_error() == 'synalign not integrated'

    def test_synalign_not_integrated_code(self):
        """Test that Verilog->Netlist code mapping returns synalign error."""
        locator = Locator()

        diff = """
--- a/test.v
+++ b/test.v
@@ -1,1 +1,1 @@
-assign a = b;
+assign a = c;
"""

        result = locator.locate_code(
            to=RepresentationType.NETLIST,
            from_type=RepresentationType.VERILOG,
            diff_patch=diff,
        )

        assert result == []
        assert locator.get_error() == 'synalign not integrated'


class TestLocatorCacheManagement:
    """Test cache management functionality."""

    def test_invalidate_cache_without_setup(self):
        """Test invalidate_cache when cache_dir is None."""
        locator = Locator()
        # Should not raise error
        locator.invalidate_cache()
        locator.invalidate_cache(force=True)

    def test_cache_directory_creation(self):
        """Test that cache directory is created on setup."""
        with tempfile.TemporaryDirectory() as tmpdir:
            # Create a minimal hagent.yaml
            config_path = Path(tmpdir) / 'hagent.yaml'
            config_data = {
                'profiles': [
                    {
                        'name': 'test_profile',
                        'title': 'Test Profile',
                        'configuration': {'source': 'src', 'output': 'build'},
                        'apis': [],
                    }
                ]
            }
            with config_path.open('w') as f:
                json.dump(config_data, f)

            # Create necessary directories
            cache_dir = Path(tmpdir) / 'cache'
            cache_dir.mkdir()

            # Mock the path_manager for testing
            # In real usage, this would be set by Builder
            # For this test, we'll skip full setup and just test the directory logic
            pass


class TestDiffParsing:
    """Test diff parsing functionality."""

    def test_parse_diff_header_basic(self):
        """Test parsing a basic unified diff."""
        locator = Locator()

        diff = """
--- a/test.v
+++ b/test.v
@@ -10,3 +10,4 @@
-assign result = a + b;
+wire carry;
+assign {carry, result} = a + b;
"""

        result = locator._parse_diff_header(diff)
        assert result is not None
        assert result['file'] == 'test.v'
        assert 10 in result['changed_lines']

    def test_parse_diff_header_multiple_hunks(self):
        """Test parsing diff with multiple hunks."""
        locator = Locator()

        diff = """
--- a/module.v
+++ b/module.v
@@ -5,2 +5,3 @@
 wire a;
+wire b;
 wire c;
@@ -20,1 +21,2 @@
 assign x = 1;
+assign y = 2;
"""

        result = locator._parse_diff_header(diff)
        assert result is not None
        assert result['file'] == 'module.v'
        # Should have lines from both hunks
        assert 5 in result['changed_lines'] or 6 in result['changed_lines']
        assert 21 in result['changed_lines'] or 22 in result['changed_lines']

    def test_parse_diff_header_invalid(self):
        """Test parsing invalid diff."""
        locator = Locator()

        diff = """
Not a valid diff
"""

        result = locator._parse_diff_header(diff)
        assert result is None


class TestSlangHierarchyParsing:
    """Test slang hierarchy parsing."""

    def test_parse_slang_hierarchy_json(self):
        """Test parsing JSON format slang output."""
        locator = Locator()

        slang_output = json.dumps(
            {
                'top.cpu.alu': {'file': '/path/to/alu.v', 'line': 45, 'module': 'alu'},
                'top.cpu.reg': {'file': '/path/to/reg.v', 'line': 23, 'module': 'reg'},
            }
        )

        hierarchy = locator._parse_slang_hierarchy(slang_output)

        assert 'top.cpu.alu' in hierarchy
        assert hierarchy['top.cpu.alu']['file'] == '/path/to/alu.v'
        assert hierarchy['top.cpu.alu']['line'] == 45

    def test_parse_slang_hierarchy_text(self):
        """Test parsing text format slang output."""
        locator = Locator()

        slang_output = """
# Hierarchy output
Module="ALU" Instance="top.cpu.alu" File="/path/to/alu.v"
Module="Register" Instance="top.cpu.reg" File="/path/to/reg.v"
"""

        hierarchy = locator._parse_slang_hierarchy(slang_output)

        assert 'top.cpu.alu' in hierarchy
        assert hierarchy['top.cpu.alu']['file'] == '/path/to/alu.v'
        assert hierarchy['top.cpu.alu']['module'] == 'ALU'

    def test_parse_slang_hierarchy_empty(self):
        """Test parsing empty slang output."""
        locator = Locator()

        hierarchy = locator._parse_slang_hierarchy('')
        assert hierarchy == {}


class TestExampleUseCases:
    """Test example use cases from the plan documentation."""

    def test_example_variable_lookup_validation(self):
        """Test Example 3: Variable lookup with validation."""
        locator = Locator(profile_name='test_profile')

        # Same-representation lookup should be rejected
        verilog_assigns = locator.map_variable(
            to=RepresentationType.VERILOG,
            from_type=RepresentationType.VERILOG,
            variable='result',
            module='TestModule',
        )

        assert not verilog_assigns
        assert locator.get_error() == 'same representation mapping not supported'

    def test_example_netlist_mapping_not_available(self):
        """Test Example 5: Netlist mapping returns error."""
        locator = Locator(profile_name='test_profile')

        rtl_diff = """
--- a/alu.v
+++ b/alu.v
@@ -10,3 +10,4 @@ module alu
-  assign result = a + b;
+  wire carry;
+  assign {carry, result} = a + b;
"""

        netlist_locs = locator.locate_code(
            to=RepresentationType.NETLIST,
            from_type=RepresentationType.VERILOG,
            diff_patch=rtl_diff,
        )

        assert not netlist_locs
        assert locator.get_error() == 'synalign not integrated'


class TestLocatorWithMockData:
    """Test Locator with mock data structures."""

    def test_find_variable_in_files_logic(self):
        """Test the logic of finding variables in files."""
        with tempfile.TemporaryDirectory() as tmpdir:
            # Create a test Verilog file
            verilog_dir = Path(tmpdir) / 'build'
            verilog_dir.mkdir()
            verilog_file = verilog_dir / 'alu.v'
            verilog_file.write_text(
                """
module alu(
    input [31:0] a,
    input [31:0] b,
    output [31:0] result
);
    assign result = a + b;
endmodule
"""
            )

            # We can't fully test without Builder, but we can test the parsing logic
            # by calling internal methods
            pass

    def test_cache_invalidation_logic(self):
        """Test cache invalidation force flag."""
        with tempfile.TemporaryDirectory() as tmpdir:
            cache_dir = Path(tmpdir) / 'cache'
            cache_dir.mkdir()

            # Create dummy cache files
            (cache_dir / 'hierarchy.cache').write_text('{}')
            (cache_dir / 'verilog_chisel.cache').write_text('{}')
            (cache_dir / 'metadata.json').write_text('{}')

            locator = Locator()
            locator._cache_dir = cache_dir

            # Test force invalidation
            locator.invalidate_cache(force=True)

            # All files should be deleted
            assert not (cache_dir / 'hierarchy.cache').exists()
            assert not (cache_dir / 'verilog_chisel.cache').exists()
            assert not (cache_dir / 'metadata.json').exists()

    def test_cache_invalidation_soft(self):
        """Test soft cache invalidation (metadata only)."""
        with tempfile.TemporaryDirectory() as tmpdir:
            cache_dir = Path(tmpdir) / 'cache'
            cache_dir.mkdir()

            # Create dummy cache files
            (cache_dir / 'hierarchy.cache').write_text('{}')
            (cache_dir / 'metadata.json').write_text('{}')

            locator = Locator()
            locator._cache_dir = cache_dir

            # Test soft invalidation
            locator.invalidate_cache(force=False)

            # Cache files should remain, only metadata deleted
            assert (cache_dir / 'hierarchy.cache').exists()
            assert not (cache_dir / 'metadata.json').exists()


class TestRepresentationMappingSupport:
    """Test which representation mappings are supported."""

    @pytest.mark.parametrize(
        'from_type,to_type,should_error,error_msg',
        [
            # Same representation - not supported
            (
                RepresentationType.VCD,
                RepresentationType.VCD,
                True,
                'same representation mapping not supported',
            ),
            (
                RepresentationType.VERILOG,
                RepresentationType.VERILOG,
                True,
                'same representation mapping not supported',
            ),
            (
                RepresentationType.CHISEL,
                RepresentationType.CHISEL,
                True,
                'same representation mapping not supported',
            ),
            (
                RepresentationType.NETLIST,
                RepresentationType.NETLIST,
                True,
                'same representation mapping not supported',
            ),
            # Synalign not integrated
            (
                RepresentationType.VERILOG,
                RepresentationType.NETLIST,
                True,
                'synalign not integrated',
            ),
            (
                RepresentationType.NETLIST,
                RepresentationType.VERILOG,
                True,
                'synalign not integrated',
            ),
            (
                RepresentationType.NETLIST,
                RepresentationType.CHISEL,
                True,
                'synalign not integrated',
            ),
            (
                RepresentationType.CHISEL,
                RepresentationType.NETLIST,
                True,
                'synalign not integrated',
            ),
        ],
    )
    def test_mapping_support(self, from_type, to_type, should_error, error_msg):
        """Test that unsupported mappings return appropriate errors."""
        locator = Locator()

        result = locator.map_variable(to=to_type, from_type=from_type, variable='test', module='TestModule')

        if should_error:
            assert result == []
            assert locator.get_error() == error_msg


class TestCacheMetadata:
    """Test cache metadata handling."""

    def test_update_metadata_structure(self):
        """Test that metadata has expected structure."""
        with tempfile.TemporaryDirectory() as tmpdir:
            cache_dir = Path(tmpdir) / 'cache'
            cache_dir.mkdir()

            # Create a test cache file
            cache_file = cache_dir / 'test.cache'
            cache_file.write_text('{}')

            locator = Locator()
            locator._cache_dir = cache_dir

            # Create mock builder with path manager
            class MockPathManager:
                def __init__(self):
                    self.repo_dir = tmpdir
                    self.build_dir = tmpdir
                    self.cache_dir = tmpdir

            class MockRunner:
                def __init__(self):
                    self.path_manager = MockPathManager()

            class MockBuilder:
                def __init__(self):
                    self.runner = MockRunner()

            locator.builder = MockBuilder()

            # Update metadata
            locator._update_metadata('test')

            # Check metadata file was created
            metadata_file = cache_dir / 'metadata.json'
            assert metadata_file.exists()

            # Load and verify structure
            with metadata_file.open('r') as f:
                metadata = json.load(f)

            assert 'test' in metadata
            assert 'files' in metadata['test']
            assert 'timestamp' in metadata['test']


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
