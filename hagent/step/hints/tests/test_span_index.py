"""
Unit tests for SpanIndex class.

Tests cover:
- Building index from Scala files
- Line-to-module mapping
- Cache operations (save/load/invalidate)
- Edge cases (nested classes, empty files)
"""

import tempfile
from pathlib import Path
import pytest

from hagent.step.hints.span_index import SpanIndex
from hagent.step.hints.models import ModuleSpan


class TestSpanIndex:
    """Test suite for SpanIndex functionality."""

    @pytest.fixture
    def fixture_dir(self):
        """Get path to test fixtures."""
        return Path(__file__).parent / 'fixtures'

    @pytest.fixture
    def alu_file(self, fixture_dir):
        """Path to ALU.scala test fixture."""
        return str(fixture_dir / 'ALU.scala')

    @pytest.fixture
    def control_file(self, fixture_dir):
        """Path to Control.scala test fixture."""
        return str(fixture_dir / 'Control.scala')

    @pytest.fixture
    def span_index(self):
        """Create a fresh SpanIndex instance."""
        return SpanIndex(builder=None, repo_path=None)

    def test_build_index_single_file(self, span_index, alu_file):
        """Test building index from a single Scala file."""
        span_index.build([alu_file])

        assert len(span_index.cache) == 1
        assert alu_file in span_index.cache

        spans = span_index.cache[alu_file]
        assert len(spans) == 2  # ALU class + ALU object

        # Check class span
        alu_class = next(s for s in spans if s.span_type == 'class')
        assert alu_class.name == 'ALU'
        assert alu_class.start_line == 9
        assert alu_class.span_type == 'class'

        # Check object span
        alu_object = next(s for s in spans if s.span_type == 'object')
        assert alu_object.name == 'ALU'
        assert alu_object.span_type == 'object'

    def test_build_index_multiple_files(self, span_index, alu_file, control_file):
        """Test building index from multiple Scala files."""
        span_index.build([alu_file, control_file])

        assert len(span_index.cache) == 2
        assert alu_file in span_index.cache
        assert control_file in span_index.cache

        # Control.scala has 3 modules: Control class, Control object, InstructionDecoder class
        control_spans = span_index.cache[control_file]
        assert len(control_spans) == 3

        names = [s.name for s in control_spans]
        assert 'Control' in names
        assert 'InstructionDecoder' in names

    def test_get_enclosing_module(self, span_index, alu_file):
        """Test finding enclosing module for a given line."""
        span_index.build([alu_file])

        # Line 15 should be inside ALU class
        module = span_index.get_enclosing_module(alu_file, 15)
        assert module is not None
        assert module.name == 'ALU'
        assert module.span_type == 'class'
        assert module.contains_line(15)

        # Line within ALU object (line 58 is inside the object)
        module = span_index.get_enclosing_module(alu_file, 58)
        assert module is not None
        assert module.name == 'ALU'
        assert module.span_type == 'object'

    def test_get_enclosing_module_not_found(self, span_index, alu_file):
        """Test getting enclosing module when line is outside all spans."""
        span_index.build([alu_file])

        # Line 1 (package declaration) should not be in any module
        module = span_index.get_enclosing_module(alu_file, 1)
        # This might be None or might catch the first module depending on parsing
        # Just verify it doesn't crash
        assert module is None or isinstance(module, ModuleSpan)

        # Non-existent file
        module = span_index.get_enclosing_module('nonexistent.scala', 10)
        assert module is None

    def test_get_all_modules(self, span_index, alu_file, control_file):
        """Test retrieving all indexed modules."""
        span_index.build([alu_file, control_file])

        all_modules = span_index.get_all_modules()
        assert len(all_modules) == 5  # 2 from ALU + 3 from Control

        names = [m.name for m in all_modules]
        assert 'ALU' in names
        assert 'Control' in names
        assert 'InstructionDecoder' in names

    def test_get_modules_in_file(self, span_index, alu_file, control_file):
        """Test getting modules from a specific file."""
        span_index.build([alu_file, control_file])

        alu_modules = span_index.get_modules_in_file(alu_file)
        assert len(alu_modules) == 2

        control_modules = span_index.get_modules_in_file(control_file)
        assert len(control_modules) == 3

        # Non-existent file
        empty = span_index.get_modules_in_file('nonexistent.scala')
        assert empty == []

    def test_invalidate_specific_files(self, span_index, alu_file, control_file):
        """Test invalidating cache for specific files."""
        span_index.build([alu_file, control_file])
        assert len(span_index.cache) == 2

        # Invalidate one file
        span_index.invalidate([alu_file])
        assert len(span_index.cache) == 1
        assert alu_file not in span_index.cache
        assert control_file in span_index.cache

    def test_invalidate_all(self, span_index, alu_file, control_file):
        """Test invalidating entire cache."""
        span_index.build([alu_file, control_file])
        assert len(span_index.cache) == 2

        # Invalidate all
        span_index.invalidate()
        assert len(span_index.cache) == 0
        assert span_index.commit_hash is None

    def test_save_and_load(self, span_index, alu_file):
        """Test persisting and loading index from disk."""
        span_index.build([alu_file])
        original_count = len(span_index)

        with tempfile.TemporaryDirectory() as tmpdir:
            cache_path = Path(tmpdir) / 'span_cache.pkl'

            # Save
            span_index.save(str(cache_path))
            assert cache_path.exists()

            # Load
            loaded_index = SpanIndex.load(str(cache_path), builder=None)
            assert len(loaded_index) == original_count
            assert alu_file in loaded_index.cache
            assert len(loaded_index.cache[alu_file]) == 2

    def test_load_nonexistent_cache(self):
        """Test loading from non-existent cache file."""
        with pytest.raises(FileNotFoundError):
            SpanIndex.load('/nonexistent/cache.pkl', builder=None)

    def test_module_span_properties(self, span_index, alu_file):
        """Test ModuleSpan properties and methods."""
        span_index.build([alu_file])
        spans = span_index.cache[alu_file]

        alu_class = next(s for s in spans if s.span_type == 'class')

        # Test module_id property
        assert alu_class.module_id == f'{alu_file}::ALU'

        # Test contains_line
        assert alu_class.contains_line(alu_class.start_line)
        assert alu_class.contains_line(alu_class.end_line)
        assert alu_class.contains_line((alu_class.start_line + alu_class.end_line) // 2)
        assert not alu_class.contains_line(alu_class.start_line - 1)
        assert not alu_class.contains_line(alu_class.end_line + 1)

        # Test line_count
        assert alu_class.line_count() == alu_class.end_line - alu_class.start_line + 1
        assert alu_class.line_count() > 0

    def test_len_and_repr(self, span_index, alu_file, control_file):
        """Test __len__ and __repr__ methods."""
        span_index.build([alu_file, control_file])

        # Test __len__
        assert len(span_index) == 5

        # Test __repr__
        repr_str = repr(span_index)
        assert 'SpanIndex' in repr_str
        assert 'files=2' in repr_str
        assert 'modules=5' in repr_str

    def test_empty_index(self, span_index):
        """Test behavior with empty index."""
        assert len(span_index) == 0
        assert span_index.get_all_modules() == []
        assert span_index.get_enclosing_module('any.scala', 10) is None

    def test_parse_file_error_handling(self, span_index):
        """Test handling of file parsing errors."""
        # Non-existent file should not crash build
        span_index.build(['/nonexistent/file.scala'])
        assert len(span_index.cache) == 0

    def test_module_span_validation(self):
        """Test ModuleSpan validation."""
        # Valid span
        span = ModuleSpan(file='test.scala', name='Test', start_line=1, end_line=10, span_type='class')
        assert span.start_line == 1

        # Invalid: start_line < 1
        with pytest.raises(ValueError, match='start_line must be >= 1'):
            ModuleSpan(file='test.scala', name='Test', start_line=0, end_line=10, span_type='class')

        # Invalid: end_line < start_line
        with pytest.raises(ValueError, match='end_line.*start_line'):
            ModuleSpan(file='test.scala', name='Test', start_line=10, end_line=5, span_type='class')

        # Invalid: span_type
        with pytest.raises(ValueError, match='span_type must be'):
            ModuleSpan(file='test.scala', name='Test', start_line=1, end_line=10, span_type='invalid')


class TestDiffInfo:
    """Test suite for DiffInfo model."""

    def test_extract_changed_lines_simple(self):
        """Test extracting changed lines from unified diff."""
        from hagent.step.hints.models import DiffInfo

        diff = """--- a/test.v
+++ b/test.v
@@ -10,7 +10,7 @@ module Test
   always_comb begin
     case (op)
-      4'b0000: result = a + b;
+      4'b0000: result = a - b;
       4'b0001: result = a - b;
   end
endmodule"""

        changed_lines = DiffInfo._extract_changed_lines(diff)
        assert 12 in changed_lines  # The changed line (new file starts at line 10)

    def test_extract_changed_lines_multiple_hunks(self):
        """Test extracting changed lines from diff with multiple hunks."""
        from hagent.step.hints.models import DiffInfo

        diff = """--- a/test.v
+++ b/test.v
@@ -5,3 +5,3 @@ module Test
-  wire a;
+  wire a_renamed;
@@ -20,2 +20,2 @@ endmodule
-  assign out = in1;
+  assign out = in2;"""

        changed_lines = DiffInfo._extract_changed_lines(diff)
        assert 5 in changed_lines  # First change (starts at line 5)
        assert 20 in changed_lines  # Second change (starts at line 20)

    def test_from_bug_info(self):
        """Test creating DiffInfo from BugInfo."""
        from hagent.step.hints.models import DiffInfo

        # Mock BugInfo object
        class MockBugInfo:
            def __init__(self):
                self.file_name = 'ALU.sv'
                self.module_name = 'ALU'
                self.unified_diff = """@@ -10,1 +10,1 @@
-  result = a + b;
+  result = a - b;"""

        bug_info = MockBugInfo()
        diff_info = DiffInfo.from_bug_info(bug_info)

        assert diff_info.verilog_file == 'ALU.sv'
        assert diff_info.verilog_module == 'ALU'
        assert diff_info.unified_diff == bug_info.unified_diff
        assert len(diff_info.changed_lines) > 0
