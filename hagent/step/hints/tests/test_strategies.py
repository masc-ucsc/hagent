"""
Unit tests for hint generation strategies.

Tests cover:
- ModuleFinder strategy (fuzzy name matching)
- SourceLocator strategy (RTL breadcrumb mapping)
- FuzzyGrepStrategy (identifier search using existing tools)
"""

from pathlib import Path
import pytest

from hagent.step.hints.span_index import SpanIndex
from hagent.step.hints.models import DiffInfo
from hagent.step.hints.module_finder_strategy import ModuleFinder
from hagent.step.hints.source_locator import SourceLocator
from hagent.step.hints.fuzzy_grep_strategy import FuzzyGrepStrategy


class TestModuleFinder:
    """Test suite for ModuleFinder strategy."""

    @pytest.fixture
    def span_index(self):
        """Create span index with test fixtures."""
        fixture_dir = Path(__file__).parent / 'fixtures'
        alu_file = str(fixture_dir / 'ALU.scala')
        control_file = str(fixture_dir / 'Control.scala')

        index = SpanIndex()
        index.build([alu_file, control_file])
        return index

    @pytest.fixture
    def strategy(self):
        """Create ModuleFinder strategy."""
        return ModuleFinder(min_confidence=0.3)

    def test_exact_match(self, strategy, span_index):
        """Test exact module name match."""
        diff_info = DiffInfo(verilog_file='ALU.sv', verilog_module='ALU', unified_diff='')

        hints = strategy.generate_hints(diff_info, span_index, builder=None)

        assert len(hints) > 0
        # Should find ALU module with high confidence
        alu_hints = [h for h in hints if h.span.name == 'ALU']
        assert len(alu_hints) > 0
        assert alu_hints[0].confidence == 1.0  # Exact match

    def test_case_insensitive_match(self, strategy, span_index):
        """Test case-insensitive matching."""
        diff_info = DiffInfo(verilog_file='alu.sv', verilog_module='alu', unified_diff='')

        hints = strategy.generate_hints(diff_info, span_index, builder=None)

        assert len(hints) > 0
        alu_hints = [h for h in hints if h.span.name == 'ALU']
        assert len(alu_hints) > 0
        assert alu_hints[0].confidence == 1.0  # Case-insensitive exact match

    def test_partial_match(self, strategy, span_index):
        """Test partial name matching."""
        diff_info = DiffInfo(verilog_file='Control.sv', verilog_module='Control', unified_diff='')

        hints = strategy.generate_hints(diff_info, span_index, builder=None)

        assert len(hints) > 0
        control_hints = [h for h in hints if 'Control' in h.span.name]
        assert len(control_hints) > 0

    def test_no_match(self, strategy, span_index):
        """Test no matches for unrelated module."""
        diff_info = DiffInfo(verilog_file='Nonexistent.sv', verilog_module='XyZZy123', unified_diff='')

        hints = strategy.generate_hints(diff_info, span_index, builder=None)

        # Should return empty or very low confidence hints
        assert all(h.confidence < 0.5 for h in hints)

    def test_confidence_ordering(self, strategy, span_index):
        """Test that hints are ordered by confidence."""
        diff_info = DiffInfo(verilog_file='ALU.sv', verilog_module='ALU', unified_diff='')

        hints = strategy.generate_hints(diff_info, span_index, builder=None)

        if len(hints) > 1:
            for i in range(len(hints) - 1):
                assert hints[i].confidence >= hints[i + 1].confidence

    def test_evidence_structure(self, strategy, span_index):
        """Test that evidence dictionary has expected keys."""
        diff_info = DiffInfo(verilog_file='ALU.sv', verilog_module='ALU', unified_diff='')

        hints = strategy.generate_hints(diff_info, span_index, builder=None)

        assert len(hints) > 0
        evidence = hints[0].evidence
        assert 'verilog_module' in evidence
        assert 'chisel_module' in evidence
        assert 'fuzzy_ratio' in evidence
        assert 'match_type' in evidence

    def test_normalize_name(self, strategy):
        """Test name normalization."""
        assert strategy._normalize_name('ALU_Module') == 'alu'
        assert strategy._normalize_name('Top_Control') == 'control'
        assert strategy._normalize_name('MyModule') == 'my'  # 'module' suffix stripped

    def test_string_similarity(self, strategy):
        """Test string similarity calculation."""
        assert strategy._string_similarity('abc', 'abc') == 1.0
        assert strategy._string_similarity('abc', 'xyz') < 0.5
        assert strategy._string_similarity('', '') == 1.0
        assert strategy._string_similarity('a', '') == 0.0


class TestSourceLocator:
    """Test suite for SourceLocator strategy."""

    @pytest.fixture
    def strategy(self):
        """Create SourceLocator strategy."""
        return SourceLocator()

    def test_name_property(self, strategy):
        """Test strategy name."""
        assert strategy.name == 'source_locator'

    def test_no_builder_returns_empty(self, strategy):
        """Test that strategy returns empty hints without builder."""
        diff_info = DiffInfo(verilog_file='ALU.sv', verilog_module='ALU', unified_diff='')
        span_index = SpanIndex()

        hints = strategy.generate_hints(diff_info, span_index, builder=None)

        assert hints == []

    def test_metadata_pattern(self, strategy):
        """Test metadata pattern regex."""
        test_content = """
        // @[ALU.scala:15:3]
        /* @[Control.scala:42:7] */
        assign result = a + b; // @[ALU.scala:20:10]
        """

        matches = list(strategy.metadata_pattern.finditer(test_content))
        assert len(matches) == 3

        # Check first match
        assert matches[0].group(1) == 'ALU.scala'
        assert matches[0].group(2) == '15'
        assert matches[0].group(3) == '3'

    def test_locality_factor_computation(self, strategy):
        """Test locality factor calculation."""
        breadcrumb_lines = [10, 12, 15]
        changed_lines = {11, 13}

        locality = strategy._compute_locality_factor(breadcrumb_lines, changed_lines)

        # Should be high since breadcrumbs are close to changed lines
        assert 0.5 <= locality <= 1.0

        # Test with distant lines
        distant_breadcrumbs = [100, 200, 300]
        locality_distant = strategy._compute_locality_factor(distant_breadcrumbs, changed_lines)

        # Should be lower than close breadcrumbs
        assert locality_distant < locality


class TestFuzzyGrepStrategy:
    """Test suite for FuzzyGrepStrategy."""

    @pytest.fixture
    def span_index(self):
        """Create span index with test fixtures."""
        fixture_dir = Path(__file__).parent / 'fixtures'
        alu_file = str(fixture_dir / 'ALU.scala')
        control_file = str(fixture_dir / 'Control.scala')

        index = SpanIndex()
        index.build([alu_file, control_file])
        return index

    @pytest.fixture
    def strategy(self):
        """Create FuzzyGrepStrategy."""
        return FuzzyGrepStrategy(threshold=70, min_matches=1)

    def test_name_property(self, strategy):
        """Test strategy name."""
        assert strategy.name == 'fuzzy_grep'

    def test_extract_identifiers_from_diff(self, strategy):
        """Test identifier extraction using existing tool."""
        diff = """--- a/ALU.v
+++ b/ALU.v
@@ -10,1 +10,1 @@
-  result = inputx + inputy;
+  result = inputx - inputy;
"""
        from hagent.tool.extract_verilog_diff_keywords import Extract_verilog_diff_keywords

        identifiers = Extract_verilog_diff_keywords.get_user_variables(diff)

        assert 'result' in identifiers or 'inputx' in identifiers or 'inputy' in identifiers

    def test_search_finds_matches(self, strategy, span_index):
        """Test that fuzzy search finds relevant modules."""
        # Create diff with identifiers that appear in ALU.scala
        diff = """--- a/ALU.v
+++ b/ALU.v
@@ -10,1 +10,1 @@
-  result = operation + inputx;
+  result = operation - inputx;
"""
        diff_info = DiffInfo(verilog_file='ALU.v', verilog_module='ALU', unified_diff=diff)

        hints = strategy.generate_hints(diff_info, span_index, builder=None)

        # Should find ALU module (contains 'operation', 'inputx', 'result')
        alu_hints = [h for h in hints if h.span.name == 'ALU']
        assert len(alu_hints) > 0
        assert alu_hints[0].confidence > 0.0

    def test_no_identifiers_returns_empty(self, strategy, span_index):
        """Test that empty diff returns no hints."""
        diff_info = DiffInfo(verilog_file='test.v', verilog_module='test', unified_diff='')

        hints = strategy.generate_hints(diff_info, span_index, builder=None)

        assert hints == []

    def test_evidence_structure(self, strategy, span_index):
        """Test that evidence dictionary has expected keys."""
        diff = """--- a/ALU.v
+++ b/ALU.v
@@ -10,1 +10,1 @@
-  result = operation;
+  result = inputx;
"""
        diff_info = DiffInfo(verilog_file='ALU.v', verilog_module='ALU', unified_diff=diff)

        hints = strategy.generate_hints(diff_info, span_index, builder=None)

        if hints:
            evidence = hints[0].evidence
            assert 'match_count' in evidence
            assert 'match_density' in evidence
            assert 'matched_lines' in evidence

    def test_min_matches_threshold(self):
        """Test min_matches filtering."""
        strategy = FuzzyGrepStrategy(threshold=70, min_matches=5)
        assert strategy.min_matches == 5


class TestStrategyComparison:
    """Test comparing strategies on the same input."""

    @pytest.fixture
    def span_index(self):
        """Create span index with test fixtures."""
        fixture_dir = Path(__file__).parent / 'fixtures'
        alu_file = str(fixture_dir / 'ALU.scala')
        control_file = str(fixture_dir / 'Control.scala')

        index = SpanIndex()
        index.build([alu_file, control_file])
        return index

    def test_all_strategies_implement_interface(self):
        """Test that all strategies implement the required interface."""
        strategies = [ModuleFinder(), SourceLocator(), FuzzyGrepStrategy()]

        for strategy in strategies:
            assert hasattr(strategy, 'name')
            assert hasattr(strategy, 'generate_hints')
            assert callable(strategy.generate_hints)

    def test_strategies_return_correct_source(self, span_index):
        """Test that each strategy sets correct source name."""
        diff_info = DiffInfo(verilog_file='ALU.sv', verilog_module='ALU', unified_diff='')

        mf = ModuleFinder()
        mf_hints = mf.generate_hints(diff_info, span_index)
        assert all(h.source == 'module_finder' for h in mf_hints)

        sl = SourceLocator()
        sl_hints = sl.generate_hints(diff_info, span_index, builder=None)
        assert all(h.source == 'source_locator' for h in sl_hints)

        fg = FuzzyGrepStrategy()
        fg_hints = fg.generate_hints(diff_info, span_index)
        assert all(h.source == 'fuzzy_grep' for h in fg_hints)
