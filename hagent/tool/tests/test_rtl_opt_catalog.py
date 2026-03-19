"""Tests for the RTL optimization technique catalog and OptimizationMemory."""

import pytest

from hagent.tool.memory import OptimizationMemory, Memory_shot
from hagent.tool.rtl_opt_catalog import TECHNIQUES, seed_db


@pytest.fixture
def opt_db(tmp_path):
    """Create a temporary OptimizationMemory for testing."""
    db_path = str(tmp_path / 'test_opt_db')
    return OptimizationMemory(db_path=db_path, learn=True)


class TestOptCatalog:
    def test_techniques_defined(self):
        """All four technique categories are present."""
        categories = {t.category for t in TECHNIQUES}
        assert 'opt_logic_duplication' in categories
        assert 'opt_critical_signal_isolation' in categories
        assert 'opt_shannon_expansion' in categories
        assert 'opt_tree_balancing' in categories

    def test_each_technique_has_examples(self):
        """Every technique has at least one (before, after) pair."""
        for tech in TECHNIQUES:
            assert len(tech.examples) >= 1, f'{tech.category} has no examples'
            for before, after in tech.examples:
                assert len(before.strip()) > 0
                assert len(after.strip()) > 0

    def test_seed_db_populates(self, opt_db):
        """seed_db inserts all examples into the memory DB."""
        count = seed_db(opt_db)
        assert count == sum(len(t.examples) for t in TECHNIQUES)
        assert count >= 4  # at least one per technique

    def test_find_similar_returns_results(self, opt_db):
        """Semantic cross-category search finds relevant examples."""
        seed_db(opt_db)

        query = 'if (req[0]) result = data[0]; else if (req[1]) result = data[1];'
        results = opt_db.find_similar(query_code=query, n_results=2)
        assert len(results) > 0
        assert results[0].description  # description should be populated

    def test_find_similar_has_description(self, opt_db):
        """Returned Memory_shot objects carry the technique description."""
        seed_db(opt_db)
        results = opt_db.find_similar(query_code='assign shared_sel = mode_a & flag_b;', n_results=1)
        assert len(results) == 1
        assert len(results[0].description) > 10

    def test_find_by_category_isolates(self, opt_db):
        """find_by_category only returns that category."""
        seed_db(opt_db)

        results = opt_db.find_by_category(category='opt_logic_duplication', query_code='fanout mux select', n_results=5)
        for r in results:
            assert 'fanout' in r.description.lower() or 'duplicate' in r.description.lower()

    def test_nonexistent_category_returns_empty(self, opt_db):
        """Querying a category that has no entries returns nothing."""
        seed_db(opt_db)
        results = opt_db.find_by_category(category='nonexistent_category', query_code='always_comb begin', n_results=5)
        assert len(results) == 0

    def test_memory_shot_description_default(self):
        """Memory_shot with no description defaults to empty string."""
        shot = Memory_shot(question='q', answer='a')
        assert shot.description == ''
