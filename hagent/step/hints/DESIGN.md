# Multi-Strategy Hint Generation - Design Document

## Overview
This document defines the interfaces and data structures for the new multi-strategy hint generation system that combines ModuleFinder, SourceLocator, and FuzzyGrep strategies.

## Data Structures

### Core Models

```python
@dataclass
class ModuleSpan:
    """Represents a Scala/Chisel class or object span in a file."""
    file: str  # Absolute path or docker:container:path
    name: str  # Class/object name
    start_line: int  # 1-indexed
    end_line: int  # 1-indexed inclusive
    span_type: str  # "class" or "object"

@dataclass
class ModuleHint:
    """Evidence from a single strategy about a candidate module."""
    module_id: str  # Unique identifier: f"{file}::{name}"
    span: ModuleSpan
    confidence: float  # [0.0, 1.0]
    source: str  # "module_finder", "source_locator", or "fuzzy_grep"
    evidence: Dict[str, Any]  # Strategy-specific metadata

    # Evidence examples:
    # - module_finder: {"fuzzy_ratio": 0.88, "verilog_module": "ALU"}
    # - source_locator: {"breadcrumb_count": 12, "locality_factor": 0.85, "mean_distance": 15}
    # - fuzzy_grep: {"identifiers": {"alu_op": 0.92, "rs1": 0.87}, "hit_count": 8}

@dataclass
class ModuleCandidate:
    """Unified candidate module with evidence from all sources."""
    module_id: str
    span: ModuleSpan
    scores: Dict[str, float]  # {"mf": 0.88, "sl": 0.95, "fg": 0.76}
    fused_score: float  # Combined confidence [0.0, 1.0]
    sources_hit: int  # Number of strategies that found this module (1-3)
    all_evidence: List[ModuleHint]  # All hints contributing to this candidate

@dataclass
class TrialRecord:
    """Ledger entry tracking attempt history for a module candidate."""
    module_id: Dict[str, str]  # {"file": "path/Foo.scala", "name": "Foo"}
    score: float
    sources: Dict[str, float]  # Per-source scores {"mf": 0.88, "sl": 0.95, "fg": 0.76}
    tried: bool
    attempts: int
    iteration_last: int
    outcome_last: str  # "success" | "compile_fail" | "lec_fail" | "rejected" | "none"
    commit_hash: str  # Git commit to detect code changes
    timestamps: List[str]  # ISO timestamps of attempts
    notes: str  # Optional human-readable notes
```

### Input Structure

```python
@dataclass
class DiffInfo:
    """Input information about the bug/diff to analyze."""
    verilog_file: str  # RTL file name (e.g., "ALU.sv")
    verilog_module: str  # Module name extracted from file
    unified_diff: str  # Verilog unified diff
    changed_lines: Set[int]  # Line numbers changed in RTL (for locality)

    # Optional: extracted from diff
    identifiers: Dict[str, List[str]]  # {"ports": [...], "signals": [...], "module": [...]}
```

## Interfaces

### Strategy Base Class

```python
class HintStrategy(ABC):
    """Abstract base for hint generation strategies."""

    @abstractmethod
    def generate_hints(
        self,
        diff_info: DiffInfo,
        span_index: SpanIndex,
        builder: Builder
    ) -> List[ModuleHint]:
        """
        Generate module hints for the given diff.

        Args:
            diff_info: Information about the bug/diff
            span_index: Pre-built index of module spans
            builder: Builder instance for file I/O

        Returns:
            List of ModuleHint objects (may be empty)
        """
        pass

    @property
    @abstractmethod
    def name(self) -> str:
        """Strategy identifier: 'module_finder', 'source_locator', 'fuzzy_grep'"""
        pass
```

### Span Index

```python
class SpanIndex:
    """Cache of Scala/Chisel module spans for efficient lookup."""

    def __init__(self, builder: Builder, repo_path: str):
        self.builder = builder
        self.repo_path = repo_path
        self.cache: Dict[str, List[ModuleSpan]] = {}  # file -> spans
        self.commit_hash: Optional[str] = None

    def build(self, scala_files: List[str]) -> None:
        """Build index from list of Scala files."""

    def get_enclosing_module(self, file: str, line: int) -> Optional[ModuleSpan]:
        """Find the module span that contains the given line."""

    def get_all_modules(self) -> List[ModuleSpan]:
        """Return all indexed module spans."""

    def invalidate(self, files: Optional[List[str]] = None) -> None:
        """Invalidate cache for specific files or entire index."""

    def save(self, cache_path: str) -> None:
        """Persist index to disk (pickle)."""

    @classmethod
    def load(cls, cache_path: str, builder: Builder) -> 'SpanIndex':
        """Load index from disk."""
```

### Unifier

```python
class HintUnifier:
    """Aggregates hints from multiple strategies into ranked candidates."""

    def __init__(
        self,
        span_index: SpanIndex,
        strategies: List[HintStrategy],
        fusion_config: Optional[Dict] = None
    ):
        self.span_index = span_index
        self.strategies = strategies
        self.fusion_config = fusion_config or self._default_fusion_config()

    def run_strategies(self, diff_info: DiffInfo, builder: Builder) -> List[ModuleHint]:
        """Run all strategies in parallel and collect hints."""

    def aggregate_evidence(self, hints: List[ModuleHint]) -> List[ModuleCandidate]:
        """
        Group hints by module_id and compute fused scores.

        Fusion formula:
            fused_score = min(1.0, max(mf, sl, fg) + 0.05 * (sources_hit - 1))
        """

    def run_and_aggregate(
        self,
        diff_info: DiffInfo,
        builder: Builder
    ) -> List[ModuleCandidate]:
        """Convenience method: run strategies + aggregate."""

    @staticmethod
    def _default_fusion_config() -> Dict:
        return {
            "cross_source_bonus": 0.05,
            "max_score": 1.0
        }
```

### Selector

```python
class CandidateSelector:
    """Selects module candidates using tier-based weighted random policy."""

    TIER_HIGH = 0.95
    TIER_MEDIUM = 0.70
    TIER_LOW = 0.50

    def __init__(self, trial_ledger_path: str):
        self.ledger = TrialLedger(trial_ledger_path)

    def select(
        self,
        candidates: List[ModuleCandidate],
        commit_hash: str,
        iteration: int
    ) -> Optional[ModuleCandidate]:
        """
        Select a candidate using tier-based weighted random policy.

        Policy:
        1. Filter out already-tried candidates (unless code changed)
        2. Assign to tiers: high (≥0.95), medium (≥0.70), low (≥0.50)
        3. Select from highest non-empty tier
        4. Use weighted random within tier (weights = fused_score + ε-noise)
        5. If all tried, either re-try with exploration boost or return None

        Returns:
            Selected candidate or None if exhausted
        """

    def record_outcome(
        self,
        module_id: str,
        outcome: str,
        iteration: int,
        commit_hash: str,
        score: float,
        notes: str = ""
    ) -> None:
        """Record trial outcome to ledger."""
```

### Trial Ledger

```python
class TrialLedger:
    """Persistent storage for trial history."""

    def __init__(self, ledger_path: str):
        self.ledger_path = Path(ledger_path)
        self.records: Dict[str, TrialRecord] = {}
        self._load()

    def get_record(self, module_id: str) -> Optional[TrialRecord]:
        """Retrieve trial record for a module."""

    def update_record(self, record: TrialRecord) -> None:
        """Update or create a trial record."""

    def get_untried(
        self,
        candidates: List[ModuleCandidate],
        commit_hash: str
    ) -> List[ModuleCandidate]:
        """Filter candidates to only untried ones (accounting for code changes)."""

    def mark_tried(
        self,
        module_id: str,
        outcome: str,
        iteration: int,
        commit_hash: str,
        score: float,
        notes: str = ""
    ) -> None:
        """Mark a candidate as tried with outcome."""

    def invalidate_on_change(self, commit_hash: str) -> None:
        """Reset 'tried' flags if commit hash changed."""

    def save(self) -> None:
        """Persist ledger to JSON."""

    def _load(self) -> None:
        """Load ledger from JSON."""
```

## Integration Points

### Current Integration (v2chisel_batch.py:2265)

```python
# OLD:
hints_result = self.hints_generator.find_hints(bug_info, all_files, docker_container)
final_hints = hints_result['hints']

# NEW:
diff_info = DiffInfo.from_bug_info(bug_info)
candidates = self.hint_unifier.run_and_aggregate(diff_info, self.builder)
selected = self.candidate_selector.select(candidates, commit_hash, iteration)

if selected:
    final_hints = self._format_hints_from_candidate(selected, docker_container)
else:
    # Fallback to metadata-only
    final_hints = self._get_metadata_fallback_hints(...)
```

### Initialization (v2chisel_batch.py:118-123)

```python
# NEW initialization in __init__:
self.span_index = SpanIndex(self.builder, repo_path)
self.span_index.build(all_scala_files)  # Build once at startup

strategies = [
    ModuleFinder(self.module_finder),  # Wrap existing tool
    SourceLocator(),
    FuzzyGrep()
]
self.hint_unifier = HintUnifier(self.span_index, strategies)
self.candidate_selector = CandidateSelector(trial_ledger_path)
```

## Backward Compatibility

- Keep existing `HintsGenerator` class for now (deprecate later)
- New system accessed via flag: `use_multi_strategy_hints=True`
- Falls back to old system if flag=False

## File Structure

```
hagent/step/hints/
├── __init__.py
├── models.py              # Data structures (ModuleSpan, ModuleHint, etc.)
├── span_index.py          # SpanIndex class
├── strategy_base.py       # HintStrategy abstract base
├── module_finder.py       # ModuleFinder strategy (wraps existing tool)
├── source_locator.py      # SourceLocator strategy (new)
├── fuzzy_grep.py          # FuzzyGrep strategy (new)
├── unifier.py             # HintUnifier class
├── selector.py            # CandidateSelector class
├── trial_ledger.py        # TrialLedger persistence
└── tests/
    ├── test_span_index.py
    ├── test_module_finder_strategy.py
    ├── test_source_locator.py
    ├── test_fuzzy_grep.py
    ├── test_unifier.py
    ├── test_selector.py
    └── fixtures/
        ├── sample.scala
        ├── sample.v
        └── sample_diff.txt
```

## Dependencies

- **rapidfuzz**: Fuzzy string matching (already used?)
- **asyncio / concurrent.futures**: Parallel strategy execution
- Existing: `hagent.tool.module_finder`, `builder.filesystem`, `path_manager`

## Configuration Knobs (via config dict or env vars)

```python
HINT_CONFIG = {
    # Fusion
    "cross_source_bonus": 0.05,
    "max_fused_score": 1.0,

    # Tiers
    "tier_high": 0.95,
    "tier_medium": 0.70,
    "tier_low": 0.50,

    # SourceLocator
    "locality_decay": 100,  # μ / 100 in locality_factor formula
    "breadcrumb_scale": 10,  # log1p(n) / log1p(10)

    # FuzzyGrep
    "identifier_weights": {"port": 1.0, "signal": 0.7, "module": 1.2},
    "top_k_per_identifier": 3,

    # Selection
    "epsilon_noise": 0.01,  # For tie-breaking
    "top_n_selection": 5
}
```

## Next Steps (Phase 1+)

1. Implement `models.py` and `span_index.py`
2. Implement three strategies
3. Implement unifier + selector
4. Write integration tests
5. Wire into v2chisel_batch