"""
TrialLedger: Persistent storage for trial history.

This module manages the ledger of module candidates that have been tried,
tracking outcomes, iterations, and commit hashes to enable iterative selection.
"""

import json
from pathlib import Path
from typing import Dict, List, Optional
from datetime import datetime
from .models import TrialRecord, ModuleCandidate


class TrialLedger:
    """
    Persistent storage for trial history.

    The ledger tracks which module candidates have been tried, their outcomes,
    and maintains this information across iterations to enable smart selection.
    """

    def __init__(self, ledger_path: str):
        """
        Initialize TrialLedger.

        Args:
            ledger_path: Path to JSON ledger file
        """
        self.ledger_path = Path(ledger_path)
        self.records: Dict[str, TrialRecord] = {}
        self._load()

    def get_record(self, module_id: str) -> Optional[TrialRecord]:
        """
        Retrieve trial record for a module.

        Args:
            module_id: Module identifier (file::name)

        Returns:
            TrialRecord if exists, None otherwise
        """
        return self.records.get(module_id)

    def update_record(self, record: TrialRecord) -> None:
        """
        Update or create a trial record.

        Args:
            record: TrialRecord to update/create
        """
        module_key = record.module_key
        self.records[module_key] = record
        self.save()

    def get_untried(self, candidates: List[ModuleCandidate], commit_hash: str) -> List[ModuleCandidate]:
        """
        Filter candidates to only untried ones (accounting for code changes).

        If the commit hash has changed, all candidates are considered untried.

        Args:
            candidates: List of module candidates
            commit_hash: Current git commit hash

        Returns:
            List of untried candidates
        """
        untried = []
        for candidate in candidates:
            module_key = candidate.module_id
            record = self.records.get(module_key)

            if record is None:
                # Never tried
                untried.append(candidate)
            elif record.commit_hash != commit_hash:
                # Code changed, consider untried
                untried.append(candidate)
            elif not record.tried:
                # Explicitly marked as not tried
                untried.append(candidate)
            # else: already tried at this commit

        return untried

    def mark_tried(
        self,
        module_id: str,
        outcome: str,
        iteration: int,
        commit_hash: str,
        score: float,
        sources: Dict[str, float],
        notes: str = '',
    ) -> None:
        """
        Mark a candidate as tried with outcome.

        Args:
            module_id: Module identifier (file::name)
            outcome: Outcome string ("success", "compile_fail", "lec_fail", etc.)
            iteration: Iteration number
            commit_hash: Git commit hash
            score: Fused score at time of trial
            sources: Per-source scores
            notes: Optional notes
        """
        # Parse module_id to extract file and name
        if '::' in module_id:
            parts = module_id.split('::', 1)
            module_dict = {'file': parts[0], 'name': parts[1]}
        else:
            module_dict = {'file': 'unknown', 'name': module_id}

        record = self.records.get(module_id)

        if record is None:
            # Create new record
            record = TrialRecord(
                module_id=module_dict,
                score=score,
                sources=sources,
                tried=True,
                attempts=1,
                iteration_last=iteration,
                outcome_last=outcome,
                commit_hash=commit_hash,
                timestamps=[datetime.utcnow().isoformat()],
                notes=notes,
            )
        else:
            # Update existing record
            record.tried = True
            record.attempts += 1
            record.iteration_last = iteration
            record.outcome_last = outcome
            record.commit_hash = commit_hash
            record.timestamps.append(datetime.utcnow().isoformat())
            if notes:
                record.notes += f'\n{notes}'

        self.records[module_id] = record
        self.save()

    def invalidate_on_change(self, commit_hash: str) -> None:
        """
        Reset 'tried' flags if commit hash changed.

        Args:
            commit_hash: New git commit hash
        """
        for record in self.records.values():
            if record.commit_hash != commit_hash:
                record.tried = False

        self.save()

    def save(self) -> None:
        """Persist ledger to JSON file."""
        self.ledger_path.parent.mkdir(parents=True, exist_ok=True)

        # Convert TrialRecord objects to dicts
        data = {}
        for module_key, record in self.records.items():
            data[module_key] = {
                'module_id': record.module_id,
                'score': record.score,
                'sources': record.sources,
                'tried': record.tried,
                'attempts': record.attempts,
                'iteration_last': record.iteration_last,
                'outcome_last': record.outcome_last,
                'commit_hash': record.commit_hash,
                'timestamps': record.timestamps,
                'notes': record.notes,
            }

        with open(self.ledger_path, 'w') as f:
            json.dump(data, f, indent=2)

    def _load(self) -> None:
        """Load ledger from JSON file."""
        if not self.ledger_path.exists():
            return

        try:
            with open(self.ledger_path, 'r') as f:
                data = json.load(f)

            for module_key, record_dict in data.items():
                record = TrialRecord(
                    module_id=record_dict['module_id'],
                    score=record_dict['score'],
                    sources=record_dict['sources'],
                    tried=record_dict['tried'],
                    attempts=record_dict['attempts'],
                    iteration_last=record_dict['iteration_last'],
                    outcome_last=record_dict['outcome_last'],
                    commit_hash=record_dict['commit_hash'],
                    timestamps=record_dict.get('timestamps', []),
                    notes=record_dict.get('notes', ''),
                )
                self.records[module_key] = record
        except (json.JSONDecodeError, KeyError) as e:
            print(f'Warning: Failed to load trial ledger: {e}')
            self.records = {}

    def get_summary(self) -> Dict:
        """
        Get summary statistics of the ledger.

        Returns:
            Dictionary with summary statistics
        """
        if not self.records:
            return {'total': 0, 'tried': 0, 'success': 0, 'failed': 0}

        tried_count = sum(1 for r in self.records.values() if r.tried)
        success_count = sum(1 for r in self.records.values() if r.outcome_last == 'success')
        failed_count = sum(1 for r in self.records.values() if r.outcome_last in ('compile_fail', 'lec_fail', 'rejected'))

        return {'total': len(self.records), 'tried': tried_count, 'success': success_count, 'failed': failed_count}

    def __len__(self) -> int:
        """Return number of records in ledger."""
        return len(self.records)

    def __repr__(self) -> str:
        """String representation of ledger."""
        summary = self.get_summary()
        return f"TrialLedger(total={summary['total']}, tried={summary['tried']}, success={summary['success']})"
