# hagent/tool/memory.py
"""Simple memory system used for testing FewShotMemory integration."""
from __future__ import annotations

import os
import pickle
from dataclasses import dataclass
from typing import Dict, Optional, List
from uuid import uuid4


@dataclass
class MemoryEntry:
    id: str
    error_type: str
    faulty_code: str
    fix_answer: str


class FewShotMemory:
    """Minimal FewShotMemory implementation for tests."""

    def __init__(self, db_path: Optional[str] = None, auto_create_data: bool = False):
        self.db_path = db_path
        self.memories: Dict[str, MemoryEntry] = {}
        if db_path and os.path.exists(db_path):
            self._load()
        elif db_path and auto_create_data:
            self._save()
        elif db_path:
            raise FileNotFoundError(db_path)

    # internal helpers
    def _load(self) -> None:
        print(f"Loading memories from cache file: {self.db_path}")
        try:
            with open(self.db_path, "rb") as f:
                data = pickle.load(f)
            for mid, entry in data.items():
                self.memories[mid] = MemoryEntry(**entry)
            print(f"Successfully loaded {len(self.memories)} memories from cache")
        except FileNotFoundError:
            pass
        except Exception as e:
            print(f"Failed to load cache: {e}")

    def _save(self) -> None:
        if not self.db_path:
            return
        print(f"Saving {len(self.memories)} memories to cache: {self.db_path}")
        with open(self.db_path, "wb") as f:
            pickle.dump({mid: entry.__dict__ for mid, entry in self.memories.items()}, f)
        print(f"Successfully cached {len(self.memories)} memories")

    def add(self, err, fix_question: str, fix_answer: str) -> str:
        mem_id = str(uuid4())
        print(f"Adding new memory with ID: {mem_id}")
        entry = MemoryEntry(mem_id, getattr(err, "msg", str(err)), fix_question, fix_answer)
        self.memories[mem_id] = entry
        self._save()
        return mem_id

    def find(self, err, fix_question: str) -> List[MemoryEntry]:
        err_type = getattr(err, "msg", str(err))
        for entry in self.memories.values():
            if entry.error_type == err_type:
                print(f"Found exact match: {entry.id}")
                return [entry]
        return []
