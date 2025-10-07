"""
SpanIndex: Cached index of Scala/Chisel module spans for efficient lookup.

This module provides a class for building and querying an index of class/object
boundaries in Scala/Chisel source files. The index supports:
- Line-to-module mapping
- Fast lookup of all modules
- Persistence (save/load from disk)
- Cache invalidation on file changes
"""

import re
import pickle
from pathlib import Path
from typing import Dict, List, Optional
from .models import ModuleSpan


class SpanIndex:
    """
    Cache of Scala/Chisel module spans for efficient lookup.

    This class builds an index of class/object definitions in Scala files,
    tracking their line boundaries for quick lookup operations.
    """

    def __init__(self, builder=None, repo_path: Optional[str] = None):
        """
        Initialize SpanIndex.

        Args:
            builder: Builder instance for file I/O (handles Docker/local)
            repo_path: Path to repository root (for git operations)
        """
        self.builder = builder
        self.repo_path = repo_path
        self.cache: Dict[str, List[ModuleSpan]] = {}  # file -> spans
        self.commit_hash: Optional[str] = None

        # Regex patterns for Scala parsing
        self.class_pattern = re.compile(r'^\s*class\s+(\w+)', re.MULTILINE)
        self.object_pattern = re.compile(r'^\s*object\s+(\w+)', re.MULTILINE)

    def build(self, scala_files: List[str]) -> None:
        """
        Build index from list of Scala files.

        Args:
            scala_files: List of Scala file paths (absolute or docker: format)
        """
        self.cache.clear()

        for file_path in scala_files:
            try:
                spans = self._parse_file(file_path)
                if spans:
                    self.cache[file_path] = spans
            except Exception as e:
                # Log but don't fail on individual file errors
                print(f'Warning: Failed to parse {file_path}: {e}')
                continue

        # Update commit hash if repo_path is set
        if self.repo_path:
            self.commit_hash = self._get_git_commit_hash()

    def get_enclosing_module(self, file: str, line: int) -> Optional[ModuleSpan]:
        """
        Find the module span that contains the given line.

        Args:
            file: File path
            line: Line number (1-indexed)

        Returns:
            ModuleSpan containing the line, or None if not found
        """
        if file not in self.cache:
            return None

        # Find the deepest (most specific) span containing this line
        # In case of nested classes, return the innermost one
        best_match = None
        for span in self.cache[file]:
            if span.contains_line(line):
                if best_match is None or span.line_count() < best_match.line_count():
                    best_match = span

        return best_match

    def get_all_modules(self) -> List[ModuleSpan]:
        """
        Return all indexed module spans.

        Returns:
            List of all ModuleSpan objects in the index
        """
        all_spans = []
        for spans in self.cache.values():
            all_spans.extend(spans)
        return all_spans

    def get_modules_in_file(self, file: str) -> List[ModuleSpan]:
        """
        Get all module spans in a specific file.

        Args:
            file: File path

        Returns:
            List of ModuleSpan objects in the file, or empty list if not found
        """
        return self.cache.get(file, [])

    def invalidate(self, files: Optional[List[str]] = None) -> None:
        """
        Invalidate cache for specific files or entire index.

        Args:
            files: List of files to invalidate, or None to clear entire cache
        """
        if files is None:
            self.cache.clear()
            self.commit_hash = None
        else:
            for file in files:
                self.cache.pop(file, None)

    def save(self, cache_path: str) -> None:
        """
        Persist index to disk using pickle.

        Args:
            cache_path: Path to save cache file
        """
        cache_data = {'cache': self.cache, 'commit_hash': self.commit_hash, 'repo_path': self.repo_path}

        cache_file = Path(cache_path)
        cache_file.parent.mkdir(parents=True, exist_ok=True)

        with open(cache_file, 'wb') as f:
            pickle.dump(cache_data, f)

    @classmethod
    def load(cls, cache_path: str, builder=None) -> 'SpanIndex':
        """
        Load index from disk.

        Args:
            cache_path: Path to cache file
            builder: Builder instance for file I/O

        Returns:
            SpanIndex instance loaded from cache

        Raises:
            FileNotFoundError: If cache file doesn't exist
        """
        cache_file = Path(cache_path)
        if not cache_file.exists():
            raise FileNotFoundError(f'Cache file not found: {cache_path}')

        with open(cache_file, 'rb') as f:
            cache_data = pickle.load(f)

        index = cls(builder=builder, repo_path=cache_data.get('repo_path'))
        index.cache = cache_data['cache']
        index.commit_hash = cache_data.get('commit_hash')

        return index

    def _parse_file(self, file_path: str) -> List[ModuleSpan]:
        """
        Parse a Scala file to extract class/object spans.

        Args:
            file_path: Path to Scala file

        Returns:
            List of ModuleSpan objects found in the file
        """
        # Read file content
        content = self._read_file(file_path)
        if not content:
            return []

        lines = content.split('\n')
        spans = []

        # Find class definitions
        for match in self.class_pattern.finditer(content):
            name = match.group(1)
            start_pos = match.start()
            start_line = content[:start_pos].count('\n') + 1
            end_line = self._find_span_end_line(lines, start_line - 1)  # Convert to 0-indexed

            span = ModuleSpan(file=file_path, name=name, start_line=start_line, end_line=end_line, span_type='class')
            spans.append(span)

        # Find object definitions
        for match in self.object_pattern.finditer(content):
            name = match.group(1)
            start_pos = match.start()
            start_line = content[:start_pos].count('\n') + 1
            end_line = self._find_span_end_line(lines, start_line - 1)  # Convert to 0-indexed

            span = ModuleSpan(file=file_path, name=name, start_line=start_line, end_line=end_line, span_type='object')
            spans.append(span)

        return spans

    def _find_span_end_line(self, lines: List[str], start_line_idx: int) -> int:
        """
        Find the end line of a class/object by matching braces.

        Args:
            lines: List of file lines
            start_line_idx: Starting line index (0-indexed)

        Returns:
            End line number (1-indexed)
        """
        if start_line_idx >= len(lines):
            return start_line_idx + 1

        brace_count = 0
        found_opening = False

        for i in range(start_line_idx, len(lines)):
            line = lines[i]

            # Count braces (ignoring braces in strings/comments - simplified)
            for char in line:
                if char == '{':
                    brace_count += 1
                    found_opening = True
                elif char == '}':
                    brace_count -= 1

            # If we've found the opening brace and returned to balance, we're done
            if found_opening and brace_count == 0:
                return i + 1  # Convert back to 1-indexed

        # If we couldn't find the end, estimate
        return min(start_line_idx + 50, len(lines))

    def _read_file(self, file_path: str) -> str:
        """
        Read file content using Builder API if available, else direct file I/O.

        Args:
            file_path: Path to file (may be docker: format)

        Returns:
            File content as string
        """
        if file_path.startswith('docker:'):
            # Parse docker path: docker:container:file_path
            parts = file_path.split(':', 2)
            if len(parts) != 3:
                raise ValueError(f'Invalid docker path format: {file_path}')
            actual_path = parts[2]

            if self.builder:
                return self.builder.filesystem.read_text(actual_path)
            else:
                raise RuntimeError('Builder required for docker: paths')
        else:
            # Local file
            with open(file_path, 'r', encoding='utf-8') as f:
                return f.read()

    def _get_git_commit_hash(self) -> Optional[str]:
        """
        Get current git commit hash for the repository.

        Returns:
            Short commit hash (8 chars) or None if not a git repo
        """
        if not self.repo_path:
            return None

        try:
            import subprocess

            result = subprocess.run(
                ['git', 'rev-parse', '--short=8', 'HEAD'],
                cwd=self.repo_path,
                capture_output=True,
                text=True,
                check=True,
            )
            return result.stdout.strip()
        except (subprocess.CalledProcessError, FileNotFoundError):
            return None

    def __len__(self) -> int:
        """Return total number of indexed modules."""
        return sum(len(spans) for spans in self.cache.values())

    def __repr__(self) -> str:
        """String representation of index."""
        return f'SpanIndex(files={len(self.cache)}, modules={len(self)}, commit={self.commit_hash})'
