"""
Docker-aware file tracking using in-container filesystem and in-memory baselines.

This implementation avoids git requirements by capturing a baseline snapshot
of tracked files' contents inside the container and generating unified diffs
against the current contents later.
"""

import difflib
import logging
import posixpath
from pathlib import Path
from typing import Optional, Set, List, Dict, Any

from .path_manager import PathManager


class FileTrackerDocker:
    """
    Docker-aware file tracker using in-container filesystem and in-memory baselines.

    This implementation avoids git requirements by capturing a baseline snapshot
    of tracked files' contents inside the container and generating unified diffs
    against the current contents later.
    """

    def __init__(self, path_manager: PathManager, container_manager):
        self.path_manager = path_manager
        self.container_manager = container_manager
        self.logger = logging.getLogger(__name__)

        # Tracking state
        self._tracked_files: Set[str] = set()
        self._tracked_dirs: List[Dict[str, Any]] = []  # [{'path': str, 'ext': Optional[str]}]
        self._baseline: Dict[str, str] = {}  # path -> content (from initial snapshot)

        # No-op setup; defer checks to operations

    # ---- helpers ----
    def _container_read_file(self, path: str) -> Optional[str]:
        rc, out, err = self.container_manager.run_cmd(f'cat "{path}" 2>/dev/null || true', quiet=True)
        if rc == 0 and out is not None:
            return out
        return None

    def _container_exists(self, path: str, is_dir: bool = False) -> bool:
        test_flag = '-d' if is_dir else '-f'
        rc, out, err = self.container_manager.run_cmd(f'test {test_flag} "{path}" && echo OK || echo MISS', quiet=True)
        return rc == 0 and 'OK' in out

    def _container_find_files(self, dir_path: str) -> List[str]:
        rc, out, err = self.container_manager.run_cmd(f'find "{dir_path}" -type f 2>/dev/null || true', quiet=True)
        if rc != 0:
            return []
        return [line.strip() for line in out.splitlines() if line.strip()]

    def _matches_filter(self, file_path: str, ext_filter: Optional[str], dir_ext: Optional[str]) -> bool:
        if ext_filter is not None and not file_path.endswith(ext_filter):
            return False
        if dir_ext is not None and not file_path.endswith(dir_ext):
            return False
        return True

    # ---- API ----
    def cleanup(self) -> None:
        self._tracked_files.clear()
        self._tracked_dirs.clear()
        self._baseline.clear()

    def track_file(self, file_path: str) -> bool:
        # Resolve container path relative to repo_dir if not absolute
        if not posixpath.isabs(file_path):
            path = str(Path('/code/workspace/repo') / file_path)
        else:
            path = file_path

        # Parent dir must exist
        parent = posixpath.dirname(path.rstrip('/')) or '/'
        if not self._container_exists(parent, is_dir=True):
            self.logger.warning(f"Cannot track file - parent directory doesn't exist (container): {path}")
            return False

        # Snapshot baseline content (empty if file missing)
        content = self._container_read_file(path)
        if content is None:
            content = ''

        self._tracked_files.add(path)
        # Only store baseline once
        self._baseline.setdefault(path, content)
        return True

    def track_dir(self, dir_path: str, ext_filter: Optional[str] = None) -> bool:
        # Resolve container path relative to repo_dir if not absolute
        if not posixpath.isabs(dir_path):
            path = str(Path('/code/workspace/repo') / dir_path)
        else:
            path = dir_path

        parent = posixpath.dirname(path.rstrip('/')) or '/'
        if not self._container_exists(parent, is_dir=True):
            self.logger.warning(f"Cannot track directory - parent doesn't exist (container): {path}")
            return False

        # Store tracked dir and capture baseline snapshot of files currently present
        self._tracked_dirs.append({'path': path, 'ext': ext_filter})

        for f in self._container_find_files(path):
            if self._matches_filter(f, None, ext_filter):
                if f not in self._baseline:
                    content = self._container_read_file(f) or ''
                    self._baseline[f] = content
        return True

    def get_tracked_files(self, ext_filter: Optional[str] = None) -> Set[str]:
        files: Set[str] = set()
        for f in self._tracked_files:
            if self._matches_filter(f, ext_filter, None):
                files.add(f)
        for d in self._tracked_dirs:
            base = d['path']
            dir_ext = d['ext']
            for f in self._container_find_files(base):
                if self._matches_filter(f, ext_filter, dir_ext):
                    files.add(f)
        return files

    def get_diff(self, file_path: str) -> str:
        # Resolve container path
        if not posixpath.isabs(file_path):
            path = str(Path('/code/workspace/repo') / file_path)
        else:
            path = file_path

        old = self._baseline.get(path, '')
        cur = self._container_read_file(path)
        if cur is None:
            cur = ''

        if old == cur:
            return ''

        old_lines = old.splitlines(keepends=True)
        cur_lines = cur.splitlines(keepends=True)
        diff = difflib.unified_diff(old_lines, cur_lines, fromfile=f'{path} (baseline)', tofile=f'{path} (current)', lineterm='')
        return ''.join(diff)

    def get_all_diffs(self, ext_filter: Optional[str] = None) -> Dict[str, str]:
        diffs: Dict[str, str] = {}
        for f in self.get_tracked_files(ext_filter):
            d = self.get_diff(f)
            if d.strip():
                diffs[f] = d
        return diffs

    def get_patch_dict(self) -> Dict[str, Any]:
        patch_dict = {'full': [], 'patch': []}
        all_diffs = self.get_all_diffs()
        for path, diff_content in all_diffs.items():
            cur = self._container_read_file(path) or ''
            # Use similar heuristic to local version
            if (
                not diff_content
                or not cur
                or len(cur.encode('utf-8')) < 1024
                or len(cur.splitlines()) < 10
                or (len(cur) > 0 and len(diff_content.encode('utf-8')) / max(1, len(cur.encode('utf-8'))) > 0.5)
            ):
                patch_dict['full'].append({'filename': path, 'contents': cur})
            else:
                patch_dict['patch'].append({'filename': path, 'diff': diff_content})
        return patch_dict

    # Context manager
    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.cleanup()
        return False

    def __del__(self) -> None:
        try:
            self.cleanup()
        except Exception:
            pass