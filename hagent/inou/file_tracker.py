"""
File Tracker for HAgent

Git-based file tracking using stash snapshots for both Docker and local execution.
Replaces File_manager tracking functionality with optimized git-based approach.
"""

import os
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Optional, Set, List

from .path_manager import PathManager


class FileTracker:
    """
    Tracks file changes using git stash snapshots.

    Uses git diff for tracking both REPO_DIR and BUILD_DIR changes.
    Only tracks explicitly specified files and directories for optimization.
    """

    def __init__(self, path_manager: Optional[PathManager] = None):
        """
        Initialize FileTracker.

        Args:
            path_manager: PathManager instance for path resolution
        """
        self.path_manager = path_manager or PathManager()
        self._tracked_paths: Set[str] = set()
        self._stash_name: Optional[str] = None
        self._stash_created: bool = False
        self._build_cache_synced: bool = False

        # Initialize tracking session
        self._initialize_session()

    def _initialize_session(self) -> None:
        """Initialize the tracking session with git stash snapshot."""
        try:
            # Create pre-session snapshot for repo directory
            result = subprocess.run(
                ['git', 'stash', 'create', 'pre-hagent-session'],
                cwd=str(self.path_manager.repo_dir),
                capture_output=True,
                text=True,
            )

            if result.returncode == 0 and result.stdout.strip():
                stash_commit = result.stdout.strip()

                # Store the stash
                store_result = subprocess.run(
                    ['git', 'stash', 'store', '-m', 'pre-hagent-session', stash_commit],
                    cwd=str(self.path_manager.repo_dir),
                    capture_output=True,
                    text=True,
                )

                if store_result.returncode == 0:
                    self._stash_name = 'stash@{0}'
                    self._stash_created = True
                else:
                    print(f'Warning: Failed to store git stash: {store_result.stderr}', file=sys.stderr)
            else:
                # No changes to stash - create empty stash for consistency
                self._create_empty_stash()

            # For local mode, sync build directory to cache for tracking
            if self.path_manager.is_local_mode():
                self._sync_build_directory()

        except Exception as e:
            print(f'Warning: Failed to initialize file tracking session: {e}', file=sys.stderr)

    def _create_empty_stash(self) -> None:
        """Create an empty stash when there are no changes to stash."""
        try:
            # Create a temporary file, add it, stash it, then remove it
            temp_file = self.path_manager.repo_dir / '.hagent_temp_for_stash'
            temp_file.write_text('')

            # Add and stash the temp file
            subprocess.run(['git', 'add', str(temp_file)], cwd=str(self.path_manager.repo_dir), check=True)

            result = subprocess.run(
                ['git', 'stash', 'create', 'pre-hagent-session-empty'],
                cwd=str(self.path_manager.repo_dir),
                capture_output=True,
                text=True,
                check=True,
            )

            if result.stdout.strip():
                stash_commit = result.stdout.strip()

                # Store the stash
                subprocess.run(
                    ['git', 'stash', 'store', '-m', 'pre-hagent-session-empty', stash_commit],
                    cwd=str(self.path_manager.repo_dir),
                    check=True,
                )

                self._stash_name = 'stash@{0}'
                self._stash_created = True

            # Clean up temp file
            subprocess.run(['git', 'reset', 'HEAD', str(temp_file)], cwd=str(self.path_manager.repo_dir))
            temp_file.unlink(missing_ok=True)

        except Exception as e:
            print(f'Warning: Failed to create empty stash: {e}', file=sys.stderr)

    def _sync_build_directory(self) -> None:
        """Sync build directory to cache directory for local mode tracking."""
        try:
            build_cache_dir = Path(self.path_manager.get_build_cache_dir())

            # Remove existing cache and copy build directory
            if build_cache_dir.exists():
                shutil.rmtree(build_cache_dir)

            if self.path_manager.build_dir.exists():
                shutil.copytree(self.path_manager.build_dir, build_cache_dir)
                self._build_cache_synced = True
        except Exception as e:
            print(f'Warning: Failed to sync build directory to cache: {e}', file=sys.stderr)

    def track_file(self, filepath: str) -> bool:
        """
        Track a specific file for changes.

        Args:
            filepath: Path to the file to track (can be relative or absolute)

        Returns:
            True if successfully added to tracking, False otherwise
        """
        try:
            # Resolve path
            if os.path.isabs(filepath):
                abs_path = Path(filepath).resolve()
            else:
                # Try relative to repo_dir first, then build_dir
                repo_relative = (self.path_manager.repo_dir / filepath).resolve()
                build_relative = (self.path_manager.build_dir / filepath).resolve()

                if repo_relative.exists() or repo_relative.parent.exists():
                    abs_path = repo_relative
                else:
                    abs_path = build_relative

            # Add to tracked paths
            self._tracked_paths.add(str(abs_path))
            return True

        except Exception as e:
            print(f"Warning: Failed to track file '{filepath}': {e}", file=sys.stderr)
            return False

    def track_dir(self, dirpath: str, ext: Optional[str] = None) -> bool:
        """
        Track a directory for changes, optionally with extension filter.

        Args:
            dirpath: Path to the directory to track
            ext: Optional extension filter (e.g., '.scala', '.v')

        Returns:
            True if successfully added to tracking, False otherwise
        """
        try:
            # Resolve directory path
            if os.path.isabs(dirpath):
                abs_dir = Path(dirpath).resolve()
            else:
                # Try relative to repo_dir first, then build_dir
                repo_relative = (self.path_manager.repo_dir / dirpath).resolve()
                build_relative = (self.path_manager.build_dir / dirpath).resolve()

                if repo_relative.exists() or repo_relative.parent.exists():
                    abs_dir = repo_relative
                else:
                    abs_dir = build_relative

            # Track the directory
            if ext:
                # Track specific extension pattern
                pattern = str(abs_dir / f'*{ext}')
                self._tracked_paths.add(pattern)
            else:
                # Track the entire directory
                self._tracked_paths.add(str(abs_dir))

            return True

        except Exception as e:
            print(f"Warning: Failed to track directory '{dirpath}': {e}", file=sys.stderr)
            return False

    def get_tracked_changes(self) -> str:
        """
        Get the diff of tracked changes since session initialization.

        Returns:
            Git diff output as string showing changes to tracked paths only
        """
        if not self._stash_created or not self._stash_name or not self._tracked_paths:
            return ''

        try:
            # Build git diff command with tracked paths only
            cmd = ['git', 'diff', self._stash_name, '--']

            # Add tracked paths to command
            for path in self._tracked_paths:
                # Convert absolute paths to relative for git diff
                try:
                    abs_path = Path(path)
                    if abs_path.is_absolute():
                        if self.path_manager.repo_dir in abs_path.parents or abs_path == self.path_manager.repo_dir:
                            relative_path = abs_path.relative_to(self.path_manager.repo_dir)
                            cmd.append(str(relative_path))
                        else:
                            # This might be a build_dir path - skip for repo diff
                            continue
                    else:
                        cmd.append(path)
                except ValueError:
                    # Skip paths that can't be made relative
                    continue

            if len(cmd) <= 3:  # Only base command, no paths to diff
                return ''

            # Run git diff
            result = subprocess.run(
                cmd,
                cwd=str(self.path_manager.repo_dir),
                capture_output=True,
                text=True,
            )

            if result.returncode == 0:
                repo_diff = result.stdout
            else:
                repo_diff = ''

            # For local mode, also check build directory changes
            build_diff = ''
            if self.path_manager.is_local_mode() and self._build_cache_synced:
                build_diff = self._get_build_directory_changes()

            # Combine diffs
            combined_diff = ''
            if repo_diff:
                combined_diff += '--- Repository Changes ---\n' + repo_diff
            if build_diff:
                if combined_diff:
                    combined_diff += '\n'
                combined_diff += '--- Build Directory Changes ---\n' + build_diff

            return combined_diff

        except Exception as e:
            print(f'Warning: Failed to get tracked changes: {e}', file=sys.stderr)
            return ''

    def _get_build_directory_changes(self) -> str:
        """Get changes in build directory for local mode."""
        try:
            build_cache_dir = Path(self.path_manager.get_build_cache_dir())
            if not build_cache_dir.exists():
                return ''

            # Use diff to compare build directory with cache
            cmd = ['diff', '-u', '-r', str(build_cache_dir), str(self.path_manager.build_dir)]

            # Filter for tracked paths only
            tracked_build_paths = []
            for path in self._tracked_paths:
                abs_path = Path(path)
                if abs_path.is_absolute() and self.path_manager.build_dir in abs_path.parents:
                    tracked_build_paths.append(str(abs_path))

            if not tracked_build_paths:
                return ''

            result = subprocess.run(cmd, capture_output=True, text=True)

            # Filter diff output for tracked paths only
            if result.returncode in [0, 1]:  # 0 = no diff, 1 = differences found
                lines = result.stdout.split('\n')
                filtered_lines = []
                include_section = False

                for line in lines:
                    if line.startswith('diff -u'):
                        # Check if this diff section is for a tracked path
                        include_section = any(tracked_path in line for tracked_path in tracked_build_paths)

                    if include_section:
                        filtered_lines.append(line)

                return '\n'.join(filtered_lines)
            else:
                return ''

        except Exception as e:
            print(f'Warning: Failed to get build directory changes: {e}', file=sys.stderr)
            return ''

    def get_tracked_paths(self) -> List[str]:
        """
        Get list of currently tracked paths.

        Returns:
            List of tracked file/directory paths
        """
        return list(self._tracked_paths)

    def cleanup(self) -> None:
        """Clean up the tracking session."""
        try:
            if self._stash_created and self._stash_name:
                # Remove the stash we created
                subprocess.run(
                    ['git', 'stash', 'drop', self._stash_name],
                    cwd=str(self.path_manager.repo_dir),
                    capture_output=True,
                )
                self._stash_created = False
                self._stash_name = None

            # Clear tracked paths
            self._tracked_paths.clear()

        except Exception as e:
            print(f'Warning: Failed to cleanup tracking session: {e}', file=sys.stderr)

    def __enter__(self):
        """Context manager entry."""
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        """Context manager exit - ensures cleanup."""
        self.cleanup()
        return False

    def __del__(self) -> None:
        """On destruction, ensures cleanup."""
        try:
            self.cleanup()
        except Exception:
            # Ignore any errors during destruction cleanup
            pass
