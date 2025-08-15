"""
File tracking using git stash snapshots.

Provides consistent file tracking across Docker and local execution modes using
git stash snapshots to track changes to explicitly specified files and directories.
"""

import difflib
import logging
import os
import subprocess
import sys
from pathlib import Path
from typing import Optional, Set, List, Dict, Any

from .path_manager import PathManager


class FileTracker:
    """
    File tracking using git stash snapshots.

    This class provides file tracking capabilities by creating git stash snapshots
    and tracking changes to explicitly specified files and directories. It supports
    both Docker and local execution modes seamlessly.
    """

    def __init__(self, path_manager: PathManager):
        """
        Initialize file tracker with path manager dependency.

        Args:
            path_manager: PathManager instance for resolving HAGENT_* paths

        Raises:
            SystemExit: If git repository validation fails or git is not available
        """
        self.path_manager = path_manager
        self.logger = logging.getLogger(__name__)

        # Initialize tracking state
        self._tracked_files: Set[str] = set()
        self._tracked_dirs: List[Dict[str, str]] = []  # [{'path': str, 'ext': str}, ...]
        self._baseline_stash: Optional[str] = None
        self._hagent_stashes: List[str] = []  # Track our stash references for cleanup

        # Validate git repository and setup
        if not self._validate_git_repo():
            self._fail_fast('FileTracker requires a git repository in REPO_DIR')
            return

        if not self._check_git_available():
            self._fail_fast('FileTracker requires git command to be available')
            return

        # Create baseline snapshot for pre-existing changes
        baseline = self._create_baseline_snapshot()
        if baseline:
            self._baseline_stash = baseline
            self.logger.info(f'Created baseline snapshot: {baseline}')
        else:
            self.logger.info('No pre-existing changes to snapshot')

        self.logger.info('FileTracker initialized successfully')

    def _fail_fast(self, message: str) -> None:
        """
        Log error and exit immediately.

        Args:
            message: Error message to log and display
        """
        self.logger.error(message)
        print(f'Error: {message}', file=sys.stderr)
        sys.exit(1)
        return  # For test compatibility

    def _validate_git_repo(self) -> bool:
        """
        Validate that repo_dir is a git repository.

        Returns:
            True if valid git repository, False otherwise
        """
        repo_dir = Path(self.path_manager.repo_dir)

        # Check if directory exists
        if not repo_dir.exists():
            self.logger.error(f'Repository directory does not exist: {repo_dir}')
            return False

        # Check if it's a git repository
        git_dir = repo_dir / '.git'
        if not git_dir.exists():
            self.logger.error(f'Directory is not a git repository: {repo_dir}')
            return False

        # Test git command in the repository
        try:
            result = subprocess.run(['git', 'rev-parse', '--git-dir'], cwd=repo_dir, capture_output=True, text=True, timeout=30)
            if result.returncode != 0:
                self.logger.error(f'Git repository validation failed: {result.stderr}')
                return False

        except (subprocess.TimeoutExpired, subprocess.CalledProcessError, FileNotFoundError) as e:
            self.logger.error(f'Git command failed during validation: {e}')
            return False

        return True

    def _check_git_available(self) -> bool:
        """
        Check if git command is available.

        Returns:
            True if git is available, False otherwise
        """
        try:
            result = subprocess.run(['git', '--version'], capture_output=True, text=True, timeout=10)
            if result.returncode == 0:
                self.logger.debug(f'Git available: {result.stdout.strip()}')
                return True
            else:
                self.logger.error(f'Git command failed: {result.stderr}')
                return False

        except (subprocess.TimeoutExpired, subprocess.CalledProcessError, FileNotFoundError) as e:
            self.logger.error(f'Git command not available: {e}')
            return False

    def _create_baseline_snapshot(self) -> Optional[str]:
        """
        Create baseline stash snapshot for pre-existing changes.

        This creates a snapshot of any uncommitted changes that exist before
        FileTracker starts tracking. This allows us to distinguish between
        pre-existing changes and changes made during the tracked session.

        Returns:
            Stash hash if snapshot created, None if no changes to snapshot
        """
        try:
            # Check if there are any changes to stash (tracked, staged, and untracked)
            # First check tracked files for modifications
            result = subprocess.run(
                ['git', 'diff-index', '--quiet', 'HEAD'], cwd=self.path_manager.repo_dir, capture_output=True, timeout=30
            )
            
            has_tracked_changes = result.returncode != 0
            
            # Check for staged changes
            staged_result = subprocess.run(
                ['git', 'diff-index', '--quiet', '--cached', 'HEAD'], cwd=self.path_manager.repo_dir, capture_output=True, timeout=30
            )
            
            has_staged_changes = staged_result.returncode != 0
            
            # Check for untracked files
            untracked_result = subprocess.run(
                ['git', 'ls-files', '--others', '--exclude-standard'], 
                cwd=self.path_manager.repo_dir, capture_output=True, text=True, timeout=30
            )
            
            has_untracked_files = bool(untracked_result.stdout.strip()) if untracked_result.returncode == 0 else False

            # If no changes, no staged changes, and no untracked files, nothing to snapshot
            if not has_tracked_changes and not has_staged_changes and not has_untracked_files:
                self.logger.debug('No pre-existing changes to snapshot')
                return None

            # If we only have untracked files, temporarily add them to index for stashing
            untracked_files = []
            if has_untracked_files and not has_tracked_changes and not has_staged_changes:
                untracked_files = untracked_result.stdout.strip().split('\n')
                # Add untracked files to index temporarily
                add_result = subprocess.run(
                    ['git', 'add'] + untracked_files,
                    cwd=self.path_manager.repo_dir,
                    capture_output=True,
                    timeout=30,
                )
                if add_result.returncode != 0:
                    self.logger.warning(f'Failed to stage untracked files: {add_result.stderr}')
                    return None

            try:
                # Create stash snapshot without modifying working tree
                result = subprocess.run(
                    ['git', 'stash', 'create', 'hagent-baseline-snapshot'],
                    cwd=self.path_manager.repo_dir,
                    capture_output=True,
                    text=True,
                    timeout=30,
                )
            finally:
                # If we temporarily added untracked files, unstage them
                if untracked_files:
                    subprocess.run(
                        ['git', 'reset', 'HEAD'] + untracked_files,
                        cwd=self.path_manager.repo_dir,
                        capture_output=True,
                        timeout=30,
                    )

            if result.returncode != 0:
                self.logger.warning(f'Failed to create baseline snapshot: {result.stderr}')
                return None

            stash_hash = result.stdout.strip()
            if not stash_hash:
                self.logger.debug('No changes to create baseline snapshot')
                return None

            # Store the stash with a descriptive message
            store_result = subprocess.run(
                ['git', 'stash', 'store', '-m', 'hagent-baseline-snapshot', stash_hash],
                cwd=self.path_manager.repo_dir,
                capture_output=True,
                text=True,
                timeout=30,
            )

            if store_result.returncode != 0:
                self.logger.warning(f'Failed to store baseline snapshot: {store_result.stderr}')
                return None

            # Track this stash for cleanup
            self._hagent_stashes.append(stash_hash)

            self.logger.info(f'Created baseline snapshot: {stash_hash}')
            return stash_hash

        except (subprocess.TimeoutExpired, subprocess.CalledProcessError) as e:
            self.logger.warning(f'Error creating baseline snapshot: {e}')
            return None

    def _create_snapshot(self, message: str) -> Optional[str]:
        """
        Create git stash snapshot without modifying working tree.

        Args:
            message: Descriptive message for the snapshot

        Returns:
            Stash hash if created successfully, None otherwise
        """
        try:
            result = subprocess.run(
                ['git', 'stash', 'create', message], cwd=self.path_manager.repo_dir, capture_output=True, text=True, timeout=30
            )

            if result.returncode != 0:
                self.logger.warning(f"Failed to create snapshot '{message}': {result.stderr}")
                return None

            stash_hash = result.stdout.strip()
            if not stash_hash:
                self.logger.debug(f"No changes to create snapshot '{message}'")
                return None

            self.logger.debug(f"Created snapshot '{message}': {stash_hash}")
            return stash_hash

        except (subprocess.TimeoutExpired, subprocess.CalledProcessError) as e:
            self.logger.warning(f"Error creating snapshot '{message}': {e}")
            return None

    def _store_snapshot(self, stash_hash: str, message: str) -> bool:
        """
        Store snapshot in git stash with descriptive message.

        Args:
            stash_hash: Hash of the stash to store
            message: Descriptive message for the stash

        Returns:
            True if stored successfully, False otherwise
        """
        try:
            result = subprocess.run(
                ['git', 'stash', 'store', '-m', message, stash_hash],
                cwd=self.path_manager.repo_dir,
                capture_output=True,
                text=True,
                timeout=30,
            )

            if result.returncode != 0:
                self.logger.warning(f'Failed to store snapshot {stash_hash}: {result.stderr}')
                return False

            # Track this stash for cleanup
            self._hagent_stashes.append(stash_hash)
            self.logger.debug(f'Stored snapshot {stash_hash} with message: {message}')
            return True

        except (subprocess.TimeoutExpired, subprocess.CalledProcessError) as e:
            self.logger.warning(f'Error storing snapshot {stash_hash}: {e}')
            return False

    def _get_snapshot_diff(self, stash_ref: str, paths: List[str]) -> str:
        """
        Get diff for specific paths since snapshot.

        Args:
            stash_ref: Stash reference (e.g., stash@{0} or hash)
            paths: List of paths to get diff for

        Returns:
            Unified diff output as string
        """
        if not paths:
            return ''

        try:
            # First try the normal git diff approach
            cmd = ['git', 'diff', stash_ref, '--']
            cmd.extend(paths)

            result = subprocess.run(cmd, cwd=self.path_manager.repo_dir, capture_output=True, text=True, timeout=60)


            if result.returncode == 0 and result.stdout.strip():
                return result.stdout
            
            # If git diff doesn't work (e.g., for untracked files), manually compare
            diffs = []
            for path in paths:
                diff_content = self._manual_diff_with_stash(stash_ref, path)
                if diff_content:
                    diffs.append(diff_content)
            
            return '\n'.join(diffs)

        except (subprocess.TimeoutExpired, subprocess.CalledProcessError) as e:
            self.logger.warning(f'Error getting snapshot diff: {e}')
            return ''

    def _manual_diff_with_stash(self, stash_ref: str, file_path: str) -> str:
        """
        Manually compare a file between stash and working tree.
        
        Args:
            stash_ref: Stash reference
            file_path: Path to file (relative to repo)
            
        Returns:
            Unified diff string
        """
        try:
            # Get file content from stash
            stash_result = subprocess.run(
                ['git', 'show', f'{stash_ref}:{file_path}'],
                cwd=self.path_manager.repo_dir,
                capture_output=True,
                text=True,
                timeout=30
            )
            
            if stash_result.returncode != 0:
                # File doesn't exist in stash
                return ''
            
            stash_content = stash_result.stdout
            
            # Get current file content
            current_file = Path(self.path_manager.repo_dir) / file_path
            if not current_file.exists():
                # File was deleted
                return f'--- {file_path}\n+++ /dev/null\n@@ -1,{len(stash_content.splitlines())} +0,0 @@\n' + \
                       '\n'.join(f'-{line}' for line in stash_content.splitlines())
            
            try:
                current_content = current_file.read_text()
            except UnicodeDecodeError:
                # Binary file
                return f'Binary files {file_path} and {file_path} differ'
            
            # Compare using difflib for unified diff
            diff_lines = list(difflib.unified_diff(
                stash_content.splitlines(keepends=True),
                current_content.splitlines(keepends=True),
                fromfile=f'{file_path} (baseline)',
                tofile=f'{file_path} (current)',
                lineterm=''
            ))
            
            return ''.join(diff_lines)
            
        except Exception as e:
            self.logger.warning(f'Manual diff failed for {file_path}: {e}')
            return ''

    def _cleanup_snapshots(self) -> None:
        """
        Clean up all hagent-created stash entries.

        This is called by cleanup() and removes only stashes created by this
        FileTracker instance.
        """
        if not self._hagent_stashes:
            return

        for stash_hash in self._hagent_stashes[:]:
            self._drop_stash_by_hash(stash_hash)

    def _drop_stash_by_hash(self, stash_hash: str) -> bool:
        """
        Drop a specific stash by its hash.

        Args:
            stash_hash: Hash of the stash to drop

        Returns:
            True if dropped successfully, False otherwise
        """
        try:
            # Find the stash reference for this hash
            result = subprocess.run(
                ['git', 'stash', 'list', '--format=%H %gd'],
                cwd=self.path_manager.repo_dir,
                capture_output=True,
                text=True,
                timeout=30,
            )

            if result.returncode != 0:
                self.logger.warning(f'Failed to list stashes: {result.stderr}')
                return False

            # Look for our stash hash
            for line in result.stdout.strip().split('\n'):
                if not line:
                    continue

                parts = line.split()
                if len(parts) >= 2 and parts[0] == stash_hash:
                    stash_ref = parts[1]

                    # Drop the stash
                    drop_result = subprocess.run(
                        ['git', 'stash', 'drop', stash_ref],
                        cwd=self.path_manager.repo_dir,
                        capture_output=True,
                        text=True,
                        timeout=30,
                    )

                    if drop_result.returncode == 0:
                        self.logger.debug(f'Dropped stash {stash_ref} ({stash_hash})')
                        self._hagent_stashes.remove(stash_hash)
                        return True
                    else:
                        self.logger.warning(f'Failed to drop stash {stash_ref}: {drop_result.stderr}')
                        return False

            # Stash not found, remove from tracking list
            self.logger.debug(f'Stash {stash_hash} no longer exists')
            self._hagent_stashes.remove(stash_hash)
            return True

        except (subprocess.TimeoutExpired, subprocess.CalledProcessError) as e:
            self.logger.warning(f'Error dropping stash {stash_hash}: {e}')
            return False

    def cleanup(self) -> None:
        """
        Clean up all tracking resources.

        This removes all git stashes created by FileTracker and cleans up
        any temporary tracking artifacts. This method is idempotent and
        safe to call multiple times.
        """
        # Clean up stashes using the dedicated method
        try:
            self._cleanup_snapshots()
        except Exception as e:
            self.logger.warning(f'Error during snapshot cleanup: {e}')

        # Clean up build tracking artifacts
        try:
            self._cleanup_build_tracking()
        except Exception as e:
            self.logger.warning(f'Error during build tracking cleanup: {e}')

        # Clear tracking state
        self._tracked_files.clear()
        self._tracked_dirs.clear()
        self._baseline_stash = None

        self.logger.info('FileTracker cleanup completed')

    def track_file(self, file_path: str) -> bool:
        """
        Track individual file for changes.

        Args:
            file_path: Path to file (can be relative or absolute)

        Returns:
            True if successfully added to tracking, False otherwise
        """
        try:
            resolved_path = self._resolve_tracking_path(file_path)

            # Validate file exists or can be created
            path_obj = Path(resolved_path)
            if not path_obj.exists() and not path_obj.parent.exists():
                self.logger.warning(f"Cannot track file - parent directory doesn't exist: {resolved_path}")
                return False

            # Add to tracked files
            self._tracked_files.add(resolved_path)
            self.logger.debug(f'Tracking file: {resolved_path}')
            return True

        except Exception as e:
            self.logger.error(f"Failed to track file '{file_path}': {e}")
            return False

    def track_dir(self, dir_path: str, ext_filter: Optional[str] = None) -> bool:
        """
        Track directory with optional extension filter.

        Args:
            dir_path: Path to directory (can be relative or absolute)
            ext_filter: Optional extension filter (e.g., '.scala', '.v')

        Returns:
            True if successfully added to tracking, False otherwise
        """
        try:
            resolved_path = self._resolve_tracking_path(dir_path)

            # Validate directory exists or can be created
            path_obj = Path(resolved_path)
            if not path_obj.exists() and not path_obj.parent.exists():
                self.logger.warning(f"Cannot track directory - parent doesn't exist: {resolved_path}")
                return False

            # Add to tracked directories
            self._tracked_dirs.append({'path': resolved_path, 'ext': ext_filter})

            self.logger.debug(f'Tracking directory: {resolved_path} (ext: {ext_filter})')
            return True

        except Exception as e:
            self.logger.error(f"Failed to track directory '{dir_path}': {e}")
            return False

    def get_tracked_files(self, ext_filter: Optional[str] = None) -> Set[str]:
        """
        Get set of currently tracked files.

        Args:
            ext_filter: Optional extension filter

        Returns:
            Set of tracked file paths (includes files from tracked directories)
        """
        tracked = set()

        # Add individually tracked files
        for file_path in self._tracked_files:
            if ext_filter is None or file_path.endswith(ext_filter):
                tracked.add(file_path)

        # Add files from tracked directories
        for dir_info in self._tracked_dirs:
            dir_path = Path(dir_info['path'])
            dir_ext = dir_info['ext']

            if dir_path.exists():
                try:
                    # Find all files in directory
                    if dir_path.is_file():
                        # Single file tracked as directory
                        if self._matches_filter(str(dir_path), ext_filter, dir_ext):
                            tracked.add(str(dir_path))
                    else:
                        # Directory - find all matching files
                        for file_path in self._find_files_in_dir(dir_path, ext_filter, dir_ext):
                            tracked.add(file_path)

                except Exception as e:
                    self.logger.warning(f'Error scanning directory {dir_path}: {e}')

        return tracked

    def _resolve_tracking_path(self, path: str) -> str:
        """
        Resolve path relative to appropriate base directory.

        Args:
            path: Path to resolve

        Returns:
            Absolute path string
        """
        if os.path.isabs(path):
            return os.path.normpath(path)

        # Try relative to repo_dir first, then build_dir
        repo_path = Path(self.path_manager.repo_dir) / path
        build_path = Path(self.path_manager.build_dir) / path

        # Check which base makes more sense based on existence
        if repo_path.exists() or repo_path.parent.exists():
            return str(repo_path.resolve())
        elif build_path.exists() or build_path.parent.exists():
            return str(build_path.resolve())
        else:
            # Default to repo_dir for new files
            return str(repo_path.resolve())

    def _matches_filter(self, file_path: str, ext_filter: Optional[str], dir_ext: Optional[str]) -> bool:
        """
        Check if file matches extension filters.

        Args:
            file_path: Path to check
            ext_filter: Extension filter from get_tracked_files
            dir_ext: Extension filter from directory tracking

        Returns:
            True if file matches all applicable filters
        """
        # Check extension filter from get_tracked_files call
        if ext_filter is not None and not file_path.endswith(ext_filter):
            return False

        # Check extension filter from directory tracking
        if dir_ext is not None and not file_path.endswith(dir_ext):
            return False

        return True

    def _find_files_in_dir(self, dir_path: Path, ext_filter: Optional[str], dir_ext: Optional[str]) -> List[str]:
        """
        Find all files in directory matching filters.

        Args:
            dir_path: Directory to search
            ext_filter: Extension filter from get_tracked_files
            dir_ext: Extension filter from directory tracking

        Returns:
            List of matching file paths
        """
        files = []

        try:
            # Use recursive glob to find all files
            for file_path in dir_path.rglob('*'):
                if file_path.is_file():
                    file_str = str(file_path)
                    if self._matches_filter(file_str, ext_filter, dir_ext):
                        files.append(file_str)

        except Exception as e:
            self.logger.warning(f'Error finding files in {dir_path}: {e}')

        return files

    def _setup_build_tracking(self) -> bool:
        """
        Setup build directory tracking based on execution mode.

        Returns:
            True if setup successful, False otherwise
        """
        try:
            if self.path_manager.is_docker_mode():
                # Docker mode: track build directory directly (mounted)
                self.logger.debug('Docker mode: tracking build directory directly')
                return True
            else:
                # Local mode: copy build to cache for tracking
                self.logger.debug('Local mode: syncing build directory to cache')
                return self._sync_build_dir_local()

        except Exception as e:
            self.logger.error(f'Failed to setup build tracking: {e}')
            return False

    def _sync_build_dir_local(self) -> bool:
        """
        Copy build dir to cache for local execution tracking.

        Returns:
            True if sync successful, False otherwise
        """
        try:
            import shutil

            build_dir = Path(self.path_manager.build_dir)
            cache_build_dir = Path(self.path_manager.cache_dir) / 'build'

            # Remove existing cache build directory
            if cache_build_dir.exists():
                shutil.rmtree(cache_build_dir)

            # Copy build directory to cache if it exists
            if build_dir.exists():
                shutil.copytree(build_dir, cache_build_dir, dirs_exist_ok=True)
                self.logger.debug(f'Synced build directory to cache: {cache_build_dir}')
            else:
                # Create empty cache directory for future builds
                cache_build_dir.mkdir(parents=True, exist_ok=True)
                self.logger.debug(f'Created empty cache build directory: {cache_build_dir}')

            return True

        except Exception as e:
            self.logger.error(f'Failed to sync build directory: {e}')
            return False

    def _track_build_changes(self, paths: List[str]) -> str:
        """
        Generate diffs for build directory changes.

        Args:
            paths: List of build directory paths to track

        Returns:
            Diff output as string
        """
        if not paths:
            return ''

        if self.path_manager.is_docker_mode():
            return self._track_build_changes_docker(paths)
        else:
            return self._track_build_changes_local(paths)

    def _track_build_changes_docker(self, paths: List[str]) -> str:
        """
        Track build changes in Docker mode (direct tracking).

        Args:
            paths: List of paths in build directory

        Returns:
            Diff output as string
        """
        # In Docker mode, we can't use git for build directory tracking
        # since build dir is typically not a git repo. We'll use simple
        # file comparison against baseline if available.

        # For now, return empty - this could be enhanced with file timestamps
        # or other change detection mechanisms if needed
        self.logger.debug('Docker build tracking not fully implemented yet')
        return ''

    def _track_build_changes_local(self, paths: List[str]) -> str:
        """
        Track build changes in local mode (cache comparison).

        Args:
            paths: List of paths in build directory

        Returns:
            Diff output as string showing changes
        """
        try:
            import subprocess

            build_dir = Path(self.path_manager.build_dir)
            cache_build_dir = Path(self.path_manager.cache_dir) / 'build'

            if not cache_build_dir.exists():
                return ''  # No baseline to compare against

            diffs = []

            for path in paths:
                build_path = Path(path)

                # Make sure this path is in the build directory
                if not str(build_path).startswith(str(build_dir)):
                    continue

                # Get relative path within build directory
                try:
                    rel_path = build_path.relative_to(build_dir)
                    cache_path = cache_build_dir / rel_path

                    # Compare files using diff command
                    if cache_path.exists() and build_path.exists():
                        result = subprocess.run(
                            ['diff', '-u', str(cache_path), str(build_path)], capture_output=True, text=True, timeout=30
                        )

                        if result.returncode == 1:  # Files differ
                            diffs.append(result.stdout)
                        elif result.returncode != 0:  # Error
                            self.logger.warning(f'Diff failed for {path}: {result.stderr}')

                    elif not cache_path.exists() and build_path.exists():
                        # New file
                        diffs.append(f'--- /dev/null\n+++ {rel_path}\n@@ -0,0 +1,1 @@\n+[New file: {rel_path}]\n')

                    elif cache_path.exists() and not build_path.exists():
                        # Deleted file
                        diffs.append(f'--- {rel_path}\n+++ /dev/null\n@@ -1,1 +0,0 @@\n-[Deleted file: {rel_path}]\n')

                except ValueError:
                    # Path is not relative to build_dir
                    continue

            return '\n'.join(diffs)

        except Exception as e:
            self.logger.error(f'Failed to track build changes: {e}')
            return ''

    def _cleanup_build_tracking(self) -> None:
        """
        Cleanup build directory tracking artifacts.

        For local mode, this means cleaning up the cache build directory.
        For Docker mode, no special cleanup is needed.
        """
        try:
            if self.path_manager.is_local_mode():
                import shutil

                cache_build_dir = Path(self.path_manager.cache_dir) / 'build'

                if cache_build_dir.exists():
                    shutil.rmtree(cache_build_dir)
                    self.logger.debug('Cleaned up cache build directory')

        except Exception as e:
            self.logger.warning(f'Error cleaning up build tracking: {e}')

    def get_diff(self, file_path: str) -> str:
        """
        Get unified diff for specific tracked file.

        Args:
            file_path: Path to file to get diff for

        Returns:
            Unified diff output as string
        """
        if not self._baseline_stash:
            return ''

        try:
            # Convert to relative path for git diff
            abs_path = self._resolve_tracking_path(file_path)
            repo_dir = Path(self.path_manager.repo_dir)


            # Check if file is in repo directory (resolve symlinks for comparison)
            abs_path_obj = Path(abs_path).resolve()
            repo_dir_resolved = repo_dir.resolve()
            if repo_dir_resolved in abs_path_obj.parents or abs_path_obj == repo_dir_resolved:
                rel_path = abs_path_obj.relative_to(repo_dir_resolved)
                return self._get_snapshot_diff(self._baseline_stash, [str(rel_path)])
            else:
                self.logger.debug(f"File is in build directory, using build tracking")
                # File is in build directory - use build tracking
                build_paths = [abs_path]
                return self._track_build_changes(build_paths)

        except Exception as e:
            self.logger.error(f"Failed to get diff for '{file_path}': {e}")
            return ''

    def get_all_diffs(self, ext_filter: Optional[str] = None) -> Dict[str, str]:
        """
        Get diffs for all tracked files with optional filtering.

        Args:
            ext_filter: Optional extension filter (e.g., '.scala')

        Returns:
            Dictionary mapping file paths to their diff content
        """
        diffs = {}

        try:
            # Get all tracked files
            tracked_files = self.get_tracked_files(ext_filter)

            # Generate diffs for each file
            for file_path in tracked_files:
                diff_content = self.get_diff(file_path)
                if diff_content.strip():  # Only include non-empty diffs
                    diffs[file_path] = diff_content

        except Exception as e:
            self.logger.error(f'Failed to get all diffs: {e}')

        return diffs

    def get_patch_dict(self) -> Dict[str, Any]:
        """
        Generate patch dictionary compatible with YAML export.

        Returns:
            Dictionary with 'full' and 'patch' lists compatible with existing format
        """
        patch_dict = {'full': [], 'patch': []}

        try:
            # Get all diffs
            all_diffs = self.get_all_diffs()

            for file_path, diff_content in all_diffs.items():
                # Read current file content for size comparison
                current_content = self._read_file_content(file_path)

                if current_content is None:
                    # Binary file or read error
                    patch_dict['full'].append({'filename': file_path, 'contents': '[Binary File or Read Error]'})
                    continue

                # Decide between full content or patch based on size
                if self._should_use_full_content(diff_content, current_content):
                    patch_dict['full'].append({'filename': file_path, 'contents': current_content})
                else:
                    patch_dict['patch'].append({'filename': file_path, 'diff': diff_content})

        except Exception as e:
            self.logger.error(f'Failed to generate patch dictionary: {e}')

        return patch_dict

    def _is_binary_file(self, file_path: str) -> bool:
        """
        Detect if file is binary to avoid diff generation.

        Args:
            file_path: Path to file to check

        Returns:
            True if file appears to be binary, False otherwise
        """
        try:
            path = Path(file_path)
            if not path.exists():
                return False

            # Read first 8192 bytes to check for binary content
            with open(path, 'rb') as f:
                chunk = f.read(8192)

            # Check for null bytes which typically indicate binary content
            if b'\0' in chunk:
                return True

            # Check if content is mostly non-text characters
            try:
                chunk.decode('utf-8')
                return False
            except UnicodeDecodeError:
                return True

        except Exception:
            # If we can't read it, assume it's binary
            return True

    def _read_file_content(self, file_path: str) -> Optional[str]:
        """
        Read file content, handling binary files gracefully.

        Args:
            file_path: Path to file to read

        Returns:
            File content as string, or None if binary/error
        """
        try:
            if self._is_binary_file(file_path):
                return None

            path = Path(file_path)
            if not path.exists():
                return ''

            with open(path, 'r', encoding='utf-8', errors='replace') as f:
                return f.read()

        except Exception as e:
            self.logger.warning(f"Failed to read file '{file_path}': {e}")
            return None

    def _should_use_full_content(self, diff_content: str, file_content: str) -> bool:
        """
        Decide whether to use full content or patch based on size comparison.

        Args:
            diff_content: The diff content
            file_content: The full file content

        Returns:
            True if should use full content, False if should use patch
        """
        if not diff_content or not file_content:
            return True

        # Use full content if:
        # - File is small (< 1KB)
        # - Diff is large relative to file size (> 50% of original)
        # - File content is very short

        file_size = len(file_content.encode('utf-8'))
        diff_size = len(diff_content.encode('utf-8'))

        if file_size < 1024:  # Files smaller than 1KB
            return True

        if len(file_content.split('\n')) < 10:  # Very short files
            return True

        if file_size > 0 and (diff_size / file_size) > 0.5:  # Large diffs
            return True

        return False

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
