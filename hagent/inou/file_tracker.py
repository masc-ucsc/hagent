"""
File tracking using unified git approach.

Always uses git for tracking any files (repo files, build files, etc.) by ensuring
a git repository exists (creating temporary one if needed) and using git stash
snapshots to track changes. This unified approach eliminates complex build directory
tracking logic and provides consistent behavior across all execution modes.
"""

import difflib
import logging
import os
import subprocess
import sys
from pathlib import Path
from typing import Optional, Set, List, Dict, Any

from .path_manager import PathManager
from .container_manager import is_docker_mode, is_docker_workspace_ready


class FileTrackerLocal:
    """
    File tracking using unified git approach.

    This class provides file tracking capabilities by ensuring a git repository
    exists (creating temporary one if needed) and using git stash snapshots to
    track changes to explicitly specified files and directories. This unified
    approach works consistently across all execution modes and directory types.
    """

    def __init__(self, path_manager: PathManager, container_manager=None):
        """
        Initialize file tracker with path manager dependency.

        Args:
            path_manager: PathManager instance for resolving HAGENT_* paths

        Raises:
            SystemExit: If git repository validation fails or git is not available
        """
        self.path_manager = path_manager
        self.logger = logging.getLogger(__name__)
        # Optional handle to an active ContainerManager when in docker mode
        self.container_manager = container_manager

        # Initialize tracking state
        self._tracked_files: Set[str] = set()
        self._tracked_dirs: List[Dict[str, str]] = []  # [{'path': str, 'ext': str}, ...]
        self._baseline_stash: Optional[str] = None
        self._hagent_stashes: List[str] = []  # Track our stash references for cleanup
        self.temp_git_created = False  # Track if we created a temporary git repo

        # Check git availability first
        if not self._check_git_available():
            self._fail_fast('FileTracker requires git command to be available')
            return

        # Ensure git repository exists (create temporary one if needed)
        if not self._ensure_git_repo():
            self._fail_fast('FileTracker failed to ensure git repository availability')
            return

        # Create baseline snapshot for pre-existing changes
        baseline = self._create_baseline_snapshot()
        if baseline:
            self._baseline_stash = baseline
            self.logger.info(f'Created baseline snapshot: {baseline}')
        else:
            self.logger.info('No pre-existing changes to snapshot')

        self.logger.info('FileTrackerLocal initialized successfully')

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

    def _ensure_git_repo(self) -> bool:
        """
        Ensure git repository exists, creating temporary one if needed.

        Returns:
            True if git repository is available, False otherwise
        """
        repo_dir = Path(self.path_manager.repo_dir)

        print(f'🔍 DEBUG: FileTracker checking repo_dir: {repo_dir}')

        # In Docker mode with container paths, check if workspace is ready
        if is_docker_mode() and str(repo_dir).startswith('/code/workspace/'):
            print('🔍 DEBUG: Docker mode with container paths - checking workspace readiness')
            if not is_docker_workspace_ready():
                self.logger.error('Docker workspace not ready - ensure ContainerManager.setup() was called first')
                return False
            return True

        # For all other cases (native mode or Docker with host-mounted paths), check if directory exists on host
        if not repo_dir.exists():
            self.logger.error(f'Repository directory does not exist: {repo_dir}')
            return False

        # Check if it's already a git repository
        git_dir = repo_dir / '.git'
        if git_dir.exists():
            # Validate existing git repository
            try:
                result = subprocess.run(
                    ['git', 'rev-parse', '--git-dir'], cwd=repo_dir, capture_output=True, text=True, timeout=30
                )
                if result.returncode == 0:
                    self.logger.debug(f'Using existing git repository: {repo_dir}')
                    return True
                else:
                    self.logger.warning(f'Existing git repository is invalid: {result.stderr}')
                    # Continue to create temporary git repo
            except (subprocess.TimeoutExpired, subprocess.CalledProcessError, FileNotFoundError) as e:
                self.logger.warning(f'Failed to validate existing git repository: {e}')
                # Continue to create temporary git repo

        # Create temporary git repository
        try:
            self.logger.info(f'Creating temporary git repository for tracking: {repo_dir}')

            # Initialize git repository
            result = subprocess.run(['git', 'init'], cwd=repo_dir, capture_output=True, text=True, timeout=30)
            if result.returncode != 0:
                self.logger.error(f'Failed to initialize git repository: {result.stderr}')
                return False

            # Configure git user for commits (required for stash operations)
            subprocess.run(['git', 'config', 'user.email', 'hagent@temporary'], cwd=repo_dir, capture_output=True, timeout=10)
            subprocess.run(['git', 'config', 'user.name', 'HAgent Temporary'], cwd=repo_dir, capture_output=True, timeout=10)

            # Create initial commit so we can use stash operations
            gitignore_path = repo_dir / '.gitignore'
            gitignore_path.write_text('# Temporary HAgent git repository for file tracking\n')

            subprocess.run(['git', 'add', '.gitignore'], cwd=repo_dir, capture_output=True, timeout=10)
            commit_result = subprocess.run(
                ['git', 'commit', '-m', 'Initial HAgent tracking commit'],
                cwd=repo_dir,
                capture_output=True,
                text=True,
                timeout=30,
            )

            if commit_result.returncode != 0:
                self.logger.warning(f'Failed to create initial commit: {commit_result.stderr}')
                # Continue anyway - stash operations might still work

            self.temp_git_created = True
            self.logger.info('Successfully created temporary git repository for tracking')
            return True

        except (subprocess.TimeoutExpired, subprocess.CalledProcessError, FileNotFoundError) as e:
            self.logger.error(f'Failed to create temporary git repository: {e}')
            return False

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
        print('🔍 DEBUG: _create_baseline_snapshot')

        # In Docker mode with container paths, skip baseline snapshot creation for now
        # Git operations in Docker require container-aware execution
        repo_dir = str(self.path_manager.repo_dir)
        if is_docker_mode() and repo_dir.startswith('/code/workspace/'):
            print('🔍 DEBUG: Docker mode with container paths - skipping baseline snapshot creation')
            self.logger.info('Skipping baseline snapshot creation in Docker mode with container paths')
            return None

        try:
            # Check if there are any changes to stash (tracked, staged, and untracked)
            # First check tracked files for modifications
            result = subprocess.run(
                ['git', 'diff-index', '--quiet', 'HEAD'], cwd=self.path_manager.repo_dir, capture_output=True, timeout=30
            )

            has_tracked_changes = result.returncode != 0

            # Check for staged changes
            staged_result = subprocess.run(
                ['git', 'diff-index', '--quiet', '--cached', 'HEAD'],
                cwd=self.path_manager.repo_dir,
                capture_output=True,
                timeout=30,
            )

            has_staged_changes = staged_result.returncode != 0

            # Check for untracked files
            untracked_result = subprocess.run(
                ['git', 'ls-files', '--others', '--exclude-standard'],
                cwd=self.path_manager.repo_dir,
                capture_output=True,
                text=True,
                timeout=30,
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
                timeout=30,
            )

            if stash_result.returncode != 0:
                # File doesn't exist in stash
                return ''

            stash_content = stash_result.stdout

            # Get current file content
            current_file = Path(self.path_manager.repo_dir) / file_path
            if not current_file.exists():
                # File was deleted
                return f'--- {file_path}\n+++ /dev/null\n@@ -1,{len(stash_content.splitlines())} +0,0 @@\n' + '\n'.join(
                    f'-{line}' for line in stash_content.splitlines()
                )

            try:
                current_content = current_file.read_text()
            except UnicodeDecodeError:
                # Binary file
                return f'Binary files {file_path} and {file_path} differ'

            # Compare using difflib for unified diff
            diff_lines = list(
                difflib.unified_diff(
                    stash_content.splitlines(keepends=True),
                    current_content.splitlines(keepends=True),
                    fromfile=f'{file_path} (baseline)',
                    tofile=f'{file_path} (current)',
                    lineterm='',
                )
            )

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

        # Clean up temporary git repository if we created it
        try:
            self._cleanup_temporary_git_repo()
        except Exception as e:
            self.logger.warning(f'Error during temporary git repo cleanup: {e}')

        # Clear tracking state
        self._tracked_files.clear()
        self._tracked_dirs.clear()
        self._baseline_stash = None

        self.logger.info('FileTrackerLocal cleanup completed')

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

            # Validate file/parent existence. In docker mode, check inside container.
            if self._is_container_path(resolved_path):
                if not self._container_parent_exists(resolved_path):
                    self.logger.warning(f"Cannot track file - parent directory doesn't exist (container): {resolved_path}")
                    return False
            else:
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

            # Validate directory existence. In docker mode, check inside container.
            if self._is_container_path(resolved_path):
                if not self._container_parent_exists(resolved_path):
                    self.logger.warning(f"Cannot track directory - parent doesn't exist (container): {resolved_path}")
                    return False
            else:
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
            dir_path_str = dir_info['path']
            dir_ext = dir_info['ext']

            if self._is_container_path(dir_path_str):
                try:
                    for f in self._find_files_in_dir_container(dir_path_str, ext_filter, dir_ext):
                        tracked.add(f)
                except Exception as e:
                    self.logger.warning(f'Error scanning container directory {dir_path_str}: {e}')
            else:
                dir_path = Path(dir_path_str)
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
        Resolve path relative to git repository root.

        With always-use-git strategy, all paths are resolved relative to
        the git repository root directory (repo_dir).

        Args:
            path: Path to resolve

        Returns:
            Absolute path string
        """
        if os.path.isabs(path):
            return os.path.normpath(path)

        # All paths are relative to repo_dir (git repository root)
        repo_path = Path(self.path_manager.repo_dir) / path
        # In docker mode, repo_dir may be a container path. Return normalized string.
        try:
            return str(repo_path.resolve())
        except Exception:
            return str(repo_path)

    # ---------------- Docker helpers ----------------
    def _is_container_path(self, path: str) -> bool:
        return is_docker_mode() and str(path).startswith('/code/workspace/') and self.container_manager is not None

    def _container_parent_exists(self, path: str) -> bool:
        if not self._is_container_path(path):
            return False
        # Use 'test -d' on parent directory in container
        parent = os.path.dirname(path.rstrip('/')) or '/'
        try:
            rc, out, err = self.container_manager.run_cmd(f'test -d "{parent}" && echo OK || echo MISS')
            return rc == 0 and 'OK' in out
        except Exception:
            return False

    def _find_files_in_dir_container(self, dir_path: str, ext_filter: Optional[str], dir_ext: Optional[str]) -> List[str]:
        """Find files in a container directory, filtering by extensions."""
        files: List[str] = []
        # If dir_path is a file, handle directly
        rc, out, err = self.container_manager.run_cmd(f'test -f "{dir_path}" && echo FILE || echo DIR', quiet=True)
        if rc == 0 and 'FILE' in out:
            candidate = dir_path
            if self._matches_filter(candidate, ext_filter, dir_ext):
                files.append(candidate)
            return files

        # Directory search via find
        rc, out, err = self.container_manager.run_cmd(f'find "{dir_path}" -type f 2>/dev/null || true', quiet=True)
        if rc != 0:
            return files
        for line in out.splitlines():
            p = line.strip()
            if not p:
                continue
            if self._matches_filter(p, ext_filter, dir_ext):
                files.append(p)
        return files

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

    def _cleanup_temporary_git_repo(self) -> None:
        """
        Cleanup temporary git repository if we created it.

        This removes the .git directory we created for tracking purposes.
        Only removes git repo if temp_git_created flag is True.
        """
        if not self.temp_git_created:
            return

        try:
            import shutil

            repo_dir = Path(self.path_manager.repo_dir)
            git_dir = repo_dir / '.git'

            if git_dir.exists():
                shutil.rmtree(git_dir)
                self.logger.debug('Cleaned up temporary git repository')

                # Also remove the .gitignore we created
                gitignore_path = repo_dir / '.gitignore'
                if gitignore_path.exists():
                    gitignore_content = gitignore_path.read_text()
                    if 'Temporary HAgent git repository' in gitignore_content:
                        gitignore_path.unlink()
                        self.logger.debug('Removed temporary .gitignore file')

        except Exception as e:
            self.logger.warning(f'Error cleaning up temporary git repository: {e}')

    def get_diff(self, file_path: str) -> str:
        """
        Get unified diff for specific tracked file using git.

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

            # Convert to relative path within git repository
            abs_path_obj = Path(abs_path).resolve()
            repo_dir_resolved = repo_dir.resolve()

            try:
                rel_path = abs_path_obj.relative_to(repo_dir_resolved)
                return self._get_snapshot_diff(self._baseline_stash, [str(rel_path)])
            except ValueError:
                # File is outside git repository - this shouldn't happen with always-use-git strategy
                # but handle gracefully
                self.logger.warning(f'File is outside git repository: {abs_path}')
                return ''

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

        # Basic validation: container must be ready
        repo_dir = str(self.path_manager.repo_dir)
        if not str(repo_dir).startswith('/code/workspace/'):
            self.logger.warning('FileTrackerDocker expected container paths for repo_dir')

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
        if not os.path.isabs(file_path):
            path = str(Path('/code/workspace/repo') / file_path)
        else:
            path = file_path

        # Parent dir must exist
        parent = os.path.dirname(path.rstrip('/')) or '/'
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
        if not os.path.isabs(dir_path):
            path = str(Path('/code/workspace/repo') / dir_path)
        else:
            path = dir_path

        parent = os.path.dirname(path.rstrip('/')) or '/'
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
        if not os.path.isabs(file_path):
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


class FileTracker:
    """
    Facade that selects Local or Docker file tracker implementation.
    """

    def __init__(self, path_manager: PathManager, container_manager=None):
        if path_manager.execution_mode == 'docker' and container_manager is not None:
            self._impl = FileTrackerDocker(path_manager, container_manager)
        else:
            self._impl = FileTrackerLocal(path_manager, container_manager)

    # Delegate API
    def cleanup(self) -> None:
        return self._impl.cleanup()

    def track_file(self, file_path: str) -> bool:
        return self._impl.track_file(file_path)

    def track_dir(self, dir_path: str, ext_filter: Optional[str] = None) -> bool:
        return self._impl.track_dir(dir_path, ext_filter)

    def get_tracked_files(self, ext_filter: Optional[str] = None) -> Set[str]:
        return self._impl.get_tracked_files(ext_filter)

    def get_diff(self, file_path: str) -> str:
        return self._impl.get_diff(file_path)

    def get_all_diffs(self, ext_filter: Optional[str] = None) -> Dict[str, str]:
        return self._impl.get_all_diffs(ext_filter)

    def get_patch_dict(self) -> Dict[str, Any]:
        return self._impl.get_patch_dict()

    def __enter__(self):
        self._impl.__enter__()
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        return self._impl.__exit__(exc_type, exc_val, exc_tb)

    def __del__(self) -> None:
        try:
            self.cleanup()
        except Exception:
            pass

    def __getattr__(self, name):
        # Delegate unknown attributes to underlying implementation
        return getattr(self._impl, name)
