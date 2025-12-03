#!/usr/bin/env python3
"""
CLI tool for demonstrating FileTracker functionality.

Provides command-line interface for testing and demonstrating the FileTracker
capabilities including tracking files/directories, getting diffs, and cleanup.
"""

import argparse
import sys

from .path_manager import PathManager
from .file_tracker import FileTracker


def cmd_track_file(args):
    """Track a single file."""
    print(f'Tracking file: {args.path}')

    try:
        with FileTracker() as tracker:
            if tracker.track_file(args.path):
                print(f'✓ Successfully tracking file: {args.path}')
                return 0
            else:
                print(f'✗ Failed to track file: {args.path}')
                return 1

    except Exception as e:
        print(f'Error: {e}')
        return 1


def cmd_track_dir(args):
    """Track a directory with optional extension filter."""
    print(f'Tracking directory: {args.path}')
    if args.ext:
        print(f'Extension filter: {args.ext}')

    try:
        with FileTracker() as tracker:
            if tracker.track_dir(args.path, args.ext):
                print(f'✓ Successfully tracking directory: {args.path}')
                return 0
            else:
                print(f'✗ Failed to track directory: {args.path}')
                return 1

    except Exception as e:
        print(f'Error: {e}')
        return 1


def cmd_get_diff(args):
    """Get diff for a specific file."""
    print(f'Getting diff for: {args.path}')

    try:
        with FileTracker() as tracker:
            # First track the file
            tracker.track_file(args.path)

            # Get the diff
            diff = tracker.get_diff(args.path)
            if diff:
                print('\n--- Diff ---')
                print(diff)
            else:
                print('No changes detected or file not tracked.')

        return 0

    except Exception as e:
        print(f'Error: {e}')
        return 1


def cmd_get_all_diffs(args):
    """Get diffs for all tracked files."""
    print('Getting diffs for all tracked files...')
    if args.ext:
        print(f'Extension filter: {args.ext}')

    try:
        with FileTracker() as tracker:
            # Track current directory by default for demo
            tracker.track_dir('.', args.ext)

            # Get all diffs
            all_diffs = tracker.get_all_diffs(args.ext)

            if not all_diffs:
                print('No changes detected in tracked files.')
                return 0

            print(f'\nFound changes in {len(all_diffs)} files:')
            for file_path, diff in all_diffs.items():
                print(f'\n--- Changes in {file_path} ---')
                print(diff)

        return 0

    except Exception as e:
        print(f'Error: {e}')
        return 1


def cmd_status(args):
    """Show status of FileTracker."""
    print('FileTracker Status:')

    try:
        # Show path manager info
        path_manager = PathManager()
        docker_mode = 'Yes' if path_manager.is_docker_mode() else 'No'
        print(f'Docker mode: {docker_mode}')
        print(f'Repo directory: {path_manager.repo_dir}')
        print(f'Build directory: {path_manager.build_dir}')
        print(f'Cache directory: {path_manager.cache_dir}')

        with FileTracker() as tracker:
            # Show some basic tracking info
            print(f'Baseline stash: {"Yes" if tracker._baseline_stash else "No"}')
            print(f'Tracked files: {len(tracker._tracked_files)}')
            print(f'Tracked directories: {len(tracker._tracked_dirs)}')

            if tracker._tracked_files:
                print('\nIndividually tracked files:')
                for file_path in tracker._tracked_files:
                    print(f'  {file_path}')

            if tracker._tracked_dirs:
                print('\nTracked directories:')
                for dir_info in tracker._tracked_dirs:
                    ext = f' (*.{dir_info["ext"]})' if dir_info['ext'] else ''
                    print(f'  {dir_info["path"]}{ext}')

        return 0

    except Exception as e:
        print(f'Error: {e}')
        return 1


def cmd_patch_dict(args):
    """Generate and display patch dictionary."""
    print('Generating patch dictionary...')

    try:
        with FileTracker() as tracker:
            # Track current directory for demo
            tracker.track_dir('.', args.ext)

            # Get patch dictionary
            patch_dict = tracker.get_patch_dict()

            print('\nPatch Dictionary Summary:')
            print(f'Full files: {len(patch_dict["full"])}')
            print(f'Patch files: {len(patch_dict["patch"])}')

            if patch_dict['full']:
                print('\nFiles with full content:')
                for item in patch_dict['full']:
                    filename = item['filename']
                    content_len = len(item['contents'])
                    print(f'  {filename} ({content_len} bytes)')

            if patch_dict['patch']:
                print('\nFiles with patches:')
                for item in patch_dict['patch']:
                    filename = item['filename']
                    diff_len = len(item['diff'])
                    print(f'  {filename} ({diff_len} bytes diff)')

            if args.show_content:
                print('\n--- Full Patch Dictionary ---')
                import json

                print(json.dumps(patch_dict, indent=2))

        return 0

    except Exception as e:
        print(f'Error: {e}')
        return 1


def cmd_cleanup(args):
    """Manually cleanup FileTracker resources."""
    print('Cleaning up FileTracker resources...')

    try:
        # Create and immediately cleanup a tracker to demonstrate
        tracker = FileTracker()
        tracker.cleanup()

        print('✓ Cleanup completed successfully')
        return 0

    except Exception as e:
        print(f'Error: {e}')
        return 1


def main():
    """Main CLI entry point."""
    parser = argparse.ArgumentParser(
        description='FileTracker CLI - Demonstrate git-based file tracking',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s track-file src/main.scala
  %(prog)s track-dir src --ext .scala
  %(prog)s get-diff src/main.scala
  %(prog)s get-all-diffs --ext .scala
  %(prog)s status
  %(prog)s patch-dict --ext .scala
  %(prog)s cleanup
        """,
    )

    subparsers = parser.add_subparsers(dest='command', help='Available commands')
    subparsers.required = True

    # track-file command
    track_file_parser = subparsers.add_parser('track-file', help='Track a single file')
    track_file_parser.add_argument('path', help='Path to file to track')
    track_file_parser.set_defaults(func=cmd_track_file)

    # track-dir command
    track_dir_parser = subparsers.add_parser('track-dir', help='Track a directory')
    track_dir_parser.add_argument('path', help='Path to directory to track')
    track_dir_parser.add_argument('--ext', help='Extension filter (e.g., .scala, .v)')
    track_dir_parser.set_defaults(func=cmd_track_dir)

    # get-diff command
    get_diff_parser = subparsers.add_parser('get-diff', help='Get diff for a file')
    get_diff_parser.add_argument('path', help='Path to file to get diff for')
    get_diff_parser.set_defaults(func=cmd_get_diff)

    # get-all-diffs command
    get_all_diffs_parser = subparsers.add_parser('get-all-diffs', help='Get diffs for all tracked files')
    get_all_diffs_parser.add_argument('--ext', help='Extension filter (e.g., .scala, .v)')
    get_all_diffs_parser.set_defaults(func=cmd_get_all_diffs)

    # status command
    status_parser = subparsers.add_parser('status', help='Show FileTracker status')
    status_parser.set_defaults(func=cmd_status)

    # patch-dict command
    patch_dict_parser = subparsers.add_parser('patch-dict', help='Generate patch dictionary')
    patch_dict_parser.add_argument('--ext', help='Extension filter (e.g., .scala, .v)')
    patch_dict_parser.add_argument('--show-content', action='store_true', help='Show full patch dictionary content')
    patch_dict_parser.set_defaults(func=cmd_patch_dict)

    # cleanup command
    cleanup_parser = subparsers.add_parser('cleanup', help='Cleanup FileTracker resources')
    cleanup_parser.set_defaults(func=cmd_cleanup)

    # Parse arguments and run command
    args = parser.parse_args()

    try:
        return args.func(args)
    except KeyboardInterrupt:
        print('\nInterrupted by user')
        return 130
    except Exception as e:
        print(f'Unexpected error: {e}')
        return 1


if __name__ == '__main__':
    sys.exit(main())
