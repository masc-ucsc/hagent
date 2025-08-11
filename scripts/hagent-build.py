#!/usr/bin/env python3

import argparse
import os
import sys
import subprocess
import yaml
from pathlib import Path
from typing import List, Optional


class HagentBuilder:
    def __init__(self, config_path: Optional[str] = None):
        self.config_path = config_path or self._find_config()
        self.config = self._load_config()

        # Base directory for config; used to derive sane defaults that are writable.
        cfg_dir = Path(self.config_path).resolve().parent

        # Repo dir: default to config directory; can be overridden by env.
        self.repo_dir = Path(os.environ.get('HAGENT_REPO_DIR', str(cfg_dir))).resolve()

        # Build base: default to "<cfg_dir>/build" (user-writable) unless env overrides it.
        self.build_base = Path(os.environ.get('HAGENT_BUILD_DIR', str(cfg_dir))).resolve()

        print(f'hagent-builder using {self.config_path} configuration')

        # Basic sanity (do not assert existence so listing still works without a repo checkout).
        assert self.config_path, 'config_path must be resolved'
        assert self.repo_dir.is_absolute(), 'repo_dir must be an absolute path'
        assert self.build_base.is_absolute(), 'build_base must be an absolute path'

    def _find_config(self) -> str:
        """Locate hagent.yaml via a small search path."""
        locations = [
            './hagent.yaml',
            'hagent.yaml',
            '/code/workspace/repo/hagent.yaml',
            '/code/workspace/hagent.yaml',
            Path(os.environ.get('HAGENT_REPO_DIR', ''), 'hagent.yaml'),
            Path(os.environ.get('HAGENT_BUILD_DIR', ''), 'hagent.yaml'),
        ]
        for loc in locations:
            if loc and os.path.exists(loc):
                return loc
        raise FileNotFoundError('No hagent.yaml found')

    def _load_config(self) -> dict:
        with open(self.config_path, 'r') as f:
            data = yaml.safe_load(f) or {}
        assert isinstance(data, dict), 'Top-level YAML must be a mapping'
        return data

    # ---------------------------- helpers ----------------------------

    @staticmethod
    def _profile_title(p: dict) -> str:
        # Prefer 'title' (new field). Fall back to 'description' for backward compatibility.
        return (p.get('title') or p.get('description') or '').strip()

    def _get_all_profiles(self) -> List[dict]:
        profs = self.config.get('profiles', []) or []
        assert isinstance(profs, list), "'profiles' must be a list"
        return profs

    def _find_by_exact_name(self, name: str) -> List[dict]:
        """Exact, case-insensitive match on unique 'name'."""
        return [p for p in self._get_all_profiles() if (p.get('name') or '').lower() == name.lower()]

    def _find_by_title_query(self, query: str) -> List[dict]:
        """Case-insensitive substring match on 'description')."""
        q = (query or '').strip().lower()
        return [p for p in self._get_all_profiles() if q in self._profile_title(p).lower()]

    def _ensure_build_dir(self, build_dir: Path) -> None:
        """Create build directory when not in dry-run."""
        # This is the only place we touch the filesystem for build dir creation.
        build_dir.mkdir(parents=True, exist_ok=True)

    def _setup_environment(self, profile: dict, build_dir: Path) -> dict:
        env = os.environ.copy()
        cfg = profile.get('configuration', {})
        if isinstance(cfg, dict):
            for k, v in (cfg.get('environment') or {}).items():
                # Allow $VAR expansion in YAML values
                env[k] = os.path.expandvars(v)
        env['HAGENT_REPO_DIR'] = str(self.repo_dir)
        env['HAGENT_BUILD_DIR'] = str(build_dir)
        return env

    def _parse_track_directive(self, directive: str, build_dir: Path) -> tuple:
        """
        Parse track_repo_dir() or track_build_dir() directives and validate paths.

        Args:
            directive: The directive string (e.g., "track_repo_dir('src/main/scala', ext='.scala')")
            build_dir: The build directory for this profile

        Returns:
            Tuple of (resolved_path, func_type, ext) where:
            - resolved_path: Absolute path to the directory
            - func_type: "repo_dir", "build_dir", or "unknown"
            - ext: The extension filter (if specified)

        Raises:
            FileNotFoundError: If repo directory doesn't exist
            PermissionError: If build directory cannot be created
        """
        if directive.startswith('track_repo_dir('):
            func_type = 'repo_dir'
            content = directive[15:-1]  # Remove "track_repo_dir(" and ")"
        elif directive.startswith('track_build_dir('):
            func_type = 'build_dir'
            content = directive[16:-1]  # Remove "track_build_dir(" and ")"
        else:
            return directive, 'unknown', None

        # Parse parameters
        parts = [p.strip().strip('\'"') for p in content.split(',')]
        path = parts[0]
        ext = None

        for part in parts[1:]:
            if part.startswith('ext='):
                ext = part[4:].strip('\'"')

        # Resolve and validate paths
        if func_type == 'repo_dir':
            resolved_path = (self.repo_dir / path).resolve()
            if not resolved_path.exists():
                raise FileNotFoundError(f'Repository directory does not exist: {resolved_path}')
        elif func_type == 'build_dir':
            resolved_path = (build_dir / path).resolve()
            # Check if we can create the build directory
            try:
                resolved_path.mkdir(parents=True, exist_ok=True)
            except PermissionError as e:
                raise PermissionError(f'Cannot create build directory: {resolved_path}') from e

        return str(resolved_path), func_type, ext

    def _validate_configuration(self, profile: dict, build_dir: Path, dry_run: bool = False) -> None:
        """
        Validate track directives in the configuration.

        Args:
            profile: Profile configuration dictionary
            build_dir: Build directory for this profile
            dry_run: If True, skip actual directory creation for build dirs

        Raises:
            FileNotFoundError: If repo directory doesn't exist
            PermissionError: If build directory cannot be created
            ValueError: If configuration is invalid
        """
        cfg = profile.get('configuration', {})
        if not isinstance(cfg, dict):
            return

        # Check source and output directives
        for key in ['source', 'output']:
            if key in cfg:
                directive = cfg[key]
                if isinstance(directive, str) and ('track_repo_dir(' in directive or 'track_build_dir(' in directive):
                    try:
                        if not dry_run or 'track_repo_dir(' in directive:
                            # Always validate repo dirs, validate build dirs only if not dry run
                            self._parse_track_directive(directive, build_dir)
                        print(f'✓ Validated {key}: {directive}')
                    except (FileNotFoundError, PermissionError) as e:
                        raise type(e)(f"Configuration validation failed for {key} '{directive}': {e}")

    # ---------------------------- listing ----------------------------

    def list_profiles(self):
        print('\nAvailable profiles:')
        print('-' * 60)
        for p in self._get_all_profiles():
            print(f'\nname: {p.get("name", "<unnamed>")}')
            print(f'  title: {self._profile_title(p) or "N/A"}')
            print('  APIs:')
            for api in p.get('apis', []):
                print(f'    - {api.get("name", "<noname>")}: {api.get("description", "N/A")}')

    def list_apis_for(self, profs: List[dict]):
        for p in profs:
            print(f'\nAPIs for {p.get("name", "<unnamed>")} [{self._profile_title(p) or "N/A"}]:')
            for api in p.get('apis', []):
                line = f'  {api.get("name", "<noname>")}: {api.get("description", "N/A")}'
                if 'command' in api:
                    line += f'\n    Command: {api["command"]}'
                print(line)

    # ---------------------------- API lookup ----------------------------

    @staticmethod
    def _find_api(profile: dict, api_name: str) -> Optional[dict]:
        for api in profile.get('apis', []):
            if api.get('name') == api_name:
                return api
        return None

    # ---------------------------- execution ----------------------------

    def _select_profile(self, exact_name: Optional[str], title_query: Optional[str]) -> dict:
        """
        Selection rules:
        - If --name is provided: exact match on 'name'. Error if 0 or >1.
        - Else if --profile is provided: substring match on 'description'. Error if 0 or >1.
        - Else: error.
        """
        if exact_name:
            hits = self._find_by_exact_name(exact_name)
            if not hits:
                # Exact error text required by user.
                avail = ', '.join(p.get('name', '<unnamed>') for p in self._get_all_profiles())
                raise ValueError(f"No profile matched --name '{exact_name}'. Available names: {avail}")
            if len(hits) > 1:  # Should not happen if names are unique, but enforce anyway.
                raise ValueError(
                    f"Multiple profiles matched --name '{exact_name}': " + ', '.join(p.get('name', '<unnamed>') for p in hits)
                )
            return hits[0]

        if title_query:
            hits = self._find_by_title_query(title_query)
            if not hits:
                raise ValueError(
                    f"No profile matched --profile '{title_query}' in titles. "
                    f'Try --name <exact_name>. Titles: '
                    + '; '.join(f'[{p.get("name")}] {self._profile_title(p) or "N/A"}' for p in self._get_all_profiles())
                )
            if len(hits) > 1:
                raise ValueError(
                    f"Multiple profiles matched --profile '{title_query}'. "
                    f'Disambiguate with --name. Matches: '
                    + '; '.join(f'[{p.get("name")}] {self._profile_title(p) or "N/A"}' for p in hits)
                )
            return hits[0]

        raise ValueError('You must specify either --name (exact match) or --profile (description substring match).')

    def execute(
        self,
        exact_name: Optional[str],
        title_query: Optional[str],
        api_name: str,
        extra_args: List[str] = None,
        dry_run: bool = False,
    ) -> int:
        profile = self._select_profile(exact_name, title_query)
        api = self._find_api(profile, api_name)
        if not api:
            self.list_apis_for([profile])
            raise ValueError(f"API '{api_name}' not found in profile '{profile.get('name')}'")

        # Validate configuration before proceeding
        self._validate_configuration(profile, self.build_base, dry_run)

        env = self._setup_environment(profile, self.build_base)

        # Compose command; replace simple placeholders.
        command = api['command']
        if extra_args:
            command = f'{command} {" ".join(extra_args)}'
        command = command.replace('$HAGENT_BUILD_DIR', str(self.build_base)).replace('$HAGENT_REPO_DIR', str(self.repo_dir))

        # Determine working directory
        cwd = api.get('cwd', str(self.repo_dir))
        cwd = cwd.replace('$HAGENT_BUILD_DIR', str(self.build_base)).replace('$HAGENT_REPO_DIR', str(self.repo_dir))
        cwd_path = Path(cwd).resolve()

        # Validate that the working directory exists
        if not cwd_path.exists():
            raise FileNotFoundError(f'Working directory does not exist: {cwd_path}')
        if not cwd_path.is_dir():
            raise NotADirectoryError(f'Working directory path is not a directory: {cwd_path}')

        print(f'Command: {command}')
        print(f'  Build directory: {self.build_base}')
        print(f'  Profile name: {profile.get("name")}')
        print(f'  Title: {self._profile_title(profile) or "N/A"}')
        print(f'  API: {api_name}')
        print(f'  Working directory: {cwd_path}')

        if dry_run:
            # No filesystem writes in dry-run; do NOT create directories.
            print('  [DRY RUN] Would execute the above command')
            print('  Environment overrides:')
            for k, v in sorted(env.items()):
                if k not in os.environ or os.environ[k] != v:
                    print(f'    {k}={v}')
            return 0

        # Create build directory only for real runs.
        self._ensure_build_dir(self.build_base)

        print('\n' + '=' * 60)
        result = subprocess.run(command, shell=True, cwd=str(cwd_path), env=env)
        return result.returncode


def main():
    parser = argparse.ArgumentParser(
        description='Hagent build tool - Unified interface for all build profiles',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # List all profiles
  %(prog)s --list

  # List APIs for a title substring
  %(prog)s --profile "Pipelined Dual Issue" --list-apis

  # Select by exact unique name (preferred)
  %(prog)s --name PipelinedDualIssueNoDbg --api compile

  # Select by title substring (legacy 'description' is now 'title')
  %(prog)s --profile "Single Cycle CPU" --api compile

  # Dry run
  %(prog)s --name GCD --api compile --dry-run
        """,
    )

    parser.add_argument('--config', help='Path to hagent.yaml')
    parser.add_argument('--list', action='store_true', help='List all profiles')

    # Selection:
    parser.add_argument('--name', '-N', help="Exact profile 'name' (unique, case-insensitive)")
    parser.add_argument('--profile', '-p', help="Substring match on profile 'description')")

    # Actions:
    parser.add_argument('--list-apis', action='store_true', help='List APIs for the selected/matched profiles')
    parser.add_argument('--api', '-a', help='API to execute (compile, lint, synthesize, etc.)')

    parser.add_argument('--dry-run', '-n', action='store_true', help='Show what would be executed without running')
    parser.add_argument('extra_args', nargs=argparse.REMAINDER, help='Extra arguments to pass to the command (after --)')

    args = parser.parse_args()

    if args.extra_args and args.extra_args[0] == '--':
        args.extra_args = args.extra_args[1:]

    try:
        builder = HagentBuilder(args.config)

        if args.list:
            builder.list_profiles()
            return 0

        # List APIs for selected profiles.
        if args.list_apis:
            if args.name:
                hits = builder._find_by_exact_name(args.name)
                if not hits:
                    # Exact error text required by user.
                    avail = ', '.join(p.get('name', '<unnamed>') for p in builder._get_all_profiles())
                    print(f"Error: No profile matched --name '{args.name}'. Available names: {avail}", file=sys.stderr)
                    return 2
                if len(hits) > 1:
                    print(
                        f"Error: --name '{args.name}' matched multiple profiles: " + ', '.join(p.get('name') for p in hits),
                        file=sys.stderr,
                    )
                    return 2
                builder.list_apis_for(hits)
                return 0
            elif args.profile:
                hits = builder._find_by_title_query(args.profile)
                if not hits:
                    print(f"Error: --profile '{args.profile}' did not match any profile titles.", file=sys.stderr)
                    builder.list_profiles()
                    return 2
                if len(hits) > 1:
                    print('Error: Multiple profiles matched --profile. Disambiguate with --name.\nMatches:', file=sys.stderr)
                    for p in hits:
                        print(f'  {p.get("name")} : {builder._profile_title(p) or "N/A"}', file=sys.stderr)
                    return 2
                builder.list_apis_for(hits)
                return 0
            else:
                print('Error: --list-apis requires either --name or --profile.', file=sys.stderr)
                return 2

        # Execute selected API
        if args.api:
            return builder.execute(args.name, args.profile, api_name=args.api, extra_args=args.extra_args, dry_run=args.dry_run)

        parser.print_help()
        return 0

    except FileNotFoundError as e:
        print(f'Error: {e}', file=sys.stderr)
        return 1
    except ValueError as e:
        # Descriptive selection/matching errors
        print(f'Error: {e}', file=sys.stderr)
        return 2
    except Exception as e:
        print(f'Error: {e}', file=sys.stderr)
        import traceback

        traceback.print_exc()
        return 1


if __name__ == '__main__':
    sys.exit(main())
