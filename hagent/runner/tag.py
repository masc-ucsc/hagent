"""Tag setup, snapshotting, and validation for the runner."""

import os
import shutil
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, Optional

import tomlkit

from . import config as cfg


class TagError(Exception):
    """Tag-related error."""


def _resolve_cache_dir(cache_dir: Optional[str] = None) -> str:
    """Get the cache directory from arg or environment."""
    if cache_dir is None:
        cache_dir = os.environ.get('HAGENT_CACHE_DIR')
        if not cache_dir:
            raise TagError('HAGENT_CACHE_DIR not set and --cache-dir not provided')
    return cache_dir


def _is_path(tag: str) -> bool:
    """True if tag looks like a filesystem path rather than a plain name."""
    return '/' in tag or tag == '.'


def get_tag_dir(tag: str, cache_dir: Optional[str] = None) -> str:
    """Resolve tag directory.

    If *tag* contains '/' or is '.', it is treated as a direct path.
    Otherwise it is looked up by name under <cache>/tags/<tag>/.
    """
    if _is_path(tag):
        return str(Path(tag).resolve())

    cache = _resolve_cache_dir(cache_dir)
    return str(Path(cache) / 'tags' / tag)


def validate_tag(tag_dir: str) -> dict:
    """Verify tag directory and config.toml exist.  Return parsed config."""
    if not os.path.isdir(tag_dir):
        raise TagError(f"tag directory does not exist: {tag_dir}")
    try:
        return cfg.load_tag_config(tag_dir)
    except FileNotFoundError:
        raise TagError(f"no config.toml in tag directory: {tag_dir}")


def resolve_input_dirs(inputs: Dict[str, str], cache_dir: Optional[str] = None) -> Dict[str, str]:
    """Resolve input tag names/paths to their directory paths.

    Each value can be a tag name or a path (contains '/').
    Validates that each input tag exists with a config.toml.
    Returns {input_name: tag_dir_path}.
    """
    if cache_dir is None:
        cache_dir = os.environ.get('HAGENT_CACHE_DIR', '')

    result = {}
    for name, tag_ref in inputs.items():
        tag_dir = get_tag_dir(tag_ref, cache_dir)
        if not os.path.isdir(tag_dir):
            raise TagError(f"input tag '{tag_ref}' (for input '{name}') does not exist at {tag_dir}")
        cfg_path = os.path.join(tag_dir, 'config.toml')
        if not os.path.exists(cfg_path):
            raise TagError(f"input tag '{tag_ref}' has no config.toml")
        result[name] = tag_dir
    return result


def tag_matches(existing_config: dict, profile_name: str, inputs: Optional[Dict[str, str]] = None) -> bool:
    """Check if existing tag config matches the requested setup."""
    meta = existing_config.get('meta', {})
    if meta.get('profile_name', '') != profile_name:
        return False

    existing_inputs = existing_config.get('inputs', {})
    requested_inputs = inputs or {}
    return dict(existing_inputs) == dict(requested_inputs)


def setup_tag(
    runner_toml_path: str,
    tag: str,
    profile_name: str,
    cache_dir: Optional[str] = None,
    inputs: Optional[Dict[str, str]] = None,
    overrides: Optional[Dict[str, str]] = None,
    force: bool = False,
    reuse: bool = False,
) -> str:
    """Create a tag directory with a snapshotted config.toml.

    If *tag* is a path (contains '/'), the tag is created there directly.
    If *tag* is a plain name, the tag is created at <cache>/tags/<tag>/.
    A plain name must not contain path characters.

    Returns the path to the created config.toml.
    """
    if _is_path(tag):
        tag_dir = str(Path(tag).resolve())
    else:
        if '.' in tag:
            raise TagError(f"tag name '{tag}' must not contain '.'; use a path like ./{tag} instead")
        cache = _resolve_cache_dir(cache_dir)
        tag_dir = str(Path(cache) / 'tags' / tag)

    toml_path = os.path.join(tag_dir, 'config.toml')

    # Handle existing tag
    if os.path.exists(toml_path):
        if reuse:
            try:
                existing = cfg.load_tag_config(tag_dir)
            except FileNotFoundError:
                raise TagError(f"tag '{tag}' exists but has no config.toml; use --force")
            if tag_matches(existing, profile_name, inputs):
                return toml_path
            else:
                raise TagError(
                    f"tag '{tag}' exists with different config; "
                    f"fix the request or use --force to overwrite"
                )
        elif not force:
            raise TagError(f"tag '{tag}' already exists at {tag_dir}; use --force to overwrite")
        else:
            # --force: remove old config and logs, keep other files
            os.remove(toml_path)
            logs_dir = os.path.join(tag_dir, 'logs')
            if os.path.isdir(logs_dir):
                shutil.rmtree(logs_dir)

    # Load runner.toml and merge default + profile
    runner_config = cfg.load_runner_toml(runner_toml_path)
    merged = cfg.merge_default_and_profile(runner_config, profile_name)

    # Apply persistent overrides
    if overrides:
        merged = cfg.apply_overrides(merged, overrides)

    # Build the tag config document
    doc = tomlkit.document()

    # [meta]
    meta = tomlkit.table()
    meta['schema_version'] = 1
    meta['created'] = datetime.now(timezone.utc).isoformat()
    meta['source_toml'] = str(Path(runner_toml_path).resolve())
    meta['profile_name'] = profile_name
    doc['meta'] = meta

    # [tag]
    tag_tbl = tomlkit.table()
    tag_tbl['dir'] = tag_dir
    doc['tag'] = tag_tbl

    # [inputs]
    if inputs:
        inputs_tbl = tomlkit.table()
        for k, v in inputs.items():
            inputs_tbl[k] = v
        doc['inputs'] = inputs_tbl

    # Copy merged sections into doc
    for key, value in merged.items():
        if key in ('meta', 'tag', 'inputs'):
            continue
        doc[key] = value

    # Create directories and write
    Path(tag_dir).mkdir(parents=True, exist_ok=True)
    Path(tag_dir, 'logs').mkdir(exist_ok=True)

    with open(toml_path, 'w') as f:
        f.write(tomlkit.dumps(doc))

    return toml_path
