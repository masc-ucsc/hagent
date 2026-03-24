"""Config loading, merging, and placeholder resolution for the runner."""

import copy
import os
import re
from pathlib import Path
from typing import Dict, List, Optional

import tomlkit


def load_runner_toml(path: str) -> dict:
    """Parse a repo-level runner.toml file.

    Raises FileNotFoundError or ValueError on problems.
    """
    with open(path, 'r') as f:
        data = tomlkit.parse(f.read())
    if not isinstance(data, dict):
        raise ValueError(f'{path}: runner.toml must be a mapping')
    return data


def load_tag_config(tag_dir: str) -> dict:
    """Parse a tag's config.toml.

    Raises FileNotFoundError if config.toml is missing.
    """
    cfg_path = os.path.join(tag_dir, 'config.toml')
    if not os.path.exists(cfg_path):
        raise FileNotFoundError(f'no config.toml in {tag_dir}')
    with open(cfg_path, 'r') as f:
        return tomlkit.parse(f.read())


def merge_default_and_profile(runner_config: dict, profile_name: str) -> dict:
    """Deep-merge [default] with [profile_name] from a runner.toml.

    Profile values win on conflict.  Returns a plain dict (not tomlkit).
    Raises ValueError if profile_name is not found or is a reserved key.
    """
    RESERVED = {'meta', 'default'}
    if profile_name in RESERVED:
        raise ValueError(f"'{profile_name}' is a reserved section name")

    if profile_name not in runner_config:
        available = [k for k in runner_config if k not in RESERVED]
        raise ValueError(f"no profile '{profile_name}'; available: {', '.join(available)}")

    defaults = _to_plain(runner_config.get('default', {}))
    profile = _to_plain(runner_config[profile_name])

    merged = _deep_merge(defaults, profile)
    return merged


def _to_plain(obj):
    """Convert tomlkit objects to plain Python dicts/lists."""
    if isinstance(obj, dict):
        return {k: _to_plain(v) for k, v in obj.items()}
    if isinstance(obj, list):
        return [_to_plain(i) for i in obj]
    return obj


def _deep_merge(base: dict, override: dict) -> dict:
    """Recursively merge override into base.  Override wins on leaf conflicts."""
    result = copy.deepcopy(base)
    for k, v in override.items():
        if k in result and isinstance(result[k], dict) and isinstance(v, dict):
            result[k] = _deep_merge(result[k], v)
        else:
            result[k] = copy.deepcopy(v)
    return result


def apply_overrides(config: dict, overrides: Dict[str, str]) -> dict:
    """Apply --set KEY=VALUE overrides to a config dict.

    Supports dotted keys like ``api.compile.cwd``.  Returns the modified config.
    """
    config = copy.deepcopy(config)
    for key, value in overrides.items():
        parts = key.split('.')
        target = config
        for part in parts[:-1]:
            if part not in target or not isinstance(target[part], dict):
                target[part] = {}
            target = target[part]
        target[parts[-1]] = value
    return config


def get_api_config(config: dict, api_name: str) -> Optional[dict]:
    """Extract the [api.<name>] section from a tag config."""
    apis = config.get('api', {})
    if not isinstance(apis, dict):
        return None
    return _to_plain(apis.get(api_name))


def list_api_names(config: dict) -> List[str]:
    """Return available API names from a tag config."""
    apis = config.get('api', {})
    if not isinstance(apis, dict):
        return []
    return list(apis.keys())


def _lookup(context: dict, key: str):
    """Walk a dotted key path through nested dicts.  Returns None on miss."""
    parts = key.split('.')
    obj = context
    for part in parts:
        if isinstance(obj, dict) and part in obj:
            obj = obj[part]
        else:
            return None
    return obj


def resolve_placeholders(text: str, context: dict) -> str:
    """Expand runner placeholders like {tag}, {tag_dir}, {input.NAME.dir}.

    Unknown placeholders pass through unchanged.  Uses regex-based
    replacement to handle dotted keys properly.
    """

    def _replace(match):
        key = match.group(1)
        val = _lookup(context, key)
        if val is None:
            return match.group(0)  # pass through
        return str(val)

    return re.sub(r'\{([a-zA-Z_][a-zA-Z0-9_.]*)\}', _replace, text)


def resolve_env_vars(text: str, env: Optional[Dict[str, str]] = None) -> str:
    """Expand $VAR references using the given env dict (or os.environ)."""
    if env is None:
        env = os.environ
    return os.path.expandvars(text)


def build_context(
    tag_name: str,
    tag_dir: str,
    input_dirs: Optional[Dict[str, str]] = None,
    api_config: Optional[dict] = None,
) -> dict:
    """Build the placeholder context dict for resolve_placeholders().

    Also includes option default values as top-level keys (e.g. {top}).
    """
    ctx: dict = {
        'tag': tag_name,
        'tag_dir': tag_dir,
    }

    # Named inputs
    if input_dirs:
        inputs_ctx = {}
        for name, path in input_dirs.items():
            inputs_ctx[name] = {'dir': path}
        ctx['input'] = inputs_ctx

    # Option defaults from api config
    if api_config:
        for opt in api_config.get('options', []):
            opt_name = opt.get('name', '')
            if opt_name and opt_name not in ctx:
                default = opt.get('default', '')
                ctx[opt_name] = default

    return ctx


def build_env(config: dict, tag_dir: str) -> Dict[str, str]:
    """Build extra environment vars from tag config.

    Returns only the config-specific vars and HAGENT overrides — not
    the full host environment.  Builder's FileSystem layer handles merging
    these into either the host env (local) or exporting them into Docker.
    """
    env: Dict[str, str] = {}

    # Set HAGENT_BUILD_DIR to tag dir (tag.dir in config, or tag_dir arg)
    cfg_tag_dir = config.get('tag', {}).get('dir', '')
    env['HAGENT_BUILD_DIR'] = cfg_tag_dir if cfg_tag_dir else tag_dir

    # Layer config [environment] vars
    cfg_env = config.get('environment', {})
    if isinstance(cfg_env, dict):
        for k, v in cfg_env.items():
            env[k] = v

    return env


def get_docker_image(config: dict) -> Optional[str]:
    """Get the Docker image from tag config.

    The ``docker`` key is a flat string (not a nested table):
      - ``docker = "img:tag"`` → use that image
      - ``docker = ""``        → force local execution
      - key absent             → use ``HAGENT_DOCKER`` from environment

    Returns:
      - image string if docker is set to a non-empty value
      - "" (empty string) if explicitly set to "" (means: force local)
      - None if docker key is absent (means: use environment default)
    """
    if 'docker' not in config:
        return None
    val = config['docker']
    if not isinstance(val, str):
        return None
    return val


def resolve_options(command: str, api_config: dict, overrides: Optional[Dict[str, str]] = None) -> str:
    """Resolve option placeholders in a command string.

    Options have name, format, and default fields.  --set overrides can
    replace defaults.  The resolved format string replaces {name} in the command.
    """
    for opt in api_config.get('options', []):
        name = opt.get('name', '')
        if not name:
            continue

        fmt = opt.get('format', '')
        default_val = opt.get('default', '')

        # Check if overridden via --set
        if overrides and name in overrides:
            value = overrides[name]
        else:
            value = default_val

        # Build the resolved string
        if value and fmt:
            resolved = fmt.replace('{value}', value)
        elif value and not fmt:
            resolved = value
        else:
            resolved = ''

        # Replace {name} placeholder in command
        command = command.replace('{' + name + '}', resolved)

    return command
