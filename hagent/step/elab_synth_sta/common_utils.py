# See LICENSE for details

import os
from pathlib import Path


def find_synth_script() -> Path:
    """Find the synth.py script in the hagent repository.

    Args:
        step_instance: A Step instance (used for error reporting).

    Returns:
        Path to scripts/synth.py.
    """
    # Go up from hagent/step/ to hagent root, then to scripts/
    hagent_root = Path(__file__).resolve().parent.parent.parent
    synth_script = hagent_root / 'scripts' / 'synth.py'

    if synth_script.exists():
        return synth_script

    # Fallback: try HAGENT_ROOT_DIR
    repo_dir = os.environ.get('HAGENT_ROOT_DIR')
    if repo_dir:
        synth_script = Path(repo_dir) / 'scripts' / 'synth.py'
        if synth_script.exists():
            return synth_script

    raise RuntimeError('synth.py script not found')
