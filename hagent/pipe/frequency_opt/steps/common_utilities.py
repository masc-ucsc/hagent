import importlib.util
import os

from pathlib import Path
from typing import Optional


def _find_synth_script() -> Path:
    """Find the synth.py script in the hagent repository."""
    this_file = Path(__file__).resolve()
    hagent_root = this_file.parent.parent.parent.parent.parent
    synth_script = hagent_root / 'scripts' / 'synth.py'

    if synth_script.exists():
        return synth_script

    repo_dir = os.environ.get('HAGENT_ROOT_DIR')
    if repo_dir:
        synth_script = Path(repo_dir) / 'scripts' / 'synth.py'
        if synth_script.exists():
            return synth_script

    raise RuntimeError('synth.py script not found')


def get_clock_signal(netlist_path: Path) -> Optional[str]:
    """Get clock signal from netlist using synth.py's find_clock_signal."""
    synth_script = _find_synth_script()
    spec = importlib.util.spec_from_file_location('synth', synth_script)
    synth_module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(synth_module)
    return synth_module.find_clock_signal(str(netlist_path))
