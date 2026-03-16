from pathlib import Path

from hagent.tool.netlist2modules import Netlist2Modules


REPO_ROOT = Path(__file__).resolve().parents[3]


def test_netlist2modules_writes_partitioned_modules_for_sample_stage1(tmp_path):
    input_path = REPO_ROOT / 'tmp' / 'sample_stage1.v'
    output_dir = tmp_path / 'sample_stage1_out'

    result = Netlist2Modules(str(input_path)).run(output_dir=str(output_dir))

    written_names = {Path(path).name for _, path in result.written_outputs}
    assert result.top_name == 'sample_stage1'
    assert len(result.partitions) >= 2
    assert any(name.startswith('sample_stage1_') for name in written_names)
    assert 'sample_stage1.v' in written_names


def test_netlist2modules_extracts_memory_wrapper_for_simple_rf1(tmp_path):
    input_path = REPO_ROOT / 'tmp' / 'simple_rf1.v'
    output_dir = tmp_path / 'simple_rf1_out'

    result = Netlist2Modules(str(input_path)).run(output_dir=str(output_dir))

    written_names = {Path(path).name for _, path in result.written_outputs}
    assert result.top_name == 'simple_rf1'
    assert result.mem_partitions
    assert any('mem' in name for name in written_names)
    assert 'simple_rf1.v' in written_names
