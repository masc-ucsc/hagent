#!/usr/bin/env python3
"""
netlist2modules: Partition a flat netlist into pipeline-stage submodules.

Usage:
  uv run python ./hagent/tool/cli_netlist2modules.py ./tmp/elab.v --output-dir tmp2
  uv run python ./hagent/tool/cli_netlist2modules.py ./tmp/elab.v --output-file out.v --top MyCore
"""

import contextlib
import os
import re
import sys
import tempfile
from collections import Counter, defaultdict
from dataclasses import dataclass

from pyosys import libyosys as ys


@dataclass
class Netlist2ModulesResult:
    top_name: str
    cell_type_counts: dict[str, int]
    partitions: dict[str, set[str]]
    mem_partitions: dict[str, str]
    flop_cell_names: set[str]
    written_outputs: list[tuple[str, str]]
    output_dir: str | None = None
    output_file: str | None = None

    def format_summary(self):
        lines = [f'Processing top module: {self.top_name}']
        lines.append(f'  Total cells: {sum(self.cell_type_counts.values())}')
        for cell_type, count in sorted(self.cell_type_counts.items(), key=lambda item: -item[1])[:10]:
            lines.append(f'    {cell_type}: {count}')

        lines.append(f'\nPartitions ({len(self.partitions)}):')
        for name, cells in sorted(self.partitions.items()):
            flop_count = sum(1 for cell in cells if cell in self.flop_cell_names)
            lines.append(f'  {name}: {len(cells)} cells ({flop_count} flops)')

        if self.mem_partitions:
            lines.append(f'\nMemory partitions ({len(self.mem_partitions)}):')
            for name, cell_name in sorted(self.mem_partitions.items()):
                lines.append(f'  {name}: {cell_name}')

        if self.output_dir:
            lines.append(f'\nWriting modules to {self.output_dir}/')
            for _, path in self.written_outputs:
                lines.append(f'  {path}')
            lines.append(f'\nDone: {len(self.written_outputs)} files written')
        elif self.output_file:
            lines.append(f'\nDone: written to {self.output_file}')

        return '\n'.join(lines)


class UnionFind:
    def __init__(self):
        self.parent = {}
        self.rank = {}

    def find(self, value):
        if value not in self.parent:
            self.parent[value] = value
            self.rank[value] = 0
        while self.parent[value] != value:
            self.parent[value] = self.parent[self.parent[value]]
            value = self.parent[value]
        return value

    def union(self, left, right):
        left_root, right_root = self.find(left), self.find(right)
        if left_root == right_root:
            return
        if self.rank[left_root] < self.rank[right_root]:
            left_root, right_root = right_root, left_root
        self.parent[right_root] = left_root
        if self.rank[left_root] == self.rank[right_root]:
            self.rank[left_root] += 1

    def groups(self):
        grouped = defaultdict(list)
        for value in self.parent:
            grouped[self.find(value)].append(value)
        return dict(grouped)


FLOP_PREFIXES = (
    '$dff',
    '$sdff',
    '$dffe',
    '$adff',
    '$sdffe',
    '$adffe',
    '$aldff',
    '$dlatch',
    '$adlatch',
    '$_DFF_',
    '$_SDFF_',
    '$_DFFE_',
    '$_ALDFF_',
    '$_DLATCH_',
)

MEM_PREFIXES = ('$mem', '$memrd', '$memwr', '$meminit')

ZERO_COST_TYPES = frozenset(
    (
        '$pos',
        '$slice',
        '$concat',
        '$not',
        '$buf',
        '$_NOT_',
        '$_BUF_',
    )
)


def is_flop(cell):
    cell_type = cell.type.str()
    return any(cell_type.startswith(prefix) for prefix in FLOP_PREFIXES)


def is_memory(cell):
    cell_type = cell.type.str()
    return any(cell_type.startswith(prefix) for prefix in MEM_PREFIXES)


def is_zero_cost(cell):
    return cell.type.str() in ZERO_COST_TYPES


def sanitize_name(name):
    name = name.lstrip('\\')
    name = re.sub(r'[^a-zA-Z0-9_]', '_', name)
    name = re.sub(r'_+', '_', name)
    name = name.strip('_')
    return name or 'unnamed'


def bit_key(bit):
    if bit.is_wire():
        return (bit.wire.name.str(), bit.offset)
    return ('__const__', bit.data)


def build_driver_map(module):
    drivers = {}
    for cell_id in module.cells_:
        cell = module.cells_[cell_id]
        cell_name = cell_id.str()
        for port_id in cell.connections_:
            if cell.output(port_id):
                for bit in cell.connections_[port_id]:
                    drivers[bit_key(bit)] = cell_name
    return drivers


def get_port_wires(module):
    pi_bits = set()
    po_bits = set()
    for wire_id in module.wires_:
        wire = module.wires_[wire_id]
        wire_name = wire_id.str()
        for offset in range(wire.width):
            if wire.port_input:
                pi_bits.add((wire_name, offset))
            if wire.port_output:
                po_bits.add((wire_name, offset))
    return pi_bits, po_bits


def get_flop_q_wire_name(cell):
    for port_id in cell.connections_:
        if port_id.str() == '\\Q' and cell.output(port_id):
            bits = list(cell.connections_[port_id])
            if bits and bits[0].is_wire():
                return bits[0].wire.name.str()
    return None


def trace_input_cone(seed_bits, driver_map, cells_by_name, stop_cell_names):
    combo_cells = set()
    visited = set()
    work = list(seed_bits)

    while work:
        signal = work.pop()
        if signal in visited:
            continue
        visited.add(signal)

        driver_name = driver_map.get(signal)
        if driver_name is None or driver_name in stop_cell_names or driver_name in combo_cells:
            continue

        cell = cells_by_name.get(driver_name)
        if cell is None:
            continue

        combo_cells.add(driver_name)
        for port_id in cell.connections_:
            if cell.input(port_id):
                for bit in cell.connections_[port_id]:
                    work.append(bit_key(bit))

    return combo_cells


def derive_stage_name(flop_q_names, stage_idx):
    prefixes = []
    for qname in flop_q_names:
        if qname is None:
            continue
        clean_name = qname.lstrip('\\')
        if '.' in clean_name:
            prefix = clean_name.rsplit('.', 1)[0]
        else:
            prefix = clean_name
        prefixes.append(prefix)

    if not prefixes:
        return f'stage_{stage_idx}'
    if len(prefixes) == 1:
        return sanitize_name(prefixes[0])

    common = os.path.commonprefix(prefixes).rstrip('._ ')
    if len(common) >= 2:
        return sanitize_name(common)

    most_common = Counter(prefixes).most_common(1)[0][0]
    return sanitize_name(most_common)


def partition_module(module):
    cells_by_name = {}
    flop_names = set()
    mem_names = set()
    combo_names = set()
    flop_q_names = {}

    for cell_id in module.cells_:
        cell = module.cells_[cell_id]
        cell_name = cell_id.str()
        cells_by_name[cell_name] = cell
        if is_memory(cell):
            mem_names.add(cell_name)
        elif is_flop(cell):
            flop_names.add(cell_name)
            flop_q_names[cell_name] = get_flop_q_wire_name(cell)
        else:
            combo_names.add(cell_name)

    boundary_cells = flop_names | mem_names
    driver_map = build_driver_map(module)
    _, po_bits = get_port_wires(module)

    flop_cones = {}
    cell_to_owners = defaultdict(set)
    for flop_name in flop_names:
        cell = cells_by_name[flop_name]
        d_bits = []
        for port_id in cell.connections_:
            port_name = port_id.str()
            if port_name in ('\\D', '\\AD') and cell.input(port_id):
                for bit in cell.connections_[port_id]:
                    d_bits.append(bit_key(bit))

        cone = trace_input_cone(d_bits, driver_map, cells_by_name, boundary_cells)
        flop_cones[flop_name] = cone
        for cone_cell in cone:
            cell_to_owners[cone_cell].add(flop_name)

    po_wire_groups = defaultdict(list)
    for wire_name, offset in po_bits:
        po_wire_groups[wire_name].append((wire_name, offset))

    po_group_cones = {}
    po_prefix = '__po__'
    for wire_name, bits in po_wire_groups.items():
        po_id = f'{po_prefix}{wire_name}'
        cone = trace_input_cone(bits, driver_map, cells_by_name, boundary_cells)
        if cone:
            po_group_cones[po_id] = cone
            for cone_cell in cone:
                cell_to_owners[cone_cell].add(po_id)

    union_find = UnionFind()
    for owner in list(flop_names) + list(po_group_cones):
        union_find.find(owner)

    for owners in cell_to_owners.values():
        owner_list = list(owners)
        for index in range(1, len(owner_list)):
            union_find.union(owner_list[0], owner_list[index])

    partitions = {}
    for stage_idx, (_, members) in enumerate(sorted(union_find.groups().items(), key=lambda item: item[0])):
        member_flops = [member for member in members if member in flop_names]
        member_pos = [member for member in members if member.startswith(po_prefix)]

        stage_cells = set(member_flops)
        for flop_name in member_flops:
            stage_cells |= flop_cones[flop_name]
        for po_id in member_pos:
            stage_cells |= po_group_cones[po_id]
        if not stage_cells:
            continue

        if member_flops:
            stage_name = derive_stage_name([flop_q_names.get(name) for name in member_flops], stage_idx)
        else:
            po_wires = [member.replace(po_prefix, '') for member in member_pos]
            stage_name = sanitize_name('out_' + '_'.join(wire.lstrip('\\').split('.')[0] for wire in po_wires[:2]))[:40]

        base_name = stage_name
        suffix = 1
        while stage_name in partitions:
            stage_name = f'{base_name}_{suffix}'
            suffix += 1

        partitions[stage_name] = stage_cells

    mem_partitions = {}
    for mem_name in mem_names:
        mem_partitions[f'mem_{sanitize_name(mem_name)}'[:40]] = mem_name

    assigned = set()
    for cells in partitions.values():
        assigned |= cells
    unassigned = combo_names - assigned
    misc_cells = {cell_name for cell_name in unassigned if not is_zero_cost(cells_by_name[cell_name])}
    if misc_cells:
        partitions['misc'] = misc_cells

    return partitions, mem_partitions


def apply_submod(design, module, partitions):
    for stage_name, cell_names in partitions.items():
        for cell_name in cell_names:
            cell_id = ys.IdString(cell_name)
            if cell_id in module.cells_:
                module.cells_[cell_id].set_string_attribute(ys.IdString('\\submod'), stage_name)
    ys.run_pass('submod', design)


def get_mem_v2_info(mem_cell):
    params = {}
    for parameter_id in mem_cell.parameters:
        name = parameter_id.str().lstrip('\\')
        value = mem_cell.parameters[parameter_id]
        try:
            params[name] = value.as_int()
        except Exception:
            params[name] = str(value)
    return params


def generate_mem_verilog_text(mod_name, mem_name, mem_cell):
    params = get_mem_v2_info(mem_cell)
    width = params.get('WIDTH', 8)
    size = params.get('SIZE', 1)
    abits = params.get('ABITS', 1)
    rd_ports = params.get('RD_PORTS', 1)
    wr_ports = params.get('WR_PORTS', 1)
    wr_clk_enable = params.get('WR_CLK_ENABLE', 1)

    lines = [f'// Memory wrapper for {mem_name}', f'module {mod_name} (']
    ports = []
    if wr_clk_enable:
        ports.append('  input wr_clk')
    for index in range(wr_ports):
        suffix = f'_{index}' if wr_ports > 1 else ''
        ports.append(f'  input [{abits - 1}:0] wr_addr{suffix}')
        ports.append(f'  input [{width - 1}:0] wr_data{suffix}')
        ports.append(f'  input [{width - 1}:0] wr_en{suffix}')
    for index in range(rd_ports):
        suffix = f'_{index}' if rd_ports > 1 else ''
        ports.append(f'  input [{abits - 1}:0] rd_addr{suffix}')
        ports.append(f'  output reg [{width - 1}:0] rd_data{suffix}')
    lines.append(',\n'.join(ports))
    lines.extend(
        [
            ');',
            '',
            f'  reg [{width - 1}:0] mem [0:{size - 1}];',
            '',
        ]
    )

    for index in range(rd_ports):
        suffix = f'_{index}' if rd_ports > 1 else ''
        lines.extend(
            [
                '  always @(*) begin',
                f'    rd_data{suffix} = mem[rd_addr{suffix}];',
                '  end',
                '',
            ]
        )

    for index in range(wr_ports):
        suffix = f'_{index}' if wr_ports > 1 else ''
        lines.extend(
            [
                '  always @(posedge wr_clk) begin',
                f"    if (wr_en{suffix} != {width}'d0)",
                f'      mem[wr_addr{suffix}] <= wr_data{suffix};',
                '  end',
                '',
            ]
        )

    lines.append('endmodule')
    return '\n'.join(lines) + '\n'


def extract_memories(design, top_module, mem_partitions, top_name, out_dir=None):
    if not mem_partitions:
        return []

    results = []
    for mem_mod_name, mem_cell_name in mem_partitions.items():
        cell_id = ys.IdString(mem_cell_name)
        if cell_id not in top_module.cells_:
            continue

        mem_cell = top_module.cells_[cell_id]
        full_mod_name = f'{top_name}_{mem_mod_name}'
        verilog_text = generate_mem_verilog_text(full_mod_name, mem_cell_name.lstrip('\\'), mem_cell)

        if out_dir is not None:
            os.makedirs(out_dir, exist_ok=True)
            output_path = os.path.join(out_dir, sanitize_name(full_mod_name) + '.v')
            with open(output_path, 'w') as handle:
                handle.write(verilog_text)
            results.append((full_mod_name, output_path))
        else:
            results.append((full_mod_name, verilog_text))

        orig_connections = {}
        for port_id in mem_cell.connections_:
            orig_connections[port_id.str()] = mem_cell.connections_[port_id]

        params = get_mem_v2_info(mem_cell)
        width = params.get('WIDTH', 8)
        abits = params.get('ABITS', 1)
        rd_ports = params.get('RD_PORTS', 1)
        wr_ports = params.get('WR_PORTS', 1)

        top_module.remove(mem_cell)

        bb_mod_name = ys.IdString(f'\\{full_mod_name}')
        bb_mod = design.addModule(bb_mod_name)
        bb_mod.set_bool_attribute(ys.IdString('\\blackbox'), True)

        port_idx = 1
        wire = bb_mod.addWire(ys.IdString('\\wr_clk'), 1)
        wire.port_input = True
        wire.port_id = port_idx
        port_idx += 1

        for index in range(wr_ports):
            suffix = f'_{index}' if wr_ports > 1 else ''
            for port_name, port_width in [('wr_addr', abits), ('wr_data', width), ('wr_en', width)]:
                wire = bb_mod.addWire(ys.IdString(f'\\{port_name}{suffix}'), port_width)
                wire.port_input = True
                wire.port_id = port_idx
                port_idx += 1

        for index in range(rd_ports):
            suffix = f'_{index}' if rd_ports > 1 else ''
            wire = bb_mod.addWire(ys.IdString(f'\\rd_addr{suffix}'), abits)
            wire.port_input = True
            wire.port_id = port_idx
            port_idx += 1
            wire = bb_mod.addWire(ys.IdString(f'\\rd_data{suffix}'), width)
            wire.port_output = True
            wire.port_id = port_idx
            port_idx += 1

        bb_mod.fixup_ports()

        inst = top_module.addCell(ys.IdString(f'\\{mem_mod_name}_inst'), bb_mod_name)
        if '\\WR_CLK' in orig_connections:
            inst.setPort(ys.IdString('\\wr_clk'), orig_connections['\\WR_CLK'])

        for index in range(wr_ports):
            suffix = f'_{index}' if wr_ports > 1 else ''
            if '\\WR_ADDR' in orig_connections:
                inst.setPort(ys.IdString(f'\\wr_addr{suffix}'), orig_connections['\\WR_ADDR'])
            if '\\WR_DATA' in orig_connections:
                inst.setPort(ys.IdString(f'\\wr_data{suffix}'), orig_connections['\\WR_DATA'])
            if '\\WR_EN' in orig_connections:
                inst.setPort(ys.IdString(f'\\wr_en{suffix}'), orig_connections['\\WR_EN'])

        for index in range(rd_ports):
            suffix = f'_{index}' if rd_ports > 1 else ''
            if '\\RD_ADDR' in orig_connections:
                inst.setPort(ys.IdString(f'\\rd_addr{suffix}'), orig_connections['\\RD_ADDR'])
            if '\\RD_DATA' in orig_connections:
                inst.setPort(ys.IdString(f'\\rd_data{suffix}'), orig_connections['\\RD_DATA'])

    return results


def write_modules_to_dir(design, out_dir):
    os.makedirs(out_dir, exist_ok=True)
    written = []
    for mod_id in list(design.modules_.keys()):
        mod = design.modules_[mod_id]
        if ys.IdString('\\blackbox') in mod.attributes:
            continue
        mod_name = mod_id.str().lstrip('\\')
        path = os.path.join(out_dir, sanitize_name(mod_name) + '.v')
        ys.run_pass(f'select {mod_id.str()}', design)
        ys.run_pass(f'write_verilog -sv -selected {path}', design)
        ys.run_pass('select -clear', design)
        written.append((mod_name, path))
    return written


def write_modules_to_file(design, out_file, mem_verilog_blocks):
    parts = [verilog_text for _, verilog_text in mem_verilog_blocks]
    for mod_id in list(design.modules_.keys()):
        mod = design.modules_[mod_id]
        if ys.IdString('\\blackbox') in mod.attributes:
            continue

        temp_fd, temp_path = tempfile.mkstemp(suffix='.v')
        os.close(temp_fd)
        ys.run_pass(f'select {mod_id.str()}', design)
        ys.run_pass(f'write_verilog -sv -selected {temp_path}', design)
        ys.run_pass('select -clear', design)
        with open(temp_path, 'r') as handle:
            parts.append(handle.read())
        os.unlink(temp_path)

    os.makedirs(os.path.dirname(os.path.abspath(out_file)), exist_ok=True)
    with open(out_file, 'w') as handle:
        handle.write('\n'.join(parts))
    return out_file


@contextlib.contextmanager
def suppress_stdout():
    sys.stdout.flush()
    devnull = os.open(os.devnull, os.O_WRONLY)
    old_stdout = os.dup(1)
    os.dup2(devnull, 1)
    os.close(devnull)
    try:
        yield
    finally:
        ys.log_flush()
        os.dup2(old_stdout, 1)
        os.close(old_stdout)


class Netlist2Modules:
    def __init__(self, input_path, top=None, verbose=False):
        self.input_path = input_path
        self.top = top
        self.verbose = verbose

    def run(self, output_dir=None, output_file=None):
        if bool(output_dir) == bool(output_file):
            raise ValueError('Exactly one of output_dir or output_file must be provided')

        design = ys.Design()
        self._load_design(design)
        top_module = self._find_top_module(design)
        top_name = top_module.name.str().lstrip('\\')
        cell_type_counts = self._count_cells(top_module)
        partitions, mem_partitions = partition_module(top_module)
        flop_cell_names = {cell_id.str() for cell_id in top_module.cells_ if is_flop(top_module.cells_[cell_id])}

        with self._quiet_context():
            apply_submod(design, top_module, partitions)

        if output_dir:
            mem_written = extract_memories(design, top_module, mem_partitions, top_name, output_dir)
            with self._quiet_context():
                written = write_modules_to_dir(design, output_dir)
            written_outputs = mem_written + written
        else:
            mem_blocks = extract_memories(design, top_module, mem_partitions, top_name, out_dir=None)
            with self._quiet_context():
                write_modules_to_file(design, output_file, mem_blocks)
            written_outputs = [(top_name, output_file)]

        return Netlist2ModulesResult(
            top_name=top_name,
            cell_type_counts=cell_type_counts,
            partitions=partitions,
            mem_partitions=mem_partitions,
            flop_cell_names=flop_cell_names,
            written_outputs=written_outputs,
            output_dir=output_dir,
            output_file=output_file,
        )

    def _load_design(self, design):
        ys.run_pass(f'read_verilog -sv {self.input_path}', design)
        with self._quiet_context():
            if self.top:
                ys.run_pass(f'hierarchy -top {self.top}', design)
                ys.run_pass('flatten', design)
            ys.run_pass('proc', design)
            ys.run_pass('opt -fast', design)
            ys.run_pass('memory -nomap', design)
            ys.run_pass('opt -fast', design)

    def _find_top_module(self, design):
        for mod_id in design.modules_:
            mod = design.modules_[mod_id]
            if self.top and mod_id.str() == f'\\{self.top}':
                return mod
            if ys.IdString('\\top') in mod.attributes:
                return mod
        return design.modules_[list(design.modules_.keys())[0]]

    def _count_cells(self, top_module):
        counts = defaultdict(int)
        for cell_id in top_module.cells_:
            counts[top_module.cells_[cell_id].type.str()] += 1
        return dict(counts)

    def _quiet_context(self):
        return suppress_stdout() if not self.verbose else contextlib.nullcontext()
