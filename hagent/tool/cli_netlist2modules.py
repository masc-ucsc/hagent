#!/usr/bin/env python3
"""
netlist2modules: Partition a flat netlist into pipeline-stage submodules.

Algorithm:
  1. Load Verilog into Yosys, run proc + opt -fast + memory -nomap to get clean RTLIL
  2. Separate memory cells ($mem_v2) -- they stay in the top module since
     Yosys submod cannot extract modules containing memories
  3. For each flop, trace the input cone of combinational logic back to
     flop Q outputs or primary inputs
  4. Union-find: merge flops that share any combinational cell
  5. Primary outputs also seed their own cones (like virtual registers)
  6. Tag non-memory cells with 'submod' attribute, run Yosys submod pass
  7. For each $mem_v2 left in the top module, create a wrapper submodule
     containing only the memory (no complex logic)
  8. Write each resulting module to separate Verilog files in --output-dir,
     or to a single combined file with --output-file

Usage:
  uv run python ./hagent/tool/netlist2modules.py ./tmp/elab.v --output-dir tmp2
  uv run python ./hagent/tool/netlist2modules.py ./tmp/elab.v --output-file out.v --top MyCore
"""

import argparse
import contextlib
import os
import re
import sys
from collections import Counter, defaultdict

from pyosys import libyosys as ys


# ---------------------------------------------------------------------------
# Union-Find
# ---------------------------------------------------------------------------
class UnionFind:
    def __init__(self):
        self.parent = {}
        self.rank = {}

    def find(self, x):
        if x not in self.parent:
            self.parent[x] = x
            self.rank[x] = 0
        while self.parent[x] != x:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def union(self, a, b):
        ra, rb = self.find(a), self.find(b)
        if ra == rb:
            return
        if self.rank[ra] < self.rank[rb]:
            ra, rb = rb, ra
        self.parent[rb] = ra
        if self.rank[ra] == self.rank[rb]:
            self.rank[ra] += 1

    def groups(self):
        grps = defaultdict(list)
        for x in self.parent:
            grps[self.find(x)].append(x)
        return dict(grps)


# ---------------------------------------------------------------------------
# Cell classification helpers
# ---------------------------------------------------------------------------
FLOP_PREFIXES = (
    "$dff", "$sdff", "$dffe", "$adff", "$sdffe", "$adffe",
    "$aldff", "$dlatch", "$adlatch",
    "$_DFF_", "$_SDFF_", "$_DFFE_", "$_ALDFF_", "$_DLATCH_",
)

MEM_PREFIXES = ("$mem", "$memrd", "$memwr", "$meminit")

ZERO_COST_TYPES = frozenset((
    "$pos", "$slice", "$concat", "$not", "$buf",
    "$_NOT_", "$_BUF_",
))


def is_flop(cell):
    typ = cell.type.str()
    return any(typ.startswith(p) for p in FLOP_PREFIXES)


def is_memory(cell):
    typ = cell.type.str()
    return any(typ.startswith(p) for p in MEM_PREFIXES)


def is_zero_cost(cell):
    return cell.type.str() in ZERO_COST_TYPES


def sanitize_name(name):
    """Make a string safe for Verilog identifiers and filenames."""
    name = name.lstrip("\\")
    name = re.sub(r'[^a-zA-Z0-9_]', '_', name)
    name = re.sub(r'_+', '_', name)
    name = name.strip('_')
    return name or "unnamed"


# ---------------------------------------------------------------------------
# Signal tracing
# ---------------------------------------------------------------------------
def bit_key(bit):
    """Stable hashable key for a SigBit."""
    if bit.is_wire():
        return (bit.wire.name.str(), bit.offset)
    return ("__const__", bit.data)


def build_driver_map(module):
    """Map bit_key -> cell_name_str for every cell output bit."""
    drivers = {}
    for cell_id in module.cells_:
        cell = module.cells_[cell_id]
        cname = cell_id.str()
        for port_id in cell.connections_:
            if cell.output(port_id):
                for bit in cell.connections_[port_id]:
                    drivers[bit_key(bit)] = cname
    return drivers


def get_port_wires(module):
    """Return sets of bit_keys that are primary inputs/outputs."""
    pi_bits = set()
    po_bits = set()
    for wire_id in module.wires_:
        w = module.wires_[wire_id]
        wname = wire_id.str()
        for offset in range(w.width):
            if w.port_input:
                pi_bits.add((wname, offset))
            if w.port_output:
                po_bits.add((wname, offset))
    return pi_bits, po_bits


def get_flop_q_wire_name(cell):
    """Get the Q output wire name for a flop cell (meaningful hierarchy name)."""
    for port_id in cell.connections_:
        if port_id.str() == "\\Q" and cell.output(port_id):
            sig = cell.connections_[port_id]
            bits = list(sig)
            if bits and bits[0].is_wire():
                return bits[0].wire.name.str()
    return None


def trace_input_cone(seed_bits, driver_map, cells_by_name, stop_cell_names):
    """
    BFS backward from seed_bits through combinational logic.
    Stop at primary inputs, flop Q outputs, or memory outputs.
    Returns set of combo cell name strings in the cone.
    """
    combo_cells = set()
    visited = set()
    work = list(seed_bits)

    while work:
        bk = work.pop()
        if bk in visited:
            continue
        visited.add(bk)

        driver_name = driver_map.get(bk)
        if driver_name is None:
            continue

        if driver_name in stop_cell_names:
            continue

        if driver_name in combo_cells:
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


# ---------------------------------------------------------------------------
# Naming: derive module name from flop Q wire names
# ---------------------------------------------------------------------------
def derive_stage_name(flop_q_names, stage_idx):
    """Derive a readable module name from flop Q wire names."""
    prefixes = []
    for qname in flop_q_names:
        if qname is None:
            continue
        clean = qname.lstrip("\\")
        if "." in clean:
            prefix = clean.rsplit(".", 1)[0]
        else:
            prefix = clean
        prefixes.append(prefix)

    if not prefixes:
        return f"stage_{stage_idx}"

    if len(prefixes) == 1:
        return sanitize_name(prefixes[0])

    common = os.path.commonprefix(prefixes)
    common = common.rstrip("._ ")

    if len(common) >= 2:
        return sanitize_name(common)

    counts = Counter(prefixes)
    most_common = counts.most_common(1)[0][0]
    return sanitize_name(most_common)


# ---------------------------------------------------------------------------
# Main partitioning logic
# ---------------------------------------------------------------------------
def partition_module(module):
    """
    Partition cells in a module into stages.
    Returns:
      partitions: dict stage_name -> set of cell name strings (non-memory)
      mem_partitions: dict mem_name -> cell name string (memory cells)
    """
    cells_by_name = {}
    flop_names = set()
    mem_names = set()
    combo_names = set()
    flop_q_names = {}

    for cell_id in module.cells_:
        cell = module.cells_[cell_id]
        cname = cell_id.str()
        cells_by_name[cname] = cell
        if is_memory(cell):
            mem_names.add(cname)
        elif is_flop(cell):
            flop_names.add(cname)
            flop_q_names[cname] = get_flop_q_wire_name(cell)
        else:
            combo_names.add(cname)

    boundary_cells = flop_names | mem_names
    driver_map = build_driver_map(module)
    _, po_bits = get_port_wires(module)

    # --- Trace input cone for each flop ---
    flop_cones = {}
    cell_to_owners = defaultdict(set)

    for fname in flop_names:
        cell = cells_by_name[fname]
        d_bits = []
        for port_id in cell.connections_:
            pname = port_id.str()
            if pname in ("\\D", "\\AD") and cell.input(port_id):
                for bit in cell.connections_[port_id]:
                    d_bits.append(bit_key(bit))

        cone = trace_input_cone(d_bits, driver_map, cells_by_name, boundary_cells)
        flop_cones[fname] = cone
        for c in cone:
            cell_to_owners[c].add(fname)

    # --- Trace input cone for primary outputs ---
    po_wire_groups = defaultdict(list)
    for wname, offset in po_bits:
        po_wire_groups[wname].append((wname, offset))

    po_group_cones = {}
    po_prefix = "__po__"
    for wname, bits in po_wire_groups.items():
        po_id = f"{po_prefix}{wname}"
        cone = trace_input_cone(bits, driver_map, cells_by_name, boundary_cells)
        if cone:
            po_group_cones[po_id] = cone
            for c in cone:
                cell_to_owners[c].add(po_id)

    # --- Union-find: merge flops/po-groups sharing combo cells ---
    uf = UnionFind()
    all_owners = list(flop_names) + list(po_group_cones.keys())
    for name in all_owners:
        uf.find(name)

    for combo_cell, owners in cell_to_owners.items():
        owner_list = list(owners)
        for i in range(1, len(owner_list)):
            uf.union(owner_list[0], owner_list[i])

    # --- Build partitions (non-memory only) ---
    groups = uf.groups()
    partitions = {}

    for stage_idx, (rep, members) in enumerate(sorted(groups.items(), key=lambda x: x[0])):
        member_flops = [m for m in members if m in flop_names]
        member_pos = [m for m in members if m.startswith(po_prefix)]

        stage_cells = set()
        stage_cells.update(member_flops)
        for fname in member_flops:
            stage_cells |= flop_cones[fname]
        for po_id in member_pos:
            stage_cells |= po_group_cones[po_id]

        if not stage_cells:
            continue

        if member_flops:
            q_names = [flop_q_names.get(f) for f in member_flops]
            stage_name = derive_stage_name(q_names, stage_idx)
        else:
            po_wires = [m.replace(po_prefix, "") for m in member_pos]
            stage_name = sanitize_name("out_" + "_".join(
                w.lstrip("\\").split(".")[0] for w in po_wires[:2]
            ))[:40]

        base_name = stage_name
        counter = 1
        while stage_name in partitions:
            stage_name = f"{base_name}_{counter}"
            counter += 1

        partitions[stage_name] = stage_cells

    # --- Memory partitions (tracked separately) ---
    mem_partitions = {}
    for mname in mem_names:
        clean = sanitize_name(mname)
        mem_stage = f"mem_{clean}"[:40]
        mem_partitions[mem_stage] = mname

    # --- Unassigned combo cells ---
    assigned = set()
    for cells in partitions.values():
        assigned |= cells
    unassigned = combo_names - assigned
    misc_cells = {c for c in unassigned if not is_zero_cost(cells_by_name[c])}
    if misc_cells:
        partitions["misc"] = misc_cells

    return partitions, mem_partitions


# ---------------------------------------------------------------------------
# Apply partitions via Yosys submod (non-memory cells only)
# ---------------------------------------------------------------------------
def apply_submod(design, module, partitions):
    """Tag non-memory cells with submod attribute and run the submod pass."""
    for stage_name, cell_names in partitions.items():
        for cname in cell_names:
            cell_id = ys.IdString(cname)
            if cell_id in module.cells_:
                cell = module.cells_[cell_id]
                cell.set_string_attribute(ys.IdString("\\submod"), stage_name)

    ys.run_pass("submod", design)


# ---------------------------------------------------------------------------
# Extract memories into their own submodules
# ---------------------------------------------------------------------------
def get_mem_v2_info(mem_cell):
    """Extract memory parameters from a $mem_v2 cell."""
    params = {}
    for pid in mem_cell.parameters:
        pname = pid.str().lstrip("\\")
        val = mem_cell.parameters[pid]
        # Try to get integer value
        try:
            params[pname] = val.as_int()
        except Exception:
            params[pname] = str(val)
    return params


def generate_mem_verilog_text(mod_name, mem_name, mem_cell):
    """
    Generate Verilog text for a memory wrapper module for a $mem_v2 cell.
    Returns the Verilog source as a string.
    """
    params = get_mem_v2_info(mem_cell)
    width = params.get("WIDTH", 8)
    size = params.get("SIZE", 1)
    abits = params.get("ABITS", 1)
    rd_ports = params.get("RD_PORTS", 1)
    wr_ports = params.get("WR_PORTS", 1)
    wr_clk_enable = params.get("WR_CLK_ENABLE", 1)

    lines = []
    lines.append(f"// Memory wrapper for {mem_name}")
    lines.append(f"module {mod_name} (")

    ports = []
    if wr_clk_enable:
        ports.append("  input wr_clk")
    for i in range(wr_ports):
        sfx = f"_{i}" if wr_ports > 1 else ""
        ports.append(f"  input [{abits-1}:0] wr_addr{sfx}")
        ports.append(f"  input [{width-1}:0] wr_data{sfx}")
        ports.append(f"  input [{width-1}:0] wr_en{sfx}")
    for i in range(rd_ports):
        sfx = f"_{i}" if rd_ports > 1 else ""
        ports.append(f"  input [{abits-1}:0] rd_addr{sfx}")
        ports.append(f"  output reg [{width-1}:0] rd_data{sfx}")

    lines.append(",\n".join(ports))
    lines.append(");")
    lines.append("")
    lines.append(f"  reg [{width-1}:0] mem [0:{size-1}];")
    lines.append("")

    for i in range(rd_ports):
        sfx = f"_{i}" if rd_ports > 1 else ""
        lines.append(f"  always @(*) begin")
        lines.append(f"    rd_data{sfx} = mem[rd_addr{sfx}];")
        lines.append(f"  end")
        lines.append("")

    for i in range(wr_ports):
        sfx = f"_{i}" if wr_ports > 1 else ""
        lines.append(f"  always @(posedge wr_clk) begin")
        lines.append(f"    if (wr_en{sfx} != {width}'d0)")
        lines.append(f"      mem[wr_addr{sfx}] <= wr_data{sfx};")
        lines.append(f"  end")
        lines.append("")

    lines.append("endmodule")
    return "\n".join(lines) + "\n"


def extract_memories(design, top_module, mem_partitions, top_name, out_dir=None):
    """
    For each $mem_v2 cell in the top module:
    1. Generate a Verilog wrapper module (to file if out_dir given, else as text)
    2. Replace the $mem_v2 cell with a blackbox instance in the top module

    Returns list of (mod_name, filepath_or_text) tuples.
    When out_dir is set, writes files and returns (name, filepath).
    When out_dir is None, returns (name, verilog_text) for later combining.
    """
    if not mem_partitions:
        return []

    results = []

    for mem_mod_name, mem_cell_name in mem_partitions.items():
        cell_id = ys.IdString(mem_cell_name)
        if cell_id not in top_module.cells_:
            continue

        mem_cell = top_module.cells_[cell_id]
        full_mod_name = f"{top_name}_{mem_mod_name}"

        vtext = generate_mem_verilog_text(
            full_mod_name,
            mem_cell_name.lstrip("\\"),
            mem_cell,
        )

        if out_dir is not None:
            filepath = os.path.join(out_dir, sanitize_name(full_mod_name) + ".v")
            os.makedirs(out_dir, exist_ok=True)
            with open(filepath, "w") as f:
                f.write(vtext)
            results.append((full_mod_name, filepath))
        else:
            results.append((full_mod_name, vtext))

        # Save original connections before removing
        orig_connections = {}
        for port_id in mem_cell.connections_:
            orig_connections[port_id.str()] = mem_cell.connections_[port_id]

        params = get_mem_v2_info(mem_cell)
        width = params.get("WIDTH", 8)
        abits = params.get("ABITS", 1)
        rd_ports = params.get("RD_PORTS", 1)
        wr_ports = params.get("WR_PORTS", 1)

        # Remove the $mem_v2 cell
        top_module.remove(mem_cell)

        # Create a blackbox module definition so Yosys knows the ports
        bb_mod_name = ys.IdString(f"\\{full_mod_name}")
        bb_mod = design.addModule(bb_mod_name)
        bb_mod.set_bool_attribute(ys.IdString("\\blackbox"), True)

        port_idx = 1
        # wr_clk
        w = bb_mod.addWire(ys.IdString("\\wr_clk"), 1)
        w.port_input = True
        w.port_id = port_idx
        port_idx += 1

        for i in range(wr_ports):
            sfx = f"_{i}" if wr_ports > 1 else ""
            for pname, pwidth in [("wr_addr", abits), ("wr_data", width), ("wr_en", width)]:
                w = bb_mod.addWire(ys.IdString(f"\\{pname}{sfx}"), pwidth)
                w.port_input = True
                w.port_id = port_idx
                port_idx += 1

        for i in range(rd_ports):
            sfx = f"_{i}" if rd_ports > 1 else ""
            w = bb_mod.addWire(ys.IdString(f"\\rd_addr{sfx}"), abits)
            w.port_input = True
            w.port_id = port_idx
            port_idx += 1
            w = bb_mod.addWire(ys.IdString(f"\\rd_data{sfx}"), width)
            w.port_output = True
            w.port_id = port_idx
            port_idx += 1

        bb_mod.fixup_ports()

        # Add instance of the wrapper in the top module
        inst_name = ys.IdString(f"\\{mem_mod_name}_inst")
        inst = top_module.addCell(inst_name, bb_mod_name)

        # Map $mem_v2 ports to wrapper ports
        if "\\WR_CLK" in orig_connections:
            inst.setPort(ys.IdString("\\wr_clk"), orig_connections["\\WR_CLK"])

        for i in range(wr_ports):
            sfx = f"_{i}" if wr_ports > 1 else ""
            if "\\WR_ADDR" in orig_connections:
                inst.setPort(ys.IdString(f"\\wr_addr{sfx}"), orig_connections["\\WR_ADDR"])
            if "\\WR_DATA" in orig_connections:
                inst.setPort(ys.IdString(f"\\wr_data{sfx}"), orig_connections["\\WR_DATA"])
            if "\\WR_EN" in orig_connections:
                inst.setPort(ys.IdString(f"\\wr_en{sfx}"), orig_connections["\\WR_EN"])

        for i in range(rd_ports):
            sfx = f"_{i}" if rd_ports > 1 else ""
            if "\\RD_ADDR" in orig_connections:
                inst.setPort(ys.IdString(f"\\rd_addr{sfx}"), orig_connections["\\RD_ADDR"])
            if "\\RD_DATA" in orig_connections:
                inst.setPort(ys.IdString(f"\\rd_data{sfx}"), orig_connections["\\RD_DATA"])

    return results


# ---------------------------------------------------------------------------
# Write modules
# ---------------------------------------------------------------------------
def write_modules_to_dir(design, out_dir):
    """Write each module in the design to a separate Verilog file."""
    os.makedirs(out_dir, exist_ok=True)
    written = []

    mod_ids = list(design.modules_.keys())

    for mod_id in mod_ids:
        mod = design.modules_[mod_id]
        # Skip blackbox modules (memory wrappers are written separately)
        bb_attr = ys.IdString("\\blackbox")
        if bb_attr in mod.attributes:
            continue

        mod_name = mod_id.str().lstrip("\\")
        filename = sanitize_name(mod_name) + ".v"
        filepath = os.path.join(out_dir, filename)
        ys.run_pass(f"select {mod_id.str()}", design)
        ys.run_pass(f"write_verilog -selected {filepath}", design)
        ys.run_pass("select -clear", design)
        written.append((mod_name, filepath))

    return written


def write_modules_to_file(design, out_file, mem_verilog_blocks):
    """Write all modules to a single Verilog file.

    mem_verilog_blocks: list of (mod_name, verilog_text) for memory wrappers
                        that were generated as text (not via Yosys).
    """
    # Write non-blackbox modules via Yosys to a temp file, then combine
    import tempfile

    parts = []

    # First, add memory wrapper modules (generated as text)
    for mod_name, vtext in mem_verilog_blocks:
        parts.append(vtext)

    # Then write Yosys modules to temp files and collect
    mod_ids = list(design.modules_.keys())
    for mod_id in mod_ids:
        mod = design.modules_[mod_id]
        bb_attr = ys.IdString("\\blackbox")
        if bb_attr in mod.attributes:
            continue

        tmp_fd, tmp_path = tempfile.mkstemp(suffix=".v")
        os.close(tmp_fd)
        ys.run_pass(f"select {mod_id.str()}", design)
        ys.run_pass(f"write_verilog -selected {tmp_path}", design)
        ys.run_pass("select -clear", design)
        with open(tmp_path, "r") as f:
            parts.append(f.read())
        os.unlink(tmp_path)

    os.makedirs(os.path.dirname(os.path.abspath(out_file)), exist_ok=True)
    with open(out_file, "w") as f:
        f.write("\n".join(parts))

    return out_file


@contextlib.contextmanager
def suppress_stdout():
    """Redirect fd 1 to /dev/null to suppress yosys C-level log output."""
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


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------
def main():
    parser = argparse.ArgumentParser(
        description="Partition a flat netlist into pipeline-stage submodules.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""\
examples:
  # Partition an elaborated netlist, one file per module
  uv run python ./hagent/tool/netlist2modules.py ./tmp/elab.v --output-dir out

  # Partition with hierarchy + flatten, specifying the top module
  uv run python ./hagent/tool/netlist2modules.py design.sv --output-dir out --top MyCore

  # Write all modules to a single Verilog file
  uv run python ./hagent/tool/netlist2modules.py ./tmp/elab.v --output-file combined.v

  # Show yosys internal log output for debugging
  uv run python ./hagent/tool/netlist2modules.py design.v --output-dir partitions -v
""",
    )
    parser.add_argument("input", help="Input Verilog/SystemVerilog netlist file")
    output_group = parser.add_mutually_exclusive_group(required=True)
    output_group.add_argument("--output-dir", help="Output directory (one file per module)")
    output_group.add_argument("--output-file", help="Output file (all modules in one file)")
    parser.add_argument("--top", default=None,
                        help="Top module name. If set, runs hierarchy -top and flatten before processing")
    parser.add_argument("-v", "--verbose", action="store_true", help="Show yosys log output")
    args = parser.parse_args()

    if not os.path.isfile(args.input):
        print(f"Error: input file not found: {args.input}", file=sys.stderr)
        sys.exit(1)

    # --- Load design ---
    design = ys.Design()

    def quiet_ctx():
        return suppress_stdout() if not args.verbose else contextlib.nullcontext()

    # read_verilog is never suppressed: Yosys hard-exits (_exit) on parse
    # errors, bypassing atexit/finally handlers, so if stdout were redirected
    # the error message would be lost silently.
    read_cmd = f"read_verilog -sv {args.input}"
    ys.run_pass(read_cmd, design)

    # These passes are safe to suppress — they only fail on internal bugs
    with quiet_ctx():
        if args.top:
            ys.run_pass(f"hierarchy -top {args.top}", design)
            ys.run_pass("flatten", design)
        ys.run_pass("proc", design)
        ys.run_pass("opt -fast", design)
        # Consolidate $memrd/$memwr into $mem_v2 (keeps memory abstraction)
        ys.run_pass("memory -nomap", design)
        ys.run_pass("opt -fast", design)

    # --- Find top module ---
    top_module = None
    for mod_id in design.modules_:
        mod = design.modules_[mod_id]
        if args.top and mod_id.str() == f"\\{args.top}":
            top_module = mod
            break
        top_attr = ys.IdString("\\top")
        if top_attr in mod.attributes:
            top_module = mod
            break

    if top_module is None:
        mod_id = list(design.modules_.keys())[0]
        top_module = design.modules_[mod_id]

    top_name = top_module.name.str().lstrip("\\")
    print(f"Processing top module: {top_name}")

    # --- Count cells ---
    types = defaultdict(int)
    for cell_id in top_module.cells_:
        types[top_module.cells_[cell_id].type.str()] += 1
    print(f"  Total cells: {sum(types.values())}")
    for t, cnt in sorted(types.items(), key=lambda x: -x[1])[:10]:
        print(f"    {t}: {cnt}")

    # --- Partition ---
    partitions, mem_partitions = partition_module(top_module)

    # Precompute flop set for summary
    flop_cell_names = {cid.str() for cid in top_module.cells_ if is_flop(top_module.cells_[cid])}

    print(f"\nPartitions ({len(partitions)}):")
    for name, cells in sorted(partitions.items()):
        nflops = sum(1 for c in cells if c in flop_cell_names)
        print(f"  {name}: {len(cells)} cells ({nflops} flops)")

    if mem_partitions:
        print(f"\nMemory partitions ({len(mem_partitions)}):")
        for name, cell_name in sorted(mem_partitions.items()):
            print(f"  {name}: {cell_name}")

    # --- Apply submod for non-memory partitions ---
    with quiet_ctx():
        apply_submod(design, top_module, partitions)

    # --- Output ---
    if args.output_dir:
        # One file per module
        mem_written = extract_memories(design, top_module, mem_partitions, top_name, args.output_dir)

        with quiet_ctx():
            written = write_modules_to_dir(design, args.output_dir)

        all_written = mem_written + written
        print(f"\nWriting modules to {args.output_dir}/")
        for mod_name, filepath in all_written:
            print(f"  {filepath}")
        print(f"\nDone: {len(all_written)} files written")

    else:
        # Single combined file
        mem_results = extract_memories(design, top_module, mem_partitions, top_name, out_dir=None)
        mem_blocks = [(name, vtext) for name, vtext in mem_results]

        with quiet_ctx():
            write_modules_to_file(design, args.output_file, mem_blocks)

        print(f"\nDone: written to {args.output_file}")


if __name__ == "__main__":
    main()
