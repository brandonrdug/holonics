"""The cells whose moves carry a value deposited when the second operand's units arrive (cell pb)
to the cell that codes the result's units (U, cell pu-1): cells pb+1 .. pu-1, for the true sums
whose U cell is in char/block{c}.usum128. Writes char/block{c}.bupath (sorted cells)."""
import importlib.util, sys
spec = importlib.util.spec_from_file_location("tm", "../../tools/tower_modes.py"); tm = importlib.util.module_from_spec(spec); spec.loader.exec_module(tm)
tot = 0
for c in range(8):
    text = open(f"modes/block{c}.txt", "rb").read()
    ucells = set(int(x) for x in open(f"char/block{c}.usum128").read().split())
    out, start = set(), 0
    for line in text.split(b"\n"):
        m = tm.tower_circuit.EQ.match(line)
        if m:
            a, op, b, cc = m.groups()
            pu = start + len(line) - 1
            if op == b"+" and pu - 1 in ucells:
                pb = start + len(a) + len(b)
                out.update(range(pb + 1, pu))
        start += len(line) + 1
    open(f"char/block{c}.bupath", "w").write("\n".join(map(str, sorted(out))) + "\n")
    tot += len(out)
    print(c, len(ucells), len(out))
print("cells", tot)
