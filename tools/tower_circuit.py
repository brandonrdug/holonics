"""Read a tower's circuit reading (the read-tower-circuit command) over a text of equation lines,
partitioned by the role of the class each cell's face predicts: the first operand's digits (`a`), the
operation (`op`), the second operand's digits (`b`), `=` (`eq`), the result's leading digit when it
has more than one (`c_lead`), its other digits by place counted from the right (`c_p0` the units),
and the line's end (`stop`). The result's digits and end are also split by the result's length
against its operands (a sum or difference expands, holds or contracts; a product is full or short)
and, for sums and differences, by whether the operands' units carry or borrow. Only whole, true
equation lines are partitioned; other cells are left out.

A row's cells are summed and divided by its count, and each level's energies by that level's mean
stored energy over every cell of the reading: `E` the stored energy before the class arrives,
`lost` what the moves dissipate (`before − carried`), `push` the power the arriving class brings
(`after − carried`), `dE` the change (`after − before`), `cancel` the share of cells where the push
lowers the energy the moves carried, and `r` the read's mean `‖r‖_rms` on its unit. `bits` is the
mean code of the predicted class. An exterior reading of the machine's own exact quantities, written
as ratios for the report.

usage: python3 -I tower_circuit.py TEXT CIRCUIT [CIRCUIT ...]
"""
import collections
import os
import re
import sys

EQ = re.compile(rb"^(\d+)([+\-*])(\d+)=(\d+)$")
ORDER = ["a", "op", "b", "eq", "c_lead", "c_p2", "c_p1", "c_p0", "stop"]


def roles(text):
    """Each position's role and its line's (operation, shape, carry), or None."""
    role, info, start = [None] * len(text), [None] * len(text), 0
    for line in text.split(b"\n"):
        m = EQ.match(line)
        if m:
            a, op, b, c = m.groups()
            op = op.decode()
            t = int(a) + int(b) if op == "+" else int(a) - int(b) if op == "-" else int(a) * int(b)
            if t == int(c):
                width = max(len(a), len(b))
                if op == "*":
                    shape = "full" if len(c) == len(a) + len(b) else "short"
                else:
                    shape = "expands" if len(c) > width else "contracts" if len(c) < width else "holds"
                a0, b0 = int(a[-1:]), int(b[-1:])
                carry = {"+": "carry" if a0 + b0 >= 10 else "nocarry", "-": "borrow" if a0 < b0 else "noborrow"}.get(op, "-")
                result = len(a) + 2 + len(b)
                for k in range(len(line) + 1):
                    p = start + k
                    if p >= len(text):
                        break
                    if k < len(a):
                        r = "a"
                    elif k == len(a):
                        r = "op"
                    elif k < len(a) + 1 + len(b):
                        r = "b"
                    elif k == len(a) + 1 + len(b):
                        r = "eq"
                    elif k < len(line):
                        place = len(c) - 1 - (k - result)
                        r = "c_lead" if k == result and place > 0 else f"c_p{place}"
                    else:
                        r = "stop"
                    role[p], info[p] = r, (op, shape, carry)
        start += len(line) + 1
    return role, info


def load(path):
    cells = []
    for line in open(path):
        if line.startswith("CIRCUIT "):
            parts = line.split()
            levels = [tuple(int(v) for v in x.split("=")[1].split(",")) for x in parts[4:]]
            cells.append((int(parts[1]), int(parts[3]), levels))
    return cells


def main():
    text = open(sys.argv[1], "rb").read()
    role, info = roles(text)
    for path in sys.argv[2:]:
        cells = load(path)
        levels = len(cells[0][2])
        mean = [sum(c[2][l][0] for c in cells) / len(cells) for l in range(levels)]
        print(f"== {os.path.basename(path)} cells={len(cells)} bits_a_byte={sum(c[1] for c in cells) / len(cells) / 2**20:.3f} "
              + " ".join(f"L{l}_mean_energy={mean[l] / 2**48:.0f}" for l in range(levels)))
        groups = collections.defaultdict(list)
        for i, code, lv in cells:
            r = role[i + 1] if i + 1 < len(role) else None
            if r is None:
                continue
            op, shape, carry = info[i + 1]
            groups[(op, r)].append((code, lv))
            if r.startswith("c_") or r == "stop":
                groups[(op, shape, r)].append((code, lv))
                if carry != "-" and r in ("c_lead", "c_p1", "c_p0", "stop"):
                    groups[(op, carry, r)].append((code, lv))

        def row(key, xs):
            n = len(xs)
            out = [f"{'/'.join(key):24s} n={n:4d} bits={sum(x[0] for x in xs) / n / 2**20:5.2f}"]
            for l in range(levels):
                e = [x[1][l] for x in xs]
                out.append(
                    f"L{l}: E={sum(v[0] for v in e) / n / mean[l]:5.2f} lost={sum(v[0] - v[1] for v in e) / n / mean[l]:6.3f} "
                    f"push={sum(v[2] - v[1] for v in e) / n / mean[l]:+6.3f} dE={sum(v[2] - v[0] for v in e) / n / mean[l]:+6.3f} "
                    f"cancel={sum(1 for v in e if v[2] < v[1]) / n:4.2f} r={sum(v[3] for v in e) / n / 2**16:7.1f}"
                )
            return "  ".join(out)

        for op in ["+", "-", "*"]:
            for r in ORDER:
                if (op, r) in groups:
                    print(row((op, r), groups[(op, r)]))
            for key in sorted(k for k in groups if len(k) == 3 and k[0] == op):
                print(row(key, groups[key]))


if __name__ == "__main__":
    main()
