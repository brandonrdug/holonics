#!/usr/bin/env -S python3 -I
"""polar_map.py RECEIPT: a block's polarization, read from a `tools/state_travel.py weighed` output of four states (a host ruler,
never machinery; arithmetic on printed lines only).

For each block (block, lane, contacts): heat, the mean over the receipt's laps of its WEIGHED_LAP heat_micro (the standing spread's
cost at the rates the laps ran at: 2^-rate s_i / 4 summed over the block's entries); fall2, its WEIGHED_LAG fall_micro two laps on
(the first-order fall of the code that a lap's travel makes along the travel two laps before it: the part of the travel that keeps
one sign); polarization fall2 / heat. Units: millionths of a bit a site of the lap, as the ruler prints them. Classes: polar 0.5 or
more, middle 0.1 to 0.5, thermal under 0.1 with fall2 at or above zero, reversing fall2 under zero. Prints one line a block, in
falling polarization, then one line a class with its share of the field's heat and fall2. Numbers only.
"""
import re
import sys
from collections import defaultdict


def load(path):
    heat, entries, lag = defaultdict(list), {}, {}
    for line in open(path):
        kv = dict(re.findall(r"(\w+)=([^\s]+)", line))
        if "block" not in kv:
            continue
        key = (kv["block"], kv["lane"], kv["contacts"])
        if line.startswith("TRAVEL_WEIGHED_LAP "):
            heat[key].append(float(kv["heat_micro"]))
            entries[key] = int(kv["entries"])
        elif line.startswith("TRAVEL_WEIGHED_LAG ") and kv.get("lag") == "2":
            lag[key] = (float(kv["fall_micro"]), float(kv["cos_w"]))
    return heat, entries, lag


def kind(polarization, fall):
    if fall < 0:
        return "reversing"
    if polarization >= 0.5:
        return "polar"
    return "middle" if polarization >= 0.1 else "thermal"


def main(path):
    heat, entries, lag = load(path)
    rows = []
    for key, (fall, cos_w) in lag.items():
        h = sum(heat[key]) / len(heat[key])
        rows.append((fall / h if h else 0.0, key, entries[key], h, fall, cos_w))
    rows.sort(key=lambda r: -r[0])
    classes = defaultdict(lambda: [0, 0, 0.0, 0.0])
    for pol, (block, lane, contacts), n, h, fall, cos_w in rows:
        k = kind(pol, fall)
        c = classes[k]
        c[0] += 1; c[1] += n; c[2] += h; c[3] += fall
        print(f"POLAR_BLOCK class={k} block={block} lane={lane} contacts={contacts} entries={n} heat_micro={h:.1f} fall2_micro={fall:+.1f} polarization={pol:+.3f} cos_w={cos_w:+.3f}")
    th = sum(c[2] for c in classes.values())
    tf = sum(c[3] for c in classes.values())
    for k in ("polar", "middle", "thermal", "reversing"):
        c = classes[k]
        print(f"POLAR_CLASS class={k} blocks={c[0]} entries={c[1]} heat_micro={c[2]:.1f} heat_share={c[2] / th:.3f} fall2_micro={c[3]:+.1f} fall2_share={c[3] / tf:+.3f}")
    print(f"POLAR_TOTAL blocks={len(rows)} entries={sum(r[2] for r in rows)} heat_micro={th:.1f} fall2_micro={tf:+.1f}")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit("usage: polar_map.py RECEIPT")
    main(sys.argv[1])
