#!/usr/bin/env -S python3 -I
"""The worth of the past by the octave of a place's age past a cut, state by state: a host tabulation of the lead's cut tables.

Each `cut_table_NAME.txt` (the lead's `read-cut` on 100 held rows, a cut at 256, 19,200 places past it) prints her code by the
octave of a place's age past the cut under each setting. `cut:256:0` lets nothing cross the cut, so at a place of age `a` its
code less the law's is what everything older than `a` places is worth to her there: her reach, parted by octave. `cut:256:64`
lets every site before the cut be heard one by one and empties every store (the cut record of November 25, its table of
settings), so its code less the law's is what the stores alone were carrying. The table is each difference a state, with the same
rows' mean beside it, and the first in the far past's own unit (nats over a span of 115 places, a sentence's length), since a
place's nats weigh a slow level by its rate.

Usage:  reach_by_age.py DIRECTORY NAME [NAME ...]
"""
import re
import sys


def read(path):
    rows, mean = {}, {}
    for line in open(path, encoding="utf-8"):
        if line.startswith("CUT_BY_AGE"):
            parts = line.split()
            rows[parts[1].split("=")[1]] = [(p.split(":")[0], float(p.split(":")[1])) for p in parts[2:]]
        elif line.startswith("CUT_MEAN group=all"):
            mean[re.search(r"setting=(\S+)", line).group(1)] = float(re.search(r"nats=(\S+)", line).group(1))
    return rows, mean


def main():
    directory, names = sys.argv[1], sys.argv[2:]
    tables = {n: read(f"{directory}/cut_table_{n}.txt") for n in names}
    bands = [b for b, _ in tables[names[0]][0]["law"]]
    print("REACH_BY_AGE nats a place; columns are a place's age past the cut")
    print(f"{'state':7} {'reading':22} " + " ".join(f"{b:>8}" for b in bands) + "     mean")
    for n in names:
        rows, mean = tables[n]
        print(f"{n:7} {'the law':22} " + " ".join(f"{v:8.3f}" for _, v in rows["law"]) + f"   {mean['law']:.4f}")
    for setting, label in (("cut:256:0", "nothing crossing"), ("cut:256:64", "sites heard, no store")):
        for n in names:
            rows, mean = tables[n]
            worth = [c - l for (_, c), (_, l) in zip(rows[setting], rows["law"])]
            print(f"{n:7} {label:22} " + " ".join(f"{w:8.3f}" for w in worth) + f"   {mean[setting] - mean['law']:.4f}")
    print("REACH_OWN_UNIT nothing crossing, less the law, over a span of 115 places (nats a span)")
    for n in names:
        rows, _ = tables[n]
        worth = [c - l for (_, c), (_, l) in zip(rows["cut:256:0"], rows["law"])]
        print(f"{n:7} {'':22} " + " ".join(f"{115 * w:8.1f}" for w in worth))


if __name__ == "__main__":
    main()
