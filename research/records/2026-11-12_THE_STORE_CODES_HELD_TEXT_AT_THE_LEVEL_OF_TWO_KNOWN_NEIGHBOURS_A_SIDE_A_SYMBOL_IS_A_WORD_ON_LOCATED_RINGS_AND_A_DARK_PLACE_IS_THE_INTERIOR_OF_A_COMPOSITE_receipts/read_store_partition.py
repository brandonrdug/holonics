#!/usr/bin/env python3 -I
"""read_store_partition.py NAME=LOG ...: P53 item 4, a ruler: read-store's STORE_READ_PARTITION lines (codes summed on 2^-20 bits) as a count and
a mean code in nats a cell, by state and slice (a reading; the mean is a decimal). Numbers only."""
import math
import sys

for arg in sys.argv[1:]:
    name, path = arg.split("=", 1)
    for line in open(path):
        if not line.startswith("STORE_READ_PARTITION "):
            continue
        words = line.split()
        slc = words[1].split("=")[1]
        group = None
        for w in words[2:]:
            if "(count/code)" in w:
                group = w.split("(")[0]
                continue
            cell, v = w.split("=")
            count, code = (int(x) for x in v.split("/"))
            nats = code / (1 << 20) * math.log(2) / count if count else float("nan")
            print(f"PARTITION state={name} slice={slc} group={group} cell={cell} places={count} mean_code_nats={nats:.4f}")
