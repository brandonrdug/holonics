#!/usr/bin/env python3
"""twin27 against carry13e, line by line on the learning lines (timings and the retired persistent path's zero fields dropped).
Args: CARRY_LOG TWIN_LOG. A reading only."""
import re, sys
DROP = r' (ms|sweep_ms|read_ms|elapsed_ms|[a-z_]*_ms)=\d+| (write_energy_milli|moved|proposed|accept_milli)=-?\d+'
def lines(f):
    out = {}
    for l in open(f):
        k = l.split(' ')[0]
        if k not in {'FIELD_FRESH_SWEEP', 'FIELD_FRESH_RETAIN', 'FIELD_STEP', 'FIELD_PERSISTENT', 'FIELD_LENGTHS'}: continue
        s = re.sub(DROP, '', l.strip()); n = re.search(r' n=(\d+)', s); sw = re.search(r' sweep=(\d+)', s)
        out.setdefault((k, n.group(1) if n else '', sw.group(1) if sw else ''), []).append(s)
    return out
A, B = lines(sys.argv[1]), lines(sys.argv[2])
common = [k for k in B if k in A]; bad = [k for k in common if A[k] != B[k]]
secs = sorted(set(int(k[1]) for k in common if k[1]))
print(f"twin keys {len(B)}, in both {len(common)}, differing {len(bad)}; sections compared {secs[0] if secs else '-'}-{secs[-1] if secs else '-'}")
for k in sorted(bad)[:3]: print(k, '\n carry:', A[k][0][:260], '\n twin: ', B[k][0][:260])
