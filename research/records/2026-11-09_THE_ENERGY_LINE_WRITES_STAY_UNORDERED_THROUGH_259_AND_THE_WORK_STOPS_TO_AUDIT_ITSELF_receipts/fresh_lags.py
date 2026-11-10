#!/usr/bin/env python3
"""Lag bands of each section's fresh writes (theory, November 9 11:28): from a contrast run's FRESH_WRITES.txt, the writes alone
(never the truths), 1-5, 6-20 and 1-20 summed MI over within-write shuffles, jackknifed over the section's writes. Numbers only."""
import re, sys, math
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from write_mi import prepare
import mi_lags_core as core
txt = open(sys.argv[1], encoding="utf-8", errors="replace").read()
parts = re.split(r"^(=== section \d+ (?:write|truth) \d+ ===)\n", txt, flags=re.M)
by = {}
for i in range(1, len(parts), 2):
    m = re.match(r"=== section (\d+) write (\d+) ===", parts[i])
    if m:
        by.setdefault(int(m.group(1)), {})[int(m.group(2))] = parts[i + 1].rstrip("\n")
for n in sorted(by):
    ws = [by[n][k] for k in sorted(by[n])]
    if len(ws) < 2:
        continue
    sh = prepare(ws, 20261109 + n)
    full = core.band_stats(ws, sh, list(range(len(ws))))
    loo = [core.band_stats(ws, sh, [j for j in range(len(ws)) if j != k]) for k in range(len(ws))]
    out = []
    for name in ("1-5", "6-20", "1-20"):
        vals = [l[name] for l in loo]; m = sum(vals) / len(vals)
        se = math.sqrt((len(vals) - 1) / len(vals) * sum((v - m) ** 2 for v in vals))
        out.append(f"{name} {full[name]:+.4f} ({se:.4f})")
    print(f"section {n}: {len(ws)} writes, {sum(map(len, ws))} letters; " + "; ".join(out))
