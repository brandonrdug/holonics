#!/usr/bin/env python3
"""The scan test's reads (the unified-theory reading of November 6, 21:14), fixed before the walks.

Usage: scan_reads.py HELD128.txt NAME=SAMPLE_DIR ... (keyedA, keyedB, place, reversed and truth120 by name)

Per walk: a place's mean standing code S at pass 40 and over passes 31-40 (PASSES.tsv), the drive D at pass 40, and at
pass 40's writes the answers that parse as Python and the fences closed (code_reading.py). The keyed walks' gap is the
spread of the keyed walk at two keys. A walk reads apart from another when, in some read, their difference passes the
keyed gap by 0.15 bits a place in S, by 5 parses or by 4 closed fences. A scan is judged against the nearer keyed walk
[agent-inferred: the conservative reading of "beyond the two keyed walks' gap"], and the mean of the two is shown beside.
Judgement:
- keyedA (run bits 0) apart from truth120 (run bits 1, same key): runs move the walk, refine reads move to run bits 0.
- place or reversed apart from keyed: the curl moves the walk's law; with no slow mode, the structural face is owed.
- neither: the curl's effect on the release is below these reads; H2 (far structure) is the subject.
A reading only.
"""
import csv, collections, re, subprocess, sys, os

B = 1 << 20
HERE = os.path.dirname(os.path.abspath(__file__))
held = sys.argv[1]
walks = dict(a.split("=", 1) for a in sys.argv[2:])


def reads(d):
    rows = list(csv.DictReader(open(f"{d}/PASSES.tsv"), delimiter="\t"))
    by = collections.defaultdict(lambda: [0, 0, 0])
    for r in rows:
        b = by[int(r["pass"])]
        b[0] += int(r["redrawn"])
        b[1] += int(r["standing"])
        b[2] += int(r["entropy"])
    s = {p: v[1] / B / v[0] for p, v in by.items() if v[0]}
    dd = {p: (v[1] - v[2]) / B / v[0] for p, v in by.items() if v[0]}
    last = max(s)
    tail = [s[p] for p in range(31, 41) if p in s]
    text = subprocess.run([sys.executable, "-I", f"{HERE}/code_reading.py", held, f"{d}/SAMPLE.tsv"], capture_output=True, text=True).stdout.splitlines()
    line = text[1] if len(text) > 1 else ""
    m = re.search(r"fence opened (\d+), closed (\d+); parses as Python (\d+)", line)
    opened, closed, parses = (int(x) for x in m.groups()) if m else (-1, -1, -1)
    return {"last": last, "S40": s[last], "S31_40": sum(tail) / len(tail), "D40": dd[last], "parses": parses, "closed": closed, "opened": opened}


got = {n: reads(d) for n, d in walks.items()}
print("walk\tpass\tS40\tS31-40\tD40\tparses\tfences opened/closed")
for n, r in got.items():
    print(f"{n}\t{r['last']}\t{r['S40']:.3f}\t{r['S31_40']:.3f}\t{r['D40']:+.3f}\t{r['parses']}\t{r['opened']}/{r['closed']}")
A, Bk = got["keyedA"], got["keyedB"]
gap = {k: abs(A[k] - Bk[k]) for k in ("S40", "S31_40", "parses", "closed")}
margin = {"S40": 0.15, "S31_40": 0.15, "parses": 5, "closed": 4}
print("keyed gap: " + ", ".join(f"{k} {v:.3f}" if k.startswith("S") else f"{k} {v}" for k, v in gap.items()))


def apart(x, ys, label):
    out = []
    for k in gap:
        near = min(abs(x[k] - y[k]) for y in ys)
        mean = abs(x[k] - sum(y[k] for y in ys) / len(ys))
        beyond = near - gap[k]
        out.append((k, near, mean, beyond, beyond > margin[k]))
    flag = any(o[4] for o in out)
    print(f"{label}: " + "; ".join(f"{k} near {n:.3f} mean {m:.3f} past gap {b:+.3f}{' APART' if a else ''}" for k, n, m, b, a in out) + f" -> {'apart' if flag else 'inside'}")
    return flag


runs = apart(A, [got["truth120"]], "keyedA (run 0) vs truth120 (run 1)") if "truth120" in got else None
scans = {n: apart(got[n], [A, Bk], f"{n} vs keyed") for n in ("place", "reversed") if n in got}
print("JUDGE runs:", "runs move the walk; refine reads move to run bits 0" if runs else "runs inside the keyed gap")
if any(scans.values()):
    print("JUDGE scans: the curl moves the walk's law (" + ", ".join(n for n, f in scans.items() if f) + " apart); with no slow mode the structural face is owed")
else:
    print("JUDGE scans: neither scan apart; the curl's effect on the release is below these reads; H2 (far structure) is the subject")
