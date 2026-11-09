#!/usr/bin/env python3
"""The reach of the twin's support flips (theory, November 9 09:34 and 09:42): every changed far membership (receiver i at t-1..t+1,
source j) of the truth letter's lock rows between two saves, classed (c) the width law's tree split differently on i's probe path
or j's key path, else (a) i's probe words changed trit or band side on the modes its path reads (the base modes and its path's
split modes), else (b) j's key words moved; for (a) and (b) the moved word's wrapped |delta arg(re + i im)| on its changed modes,
against the receiver's own band half-width (1/2 arcsin eps, eps = 2^-eps_bits). A reading only.
Args: CLASSES_A WORDS_DIR_A CLASSES_B WORDS_DIR_B ENUMERATED LAP"""
import csv, math, sys, statistics
from collections import defaultdict

ca, wa, cb, wb, en, lap = sys.argv[1:7]
truth = {}
for r in csv.DictReader(open(en), delimiter="\t"):
    if r["lap"] == lap:
        truth[(r["problem"], r["place"])] = int(r["truth"])

def far_sets(path):
    out = {}
    for r in csv.DictReader(open(path), delimiter="\t"):
        k = (r["problem"], r["place"])
        if k in truth and int(r["letter"]) == truth[k]:
            f = r["far"]
            out[(k, int(r["site_offset"]), r["head"])] = set() if f == "-" else set(int(x) for x in f.split(","))
    return out

def tree(d):
    split = {}
    for r in csv.DictReader(open(f"{d}/TREE.tsv"), delimiter="\t"):
        split[(r["problem"], r["place"], r["head"], r["node"])] = r["split_mode"]
    paths, receivers = {}, defaultdict(dict)
    for r in csv.DictReader(open(f"{d}/PATHS.tsv"), delimiter="\t"):
        key = (r["problem"], r["place"], r["head"])
        nodes = r["path"].split(",")
        seq = tuple(split.get(key + (n,), "?") for n in nodes)
        paths[(key, int(r["site"]), r["kind"])] = (seq, r["eps_bits"])
        if r["kind"] == "probe":
            receivers[(r["problem"], r["place"])][int(r["site"])] = 1
    return paths, receivers

def words(d):
    w = {}
    for r in csv.DictReader(open(f"{d}/WORDS.tsv"), delimiter="\t"):
        w[((r["problem"], r["place"]), int(r["site_offset"]), r["head"], int(r["mode"]), r["kind"])] = (int(r["re"]), int(r["im"]), r["trit"], r["inside"], int(r["eps_bits"]), r["base"])
    return w

FA, FB = far_sets(ca), far_sets(cb)
PA = PB = {}
WA, WB = words(wa), words(wb)

def centre(k):
    return 0

changed = []
for key in FA:
    if key not in FB:
        continue
    k, s, h = key
    t = centre(k)
    if t is None:
        continue
    for off in FA[key] ^ FB[key]:
        changed.append((k, s, h, s, off))

def site0(d, W):
    """Each held place's absolute site in its region: the KEYS row whose head-0 key words at modes 0-3 equal WORDS' at offset 0."""
    want = {}
    for (k, off, h, m, kind), v in W.items():
        if off == 0 and h == "0" and kind == "key" and m < 4:
            want.setdefault(k, {})[m] = (v[0], v[1])
    cand = defaultdict(dict)
    for r in csv.DictReader(open(f"{d}/KEYS.tsv"), delimiter="\t"):
        if r["head"] != "0" or int(r["mode"]) >= 4:
            continue
        k = (r["problem"], r["place"])
        if k in want and want[k].get(int(r["mode"])) == (int(r["re"]), int(r["im"])):
            cand[k].setdefault(int(r["site"]), set()).add(int(r["mode"]))
    out = {}
    for k, sites in cand.items():
        full = [s for s, ms in sites.items() if len(ms) == 4]
        if len(full) == 1:
            out[k] = full[0]
    return out

def keys(d):
    out = {}
    for r in csv.DictReader(open(f"{d}/KEYS.tsv"), delimiter="\t"):
        k = (r["problem"], r["place"])
        if k not in SITE0:
            continue
        tag = (k, r["head"], int(r["site"]) - SITE0[k])
        if tag[0] in SITE0 and tag in need:
            out[tag + (int(r["mode"]),)] = (int(r["re"]), int(r["im"]), r["trit"])
    return out

SITE0 = site0(wa, WA)
print("places located", len(SITE0), "of", len(truth))
need = set((k, h, j) for k, s, h, i, j in changed if k in SITE0)
changed = [c for c in changed if c[0] in SITE0]
KA = keys(wa)
SITE0B = site0(wb, WB)
assert all(SITE0B.get(k) == v for k, v in SITE0.items() if k in SITE0B), "a place's site moved between saves"
KB = keys(wb)

def dphi(a, b):
    d = math.atan2(b[1], b[0]) - math.atan2(a[1], a[0])
    return abs((d + math.pi) % (2 * math.pi) - math.pi)

count = defaultdict(int)
moves = {"a": [], "b": []}
inside = {"a": 0, "b": 0}
unmoved_b = 0
per = defaultdict(lambda: [0, 0, 0])  # place: changed (a)+(b) with a moved word, inside, beyond
hw = 0.5 * math.asin(0.25)
for k, s, h, i, j in changed:
    moved = []
    for m in range(4):
        x, y = WA.get((k, s, h, m, "probe")), WB.get((k, s, h, m, "probe"))
        if x and y and (x[2] != y[2] or x[3] != y[3]):
            moved.append(dphi(x, y))
    if moved:
        cat = "a"
    else:
        cat = "b"
        for m in range(4):
            x, y = KA.get((k, h, j, m)), KB.get((k, h, j, m))
            if x and y and x[2] != y[2]:
                moved.append(dphi(x, y))
    count[cat] += 1
    if not moved:
        unmoved_b += 1
        continue
    d = max(moved)
    moves[cat].append(d)
    inside[cat] += d <= hw
    per[k][0] += 1
    per[k][1 if d <= hw else 2] += 1
with open(sys.argv[7], "w") as f:
    f.write("problem\tplace\tmoved\tinside\tbeyond\n")
    for k, v in per.items():
        f.write(f"{k[0]}\t{k[1]}\t{v[0]}\t{v[1]}\t{v[2]}\n")
n = len(changed)
print(f"changed memberships {n}: (c) width-law tree {count['c']} ({count['c'] / max(1, n):.2f}), (a) receiver's probe words {count['a']} ({count['a'] / max(1, n):.2f}), (b) source's key words {count['b']} ({count['b'] / max(1, n):.2f}; {unmoved_b} with no key trit moved)")
for c in ("a", "b"):
    if moves[c]:
        print(f"({c}) moved words {len(moves[c])}: inside the receiver's half-width {inside[c]} ({inside[c] / len(moves[c]):.2f}); median |dphi| {statistics.median(moves[c]):.4f} rad, quartiles {statistics.quantiles(moves[c], n=4)}")
ab = moves["a"] + moves["b"]
if ab:
    print(f"(a)+(b): inside {inside['a'] + inside['b']} of {len(ab)} ({(inside['a'] + inside['b']) / len(ab):.2f}); median |dphi| {statistics.median(ab):.4f} rad")
