"""p60_opening: P60 item 7's readings from read-cavity's rows (a host ruler; numbers only).

usage: python3 -I p60_opening.py SITE_RULER_DIR F3 F2 F0 C3
  F3, F2: the founded line's means of states of sections 2,001 to 3,000 and 1,001 to 2,000; F0: the founded state before training (the lift at
  zero); C3: the control's mean of sections 2,001 to 3,000. Each a read-cavity output directory (cavity.tsv).
Codes on 2^-20 bits are read as nats (code / 2^20 ln 2). Rows: P a place open alone among its stretch's written places (cO the opening's code,
which at a written place is its cavity code, so the P rows of a stretch are also its news with nothing masked), W a whole mask's open place,
C the code slice's copy with leading spaces doubled, S each stretch begun seven places later.
"""
import math
import sys
from collections import defaultdict

import numpy as np

sys.path.insert(0, sys.argv[1])
import site_ruler as sr  # noqa: E402

LN2 = math.log(2.0)
SLICES = ["code", "web", "science", "books", "wikidata"]


def nats(code):
    return code / float(1 << 20) * LN2


def rows(d):
    out = defaultdict(list)
    with open(d + "/cavity.tsv") as f:
        head = f.readline().rstrip("\n").split("\t")
        for line in f:
            w = dict(zip(head, line.rstrip("\n").split("\t")))
            out[w["row"]].append(w)
    return out


def mean_by_slice(rs, col):
    by = defaultdict(list)
    for r in rs:
        if r.get(col, "-") not in ("-", None):
            by[r["slice"]].append(nats(int(r[col])))
    pooled = [v for s in by.values() for v in s]
    parts = " ".join("%s=%.4f(%d)" % (s, float(np.mean(by[s])), len(by[s])) for s in SLICES if by[s])
    return (float(np.mean(pooled)) if pooled else float("nan")), len(pooled), parts


def line(label, rs, col):
    m, n, parts = mean_by_slice(rs, col)
    print("%s pooled=%.4f places=%d | %s" % (label, m, n, parts))
    return m


F3, F2, F0, C3 = (rows(d) for d in sys.argv[2:6])
print("P60_OPENING nats a place; pooled is the mean over the named places; by slice with the count of places")
print("# 7a the opening's code through the trained lift")
for name, R in (("F3", F3), ("F2", F2)):
    line("OPENING %s one_place" % name, R["P"], "cO")
    line("OPENING %s whole_open" % name, R["W"], "cO")
line("OPENING F0_bias_only one_place", F0["P"], "cO")
line("OPENING F0_bias_only whole_open", F0["W"], "cO")
print("# beside: P57's fitted face at the opening 2.502 pooled, the class frequencies 3.435 (state C, one-place masks)")
print("# 7b the last tick's code, founded against control")
for kind, col_kind in (("one_place", "P"), ("whole_open", "W")):
    a = line("LAST_TICK F3 %s" % kind, F3[col_kind], "cK")
    b = line("LAST_TICK C3 %s" % kind, C3[col_kind], "cK")
    by_f, by_c = defaultdict(list), defaultdict(list)
    for r in F3[col_kind]:
        by_f[r["slice"]].append(nats(int(r["cK"])))
    for r in C3[col_kind]:
        by_c[r["slice"]].append(nats(int(r["cK"])))
    print("LAST_TICK_DIFF %s founded_minus_control pooled=%+.4f | %s" % (kind, a - b, " ".join(
        "%s=%+.4f" % (s, float(np.mean(by_f[s]) - np.mean(by_c[s]))) for s in SLICES if by_f[s] and by_c[s])))
# The same places in both reads.
same = sum(1 for x, y in zip(F3["P"], C3["P"]) if (x["slice"], x["stretch"], x["t"], x["class"]) == (y["slice"], y["stretch"], y["t"], y["class"]))
print("SAME_PLACES one_place %d of %d %d" % (same, len(F3["P"]), len(C3["P"])))

print("# 7c the machine's own news c_t (F3's opening code, nothing masked) and its sites at 8 bits")
SIGMA = 8.0 * LN2


def stretches(rs, coord):
    by = defaultdict(list)
    for r in rs:
        by[(r["slice"], int(r["stretch"]))].append((int(r["t"]), int(r["class"]), nats(int(r["cO"])), r[coord]))
    out = {}
    for key, v in by.items():
        v.sort()
        out[key] = (np.array([c for _, _, c, _ in v]), np.array([x for _, _, _, x in v], dtype=object), np.array([k for _, k, _, _ in v]))
    return out


orig = stretches(F3["P"], "t")
later = stretches(F3["S"], "source")
doubled = stretches(F3["C"], "source")
_, _, parts = mean_by_slice(F3["P"], "cO")
print("NEWS by slice %s" % parts)


def coords(xs):
    seen, out = set(), []
    for x in xs:
        x = int(x)
        out.append(np.nan if x in seen else float(x))
        seen.add(x)
    return np.array(out)


for law, name in (("G", "landmarks"), ("C", "restarting_cut")):
    for slice_name in SLICES + ["pooled"]:
        places = sites = whole = ones = 0
        kept = {"start": [0, 0, 0], "doubled": [0, 0, 0]}
        for key, (c, _, _) in orig.items():
            if slice_name != "pooled" and key[0] != slice_name:
                continue
            if len(c) < sr.SHORT:
                continue
            rho = sr.isolation(c, np.cumsum(c))
            so = sr.sites_of(law, c, rho, SIGMA)
            places += len(c)
            sites += len(so)
            gaps = np.diff(so)
            whole += len(gaps)
            ones += int((gaps == 1).sum())
            xo = np.arange(len(c), dtype=np.float64)
            for label, copy in (("start", later), ("doubled", doubled)):
                if key not in copy:
                    continue
                c2, x2, _ = copy[key]
                xc = coords(x2)
                r2 = sr.isolation(c2, np.cumsum(c2))
                k, who, ch = sr.compare(xo, so, xc, sr.sites_of(law, c2, r2, SIGMA), 0.25, float(sr.FAR), 1.0)
                kept[label][0] += int(k.sum())
                kept[label][1] += len(k)
                kept[label][2] += ch
        if places == 0:
            continue
        tail = " | ".join("%s %s (%d compared)" % (lab, sr.show(kept[lab]), kept[lab][1]) for lab in ("start", "doubled") if kept[lab][1])
        print("SITES %s slice=%s sigma_bits=8 places=%d sites=%d mean_epoch=%.3f whole_epochs=%d one_place_share=%.4f | %s" % (
            name, slice_name, places, sites, places / max(sites, 1), whole, ones / max(whole, 1), tail))
