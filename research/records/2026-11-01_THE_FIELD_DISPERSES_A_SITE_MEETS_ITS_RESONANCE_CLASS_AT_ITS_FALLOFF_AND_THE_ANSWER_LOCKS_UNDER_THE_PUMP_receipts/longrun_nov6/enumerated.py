#!/usr/bin/env python3
"""lap 4's score (theory, November 7, 04:05): from a contrast-field run's ENUMERATED.tsv, per lap, at the held places: the exact
conditional's code -log2 P(truth | rest) with P(c | rest) proportional to 2^(-G_c / T), the face's code -log2 p_face(truth),
and KL(exact || face) in bits, their means, the KL's quartiles and the share of places at or under 0.3 bits. A reading
only: the run reads none of it."""
import csv, math, statistics, sys
rows = list(csv.DictReader(open(sys.argv[1]), delimiter="\t"))
by = {}
for r in rows:
    by.setdefault(int(r["lap"]), []).append(r)
print("lap\tplaces\tenumerated_code\tface_code\tkl_mean\tkl_q25\tkl_median\tkl_q75\tkl<=0.3\tface_zero_letters")
for lap, rs in sorted(by.items()):
    ex, fc, kl, zeros = [], [], [], 0
    for r in rs:
        t = 2.0 ** (int(r["log2_t"]) / 2 ** 24)
        g = [int(v) / 2 ** 32 for v in r["energies"].split(",")]
        lo = min(g)
        w = [2.0 ** (-(x - lo) / t) for x in g]
        z = sum(w)
        p = [x / z for x in w]
        masses = [int(v) for v in r["face_masses"].split(",")]
        total = int(r["face_total"])
        q = [m / total for m in masses]
        c = int(r["truth"])
        ex.append(-math.log2(p[c]) if p[c] > 0 else float("inf"))
        fc.append(-math.log2(q[c]) if q[c] > 0 else float("inf"))
        k = 0.0
        for a, b in zip(p, q):
            if a <= 0:
                continue
            if b <= 0:
                zeros += 1
                b = 1 / total
            k += a * math.log2(a / b)
        kl.append(k)
    s = sorted(kl)
    n = len(s)
    print(f"{lap}\t{n}\t{statistics.mean(ex):.4f}\t{statistics.mean(fc):.4f}\t{statistics.mean(kl):.4f}\t{s[n // 4]:.4f}\t{s[n // 2]:.4f}\t{s[3 * n // 4]:.4f}\t{sum(1 for x in kl if x <= 0.3)}/{n}\t{zeros}")

# The paired change of the exact code from the first lap read to each later one, place by place: its mean and standard error
# (theory, November 7, 05:33: a fall past twice its paired standard error sends the next lap).
def codes(rs):
    out = {}
    for r in rs:
        t = 2.0 ** (int(r["log2_t"]) / 2 ** 24)
        g = [int(v) / 2 ** 32 for v in r["energies"].split(",")]
        lo = min(g)
        w = [2.0 ** (-(x - lo) / t) for x in g]
        out[(r["problem"], r["place"])] = -math.log2(w[int(r["truth"])] / sum(w))
    return out
laps = sorted(by)
if len(laps) > 1:
    base = codes(by[laps[0]])
    for lap in laps[1:]:
        now = codes(by[lap])
        d = [now[k] - base[k] for k in base if k in now]
        m = statistics.mean(d)
        se = statistics.stdev(d) / len(d) ** 0.5 if len(d) > 1 else float("nan")
        print(f"# exact code from lap {laps[0]} to lap {lap}: paired change {m:+.4f} bits a place, standard error {se:.4f}, over {len(d)} places; falls past twice its error: {m < -2 * se}")
