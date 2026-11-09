#!/usr/bin/env python3
"""The writes' letter order (theory, November 9 05:31 and 08:07): the summed plug-in mutual information between letters at lags
1..20, pooled over a writer's eight equilibrium writes, less the mean over 120 within-write shuffles (each write shuffled once a
round, the same shuffles for every leave-one-out set), in nats. SE by the delete-one jackknife over the writes. With two writers
whose writes answer the same problems, the difference is jackknifed leaving write k out of both. A reading only.
Usage: write_mi.py WRITES_A [WRITES_B] [--section 'equilibrium at sweep 4']"""
import re, sys, math, random
from collections import Counter

LAGS, ROUNDS = 20, 120

def writes(path, kind):
    txt = open(path, encoding="utf-8", errors="replace").read()
    parts = re.split(r"^(=== .*? ===)\n", txt, flags=re.M)
    out = {}
    for i in range(1, len(parts), 2):
        m = re.match(r"=== (.*) answer (\d+) ===", parts[i])
        if m and m.group(1) == kind:
            out[int(m.group(2))] = parts[i + 1].rstrip("\n")
    return [out[k] for k in sorted(out)]

def pair_counts(ws):
    """Per lag, the pooled pair counts (a Counter of (x, y)) and their marginals."""
    per = []
    for k in range(1, LAGS + 1):
        c = Counter()
        for w in ws:
            for i in range(len(w) - k):
                c[(w[i], w[i + k])] += 1
        per.append(c)
    return per

def mi(c):
    n = sum(c.values())
    if n == 0:
        return 0.0
    px, py = Counter(), Counter()
    for (x, y), v in c.items():
        px[x] += v
        py[y] += v
    return sum(v / n * math.log(v * n / (px[x] * py[y])) for (x, y), v in c.items())

def summed(counts):
    return sum(mi(c) for c in counts)

def statistic(ws, shuffles, keep):
    """Summed MI of the kept writes less the mean over rounds of the kept writes' shuffles."""
    real = summed(pair_counts([ws[j] for j in keep]))
    base = sum(summed(pair_counts([shuffles[r][j] for j in keep])) for r in range(ROUNDS)) / ROUNDS
    return real - base

def prepare(ws, seed):
    rng = random.Random(seed)
    sh = []
    for _ in range(ROUNDS):
        row = []
        for w in ws:
            l = list(w)
            rng.shuffle(l)
            row.append("".join(l))
        sh.append(row)
    return sh

def jack(values_full, values_loo):
    n = len(values_loo)
    mean = sum(values_loo) / n
    return values_full, math.sqrt((n - 1) / n * sum((v - mean) ** 2 for v in values_loo))

if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    kind = "equilibrium at sweep 4"
    if "--section" in sys.argv:
        kind = sys.argv[sys.argv.index("--section") + 1]
        args = [a for a in args if a != kind]
    sets = [writes(p, kind) for p in args]
    shuf = [prepare(ws, 20261109 + i) for i, ws in enumerate(sets)]
    full, loo = [], []
    for ws, sh in zip(sets, shuf):
        n = len(ws)
        f = statistic(ws, sh, list(range(n)))
        l = [statistic(ws, sh, [j for j in range(n) if j != k]) for k in range(n)]
        est, se = jack(f, l)
        full.append(f)
        loo.append(l)
        print(f"{len(ws)} writes, {sum(map(len, ws))} letters: summed MI over shuffles {est:+.4f} nats (jackknife SE {se:.4f})")
    if len(sets) == 2 and len(sets[0]) == len(sets[1]):
        d_full = full[1] - full[0]
        d_loo = [b - a for a, b in zip(loo[0], loo[1])]
        est, se = jack(d_full, d_loo)
        print(f"difference (second less first), the same write left out of both: {est:+.4f} nats (jackknife SE {se:.4f}, z {est / se if se else float('nan'):+.2f})")
