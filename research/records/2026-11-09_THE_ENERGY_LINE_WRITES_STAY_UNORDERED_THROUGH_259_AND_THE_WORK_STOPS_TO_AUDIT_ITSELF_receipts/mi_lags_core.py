#!/usr/bin/env python3
"""Letter order by lag band (theory, November 9 10:54): the plug-in MI per lag over within-write shuffles (120 rounds, the same
rounds for every leave-one-out set), summed over lags 1-5, 6-20 and 1-20, jackknife SEs over the texts. Texts: a writer's write set
(WRITES.txt, --section) or the held file's first N answers (--truth HELD N). Prints numbers only. A reading only."""
import re, sys, math, random
from collections import Counter
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from write_mi import writes, mi, prepare, ROUNDS
LAGS = 20
BANDS = {"1-5": range(1, 6), "6-20": range(6, 21), "1-20": range(1, 21)}

def per_lag(ws):
    out = []
    for k in range(1, LAGS + 1):
        c = Counter()
        for w in ws:
            for i in range(len(w) - k):
                c[(w[i], w[i + k])] += 1
        out.append(mi(c))
    return out

def band_stats(ws, sh, keep):
    real = per_lag([ws[j] for j in keep])
    base = [0.0] * LAGS
    for r in range(ROUNDS):
        for k, v in enumerate(per_lag([sh[r][j] for j in keep])):
            base[k] += v / ROUNDS
    d = [a - b for a, b in zip(real, base)]
    return {name: sum(d[k - 1] for k in lags) for name, lags in BANDS.items()}

