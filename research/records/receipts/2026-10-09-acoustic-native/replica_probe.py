"""Reads the exact numbers the native wave port and dynamic-section reader are checked against.

It runs NO repository code. It loads the independent exact replica of the acoustic-locks record
(`research/records/receipts/2026-10-09-acoustic-locks/replica.py` on commit 35d5951634ab, sha256
6d96dfcc889f8136...) by path and prints, in `fractions.Fraction` and integers only, the ring
t = 1, 2, 3 of its declared Farey bank (C = 1, D = 0, K = 4(a^2 + t^2), Y = 1/(4a), a = t/8, h = 1)
driven from rest by its F1 sawtooth of period 7 (the zero-mean x = 7 L - 9, L = 0 0 1 1 2 2 3).

Usage:  python3 -I replica_probe.py <path to replica.py>
"""
import importlib.util
import hashlib
import sys
from fractions import Fraction as F

path = sys.argv[1]
spec = importlib.util.spec_from_file_location("replica", path)
r = importlib.util.module_from_spec(spec)
spec.loader.exec_module(r)
print("replica.py sha256", hashlib.sha256(open(path, "rb").read()).hexdigest())

kappa = r.declared_kappa(r.FAREY_ORDER)
F1 = r.fixtures()["F1 sawtooth 7"]
print("kappa", r.fmt(kappa), " F1", F1, " settle", r.SETTLE, " n", r.N_SAMPLES)


def arrivals_of(states):
    z = [(w, u) for (u, w) in states]
    ell = r.cls(*z[r.SETTLE])
    word, arr, lifts = [], [], [ell]
    for k in range(r.SETTLE, r.N_SAMPLES):
        c0, d = r.symbol(z[k], z[k + 1])
        word.append((c0, d))
        nxt = ell + d
        if nxt // 4 != ell // 4:
            arr.append((k, nxt // 4 - ell // 4))
        ell = nxt
        lifts.append(ell)
    return word, arr, lifts


def balanced(cyc):
    """Constant-rate (balanced) cyclic word: every two windows of one length differ by at most 1."""
    n = len(cyc)
    for length in range(1, n):
        counts = [sum(cyc[(s + i) % n] for i in range(length)) for s in range(n)]
        if max(counts) - min(counts) > 1:
            return False
    return True


for t in (F(1), F(2), F(3)):
    ring = r.Ring(t, kappa)
    states, outs, closes = r.run(ring, r.stream_of(F1))
    print()
    print("=== ring t = %s: a = %s, K = %s, Y = %s, M = %s; every tick's port balance closes: %s" % (
        r.fmt(t), r.fmt(ring.a), r.fmt(ring.K), r.fmt(ring.Y), r.fmt(ring.M), closes))
    if t == 1:
        for k in (0, 1, 2, 3, 7, 14):
            print("  state %2d: u = %s ; w = %s" % (k, r.fmt(states[k][0]), r.fmt(states[k][1])))
        for k in range(4):
            print("  b_out %d = %s" % (k, r.fmt(outs[k])))
    word, arr, lifts = arrivals_of(states)
    tau = r.ring_reading(word)[1]
    cycle = word[:tau]
    repeated = all(word[i] == cycle[i % tau] for i in range(len(word)))
    print("  settled word (ticks %d..%d): cycle of %d = %s ; the 120 symbols are that cycle repeated: %s" % (
        r.SETTLE, r.N_SAMPLES - 1, tau, " ".join("%d:%+d" % cd for cd in cycle), repeated))
    print("  net lift over the cycle %d, winding W = %d, mean rate W/tau = %d/%d" % (
        sum(d for _, d in cycle), sum(d for _, d in cycle) // 4, sum(d for _, d in cycle) // 4, tau))
    print("  section arrivals (tick, signed): %s" % arr)
    gaps = [b[0] - a[0] for a, b in zip(arr, arr[1:])]
    print("  arrival gaps: %s" % gaps)
    cyc_arr = [0] * tau
    for k, s in arr:
        if r.SETTLE + 2 * tau <= k < r.SETTLE + 3 * tau:
            cyc_arr[(k - r.SETTLE) % tau] += s
    print("  arrival word over one cycle (from tick %d): %s ; balanced (constant rate): %s" % (
        r.SETTLE, cyc_arr, balanced(cyc_arr)))
    if t == 1:
        neg, _, _ = r.run(ring, lambda k: -r.stream_of(F1)(k))
        wneg, aneg, lneg = arrivals_of(neg)
        ok = all(c1 == (c0 + 2) % 4 and d1 == d0 for (c0, d0), (c1, d1) in zip(word, wneg))
        print("  polarity (-x): every symbol is (cls + 2, advance): %s ; lift differs from the +x lift by %s" % (
            ok, sorted(set(b - a for a, b in zip(lifts, lneg)))))
