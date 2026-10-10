"""Predicts what the native lock reader and the joint period read, before the Rust runs.

It runs NO repository code. It loads the acoustic-locks replica (`6d96dfcc889f8136...`, the exact
ring tick and the quadrant lift) by path and applies to its settled symbols the reading the native
`hnn::section_lock` is specified to make, in `fractions.Fraction` and integers only:

  window  = the symbols of ticks SETTLE .. SETTLE + 120 of a ring driven from rest (the replica's
            declared N = 240, settle 120)
  Silent    : no symbol in the window advances the lift (nothing crossed a ray)
  Unlocked  : no tau in 1..=60 (at most half the window) with symbol[k] = symbol[k + tau] for all k
  Fractional: the cycle's net lift is not a multiple of 4
  Locked    : the least such tau, W = (sum of advances over a cycle) / 4, the address W/tau, and the
              OBSERVED arrival word (the signed crossing of ring-section ticks within one cycle)
  joint     : the lcm of the locked rings' tau (Silent rings skipped), refused if any ring is not
              locked; it must equal the least period of the joint tuple word and divide the wave's.

The declared bank is three rings of the replica's Farey bank, t = 2/3, 1, 2 (kappa = 1/8, so
a = t/8): never searched or tuned.

Usage:  python3 -I lock_predictions.py <path to the acoustic-locks replica.py>
"""
import importlib.util
import sys
from fractions import Fraction as F
from math import gcd

spec = importlib.util.spec_from_file_location("replica", sys.argv[1])
r = importlib.util.module_from_spec(spec)
spec.loader.exec_module(r)

BANK = [F(2, 3), F(1), F(2)]
KAPPA = r.declared_kappa(r.FAREY_ORDER)
SETTLE, LENGTH, MAX_PERIOD = r.SETTLE, r.N_SAMPLES - r.SETTLE, (r.N_SAMPLES - r.SETTLE) // 2


def lcm(a, b):
    return a * b // gcd(a, b)


def window(ring, stream):
    states, _, closes = r.run(ring, stream)
    assert closes
    z = [(w, u) for (u, w) in states]
    out = []
    ell = None
    for k in range(SETTLE, r.N_SAMPLES):
        if z[k] == (0, 0):
            if z[k + 1] != (0, 0):
                return ("not settled",)
            out.append((None, 0, 0))
            continue
        c, d = r.symbol(z[k], z[k + 1])
        if d == "through":
            return ("section refused",)
        landed = c + d
        out.append((c, d, 1 if landed >= 4 else (-1 if landed < 0 else 0)))
    return out


def lock(word):
    if isinstance(word, tuple):
        return word
    if all(d == 0 for (_, d, _) in word):
        return ("Silent",)
    for tau in range(1, MAX_PERIOD + 1):
        if all(word[k][:2] == word[k + tau][:2] for k in range(len(word) - tau)):
            net = sum(d for (_, d, _) in word[:tau])
            if net % 4:
                return ("Fractional", net)
            w = net // 4
            arrivals = [(k, s) for k, (_, _, s) in enumerate(word[:tau]) if s]
            return ("Locked", tau, w, F(w, tau), [s for (_, _, s) in word[:tau]], arrivals)
    return ("Unlocked",)


def show(name, stream, period=None):
    print("\n%s" % name)
    words, locks = [], []
    for t in BANK:
        ring = r.Ring(t, KAPPA)
        word = window(ring, stream)
        reading = lock(word)
        words.append(word)
        locks.append(reading)
        if reading[0] == "Locked":
            print("  t=%-3s Locked tau=%d W=%d address=%s arrival word %s arrivals(offset,sign) %s" % (
                r.fmt(t), reading[1], reading[2], r.fmt(reading[3]), reading[4], reading[5]))
        else:
            print("  t=%-3s %s" % (r.fmt(t), reading))
    locked = [x for x in locks if x[0] == "Locked"]
    bad = [i for i, x in enumerate(locks) if x[0] not in ("Locked", "Silent")]
    if bad:
        print("  joint: refused, ring(s) %s not locked" % bad)
    elif not locked:
        print("  joint: Silent")
    else:
        tau = 1
        for x in locked:
            tau = lcm(tau, x[1])
        tuple_word = list(zip(*[[(c, d) for (c, d, _) in w] for w, x in zip(words, locks) if x[0] == "Locked"]))
        least = next((p for p in range(1, MAX_PERIOD + 1)
                      if all(tuple_word[k] == tuple_word[k + p] for k in range(len(tuple_word) - p))), None)
        print("  joint: tau = lcm %s = %d ; least period of the joint tuple word %s ; each ring's tau divides it: %s%s" % (
            [x[1] for x in locked], tau, least, all(tau % x[1] == 0 for x in locked),
            "" if period is None else " ; divides the wave's period %d: %s" % (period, period % tau == 0)))


print("replica sha256", __import__("hashlib").sha256(open(sys.argv[1], "rb").read()).hexdigest())
print("kappa", r.fmt(KAPPA), " bank", [r.fmt(t) for t in BANK], " settle", SETTLE, " window", LENGTH, " max period", MAX_PERIOD)
fx = r.fixtures()
show("F1 sawtooth 7", r.stream_of(fx["F1 sawtooth 7"]), 7)
show("F3 quantized triangle 12", r.stream_of(fx["F3 quantized triangle 12"]), 12)
show("F4 two-tone 3+4", r.stream_of(fx["F4 two-tone 3+4"]), 12)
show("F5 Thue-Morse", r.thue_morse)
show("C1 zero input", lambda k: 0)
show("C3 sawtooth period 61", lambda k: (k % 61) - 30)
