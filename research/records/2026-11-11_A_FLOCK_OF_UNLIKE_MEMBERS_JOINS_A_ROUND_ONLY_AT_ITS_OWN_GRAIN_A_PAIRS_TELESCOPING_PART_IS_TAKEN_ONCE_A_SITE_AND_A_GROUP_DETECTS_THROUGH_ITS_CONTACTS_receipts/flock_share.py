#!/usr/bin/env python3
"""The share of a round between unlike members, in integer microseconds.

A round is n independent units read against one fixed state. The card reads k units in t0 + k*tc (its lanes fused: one stream of
launches). The host has L lanes; a lane reads one unit in tl, so k units take tl*ceil(k/L). The round ends when both sides have ended.

  least(n)      the least end time over every split, by trying each k (the definition)
  filled(n)     the same by the filling rule: the least T with  floor((T - t0)/tc) + L*floor(T/tl) >= n
  built(n)      the rule of November 7 (LanesField::split): k = clamp(floor(n*share), 1, n-1); the share that would end both together
                read from th/k and tc/(n-k), met halfway from the share before; opening share 1/16

Prints, for each n: the card alone, the least time and its k, the built rule's settled k and time, and whether a lane joins
(n*tc + t0 > tl). Times from design's log of November 7 (lanes.log: splits 118, host_regions 824, card_regions 43,590, host_ms 118,583,
card_ms 188,133, host_threads 20): tc = 188,133/43,590 = 4316 us a region on the card; tl = 118,583/118 = 1,004,941 us for one region on
one lane (about 7 regions a split, run in parallel); L = 20; t0 = 0. The model takes the lanes to scale freely, which that run did not
show (it used about 7): its last line prints the run's own figures beside the model's.
"""
from fractions import Fraction

TC, TL, L, T0 = 4316, 1004941, 20, 0


def host(k):
    return TL * -(-k // L) if k else 0


def card(k):
    return T0 + k * TC if k else 0


def least(n):
    return min((max(host(k), card(n - k)), k) for k in range(n + 1))


def filled(n):
    # the candidate end times are the card's and the host's own step times
    ts = sorted({card(j) for j in range(n + 1)} | {host(j * L) for j in range(n // L + 2)})
    for t in ts:
        cap = (max(t - T0, 0) // TC) + L * (t // TL)
        if cap >= n:
            return t


def built(n, rounds=200):
    share = Fraction(1, 16)
    k = wall = None
    for _ in range(rounds):
        k = max(1, min(n - 1, int(n * share)))
        th, tc = host(k), card(n - k)
        wall = max(th, tc)
        per_h, per_c = Fraction(th, k), Fraction(tc, n - k)
        share = (share + per_c / (per_h + per_c)) / 2
    return k, wall, share


print(f"tc={TC}us tl={TL}us L={L} t0={T0}us  rates add to {1 + Fraction(L * TC, TL)} = {float(1 + Fraction(L * TC, TL)):.3f} times the card alone over long rounds")
print("    n   card_alone   least(k)        gain   built(k)        gain   share    a lane joins")
for n in (16, 232, 234, 376, 752, 1600, 16000):
    alone = card(n)
    t, k = least(n)
    assert t == filled(n), (n, t, filled(n))
    kb, tb, s = built(n)
    print(f"{n:5d} {alone:10d}us {t:8d}us({k:4d}) {alone / t:6.3f} {tb:8d}us({kb:4d}) {alone / tb:6.3f}  {float(s):6.4f}   {'yes' if n * TC + T0 > TL else 'no'}")

# The run itself: 376 regions a split, about 7 on the host.
host_rate, card_rate = Fraction(824 * 1000, 118583), Fraction(43590 * 1000, 188133)
print(f"as run: host {float(host_rate):.2f} regions/s on about 7 of 20 threads, card {float(card_rate):.1f} regions/s: {float(100 * host_rate / card_rate):.1f}% of the card;"
      f" a lane {TL / TC:.0f} times the card a region; 20 lanes scaling freely {float(100 * Fraction(L * TC, TL)):.1f}% at most;"
      f" split wall {215666 / 118:.0f} ms a split against the card alone at {376 * TC / 1000:.0f} ms plus the same join")
