#!/usr/bin/env python3
"""The |dphi| gate (theory, November 9 14:17): the share of the order difference's sum of squares that falls on changes beyond the
receiver's half-width, each place's I^2 split by the fractions of its changed memberships inside and beyond. A reading only.
Args: IPLACE.tsv REACH.tsv"""
import csv, sys, math
I = {(r['problem'], r['place']): float(r['I']) for r in csv.DictReader(open(sys.argv[1]), delimiter='\t')}
P = {(r['problem'], r['place']): (int(r['moved']), int(r['inside']), int(r['beyond'])) for r in csv.DictReader(open(sys.argv[2]), delimiter='\t')}
ks = list(I); tot = sum(v * v for v in I.values())
none = [k for k in ks if k not in P or P[k][0] == 0]
w = lambda k: (P[k][2] / P[k][0]) if k in P and P[k][0] else 0.0
share = sum(I[k] ** 2 * w(k) for k in ks) / tot
print(f"places {len(ks)}; with no changed membership {len(none)} (I^2 share {sum(I[k] ** 2 for k in none) / tot:.3f})")
print(f"share of sum I^2 beyond the half-width: {share:.3f}")
print(f"I^2 share at places with any change beyond: {sum(I[k] ** 2 for k in ks if k in P and P[k][2] > 0) / tot:.3f} ({sum(1 for k in ks if k in P and P[k][2] > 0)} places)")
probs = sorted(set(k[0] for k in ks))
def stat(keep):
    kk = [k for k in ks if k[0] in keep]
    return sum(I[k] ** 2 * w(k) for k in kk) / sum(I[k] ** 2 for k in kk)
loo = [stat(set(probs) - {p}) for p in probs]; n = len(loo); m = sum(loo) / n
print(f"jackknife over {n} problems: SE {math.sqrt((n - 1) / n * sum((x - m) ** 2 for x in loo)):.3f}")
srt = sorted(ks, key=lambda k: -I[k] ** 2); top = srt[:len(ks) // 10]
bt = sum(P[k][2] for k in top if k in P); mt = sum(P[k][0] for k in top if k in P)
print(f"top tenth by I^2 ({len(top)} places) carries {sum(I[k] ** 2 for k in top) / tot:.3f} of sum I^2; beyond fraction of its changes {bt / max(1, mt):.3f} against all places' {sum(v[2] for v in P.values()) / sum(v[0] for v in P.values()):.3f}; its mean changes a place {mt / len(top):.1f} against {sum(v[0] for v in P.values()) / len(P):.1f}")
