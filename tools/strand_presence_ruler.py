#!/usr/bin/env -S python3 -I
"""A ruler: how many places' identities a strand's state carries (the lead, November 18; the record of the two streams §14).

`athena host complete-language read-strand-states` writes, for held passages read by two streams, each known site's read after the
last tick and each open place's read after every tick. This reads, by least squares, how much of the symbol standing `k` places
before a place is present in the read at the place: for a known site `k` from 0 (its own symbol, the reading's own check: a site
holds its symbol) and for the open place at a place `k` from 1 (the place before, which its opening names). A symbol's identity is
its indicator among the TOP commonest classes (a place whose symbol is rarer is left out of that `k`). Fitted on the passages of
even index and read on the odd ones: the share of the indicators' variance the fitted read removes there, in thousandths.

Outside the machine; shares only. Usage: strand_presence_ruler.py DUMP [KMAX] [TOP]"""
import sys
import numpy as np

def main():
    d = sys.argv[1]
    kmax = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    top = int(sys.argv[3]) if len(sys.argv) > 3 else 48
    dims = dict(l.split("\t") for l in open(d + "/dims.tsv").read().split("\n") if l)
    width, ticks = int(dims["read"]), int(dims["ticks"])
    rows, places, classes = [], [], []
    for line in open(d + "/rows.tsv"):
        f = line.rstrip("\n").split("\t")
        rows.append(int(f[0])); places.append(int(f[2])); classes.append(int(f[3]))
    rows, places, classes = np.array(rows), np.array(places), np.array(classes)
    n = len(rows)
    load = lambda name: np.fromfile(d + "/" + name, dtype="<i4").reshape(n, width).astype(np.float64) / 65536.0
    known = load("known.i32")
    opens = [load(f"open_{k}.i32") for k in range(ticks)]
    common = np.argsort(-np.bincount(classes))[:top]
    index = -np.ones(classes.max() + 1, dtype=int)
    index[common] = np.arange(len(common))
    fit_half = rows % 2 == 0

    def presence(x, k):
        """The share of the indicator of the symbol k places before, removed on the held half by a read fitted on the other."""
        ok = places >= k
        src = np.where(ok, np.arange(n) - k, 0)
        ok &= rows[src] == rows
        target = index[classes[src]]
        ok &= target >= 0
        if ok.sum() < 4 * width:
            return None, 0
        y = np.zeros((n, len(common)))
        y[np.arange(n)[ok], target[ok]] = 1.0
        a, b = ok & fit_half, ok & ~fit_half
        xa = np.hstack([x[a], np.ones((a.sum(), 1))])
        xb = np.hstack([x[b], np.ones((b.sum(), 1))])
        gram = xa.T @ xa
        gram += np.eye(gram.shape[0]) * 1e-6 * np.trace(gram) / gram.shape[0]
        w = np.linalg.solve(gram, xa.T @ y[a])
        resid = y[b] - xb @ w
        total = y[b] - y[a].mean(axis=0)
        return 1.0 - (resid ** 2).sum() / (total ** 2).sum(), int(b.sum())

    def report(name, x, ks):
        out = []
        for k in ks:
            share, _ = presence(x, k)
            out.append(f"{k}={'-' if share is None else round(1000 * share)}")
        print(f"PRESENCE read={name} places_back: " + " ".join(out), flush=True)

    print(f"PRESENCE passages={len(set(rows.tolist()))} places={n} width={width} ticks={ticks} top={top} (thousandths, held half)")
    report("known_site_last_tick", known, range(0, kmax + 1))
    for k in range(ticks):
        report(f"open_place_tick_{k + 1}", opens[k], range(1, kmax + 1))

if __name__ == "__main__":
    main()
