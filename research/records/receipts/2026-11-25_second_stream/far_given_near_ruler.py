#!/usr/bin/env -S python3 -I
"""A count ruler on a wave slice's held cut: what a sample n places back tells of a sample once its near past is known, in nats a place.

    far_given_near_ruler.py SLICE_DIR NAME [plant:N:P | shuffle | terrain | envelope | envelope2] [near=NAME] [lags=N,N,...]

The held documents are read on their own (no context crosses a document's end) and cross-fitted: count tables (add-1/2 within a
context) are taken on the documents of one parity and code the documents of the other, then the halves exchange. For each lag n and
each near context B (the samples one and two back; and those with the sample sixteen back), GAIN is the held code under B less the
held code under B with the sample n back added: the information a far sample holds that the near past does not, net of the price of
the larger table. FREE is the same with B empty (what the lag tells alone, the ruler of November 25's form).

`envelope` reads, in place of one far sample, a fading sum: each place's distance from the middle level, summed with a fade of
`n` places (each term kept at e^(-1/n) of itself a place), read seventeen places back, in thirteen classes of equal mass; ENVELOPE is
its gain over the near context and ENVELOPE_SHUFFLED the same with the classes drawn at random from the same document. It is the
form a store's state takes (charged by what arrives, leaking at its own rate), read by a ruler and held by no law. `envelope2` asks
whether that sum is far or near: the near context also holds the same sum read one place back (fade 4 or 16, the loudness of the
last few samples), and FAR_ENVELOPE is what the sum read seventeen places back adds to it (FAR_ENVELOPE_SHUFFLED its control).

Controls: `plant:N:P` replaces each sample, with probability P, by the sample N back (in order, so a planted run carries), and the
ruler should read a gain at N over its neighbours; `shuffle` replaces the far sample by one drawn at random from the same document,
and every GAIN should read at or under zero. A host ruler over public data; no state of hers is read.
"""
import os
import sys

import numpy as np

LAGS = [3, 4, 8, 9, 16, 24, 27, 32, 48, 64, 81, 96, 128, 160, 192, 243, 256, 384, 512, 729, 1024]
NEAR = {"none": (), "1,2": (1, 2), "1,2,16": (1, 2, 16)}


def documents(out, name):
    chart = [line.split("\t") for line in open(os.path.join(out, f"CHART_{name}.tsv")).read().rstrip("\n").split("\n")[1:]]
    level = np.full(256, -1, dtype=np.int64)
    for row in chart:
        level[int(row[1])] = int(row[0])
    sizes = [int(line.split("\t")[2]) for line in open(os.path.join(out, f"HELD_{name}.tsv")).read().rstrip("\n").split("\n")[1:]]
    docs = []
    with open(os.path.join(out, f"HELD_{name}.bin"), "rb") as f:
        for n in sizes:
            s = level[np.frombuffer(f.read(n), dtype=np.uint8)]
            if (s < 0).any():
                sys.exit("far_given_near_ruler: an octet outside the chart")
            docs.append(s)
    return len(chart), docs


def keyed(s, k, backs, far, rng, shuffle):
    """Each place's key over the samples `backs` back and the far one (`far` back, or none), then the place's own symbol."""
    lo = max(list(backs) + ([far] if far else []) + [0])
    n = len(s) - lo
    if n <= 0:
        return np.zeros(0, dtype=np.int64)
    key = np.zeros(n, dtype=np.int64)
    for b in backs:
        key = key * k + s[lo - b:lo - b + n]
    if far:
        f = s[lo - far:lo - far + n]
        if shuffle:
            f = f[rng.permutation(n)]
        key = key * k + f
    return key * k + s[lo:lo + n]


def faded(x, n):
    """y_t = e^(-1/n) y_(t-1) + x_t, in blocks short enough that the block's own scale stays inside a float's range."""
    a = np.exp(-1.0 / n)
    block = max(1, min(4096, int(600 * n)))
    y, prev = np.empty(len(x)), 0.0
    for lo in range(0, len(x), block):
        xs = x[lo:lo + block].astype(np.float64)
        i = np.arange(len(xs))
        part = np.cumsum(xs * a ** (-i)) * a ** i + prev * a ** (i + 1)
        y[lo:lo + len(xs)] = part
        prev = part[-1]
    return y


def envelopes(docs, k, n, back):
    """Each place's fading sum `back` places before it, in k classes of equal mass over every document."""
    mid = k // 2
    raw = [np.concatenate([np.zeros(back), faded(np.abs(s - mid), n)[:len(s) - back]]) for s in docs]
    cuts = np.quantile(np.concatenate(raw), np.arange(1, k) / k)
    return [np.searchsorted(cuts, r, side="right").astype(np.uint8) for r in raw]


def code(docs, k, backs, far, rng, shuffle, lo_cut, extras=()):
    """The cross-fitted held code in nats over every place at least `lo_cut` into its document; each of `extras`, a class a place,
    joins the near context in place of a far sample, and `shuffle` then draws the last of them at random from the same document."""
    cells = k ** (len(backs) + (1 if far else 0) + len(extras) + 1)
    keys = []
    for d, s in enumerate(docs):
        if not extras:
            kk = keyed(s, k, backs, far, rng, shuffle)
        else:
            lo = max(list(backs) + [0])
            kk = keyed(s, k, backs, 0, rng, False)
            key = kk // k
            for j, extra in enumerate(extras):
                e = extra[d][lo:]
                if shuffle and j == len(extras) - 1:
                    e = e[rng.permutation(len(e))]
                key = key * k + e
            kk = key * k + kk % k
        keys.append(kk[max(0, lo_cut - (len(s) - len(kk))):])
    total, places = 0.0, 0
    for parity in (0, 1):
        train = [kk for i, kk in enumerate(keys) if i % 2 == parity]
        held = [kk for i, kk in enumerate(keys) if i % 2 != parity]
        c = np.bincount(np.concatenate(train), minlength=cells).reshape(-1, k).astype(np.float64)
        logp = np.log((c + 0.5) / (c.sum(1, keepdims=True) + k / 2)).reshape(-1)
        h = np.concatenate(held)
        total -= float(logp[h].sum())
        places += len(h)
    return total / places, places


def main():
    out, name = sys.argv[1], sys.argv[2]
    opts = sys.argv[3:]
    mode = next((o for o in opts if o.startswith("plant:") or o == "shuffle"), "")
    nears = [o[5:] for o in opts if o.startswith("near=")] or list(NEAR)
    lags = next(([int(v) for v in o[5:].split(",")] for o in opts if o.startswith("lags=")), LAGS)
    rng = np.random.default_rng(20261126)
    k, docs = documents(out, name)
    if mode.startswith("plant:"):
        _, lag, p = mode.split(":")
        lag, p = int(lag), float(p)
        planted = []
        for s in docs:
            s = s.copy()
            hit = np.nonzero(rng.random(len(s)) < p)[0]
            for i in hit[hit >= lag]:
                s[i] = s[i - lag]
            planted.append(s)
        docs = planted
    shuffle = mode == "shuffle"
    lo_cut = max(LAGS) + 16
    if "envelope2" in opts:
        print(f"FAR_HEAD levels={k} documents={len(docs)} places={sum(len(s) for s in docs)} mode=envelope2 from_place={lo_cut}")
        far = {n: envelopes(docs, k, n, 17) for n in (4, 16, 64, 256, 1024)}
        for near in nears:
            backs = NEAR[near]
            for m in (4, 16):
                here = envelopes(docs, k, m, 1)
                base, places = code(docs, k, backs, 0, rng, False, lo_cut, extras=(here,))
                for label, shuf in (("FAR_ENVELOPE", False), ("FAR_ENVELOPE_SHUFFLED", True)):
                    parts = []
                    for n in far:
                        with_env, _ = code(docs, k, backs, 0, rng, shuf, lo_cut, extras=(here, far[n]))
                        parts.append(f"fade{n}:{base - with_env:+.4f}")
                    print(f"{label} near={near}+env{m}@1 base={base:.4f} places={places} " + " ".join(parts), flush=True)
        return
    if "envelope" in opts:
        print(f"FAR_HEAD levels={k} documents={len(docs)} places={sum(len(s) for s in docs)} mode=envelope from_place={lo_cut}")
        for near in nears:
            backs = NEAR[near]
            base, places = code(docs, k, backs, 0, rng, False, lo_cut)
            for label, shuf in (("ENVELOPE", False), ("ENVELOPE_SHUFFLED", True)):
                parts = []
                for n in (4, 16, 64, 256, 1024, 4096):
                    with_env, _ = code(docs, k, backs, 0, rng, shuf, lo_cut, extras=(envelopes(docs, k, n, 17),))
                    parts.append(f"fade{n}:{base - with_env:+.4f}")
                print(f"{label} near={near} base={base:.4f} places={places} " + " ".join(parts))
        return
    print(f"FAR_HEAD levels={k} documents={len(docs)} places={sum(len(s) for s in docs)} mode={mode or 'terrain'} from_place={lo_cut}")
    for near in nears:
        backs = NEAR[near]
        base, places = code(docs, k, backs, 0, rng, False, lo_cut)
        parts = []
        for lag in lags:
            if lag in backs:
                continue
            with_far, _ = code(docs, k, backs, lag, rng, shuffle, lo_cut)
            parts.append(f"{lag}:{base - with_far:+.4f}")
        label = "FREE" if not backs else "GAIN"
        print(f"{label} near={near} base={base:.4f} places={places} " + " ".join(parts))


if __name__ == "__main__":
    main()
