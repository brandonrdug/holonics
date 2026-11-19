#!/usr/bin/env -S python3 -I
"""A ruler of rows addressed by the frontier's own read, set against her own face (the lead, November 19; the frontier record §25).

`read-strand-states ... past carries` writes each open place's read after the last tick (`open_last.i32`, `D` words a place): the
operand her face at that place is linear in. A ring's row is the half-planes of ten fixed projections of that read (a residue of the
read's direction, so places whose faces point alike share it). Rows are fitted on the fitting half (the symbols met at the places that
stand at a row) and read on the held stretches of the line's frontier read, where her own code at each place is the read's rows S
(`frontier.tsv`, on 2^-20 bits). Each address's rows (combined across rings by their least, Witten-Bell to the fitting half's octets)
are mixed with her face, `(1 − λ) p_her + λ p_rows` on the arriving symbol, λ chosen on the even stretches and read on the odd ones.
Beside them at the same rows: a scramble of the four octets before and a planted address (each four octets' most met continuation in
the fitting half). Read over all places and at the settled places (a count of five on the first TRAIN octets of a slice expects under a
quarter of a nat): nats a place, the mean mass on the arriving symbol, the share paying under 0.1 nats. Rows that add to her face read
under her code at their λ; an address that is located for her reads under the scramble's. Outside the machine; counts and floats only.

Usage: read_rows_ruler.py STORE CODEC TRAIN FIT_DIR HELD_DIR FRONTIER_TSV RINGS BITS"""
import sys, math, numpy as np

G, LN2 = float(1 << 20), math.log(2)

def load(d):
    dims = dict(l.split("\t") for l in open(f"{d}/dims.tsv").read().split("\n") if l)
    D = int(dims["read"])
    rows = np.loadtxt(f"{d}/rows.tsv", dtype=object, delimiter="\t", comments=None)
    r, g, t, c = rows[:, 0].astype(int), rows[:, 1], rows[:, 2].astype(int), rows[:, 3].astype(int)
    x = np.fromfile(f"{d}/open_last.i32", dtype="<i4").reshape(-1, D).astype(np.float64)
    return r, g, t, c, x

def main():
    store, codec, train_n, fit_d, held_d, frontier, rings, bits = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4], sys.argv[5], sys.argv[6], int(sys.argv[7]), int(sys.argv[8])
    head, used = open(codec).read().split("\n")[:2]
    void = int(head.split(" ")[2]); used = [int(x) for x in used.split(" ")]
    octet = lambda c: used[c] if c < void else used[c - 1]
    fr, fg, ft, fc, fx = load(fit_d)
    hr, hg, ht, hc, hx = load(held_d)
    A = max(int(fc.max()), int(hc.max())) + 1
    her = {}
    for line in open(frontier):
        f = line.rstrip("\n").split("\t")
        if f[0] == "S":
            her[(f[1], int(f[2]), int(f[3]))] = int(f[5]) / G * LN2
    key = [(g.split(":")[0], int(g.split(":")[1]), int(t)) for g, t in zip(hg, ht)]
    have = np.array([k in her for k in key])
    p_her = np.array([math.exp(-her[k]) if k in her else 0.0 for k in key])
    def seqs(r, c):
        out = {}
        for i in range(len(r)):
            out.setdefault(r[i], []).append(octet(c[i]))
        return {k: bytes(v) for k, v in out.items()}
    fs, hs = seqs(fr, fc), seqs(hr, hc)
    ctx = lambda s, r, t, k: [s[r[i]][max(0, t[i] - k):t[i]] for i in range(len(r))]
    f4, h4 = ctx(fs, fr, ft, 4), ctx(hs, hr, ht, 4)
    draw = np.random.default_rng(1119)
    proj = [draw.standard_normal((hx.shape[1], bits)) for _ in range(rings)]
    mean = fx.mean(0)
    rows_n = 1 << bits
    def by_read(x):
        return np.stack([(((x - mean) @ proj[j]) > 0).astype(np.int64) @ (1 << np.arange(bits)) for j in range(rings)], 1)
    tally = {}
    for b, c in zip(f4, fc):
        tally.setdefault(b, {}).setdefault(c, 0); tally[b][c] += 1
    major = {b: max(d, key=d.get) for b, d in tally.items()}
    scramble = lambda cs: np.stack([np.array([(hash((7, j, b)) & 0x7fffffff) % rows_n for b in cs]) for j in range(rings)], 1)
    planted = lambda cs: np.stack([np.array([((hash((3, j, major[b], b[-1:])) if b in major else hash((7, j, b))) & 0x7fffffff) % rows_n for b in cs]) for j in range(rings)], 1)
    addresses = {"read": (by_read(fx), by_read(hx)), "scramble4": (scramble(f4), scramble(h4)), "planted": (planted(f4), planted(h4))}
    uni = np.bincount(fc, minlength=A).astype(np.float64) + 1.0; uni /= uni.sum()
    # The settled places of the held stretches.
    settled = np.zeros(len(hr), bool)
    for sl in sorted(set(k[0] for k in key)):
        idx = [i for i, k in enumerate(key) if k[0] == sl and ht[i] >= 5]
        want = set(hs[hr[i]][ht[i] - 5:ht[i]] for i in idx)
        data = open(f"{store}/DOCS_{sl}.bin", "rb").read(train_n)
        ctxs = {}
        for i in range(5, len(data)):
            k5 = data[i - 5:i]
            if k5 in want:
                d = ctxs.setdefault(k5, {}); d[data[i]] = d.get(data[i], 0) + 1
        for i in idx:
            cn = ctxs.get(hs[hr[i]][ht[i] - 5:ht[i]])
            if not cn:
                continue
            tot, kinds = sum(cn.values()), len(cn)
            p = np.array(list(cn.values())) / (tot + kinds)
            h = -(p * np.log(p)).sum() - (kinds / (tot + kinds)) * math.log(kinds / (tot + kinds) / 256)
            settled[i] = h < 0.25
    stretch = np.array([k[1] for k in key])
    choose, report = have & (stretch % 2 == 0), have & (stretch % 2 == 1)
    def line(name, p):
        for label, sel in (("all", report), ("settled", report & settled)):
            code = -np.log(np.maximum(p[sel], 1e-12))
            print(f"READROWS address={name} set={label} places={sel.sum()} code={code.mean():.4f} mass={p[sel].mean():.3f} sure={(code < 0.1).mean():.3f}", flush=True)
    line("her_face", p_her)
    for name, (fa, ha) in addresses.items():
        tables = [np.zeros((rows_n, A)) for _ in range(rings)]
        for j in range(rings):
            np.add.at(tables[j], (fa[:, j], fc), 1.0)
        p_rows = np.empty(len(hc))
        for a in range(0, len(hc), 16384):
            z = slice(a, a + 16384)
            n = np.min(np.stack([tables[j][ha[z, j]] for j in range(rings)]), 0)
            tot, kinds = n.sum(1, keepdims=True), (n > 0).sum(1, keepdims=True)
            face = (n + np.maximum(kinds, 1) * uni) / (tot + np.maximum(kinds, 1))
            p_rows[z] = face[np.arange(len(face)), hc[z]]
        best = min((0.0, 0.02, 0.05, 0.1, 0.2, 0.3, 0.5), key=lambda l: -np.log(np.maximum((1 - l) * p_her[choose] + l * p_rows[choose], 1e-12)).mean())
        print(f"READROWS address={name} rings={rings} rows={rings * rows_n} lambda={best}", flush=True)
        line(f"{name}_mixed", (1 - best) * p_her + best * p_rows)
        line(f"{name}_alone", p_rows)
    print(f"READROWS fit_places={len(fr)} held_places={len(hr)} with_her_code={int(have.sum())} settled={int((have & settled).sum())}", flush=True)

main()
