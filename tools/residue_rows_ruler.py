#!/usr/bin/env -S python3 -I
"""A ruler of the premise of rows at the residue the carry circles compose (the lead, November 19; the frontier record §23).

`read-strand-states ... past carries` writes, for each known site of a passage, the carried product before it, `Q(t − 1)`, on every
sixteenth carry circle (`carries.i32`, the written circles' real parts then imaginary, on `2^(−16)`). A ring of period P read on a
circle gives a site the residue `floor(P · arg Q / 2π)`. Rows held at a residue are fitted on the fitting half (each row counts the
symbols met at the sites that stand at it) and read on the reading half, with a ring's counts combined across rings by their least
(a symbol's count is the least its rings' rows hold, as `ring_rows_ruler.py`), backing off to the count of the two places before by
Witten-Bell. Beside it, at the same rows: an address that is a scramble of the octets before the site (`ring_rows_ruler.py`'s form), and
the count of two places before alone. Each is read over all places and at the places a count of five places fitted on the first
TRAIN octets of a slice's documents expects under a quarter of a nat (the settled places, §21): nats a place, the mean mass on the
arriving symbol and the share of places paying under 0.1 nats (sure). Where the circles' address is located, contexts that continue
alike share a residue and its rows read under the scramble's at equal rows; where it is not, they read as the scramble does.
A planted control in the same run: an address located by construction, the symbol the fitting half meets most often after the four
octets before the site (with the octet before it, so a row is a continuation and its last octet), folded onto the same rings, the
scramble's where the four octets were never met; it must read under the scramble at the settled places for the instrument to tell a
located address from a scramble at all.
Outside the machine; counts and floats only.

Usage: residue_rows_ruler.py STORE CODEC TRAIN FIT_DIR READ_DIR RINGS PERIOD [CIRCLES]
  RINGS: how many rings; PERIOD: the first ring's period (each next ring the next prime above the one before); CIRCLES: comma list of
  the written circles' indices to read as rings (default the first RINGS spread over the written ones)."""
import sys, math, numpy as np

LN2 = math.log(2)

def primes_from(p, n):
    out = []
    while len(out) < n:
        p += 1
        if all(p % d for d in range(2, int(p ** 0.5) + 1)):
            out.append(p)
    return out

def load(d):
    dims = dict(l.split("\t") for l in open(f"{d}/dims.tsv").read().split("\n") if l)
    w = int(dims["written"])
    rows = np.loadtxt(f"{d}/rows.tsv", dtype=object, delimiter="\t", comments=None)
    r, g, t, c = rows[:, 0].astype(int), rows[:, 1], rows[:, 2].astype(int), rows[:, 3].astype(int)
    q = np.fromfile(f"{d}/carries.i32", dtype="<i4").reshape(-1, 2, w).astype(np.float64)
    phase = np.arctan2(q[:, 1, :], q[:, 0, :]) % (2 * math.pi)
    return r, np.array([s.split(":")[0] for s in g]), t, c, phase

def main():
    store, codec, train_n, fit_d, read_d, rings, period = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4], sys.argv[5], int(sys.argv[6]), int(sys.argv[7])
    head, used = open(codec).read().split("\n")[:2]
    void = int(head.split(" ")[2]); used = [int(x) for x in used.split(" ")]
    octet = lambda c: used[c] if c < void else used[c - 1]
    fr, fs, ft, fc, fp = load(fit_d)
    rr, rs, rt, rc, rp = load(read_d)
    w = fp.shape[1]
    circles = [int(x) for x in sys.argv[8].split(",")] if len(sys.argv) > 8 else [round(i * (w - 1) / max(rings - 1, 1)) for i in range(rings)]
    periods = [period] + primes_from(period, rings - 1)
    A = max(int(fc.max()), int(rc.max())) + 1
    def octets(r, t, c):
        # each place's octets before it in its row, as one bytes object a row
        seqs = {}
        for i in range(len(r)):
            seqs.setdefault(r[i], []).append(octet(c[i]))
        return {k: bytes(v) for k, v in seqs.items()}
    fseq, rseq = octets(fr, ft, fc), octets(rr, rt, rc)
    def before(seqs, r, t, k):
        return [seqs[r[i]][max(0, t[i] - k):t[i]] for i in range(len(r))]
    # The addresses: the circles' residues, a scramble of the 4 octets before, and the exact 4 octets before folded onto the rings (the planted control).
    def residues(phase):
        return np.stack([np.floor(phase[:, circles[j]] * periods[j] / (2 * math.pi)).astype(np.int64) % periods[j] for j in range(rings)], 1)
    def scrambled(ctx, salt):
        return np.stack([np.array([(hash((salt, j, b)) & 0x7fffffff) % periods[j] for b in ctx]) for j in range(rings)], 1)
    fctx4, rctx4 = before(fseq, fr, ft, 4), before(rseq, rr, rt, 4)
    tally = {}
    for b, c in zip(fctx4, fc):
        tally.setdefault(b, {}).setdefault(c, 0)
        tally[b][c] += 1
    major = {b: max(d, key=d.get) for b, d in tally.items()}
    def planted(ctx):
        return np.stack([np.array([((hash((3, j, major[b], b[-1:])) if b in major else hash((7, j, b))) & 0x7fffffff) % periods[j] for b in ctx]) for j in range(rings)], 1)
    fctx2, rctx2 = before(fseq, fr, ft, 2), before(rseq, rr, rt, 2)
    # [G-1119-4's second reading] A joint address: each ring's row is the half-planes of the carried products on ten written circles
    # drawn for that ring (a residue of the carried vector's direction across circles, not of one circle's phase), folded onto its period.
    draw = np.random.default_rng(1119)
    subsets = [draw.choice(w, size=min(10, w), replace=False) for _ in range(rings)]
    def joint(phase):
        return np.stack([((phase[:, subsets[j]] < math.pi).astype(np.int64) << np.arange(len(subsets[j]))).sum(1) % periods[j] for j in range(rings)], 1)
    addresses = {"circles": (residues(fp), residues(rp)), "joint": (joint(fp), joint(rp)), "scramble4": (scrambled(fctx4, 7), scrambled(rctx4, 7)), "planted": (planted(fctx4), planted(rctx4))}
    # The back-off: a count of the two places before on the fitting half (Witten-Bell to the octets' count).
    uni = np.bincount(fc, minlength=A).astype(np.float64) + 1.0
    uni /= uni.sum()
    two = {}
    for b, c in zip(fctx2, fc):
        two.setdefault(b, np.zeros(A))[c] += 1
    def backoff(ctx):
        out = np.empty((len(ctx), A))
        for i, b in enumerate(ctx):
            n = two.get(b)
            if n is None:
                out[i] = uni
            else:
                tot, kinds = n.sum(), (n > 0).sum()
                out[i] = (n + kinds * uni) / (tot + kinds)
        return out
    CHUNK = 16384
    # The settled places: a count of five fitted on the first TRAIN octets of each slice's documents, its face's entropy under 0.25 nats.
    settled = np.zeros(len(rr), bool)
    for sl in sorted(set(rs)):
        data = open(f"{store}/DOCS_{sl}.bin", "rb").read(train_n)
        ctxs = {}
        idx = np.where(rs == sl)[0]
        want = set(rseq[rr[i]][max(0, rt[i] - 5):rt[i]] for i in idx if rt[i] >= 5)
        for i in range(5, len(data)):
            k = data[i - 5:i]
            if k in want:
                ctxs.setdefault(k, {}).setdefault(data[i], 0)
                ctxs[k][data[i]] += 1
        for i in idx:
            if rt[i] < 5:
                continue
            cn = ctxs.get(rseq[rr[i]][rt[i] - 5:rt[i]])
            if not cn:
                continue
            tot = sum(cn.values()); kinds = len(cn)
            p = np.array([v for v in cn.values()]) / (tot + kinds)
            h = -(p * np.log(p)).sum() - (kinds / (tot + kinds)) * math.log(kinds / (tot + kinds) / 256)
            settled[i] = h < 0.25
    keep = rt >= 5
    pb = np.empty(len(rc))
    for a in range(0, len(rc), CHUNK):
        b = backoff(rctx2[a:a + CHUNK])
        pb[a:a + CHUNK] = b[np.arange(len(b)), rc[a:a + CHUNK]]
    def read(name, fa, ra):
        tables = [np.zeros((periods[j], A)) for j in range(rings)]
        for j in range(rings):
            np.add.at(tables[j], (fa[:, j], fc), 1.0)
        p = np.empty(len(rc))
        for a in range(0, len(rc), CHUNK):
            z = slice(a, a + CHUNK)
            n = np.min(np.stack([tables[j][ra[z, j]] for j in range(rings)]), 0)
            tot, kinds = n.sum(1, keepdims=True), (n > 0).sum(1, keepdims=True)
            base = backoff(rctx2[z])
            face = np.where(tot > 0, (n + kinds * base) / np.maximum(tot + kinds, 1), base)
            p[z] = face[np.arange(len(face)), rc[z]]
        for label, sel in (("all", keep), ("settled", keep & settled)):
            code = -np.log(p[sel]); 
            print(f"RESIDUE address={name} rings={rings} periods={'/'.join(map(str, periods))} rows={sum(periods)} set={label} places={sel.sum()} code={code.mean():.4f} mass={p[sel].mean():.3f} sure={(code < 0.1).mean():.3f}", flush=True)
    for label, sel in (("all", keep), ("settled", keep & settled)):
        code = -np.log(pb[sel])
        print(f"RESIDUE address=two_places_alone set={label} places={sel.sum()} code={code.mean():.4f} mass={pb[sel].mean():.3f} sure={(code < 0.1).mean():.3f}", flush=True)
    print(f"RESIDUE circles_read={','.join(map(str, circles))} of {w} written; fit places={len(fr)} read places={len(rr)} settled={int((keep & settled).sum())}", flush=True)
    for name, (fa, ra) in addresses.items():
        read(name, fa, ra)

main()
