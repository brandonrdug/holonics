#!/usr/bin/env -S python3 -I
"""The founding law's premise, read on the engine's own rows (the lead, November 17).

Usage: founding_ruler.py targets DIR

DIR is a `read-tension … all` (or `shares`) directory of short sums `a + b = v`, every answer place opened alone.

The law read here: a ring's keys are located by closing the menu of one head's rows (`tools/loop_closure_ruler.py closure`, the fitting
half, head 0 at tick 0). With the keys, every open row has a closure target: the share each source would hold if the row were weighed by
where its menu closes with the written symbol,

    q_s ∝ p_s · Σ_(s' ≠ s) p_s' · c(u_s, u_s', x),      c(u, u', x) = (1 + Σ_e Re K_e(u) K_e(u') conj K_e(x)) / (E + 1),

`c` being the ring law's likelihood of the written symbol given the pair (one where the pair closes on it and zero elsewhere, with true
characters; a symbol off the ring has no key and closes nothing). `Z = Σ_s Σ_(s'≠s) p_s p_s' c` is the row's closure mass, and a place's
rows share its pull by `Z`.

`targets` reads, on the held half and with the table's labels used only to score:
  (1) the mass the target puts on the two aligned operand digits, beside the mass the row holds there now, by head, tick and column;
  (2) the written digit's code in nats under the keyed pair product `E_e = Y_e² − Σ p_s² K_e(u_s)²` read back through the keys
      (logit of a ring symbol `x`: `g · Re Σ_e conj K_e(x) E_e`, `g` fitted on the fitting half), for the row as it is, for the row
      moved to its target, and for a row holding the aligned digits at a half each;
and a planted control: the same reading with the sources' symbols dealt at random within each record, where no target may land.

A ruler: floats, labels and a table's layout, on the host, outside the machine."""
import hashlib
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import loop_closure_ruler as lc


def half_of(lab):
    return hashlib.sha256(f"half:{lab}".encode()).digest()[0] % 2


def read_rows(d):
    """Every shares line: (label, place, tick, head, site, [(source site, share)])."""
    out = []
    for line in open(os.path.join(d, "shares.tsv")):
        f = line.rstrip("\n").split("\t")
        src = [(int(j), int(p) / 1e6) for j, p, *_ in (e.split(":") for e in f[5].split())] if len(f) > 5 and f[5] else []
        out.append((f[0], int(f[1]), int(f[2]), int(f[3]), int(f[4]), src))
    return out


def aligned(label, site):
    """The column of an answer site (from the answer's end) and the sites of the operands' digits in that column (None where absent)."""
    _, _, _, a, b, v = label.split(":")
    at_b = len(a) + 3
    at_v = at_b + len(b) + 3
    c = len(v) - 1 - (site - at_v)
    if c < 0 or c >= len(v):
        return None
    return c, (len(a) - 1 - c if c < len(a) else None), (at_b + len(b) - 1 - c if c < len(b) else None)


def locate_keys(rows, head=0, tick=0):
    symbols = sorted({ch for r in rows for ch in lc.text_of(r[0])})
    index = {ch: i for i, ch in enumerate(symbols)}
    m = len(symbols)
    menu = np.zeros((m, m, m))
    for lab, _, tk, h, site, src in rows:
        if h != head or tk != tick or half_of(lab) != 0:
            continue
        text = lc.text_of(lab)
        xi = index[text[site]]
        for i1, (j1, p1) in enumerate(src):
            for i2, (j2, p2) in enumerate(src):
                if i1 != i2:
                    menu[index[text[j1]], index[text[j2]], xi] += p1 * p2
    found, _ = lc.closure(menu, symbols)
    keys = np.array([lam for _, lam in found])
    return symbols, index, keys


def nats(logits, x):
    z = logits - logits.max()
    return float(np.log(np.exp(z).sum()) - z[x])


def targets(d, deal=False, seed=5):
    rows = read_rows(d)
    symbols, index, keys = locate_keys(rows)
    e = len(keys)
    member = np.abs(keys).mean(axis=0) > 0.5
    ring = [i for i in range(len(symbols)) if member[i]]
    print(f"FOUND_KEYS eigenvectors={e} ring={''.join(symbols[i] for i in ring)!r} dealt={deal}")
    rng = np.random.default_rng(seed)
    kernel = lambda u, w, x: (1.0 + (keys[:, u] * keys[:, w] * np.conj(keys[:, x])).real.sum()) / (e + 1) if member[u] and member[w] and member[x] else 0.0
    acc = {}
    feats = {}
    for lab, place, tk, h, site, src in rows:
        al = aligned(lab, site)
        if al is None or not src:
            continue
        c, sa, sb = al
        text = lc.text_of(lab)
        x = index[text[site]]
        us = [index[text[j]] for j, _ in src]
        if deal:
            us = list(rng.permutation(us))
        ps = np.array([p for _, p in src])
        k = len(src)
        cm = np.array([[kernel(us[i], us[j], x) if i != j else 0.0 for j in range(k)] for i in range(k)])
        cm = np.maximum(cm, 0.0)
        w = ps[:, None] * ps[None, :] * cm
        z = w.sum()
        q = w.sum(axis=1) / z if z > 0 else ps
        col = "units" if c == 0 else "upper"
        both = sa is not None and sb is not None
        key = (h, tk, col)
        a = acc.setdefault(key, [0, 0.0, 0.0, 0.0])
        if both and half_of(lab) == 1:
            on = [i for i, (j, _) in enumerate(src) if j in (sa, sb)]
            a[0] += 1
            a[1] += ps[on].sum()
            a[2] += q[on].sum()
            a[3] += z
        if both:
            ku = keys[:, us]
            def pair(p):
                t = ku * p[None, :]
                return t.sum(axis=1) ** 2 - (t**2).sum(axis=1)
            ideal = np.array([0.5 if j in (sa, sb) else 0.0 for j, _ in src])
            feats.setdefault(key, []).append((half_of(lab), x, pair(ps), pair(q), pair(ideal)))
    print("FOUND_TARGET head tick column held_rows share_on_aligned_now share_on_aligned_at_target closure_mass")
    for key in sorted(acc):
        a = acc[key]
        if a[0]:
            print(f"FOUND_TARGET {key[0]} {key[1]} {key[2]} {a[0]} {a[1] / a[0]:.4f} {a[2] / a[0]:.4f} {a[3] / a[0]:.5f}")
    print("FOUND_WRITE head tick column held_rows | nats of the written digit among the ring: flat, row_now, row_at_target, aligned_halves (gain fitted on the fitting half)")
    back = np.conj(keys[:, ring]).T  # [ring symbol][eigenvector]
    for key in sorted(feats):
        rowsf = feats[key]
        res = []
        for which in (2, 3, 4):
            best = None
            for g in (0.5, 1, 2, 4, 8, 16, 32):
                fit = np.mean([nats(g * (back @ r[which]).real, ring.index(r[1])) for r in rowsf if r[0] == 0 and r[1] in ring])
                if best is None or fit < best[0]:
                    best = (fit, g)
            held = [nats(best[1] * (back @ r[which]).real, ring.index(r[1])) for r in rowsf if r[0] == 1 and r[1] in ring]
            res.append((np.mean(held), best[1], len(held)))
        print(f"FOUND_WRITE {key[0]} {key[1]} {key[2]} {res[0][2]} | {np.log(len(ring)):.3f} {res[0][0]:.3f}(g={res[0][1]}) {res[1][0]:.3f}(g={res[1][1]}) {res[2][0]:.3f}(g={res[2][1]})", flush=True)


def main():
    if len(sys.argv) < 3 or sys.argv[1] != "targets":
        sys.exit(__doc__)
    targets(sys.argv[2])
    print("FOUND_PLANTED the same reading with each record's source symbols dealt at random")
    targets(sys.argv[2], deal=True)


if __name__ == "__main__":
    main()
