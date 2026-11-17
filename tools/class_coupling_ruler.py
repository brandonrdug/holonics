#!/usr/bin/env -S python3 -I
"""A ruler: the classes' coupling through the tension their arrivals leave (the lead, November 17; the October tower's location of the
ring of ten, its record of October 24, taken on the engine).

Usage: class_coupling_ruler.py DIR [TICK [planted]]

On a `read-tension … all` directory (every site of every region written), at one tick: with `f` a site's opening chart less its
class's mean chart (the state the symbol arrives into) and `λ` the covector its tick's reverse receives, less its class's mean, `S = Σ f fᵀ`, `W = S⁻¹ Σ f λᵀ` (the state's common read), `λ' = λ − Wᵀ f`, and for each class `u`
of the written sites `M_u = Σ_(sites of u) f λ'ᵀ`. With `Y = Σ λ' λ'ᵀ`,

    K_uv = tr(S⁻¹ M_u Y⁻¹ M_vᵀ) / √(n_u n_v).

No label of the record's arithmetic enters: a site contributes under its own symbol alone. Prints `K`'s leading modes over every class
met (which symbols each stands on), then the ten digits' block: each mode's eigenvalue and its power on the characters
`χ_k(d) = e^(2πikd/10)` of the digits' order, `k = 0 … 5` (`k` and `10 − k` together). A ring of ten located from the tension shows
modes that each stand on one character, the first character first. The two moments of a pair are taken on two halves of the records
(a class's own noise otherwise stands on the diagonal and the modes read as single symbols, the first run's result), and `K` is
scaled by `N²/D`. With `planted`, the digits' sites are given one drawn map of the state turned by the digit's first character, at a
tenth of their covector's power, on the same shapes: the ruler's null is read only beside that.
"""
import hashlib
import os
import sys

import numpy as np


def main():
    d = sys.argv[1]
    tick = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    planted = len(sys.argv) > 3 and sys.argv[3] == "planted"
    dims = dict(line.split("\t") for line in open(os.path.join(d, "dims.tsv")).read().splitlines())
    dw = int(dims["lambda"])
    rows = [line.split("\t") for line in open(os.path.join(d, "rows.tsv")).read().splitlines()]
    n = len(rows)
    lam = np.memmap(os.path.join(d, "lambda.i64"), dtype="<i8", mode="r", shape=(n, dw))
    chart = np.memmap(os.path.join(d, "chart.i32"), dtype="<i4", mode="r", shape=(n, dw))
    keep, symbols = [], []
    for i, r in enumerate(rows):
        if int(r[2]) != tick or r[5] == "1":
            continue
        _, _, op, a, b, v = r[0].split(":")
        text = f"{a} {op} {b} = {v}\n"
        s = int(r[4])
        if s < len(text):
            keep.append(i)
            symbols.append(text[s])
    keep = np.array(keep)
    f = np.asarray(chart[keep], dtype=np.float64) / 2.0**16
    y = np.asarray(lam[keep], dtype=np.float64) / 2.0**24
    # The state a symbol arrives into: the site's chart less its own class's mean chart, and the covector less its class's mean. With
    # the chart itself a class's moment is its own mean chart's, the classes' means are near orthogonal, and K reads diagonal whatever
    # the tension holds (the first form of this ruler, which did not return a planted ring).
    sym0 = np.array(symbols)
    for u in set(symbols):
        sel = sym0 == u
        f[sel] -= f[sel].mean(axis=0)
        y[sel] -= y[sel].mean(axis=0)
    s_mat = f.T @ f
    s_mat += 1e-8 * np.trace(s_mat) / dw * np.eye(dw)
    w = np.linalg.solve(s_mat, f.T @ y)
    yr = y - f @ w
    y_mat = yr.T @ yr
    y_mat += 1e-8 * np.trace(y_mat) / dw * np.eye(dw)
    classes = sorted(set(symbols))
    sym = np.array(symbols)
    if planted:
        # A planted law on the same shapes: at the digits' sites, one drawn map of the state turned by the digit's first character,
        # at a tenth of the covector's own power. The ruler has to return it before a null of its own is read.
        rng = np.random.default_rng(0)
        dig = np.array([c.isdigit() for c in symbols])
        ang = 2 * np.pi * np.array([int(c) if c.isdigit() else 0 for c in symbols]) / 10
        a_re, a_im = rng.standard_normal((dw, dw)), rng.standard_normal((dw, dw))
        ring = (np.cos(ang)[:, None] * (f @ a_re) - np.sin(ang)[:, None] * (f @ a_im)) * dig[:, None]
        yr = yr + ring * np.sqrt(0.1 * (yr[dig] ** 2).sum() / (ring**2).sum())
        y_mat = yr.T @ yr + 1e-8 * np.trace(yr.T @ yr) / dw * np.eye(dw)
    s_inv, y_inv = np.linalg.inv(s_mat), np.linalg.inv(y_mat)
    # Two halves of the records, so a class's own noise does not stand on the diagonal: K_uv pairs class u's moment on one half with
    # class v's on the other.
    half = np.array([hashlib.sha256(rows[i][0].encode()).digest()[0] % 2 for i in keep])
    m, count = {}, {}
    for u in classes:
        sel = sym == u
        count[u] = int(sel.sum())
        m[u] = [f[sel & (half == h)].T @ yr[sel & (half == h)] for h in (0, 1)]
    k = np.array([[np.trace(s_inv @ m[u][0] @ y_inv @ m[v][1].T) * 4 / np.sqrt(count[u] * count[v]) for v in classes] for u in classes])
    k = k * len(keep) ** 2 / dw
    print(f"COUPLING_READ sites={len(keep)} tick={tick} planted={int(planted)} classes={len(classes)} " + " ".join(f"{repr(u)}:{count[u]}" for u in classes))
    vals, vecs = np.linalg.eigh((k + k.T) / 2)
    order = np.argsort(-vals)
    print("COUPLING_ALL mode eigenvalue weight_on_digits leading_symbols")
    digits = [classes.index(str(dd)) for dd in range(10) if str(dd) in classes]
    for j in order[:8]:
        v = vecs[:, j]
        top = np.argsort(-np.abs(v))[:4]
        print(f"COUPLING_ALL {list(order).index(j) + 1} {vals[j]:.4f} {(v[digits] ** 2).sum():.3f} " + " ".join(f"{repr(classes[t])}:{v[t]:+.2f}" for t in top))
    if len(digits) == 10:
        kd = k[np.ix_(digits, digits)]
        vals, vecs = np.linalg.eigh((kd + kd.T) / 2)
        order = np.argsort(-vals)
        chi = np.exp(2j * np.pi * np.outer(np.arange(6), np.arange(10)) / 10)
        print("COUPLING_DIGITS mode eigenvalue power_on_k0 k1 k2 k3 k4 k5")
        for rank, j in enumerate(order, 1):
            v = vecs[:, j]
            p = np.abs(chi @ v) ** 2 / 10
            p[1:5] *= 2
            print(f"COUPLING_DIGITS {rank} {vals[j]:.4f} " + " ".join(f"{x:.3f}" for x in p))


if __name__ == "__main__":
    main()
