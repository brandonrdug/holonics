#!/usr/bin/env -S python3 -I
"""The founding law's premise, read on the engine's own rows (the lead, November 17).

Usage: founding_ruler.py targets DIR
       founding_ruler.py solve DIR CODEC OUT STEP[,STEP…] [KEY_MODULUS [KEYS_DIR]]
       founding_ruler.py step DIR CODEC CLOSED_IN CLOSED_OUT ETA ETA_LEG
       founding_ruler.py mixture DIR CODEC KEYS_DIR
       founding_ruler.py codes DIR [BEFORE_DIR]

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

`solve` writes the closed characters for the engine (`athena found-closed`): the keys by class through CODEC (a ring member's eigenvalue at
unit modulus on `2^(−16)`, zero off the ring) and the return `W_K = −STEP · B`, `B` the least-squares map from every head's keyed pair
products to the covector at the open place on the fitting half (the part of the tension the products explain). The step is read, never
set: one file a step is written, each founded state's code is read on the fitting half (`codes`), and the step that codes it lowest is
the founding's; the held half is reported at that step.

A ruler: floats, labels and a table's layout, on the host, outside the machine."""
import hashlib
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import loop_closure_ruler as lc


def half_of(lab):
    """A record's half, by its sum: a label's first six fields (a table may add a seventh, the text past the answer)."""
    return hashlib.sha256(f"half:{':'.join(lab.split(':')[:6])}".encode()).digest()[0] % 2


def text_of(lab):
    """A label's text: the sum's record, then the text past its answer where the label carries it as a seventh field."""
    parts = lab.split(":")
    return lc.text_of(":".join(parts[:6])) + (parts[6] if len(parts) > 6 else "")


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
    symbols = sorted({ch for r in rows for ch in text_of(r[0])})
    index = {ch: i for i, ch in enumerate(symbols)}
    m = len(symbols)
    menu = np.zeros((m, m, m))
    for lab, _, tk, h, site, src in rows:
        if h != head or tk != tick or half_of(lab) != 0:
            continue
        text = text_of(lab)
        xi = index[text[site]]
        for i1, (j1, p1) in enumerate(src):
            for i2, (j2, p2) in enumerate(src):
                if i1 != i2:
                    menu[index[text[j1]], index[text[j2]], xi] += p1 * p2
    found, _ = lc.closure(menu, symbols)
    keys = np.array([lam for _, lam in found])
    # The ring's members: the symbols the passage wrote at the places (the closure's functions live on them, and a co-source is taken among
    # them), each key its eigenvalue at unit modulus. A diffuse row dilutes every member's eigenvalue (0.36 to 0.73 on lap 94's rows) and a
    # mark beside a number closes weakly as the ring's identity (0.30 there), so a modulus does not say who is on the ring. On rows where
    # every symbol is written the eigenvectors' support has to decide, which this ruler does not read yet.
    member = menu.sum(axis=(0, 1)) > 0
    keys = np.where(member[None, :], keys / np.maximum(np.abs(keys), 1e-12), 0.0)
    return symbols, index, keys, member


def nats(logits, x):
    z = logits - logits.max()
    return float(np.log(np.exp(z).sum()) - z[x])


def targets(d, deal=False, seed=5):
    rows = read_rows(d)
    symbols, index, keys, member = locate_keys(rows)
    e = len(keys)
    ring = [i for i in range(len(symbols)) if member[i]]
    print(f"FOUND_KEYS eigenvectors={e} ring={''.join(symbols[i] for i in ring)!r} dealt={deal}")
    rng = np.random.default_rng(seed)
    kernel = lambda u, w, x: (1.0 + (keys[:, u] * keys[:, w] * np.conj(keys[:, x])).real.sum()) / (e + 1) if member[u] and member[w] and member[x] else 0.0
    acc = {}
    feats = {}
    for lab, _, tk, h, site, src in rows:
        al = aligned(lab, site)
        if al is None or not src:
            continue
        c, sa, sb = al
        text = text_of(lab)
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


def open_rows(d):
    """A `read-tension` directory's open rows in order (a row a place and tick): labels, places, ticks, the covector at the place and the
    place's opening chart, with the shares lines grouped a row. Both layouts: `all` (every site, the open one flagged) and `shares`."""
    dims = dict(line.split("\t") for line in open(os.path.join(d, "dims.tsv")).read().splitlines())
    dw = int(dims["lambda"])
    table = [line.split("\t") for line in open(os.path.join(d, "rows.tsv")).read().splitlines()]
    opened = np.flatnonzero(np.array([len(r) < 6 or r[5] == "1" for r in table]))
    lam = np.asarray(np.memmap(os.path.join(d, "lambda.i64"), dtype="<i8", mode="r", shape=(len(table), dw))[opened]).astype(np.float64) / 2.0**24
    chart = np.asarray(np.memmap(os.path.join(d, "chart.i32"), dtype="<i4", mode="r", shape=(len(table), dw))[opened]).astype(np.float64) / 2.0**16
    rows = read_rows(d)
    heads = len(rows) // len(opened)
    assert heads * len(opened) == len(rows), "shares.tsv does not hold one line a head for every open row"
    meta = [(table[i][0], int(table[i][1]), int(table[i][2])) for i in opened]
    for n in range(0, len(rows), heads):
        assert rows[n][:3] == meta[n // heads], "shares.tsv is not in the rows' order"
    return dw, heads, meta, lam, chart, rows


def codec_classes(codec):
    with open(codec) as f:
        void = int(f.readline().split()[2])
        units = [int(v) for v in f.readline().split()]
    return {u: (k if k < void else k + 1) for k, u in enumerate(units)}, len(units) + 1


def products(rows, heads, n_rows, key_of, e):
    """Every head's keyed pair product at each open row (`[row][heads·2E]`, a head's real parts then its imaginary parts)."""
    feats = np.zeros((n_rows, heads * 2 * e))
    for n, (lab, _, _, h, _, src) in enumerate(rows):
        if not src:
            continue
        text = text_of(lab)
        t = key_of(text, [j for j, _ in src]) * np.array([p for _, p in src])[None, :]
        pair = t.sum(axis=1) ** 2 - (t**2).sum(axis=1)
        feats[n // heads, h * 2 * e : h * 2 * e + e] = pair.real
        feats[n // heads, h * 2 * e + e : (h + 1) * 2 * e] = pair.imag
    return feats


def write_closed(path, e, kwords, leg, bias, w):
    out = [np.rint(leg * 2.0**24), np.rint(bias * 2.0**16), np.rint(w * 2.0**24)]
    assert max(np.abs(o).max() for o in out) < 2**31, "a word past its 32 bits"
    with open(path, "xb") as f:
        f.write(np.array([e], dtype="<i4").tobytes())
        f.write(kwords.astype("<i4").tobytes())
        for o in out:
            f.write(o.astype("<i4").tobytes())


def least_squares(x, y):
    gram = x.T @ x
    return np.linalg.solve(gram + 1e-6 * np.trace(gram) / gram.shape[0] * np.eye(gram.shape[0]), x.T @ y).T


def solve(d, codec, out, steps, gain=1.0, keys_dir=None):
    """The closed characters' keys, leg and return, written for `athena found-closed` (see the module's text). `steps` is a comma list of
    step sizes; one file `OUT.<k>.closed` is written a step. The site's leg is founded at one. The keys are closed on KEYS_DIR's rows where
    given (a directory whose open places are a ring's symbols alone), DIR's otherwise."""
    dw, heads, meta, lam, _, rows = open_rows(d)
    symbols, index, keys, member = locate_keys(read_rows(keys_dir) if keys_dir else rows)
    for ch in {c for m in meta for c in text_of(m[0])} - set(index):
        index[ch] = len(member)
        member = np.append(member, False)
        keys = np.hstack([keys, np.zeros((len(keys), 1))])
    e = len(keys)
    feats = products(rows, heads, len(meta), lambda text, js: keys[:, [index[text[j]] for j in js]], e)
    fit = np.array([half_of(m[0]) == 0 for m in meta])
    b = least_squares(feats[fit], lam[fit])  # [D][heads·2E]
    pred = feats[~fit] @ b.T
    share = 1.0 - ((lam[~fit] - pred) ** 2).sum() / (lam[~fit] ** 2).sum()
    print(f"SOLVE_RETURN rows={len(meta)} fit={int(fit.sum())} heads={heads} characters={e} covector_share_removed_held={share:.4f} rms_covector={np.sqrt((lam**2).mean()):.3e} rms_predicted={np.sqrt((pred**2).mean()):.3e}")
    cls, alphabet = codec_classes(codec)
    kw = np.zeros((alphabet, 2 * e))
    for ch, i in index.items():
        if member[i]:
            kw[cls[ord(ch)], :e] = keys[:, i].real
            kw[cls[ord(ch)], e:] = keys[:, i].imag
    # A key at modulus `gain`: the products then stand `gain²` higher and the return's entries as much lower, inside their 32-bit words.
    kwords = np.rint(gain * kw * 2.0**16)
    print(f"SOLVE_KEYS ring={''.join(ch for ch, i in sorted(index.items(), key=lambda t: t[1]) if member[i])!r} classes={[cls[ord(ch)] for ch, i in sorted(index.items(), key=lambda t: t[1]) if member[i]]}")
    cols = heads * 2 * e
    leg, bias = np.zeros((cols, dw)), np.zeros(cols)
    for h in range(heads):
        bias[h * 2 * e : h * 2 * e + e] = 1.0
    for k, step in enumerate(steps):
        w = -step * b / gain**2
        path = f"{out}.{k}.closed"
        write_closed(path, e, kwords, leg, bias, w)
        print(f"SOLVE_WRITTEN {path} step={step:g} key_modulus={gain:g} largest_return={np.abs(w).max():.4f}")


def step(d, codec, closed_in, closed_out, eta, eta_leg):
    """One more step of the solve: DIR is a `read-tension` directory (`all` or `shares`) of the state founded with CLOSED_IN (the ruler's
    reverse, the closed characters' return held constant). With CLOSED_IN's own keys and leg the products `c = E γ` are formed at each open
    row. The return moves `−ETA` times the least-squares map from `c` to the covector at the place; the leg moves `−ETA_LEG` times the
    least-squares map from the place's opening chart to the leg's covector, `conj(E) (W_Kᵀ λ)`. Both on the fitting half."""
    dw, heads, meta, lam, chart, rows = open_rows(d)
    words = np.fromfile(closed_in, dtype="<i4")
    e = int(words[0])
    cls, alphabet = codec_classes(codec)
    cols = heads * 2 * e
    at = 1 + alphabet * 2 * e
    kwords = words[1:at]
    kw = kwords.reshape(alphabet, 2 * e).astype(np.float64) / 2.0**16
    key = kw[:, :e] + 1j * kw[:, e:]
    leg = words[at : at + cols * dw].reshape(cols, dw).astype(np.float64) / 2.0**24
    bias = words[at + cols * dw : at + cols * (dw + 1)].astype(np.float64) / 2.0**16
    w = words[at + cols * (dw + 1) :].reshape(dw, cols).astype(np.float64) / 2.0**24
    feats = products(rows, heads, len(meta), lambda text, js: key[[cls[ord(text[j])] for j in js]].T, e)
    fit = np.array([half_of(m[0]) == 0 for m in meta])
    gamma = chart @ leg.T + bias  # [row][cols]
    re = np.concatenate([np.arange(h * 2 * e, h * 2 * e + e) for h in range(heads)])
    im = re + e
    c = np.zeros_like(feats)
    c[:, re] = feats[:, re] * gamma[:, re] - feats[:, im] * gamma[:, im]
    c[:, im] = feats[:, re] * gamma[:, im] + feats[:, im] * gamma[:, re]
    b = least_squares(c[fit], lam[fit])
    pred = c[~fit] @ b.T
    share = 1.0 - ((lam[~fit] - pred) ** 2).sum() / (lam[~fit] ** 2).sum()
    dc = lam @ w  # [row][cols], the products' covector
    dg = np.zeros_like(dc)
    dg[:, re] = feats[:, re] * dc[:, re] + feats[:, im] * dc[:, im]
    dg[:, im] = -feats[:, im] * dc[:, re] + feats[:, re] * dc[:, im]
    x1 = np.hstack([chart, np.ones((len(meta), 1))])
    bg = least_squares(x1[fit], dg[fit])  # [cols][D + 1]
    w_new = w - eta * b
    leg_new, bias_new = leg - eta_leg * bg[:, :dw], bias - eta_leg * bg[:, dw]
    write_closed(closed_out, e, kwords, leg_new, bias_new, w_new)
    print(f"STEP rows={len(meta)} fit={int(fit.sum())} covector_share_removed_held={share:.4f} rms_covector={np.sqrt((lam**2).mean()):.3e} eta={eta:g} eta_leg={eta_leg:g} largest_return={np.abs(w_new).max():.3f} rms_leg_row={np.sqrt((leg_new**2).mean()):.4f} leg_bias_mean_real={bias_new[re].mean():.3f}")


def kind_of(label, place):
    v = label.split(":")[5]
    c = len(v) - 1 - place
    return "units" if c == 0 else ("top" if place == 0 else ("middle" if c > 0 else ("line_feed" if c == -1 else "past")))


def mixture(d, codec, keys_dir, rounds=400, rate=0.05):
    """The closed face as a mixture, read on a `read-tension … shares` directory (see the module's text): the written symbol's code under
    the field's own face, and under that face mixed with each head's ring face at odds read from the place's last pair chart, the odds'
    rows fitted on the fitting half by ascent on the written symbol's likelihood. By kind of place, held half, nats a place."""
    dw, heads, meta, _, _, rows = open_rows(d)
    dims = dict(line.split("\t") for line in open(os.path.join(d, "dims.tsv")).read().splitlines())
    ticks = int(dims["ticks"])
    cls, alphabet = codec_classes(codec)
    symbols, index, keys, member = locate_keys(read_rows(keys_dir))
    e = len(keys)
    ring = [i for i in range(len(symbols)) if member[i]]
    ring_cls = np.array([cls[ord(symbols[i])] for i in ring])
    rk = keys[:, ring]  # [e][ring]
    n_places = len(meta) // ticks
    faces = np.fromfile(os.path.join(d, "faces.i64"), dtype="<i8").reshape(n_places, alphabet).astype(np.float64) / 2.0**20
    table = [line.split("\t") for line in open(os.path.join(d, "rows.tsv")).read().splitlines()]
    opened = np.flatnonzero(np.array([len(r) < 6 or r[5] == "1" for r in table]))
    read = np.asarray(np.memmap(os.path.join(d, "read.i32"), dtype="<i4", mode="r", shape=(len(table), dw))[opened]).astype(np.float64) / 2.0**16
    last = np.array([i for i, m in enumerate(meta) if m[2] == ticks - 1])
    assert len(last) == n_places
    x = np.hstack([read[last], np.ones((n_places, 1))])
    labels = [meta[i][0] for i in last]
    places = [meta[i][1] for i in last]
    written = np.array([cls[ord(text_of(l)[len(text_of(l)) - len(l.split(':')[5]) - 1 - (len(l.split(':')[6]) if len(l.split(':')) > 6 else 0) + pl])] for l, pl in zip(labels, places)])
    p_field = 2.0 ** (-faces[np.arange(n_places), written])
    # Each head's ring face at the written symbol and its member-pair mass, from the last tick's rows.
    r_at = np.zeros((n_places, heads))
    m2 = np.zeros((n_places, heads))
    pos = {int(c): k for k, c in enumerate(ring_cls)}
    where = {i: n for n, i in enumerate(last)}
    for n, (lab, _, tk, h, _, src) in enumerate(rows):
        if tk != ticks - 1 or not src:
            continue
        i = where[n // heads]
        text = text_of(lab)
        us = [index[text[j]] for j, _ in src]
        ps = np.array([p for _, p in src])
        mem = np.array([member[u] for u in us])
        if mem.sum() < 2:
            continue
        t = keys[:, [u for u in us if member[u]]] * ps[mem][None, :]
        pm = ps[mem]
        mass = pm.sum() ** 2 - (pm**2).sum()
        pair = t.sum(axis=1) ** 2 - (t**2).sum(axis=1)  # [e]
        dens = np.maximum((mass + (np.conj(rk) * pair[:, None]).real.sum(axis=0)) / (e + 1), 0.0)  # over the ring
        m2[i, h] = dens.sum()
        if int(written[i]) in pos:
            r_at[i, h] = dens[pos[int(written[i])]]
    fit = np.array([half_of(l) == 0 for l in labels])
    kinds = np.array([kind_of(l, pl) for l, pl in zip(labels, places)])

    def code(w):  # w: [heads][dw + 1], the odds' rows; the mixture's code of the written symbol
        z = np.clip(x @ w.T, -40, 40)
        odds = np.exp(z)
        wt = odds / (1.0 + odds.sum(axis=1, keepdims=True))
        p = (1.0 - (wt * m2).sum(axis=1)) * p_field + (wt * r_at).sum(axis=1)
        return -np.log(np.maximum(p, 1e-300)), wt, p

    def fit_rows(cols):
        w = np.zeros((heads, dw + 1))
        w[:, dw] = -3.0
        m_, v_ = np.zeros_like(w), np.zeros_like(w)
        for it in range(1, rounds + 1):
            _, wt, p = code(w)
            # d(−log p)/dz_h = −wt_h [(r_h − m2_h p_field) − Σ_k wt_k (r_k − m2_k p_field)] / p
            a = r_at - m2 * p_field[:, None]
            g_z = -wt * (a - (wt * a).sum(axis=1, keepdims=True)) / p[:, None]
            grad = (g_z[fit].T @ x[fit][:, cols]) / fit.sum()
            m_[:, cols] = 0.9 * m_[:, cols] + 0.1 * grad
            v_[:, cols] = 0.999 * v_[:, cols] + 0.001 * grad**2
            w[:, cols] -= rate * (m_[:, cols] / (1 - 0.9**it)) / (np.sqrt(v_[:, cols] / (1 - 0.999**it)) + 1e-8)
        return w

    base = -np.log(p_field)
    w_bias = fit_rows(np.array([dw]))
    w_full = fit_rows(np.arange(dw + 1))
    c_bias, c_full = code(w_bias)[0], code(w_full)[0]
    wt_full = code(w_full)[1].sum(axis=1)
    print(f"MIXTURE places={n_places} heads={heads} characters={e} last_tick={ticks - 1} fit={int(fit.sum())}")
    print("MIXTURE kind held_places | nats: field's_face  mixed_at_one_odds_a_head  mixed_at_odds_from_the_chart | mean_weight_on_the_ring_faces  member_pair_mass(head 0)")
    for kind in ("units", "middle", "top", "line_feed", "past", "every"):
        sel = (~fit) & ((kinds == kind) | (kind == "every"))
        if sel.sum():
            print(f"MIXTURE {kind} {int(sel.sum())} | {base[sel].mean():.4f} {c_bias[sel].mean():.4f} {c_full[sel].mean():.4f} | {wt_full[sel].mean():.3f} {m2[sel, 0].mean():.3f}")
    np.save(os.path.join(d, "mixture_rows.npy"), w_full)


def codes(d, base=None):
    """The written digit's code at each answer place of a `read-tension` directory, by column, on the held and the fitting half (nats a
    place, from `rows.tsv`'s code at tick 0), beside another directory's where given."""
    def read(path):
        acc = {}
        for line in open(os.path.join(path, "rows.tsv")):
            f = line.rstrip("\n").split("\t")
            if int(f[2]) != 0 or (len(f) > 5 and f[5] != "1"):
                continue
            _, _, _, a, b, v = f[0].split(":")[:6]
            c = len(v) - 1 - int(f[1])
            kind = "units" if c == 0 else ("top" if int(f[1]) == 0 else ("middle" if c > 0 else ("line_feed" if c == -1 else "past")))
            key = (half_of(f[0]), kind)
            t = acc.setdefault(key, [0, 0.0])
            t[0] += 1
            t[1] += int(f[3]) / 2.0**20 * np.log(2.0)
        return acc
    here, there = read(d), read(base) if base else {}
    for half in (0, 1):
        n = sum(v[0] for k, v in here.items() if k[0] == half)
        if n:
            print(f"CODES half={'fit' if half == 0 else 'held'} column=every places={n} nats={sum(v[1] for k, v in here.items() if k[0] == half) / n:.4f}")
    for key in sorted(here):
        n, total = here[key]
        line = f"CODES half={'fit' if key[0] == 0 else 'held'} column={key[1]} places={n} nats={total / n:.4f}"
        if key in there:
            line += f" before={there[key][1] / there[key][0]:.4f}"
        print(line)


def main():
    if len(sys.argv) >= 6 and sys.argv[1] == "solve":
        return solve(sys.argv[2], sys.argv[3], sys.argv[4], [float(v) for v in sys.argv[5].split(",")], float(sys.argv[6]) if len(sys.argv) > 6 else 1.0, sys.argv[7] if len(sys.argv) > 7 else None)
    if len(sys.argv) == 8 and sys.argv[1] == "step":
        return step(sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5], float(sys.argv[6]), float(sys.argv[7]))
    if len(sys.argv) == 5 and sys.argv[1] == "mixture":
        return mixture(sys.argv[2], sys.argv[3], sys.argv[4])
    if len(sys.argv) >= 3 and sys.argv[1] == "codes":
        return codes(sys.argv[2], sys.argv[3] if len(sys.argv) > 3 else None)
    if len(sys.argv) < 3 or sys.argv[1] != "targets":
        sys.exit(__doc__)
    targets(sys.argv[2])
    print("FOUND_PLANTED the same reading with each record's source symbols dealt at random")
    targets(sys.argv[2], deal=True)


if __name__ == "__main__":
    main()
