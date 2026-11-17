#!/usr/bin/env -S python3 -I
"""The founding law's premise, read on the engine's own rows (the lead, November 17).

Usage: founding_ruler.py targets DIR
       founding_ruler.py solve DIR CODEC OUT STEP[,STEP…] [KEY_MODULUS]
       founding_ruler.py step DIR CODEC CLOSED_IN CLOSED_OUT ETA
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


def solve(d, codec, out, steps, gain=1.0):
    """The closed characters' keys and return, written for `athena found-closed` (see the module's text). `steps` is a comma list of step
    sizes; one file `OUT.<k>.closed` is written a step."""
    dims = dict(line.split("\t") for line in open(os.path.join(d, "dims.tsv")).read().splitlines())
    dw, ticks = int(dims["lambda"]), int(dims["ticks"])
    table = [line.split("\t") for line in open(os.path.join(d, "rows.tsv")).read().splitlines()]
    opened = np.flatnonzero(np.array([r[5] == "1" for r in table]))
    lam = np.asarray(np.memmap(os.path.join(d, "lambda.i64"), dtype="<i8", mode="r", shape=(len(table), dw))[opened]).astype(np.float64) / 2.0**24
    rows = read_rows(d)
    heads = len(rows) // len(opened)
    assert heads * len(opened) == len(rows), "shares.tsv does not hold one line a head for every open row"
    symbols, index, keys, member = locate_keys(rows)
    e = len(keys)
    feats = np.zeros((len(opened), heads * 2 * e))
    fit = np.zeros(len(opened), dtype=bool)
    for n, (lab, place, tk, h, site, src) in enumerate(rows):
        i = n // heads
        assert (table[opened[i]][0], int(table[opened[i]][1]), int(table[opened[i]][2])) == (lab, place, tk), "shares.tsv is not in the rows' order"
        fit[i] = half_of(lab) == 0
        if not src:
            continue
        text = lc.text_of(lab)
        t = keys[:, [index[text[j]] for j, _ in src]] * np.array([p for _, p in src])[None, :]
        pair = t.sum(axis=1) ** 2 - (t**2).sum(axis=1)
        feats[i, h * 2 * e : h * 2 * e + e] = pair.real
        feats[i, h * 2 * e + e : (h + 1) * 2 * e] = pair.imag
    # The return's direction: the least-squares map from the keyed pair products to the covector at the place, on the fitting half, every tick's
    # rows together (the return is every tick's). A step along it lowers the code to first order.
    x, y = feats[fit], lam[fit]
    gram = x.T @ x
    b = np.linalg.solve(gram + 1e-6 * np.trace(gram) / gram.shape[0] * np.eye(gram.shape[0]), x.T @ y).T  # [D][heads·2E]
    pred = feats[~fit] @ b.T
    share = 1.0 - ((lam[~fit] - pred) ** 2).sum() / (lam[~fit] ** 2).sum()
    print(f"SOLVE_RETURN rows={len(opened)} fit={int(fit.sum())} heads={heads} characters={e} covector_share_removed_held={share:.4f} rms_covector={np.sqrt((lam**2).mean()):.3e} rms_predicted={np.sqrt((pred**2).mean()):.3e}")
    with open(codec) as f:
        void = int(f.readline().split()[2])
        units = [int(v) for v in f.readline().split()]
    cls = {u: (k if k < void else k + 1) for k, u in enumerate(units)}
    alphabet = len(units) + 1
    kw = np.zeros((alphabet, 2 * e))
    for ch, i in index.items():
        if member[i]:
            kw[cls[ord(ch)], :e] = keys[:, i].real
            kw[cls[ord(ch)], e:] = keys[:, i].imag
    # A key at modulus `gain`: the products then stand `gain²` higher and the return's entries as much lower, inside their 32-bit words.
    kwords = np.rint(gain * kw * 2.0**16).astype("<i4")
    print(f"SOLVE_KEYS ring={''.join(ch for ch, i in sorted(index.items(), key=lambda t: t[1]) if member[i])!r} classes={[cls[ord(ch)] for ch, i in sorted(index.items(), key=lambda t: t[1]) if member[i]]}")
    for k, step in enumerate(steps):
        w = -step * b
        words = np.rint(w / gain**2 * 2.0**24)
        assert np.abs(words).max() < 2**31, "a return past its 32-bit word"
        path = f"{out}.{k}.closed"
        with open(path, "xb") as f:
            f.write(np.array([e], dtype="<i4").tobytes())
            f.write(kwords.tobytes())
            f.write(words.astype("<i4").tobytes())
        print(f"SOLVE_WRITTEN {path} step={step:g} key_modulus={gain:g} largest_return={np.abs(w).max() / gain**2:.4f} rms_move={np.sqrt(((feats @ w.T) ** 2).mean()):.4e}")


def step(d, codec, closed_in, closed_out, eta):
    """One more step of the return's solve: DIR is a `read-tension … all` directory of the state founded with CLOSED_IN (the ruler's reverse,
    the closed characters' return held constant). The keyed pair products are formed from the rows with CLOSED_IN's own keys, the covector
    at the open places is regressed on them over the fitting half, and CLOSED_OUT is CLOSED_IN with its return moved `−ETA` times that map."""
    dims = dict(line.split("\t") for line in open(os.path.join(d, "dims.tsv")).read().splitlines())
    dw = int(dims["lambda"])
    words = np.fromfile(closed_in, dtype="<i4")
    e = int(words[0])
    with open(codec) as f:
        void = int(f.readline().split()[2])
        units = [int(v) for v in f.readline().split()]
    cls = {u: (k if k < void else k + 1) for k, u in enumerate(units)}
    alphabet = len(units) + 1
    kw = words[1 : 1 + alphabet * 2 * e].reshape(alphabet, 2 * e).astype(np.float64) / 2.0**16
    key = kw[:, :e] + 1j * kw[:, e:]  # [class][character]
    table = [line.split("\t") for line in open(os.path.join(d, "rows.tsv")).read().splitlines()]
    opened = np.flatnonzero(np.array([r[5] == "1" for r in table]))
    lam = np.asarray(np.memmap(os.path.join(d, "lambda.i64"), dtype="<i8", mode="r", shape=(len(table), dw))[opened]).astype(np.float64) / 2.0**24
    rows = read_rows(d)
    heads = len(rows) // len(opened)
    assert heads * len(opened) == len(rows), "shares.tsv does not hold one line a head for every open row"
    w_old = words[1 + alphabet * 2 * e :].reshape(dw, heads * 2 * e).astype(np.float64) / 2.0**24
    feats = np.zeros((len(opened), heads * 2 * e))
    fit = np.zeros(len(opened), dtype=bool)
    for n, (lab, _, _, h, _, src) in enumerate(rows):
        i = n // heads
        fit[i] = half_of(lab) == 0
        if not src:
            continue
        text = lc.text_of(lab)
        t = key[[cls[ord(text[j])] for j, _ in src]].T * np.array([p for _, p in src])[None, :]
        pair = t.sum(axis=1) ** 2 - (t**2).sum(axis=1)
        feats[i, h * 2 * e : h * 2 * e + e] = pair.real
        feats[i, h * 2 * e + e : (h + 1) * 2 * e] = pair.imag
    x, y = feats[fit], lam[fit]
    gram = x.T @ x
    b = np.linalg.solve(gram + 1e-6 * np.trace(gram) / gram.shape[0] * np.eye(gram.shape[0]), x.T @ y).T
    pred = feats[~fit] @ b.T
    share = 1.0 - ((lam[~fit] - pred) ** 2).sum() / (lam[~fit] ** 2).sum()
    w_new = w_old - eta * b
    out = np.rint(w_new * 2.0**24)
    assert np.abs(out).max() < 2**31, "a return past its 32-bit word"
    with open(closed_out, "xb") as f:
        f.write(words[: 1 + alphabet * 2 * e].astype("<i4").tobytes())
        f.write(out.astype("<i4").tobytes())
    print(f"STEP rows={len(opened)} fit={int(fit.sum())} covector_share_removed_held={share:.4f} rms_covector={np.sqrt((lam**2).mean()):.3e} eta={eta:g} largest_return={np.abs(w_new).max():.3f} rms_return={np.sqrt((w_new**2).mean()):.4f}")


def codes(d, base=None):
    """The written digit's code at each answer place of a `read-tension` directory, by column, on the held and the fitting half (nats a
    place, from `rows.tsv`'s code at tick 0), beside another directory's where given."""
    def read(path):
        acc = {}
        for line in open(os.path.join(path, "rows.tsv")):
            f = line.rstrip("\n").split("\t")
            if int(f[2]) != 0 or (len(f) > 5 and f[5] != "1"):
                continue
            site = int(f[4]) if len(f) > 5 else None
            _, _, _, a, b, v = f[0].split(":")
            c = len(v) - 1 - int(f[1])
            if c < 0:
                continue
            key = (half_of(f[0]), "units" if c == 0 else ("top" if int(f[1]) == 0 else "middle"))
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
        return solve(sys.argv[2], sys.argv[3], sys.argv[4], [float(v) for v in sys.argv[5].split(",")], float(sys.argv[6]) if len(sys.argv) > 6 else 1.0)
    if len(sys.argv) == 7 and sys.argv[1] == "step":
        return step(sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5], float(sys.argv[6]))
    if len(sys.argv) >= 3 and sys.argv[1] == "codes":
        return codes(sys.argv[2], sys.argv[3] if len(sys.argv) > 3 else None)
    if len(sys.argv) < 3 or sys.argv[1] != "targets":
        sys.exit(__doc__)
    targets(sys.argv[2])
    print("FOUND_PLANTED the same reading with each record's source symbols dealt at random")
    targets(sys.argv[2], deal=True)


if __name__ == "__main__":
    main()
