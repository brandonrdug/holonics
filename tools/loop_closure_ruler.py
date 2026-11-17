#!/usr/bin/env -S python3 -I
"""A ruler: a ring located by loop closure on the engine's own rows and the passage (the lead, November 17; atlas
`key.menu-loop-closure`, `hnn.contact-menu-closes`, `compression.located-transport`).

Usage: loop_closure_ruler.py DIR [planted | release | planes [planted]]

DIR is a `read-tension … all` directory of sums (`tools/tension_ruler.py sums`): `rows.tsv` and `shares.tsv`, the open place's row by
tick and head, each source site with its share of the row's weight. The ruler builds a menu and closes it:

- The menu. At each open place, for a head and a tick, every ordered pair of distinct source sites `(j₁, j₂)` its row meets, weighed by
  the product of their shares, with the symbol written at the place: `T[u, w, x] += p(j₁) p(j₂)` for `u`, `w` the sources' symbols and
  `x` the written one. No label of a sum enters, and nothing says which symbols are digits.
- The closure. A source symbol `u` is an operator on functions of the written symbol, `(P_u f)(w) = E[f(x) | u, w]`, row-normalized
  from `T`. Where a group law stands under rows that are only partly on the aligned pair, `P_u = α·(translation by u) + (1 − α)·(a
  background)`, the operators commute and their common eigenvectors are the law's characters: `P_u χ_j = α ω^(ju) χ_j`. So the phase of
  `u`'s eigenvalue on a common eigenvector is `u`'s key on that ring, and its modulus says whether `u` is on the ring at all.
- The read. The eigenvectors of one drawn combination `Σ_u c_u P_u`, the leading ones past the constant; on each, every symbol's
  eigenvalue `λ_u = v⁺ P_u v`. Scored outside the closure, by the ruler's own knowledge of the digits: the ten digits' phases as
  characters of ℤ/10, `a_j = |Σ_d e^(i arg λ_d) e^(−2πijd/10)|/10` (`Σ_j a_j² = 1`), with the same statistic under permutations of the
  digits as its null. A wheel is `a_j` near one at a `j` coprime to ten; `j` even is the ring of five and `j = 5` the ring of two.

`CLOSURE_TABLE` beside each read is the labelled reading of the same menu: the share of the digit pairs' weight whose written digit is
the pair's sum modulo ten, and that or one more.

With `planted`, two menus on the same records hold the instrument: one built from the aligned operand digits alone (it must return the
wheel at one) and the true menu with the written symbols dealt at random among the places (it must return nothing past its null).

With `release`, what the located key delivers through the rows as they stand: the keys (each symbol's eigenvalue on each common
eigenvector) are located on one half of the records from one head's rows at tick 0 over every answer place; at an open place the row
then gives, on each eigenvector, its barycentre `y = Σ_s p_s λ(u_s)` and its pair product `E = Σ_(s ≠ s′) p_s p_s′ λ(u_s) λ(u_s′)`
(`y²` less the sources' self terms, the menu's own weighting). `RELEASE_HOLD` is the share of the written digit and of the wheel's
digit `a_k + b_k mod 10` a least-squares read of these features gives on the held half, and `RELEASE_TENSION` what they remove of the
covector beside the chart, by part and tick, beside the value's own digit and the pair's table. Nothing in the features is labelled.

With `planes`, DIR holds every place of each record opened in turn (operands' digits, signs and spaces as well as the value's), so
nothing chooses which places are composed. A place at an operand is written `x = v − w`: a translation composed with the reflection
`w ↦ −w`, or a translation by `−u`, by which of the two sources `u` is. The operators then generate the ring's dihedral group and
share planes `span(χ_j, χ_(−j))` in place of lines, and their eigenvalues are no longer keys. For each eigenvector of the drawn
combination the ruler takes the span its images under every operator fill (`CLOSURE_SPAN`: a line or a plane, by the share of the
images' power its first one and two singular directions hold), and in it the function of flattest modulus on its support, which in
such a plane is a character; that function's own phases at the symbols are the keys, and its support is the ring's membership. The
plain closure's read of the same menu is printed beside it, and by the ruler's knowledge of the roles the menu of the value's places
alone and of the operands' places alone.

Floats, counts and the knowledge of which bytes are digits are a ruler's (CLAUDE.md, a ruler is an instrument). The sums are synthetic,
so their records are printed freely."""
import os
import sys

import numpy as np


def text_of(label):
    _, _, op, a, b, v = label.split(":")
    return f"{a} {op} {b} = {v}\n"


def menus(d, planted=None, seed=17):
    """`T[(scope, head, tick)][u, w, x]` over the byte symbols met, and the symbols. `planted`: None (the rows as they are), "aligned"
    (the aligned operand digits alone, at equal shares) or "dealt" (the true rows, the written symbols dealt at random among places)."""
    rng = np.random.default_rng(seed)
    lines = [line.rstrip("\n").split("\t") for line in open(os.path.join(d, "shares.tsv"))]
    symbols = sorted({c for line in lines for c in text_of(line[0])})
    index = {c: i for i, c in enumerate(symbols)}
    n = len(symbols)
    written = [text_of(line[0])[int(line[4])] for line in lines]
    if planted == "dealt":
        # One deal a place (a label and its place), so every head and tick of a place sees the same dealt symbol.
        places = sorted({(line[0], line[1]) for line in lines})
        dealt = dict(zip(places, rng.permutation([text_of(lab)[len(text_of(lab)) - len(lab.split(":")[5]) - 1 + int(pl)] for lab, pl in places])))
        written = [dealt[(line[0], line[1])] for line in lines]
    out = {}
    for line, x in zip(lines, written):
        label, place, tick, head, site = line[0], int(line[1]), int(line[2]), int(line[3]), int(line[4])
        text = text_of(label)
        _, _, _, a, b, v = label.split(":")
        k = len(v) - 1 - place  # the place counted from the value's last digit
        if planted == "aligned":
            sources = []
            at_b = len(a) + 3
            if k < len(a):
                sources.append((len(a) - 1 - k, 0.5))
            if k < len(b):
                sources.append((at_b + len(b) - 1 - k, 0.5))
        else:
            sources = [(int(j), int(p) / 1e6) for j, p, _ in (entry.split(":") for entry in line[5].split())] if len(line) > 5 and line[5] else []
        for scope in ("units", "all") if k == 0 else ("all",):
            t = out.setdefault((scope, head, tick), np.zeros((n, n, n)))
            xi = index[x]
            for j1, p1 in sources:
                for j2, p2 in sources:
                    if j1 != j2:
                        t[index[text[j1]], index[text[j2]], xi] += p1 * p2
    return out, symbols


def menus_every(d, planted=None, seed=17):
    """The menus of a directory where every place of a record is opened in turn, one head and tick at a time: `every` (all places), and
    by the ruler's knowledge of the roles `value` and `operand` (the places at the value's digits, at the operands' digits). `planted`
    as in [`menus`]; "aligned" takes, at a digit's place, the two aligned digits of the record's other two numbers at equal shares."""
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import tension_ruler as tr

    rng = np.random.default_rng(seed)
    lines = [line.rstrip("\n").split("\t") for line in open(os.path.join(d, "shares.tsv"))]
    symbols = sorted({c for line in lines for c in text_of(line[0])})
    index = {c: i for i, c in enumerate(symbols)}
    n = len(symbols)
    written = [text_of(line[0])[int(line[4])] for line in lines]
    if planted == "dealt":
        places = sorted({(line[0], line[4]) for line in lines})
        dealt = dict(zip(places, rng.permutation([text_of(lab)[int(site)] for lab, site in places])))
        written = [dealt[(line[0], line[4])] for line in lines]
    out = {}
    for line, x in zip(lines, written):
        label, tick, head, site = line[0], int(line[2]), int(line[3]), int(line[4])
        text = text_of(label)
        _, _, _, a, b, v = label.split(":")
        role, k, _ = tr.site_role(label, site)
        if planted == "aligned":
            sources = []
            if role is not None:
                for name, start, number in (("a", 0, a), ("b", len(a) + 3, b), ("v", len(a) + len(b) + 6, v)):
                    if name != role and k < len(number):
                        sources.append((start + len(number) - 1 - k, 0.5))
        else:
            sources = [(int(j), int(p) / 1e6) for j, p, _ in (entry.split(":") for entry in line[5].split())] if len(line) > 5 and line[5] else []
        scopes = ["every"] + (["value"] if role == "v" else ["operand"] if role in ("a", "b") else [])
        for scope in scopes:
            t = out.setdefault((scope, head, tick), np.zeros((n, n, n)))
            xi = index[x]
            for j1, p1 in sources:
                for j2, p2 in sources:
                    if j1 != j2:
                        t[index[text[j1]], index[text[j2]], xi] += p1 * p2
    return out, symbols


def spans(t, symbols, seed=3, grid=(46, 90)):
    """The invariant lines and planes of a menu's operators, each with its flattest function: for every eigenvector `v` of one drawn
    combination, the images `P_u v` weighed by the roots of the sources' menu weights, their singular directions, and in the first one
    or two the function of flattest modulus on the support. Returns (the eigenvalue's modulus, the share of the images' power in one
    and in two directions, the flat function over all symbols (zero where a symbol is never written), its flatness, its support)."""
    n = len(symbols)
    xs = np.flatnonzero(t.sum(axis=(0, 1)) > 0)
    tx = t[:, xs][:, :, xs]
    mass = tx.sum(axis=2, keepdims=True)
    p = np.where(mass > 0, tx / np.maximum(mass, 1e-30), 0.0)
    weight = tx.sum(axis=(1, 2))
    rng = np.random.default_rng(seed)
    c = (rng.standard_normal(n) + 1j * rng.standard_normal(n)) * (weight > 0)
    values, right = np.linalg.eig(np.einsum("u,uwx->wx", c, p))
    roots = np.sqrt(weight / max(weight.sum(), 1e-30))
    angles_t = np.linspace(0, np.pi / 2, grid[0])
    angles_f = np.linspace(0, 2 * np.pi, grid[1], endpoint=False)
    out = []
    for e in np.argsort(-np.abs(values)):
        v = right[:, e]
        if np.abs(v - v.mean()).max() < 0.05 * np.abs(v).max():
            continue
        images = np.stack([roots[u] * (p[u] @ v) for u in range(n)], axis=1)
        left, sing, _ = np.linalg.svd(images, full_matrices=False)
        power = sing**2 / max((sing**2).sum(), 1e-30)
        one, two = power[0], power[:2].sum()
        # A line only where the images leave nothing beside it: under a mixture of translations and reflections an eigenvector is
        # nearly kept (most of its images' power along it) and is still no character, so the plane is searched unless the line is clean.
        basis = left[:, :1] if one >= 0.995 else left[:, :2]
        energy = (np.abs(basis) ** 2).sum(axis=1)
        support = energy >= 0.25 * energy.max()
        best = None
        if basis.shape[1] == 1:
            cands = [basis[:, 0]]
        else:
            cands = [np.cos(a) * basis[:, 0] + np.exp(1j * f_) * np.sin(a) * basis[:, 1] for a in angles_t for f_ in angles_f]
        for f in cands:
            mod = np.abs(f[support])
            flat = mod.mean() ** 2 / max((mod**2).mean(), 1e-30)
            if best is None or flat > best[0]:
                best = (flat, f)
        full = np.zeros(n, dtype=complex)
        full[xs] = best[1]
        sup = np.zeros(n, dtype=bool)
        sup[xs] = support
        out.append((abs(values[e]), one, two, full, best[0], sup))
    return out


def report_planes(name, tables, symbols, head=0, tick=0):
    digits = [symbols.index(str(d)) for d in range(10)]
    shown = {" ": "space", "\n": "feed"}
    for scope in ("every", "value", "operand"):
        t = tables.get((scope, head, tick))
        if t is None:
            continue
        found, _ = closure(t, symbols)
        best = max(((characters(np.angle(lam[digits]))[0], np.abs(lam[digits]).mean()) for _, lam in found), key=lambda r: max(r[0][j] for j in (1, 3, 7, 9)), default=None)
        if best is not None:
            j = max((1, 3, 7, 9), key=lambda q: best[0][q])
            print(f"CLOSURE_PLAIN {name} scope={scope} head={head} tick={tick} eigenvalue keys: best coprime j={j} a_j={best[0][j]:.3f} digits_modulus={best[1]:.3f}")
        seen = []
        for modulus, one, two, f, flat, sup in spans(t, symbols):
            kind = "line" if one >= 0.995 else "plane" if two >= 0.9 else "neither"
            amp, pct = characters(np.angle(f[digits]))
            j = 1 + int(amp[1:].argmax())
            keys = " ".join(f"{(np.angle(f[i] / f[digits[0]]) / (2 * np.pi) * 10) % 10:.1f}" for i in digits) if abs(f[digits[0]]) > 0 else "-"
            members = "".join(shown.get(s_, s_) + " " for i, s_ in enumerate(symbols) if sup[i]).strip()
            line = f"CLOSURE_SPAN {name} scope={scope} head={head} tick={tick} modulus={modulus:.3f} in_one={one:.3f} in_two={two:.3f} kind={kind} flatness={flat:.3f} best_j={j} a_j={amp[j]:.3f} null_pct={pct:.3f} support=[{members}] digits_keys_in_tenths_of_a_turn={keys}"
            sig = (kind, j, round(amp[j], 2), members)
            if sig not in seen:
                seen.append(sig)
                print(line, flush=True)


def characters(phases, shuffles=2000, seed=5):
    """The ten located phases as characters of ℤ/10: `a_j`, and the percentile of the largest `a_(j≠0)` under permutations of the digits."""
    omega = np.exp(-2j * np.pi * np.outer(np.arange(10), np.arange(10)) / 10)
    unit = np.exp(1j * phases)
    amp = np.abs(omega @ unit) / 10
    rng = np.random.default_rng(seed)
    null = np.array([(np.abs(omega @ unit[rng.permutation(10)]) / 10)[1:].max() for _ in range(shuffles)])
    return amp, float((null < amp[1:].max()).mean())


def closure(t, symbols, leading=9, seed=3):
    """The menu's operators, the leading common eigenvectors of one drawn combination, and each symbol's eigenvalue on them. The
    functions are on the symbols the passage wrote at the places (`X`, read from the menu), and a co-source `w` is taken in `X` too, so
    an operator maps that space to itself."""
    n = len(symbols)
    xs = np.flatnonzero(t.sum(axis=(0, 1)) > 0)
    t = t[:, xs][:, :, xs]
    mass = t.sum(axis=2, keepdims=True)
    p = np.where(mass > 0, t / np.maximum(mass, 1e-30), 0.0)  # [u][w in X][x in X]
    weight = t.sum(axis=(1, 2))
    rng = np.random.default_rng(seed)
    c = (rng.standard_normal(n) + 1j * rng.standard_normal(n)) * (weight > 0)
    m = np.einsum("u,uwx->wx", c, p)
    values, right = np.linalg.eig(m)
    left = np.linalg.pinv(right)
    order = np.argsort(-np.abs(values))
    out = []
    for e in order:
        v, vl = right[:, e], left[e]
        # The constant function is every operator's eigenvector at one; it is no ring's character.
        if np.abs(v - v.mean()).max() < 0.05 * np.abs(v).max():
            continue
        lam = np.array([vl @ p[u] @ v for u in range(n)])
        out.append((values[e], lam))
        if len(out) == leading:
            break
    return out, weight


def report(name, tables, symbols):
    digits = [symbols.index(str(d)) for d in range(10)]
    shown = {" ": "space", "\n": "feed"}
    for key in sorted(tables):
        scope, head, tick = key
        t = tables[key]
        dd = t[np.ix_(digits, digits, digits)]
        total = dd.sum()
        hit = sum(dd[u, w, (u + w) % 10] for u in range(10) for w in range(10))
        near = hit + sum(dd[u, w, (u + w + 1) % 10] for u in range(10) for w in range(10))
        print(f"CLOSURE_TABLE {name} scope={scope} head={head} tick={tick} digit_pairs_share_of_menu={total / max(t.sum(), 1e-30):.3f} written_is_sum_mod_ten={hit / max(total, 1e-30):.3f} sum_or_one_more={near / max(total, 1e-30):.3f}")
        found, weight = closure(t, symbols)
        for rank, (value, lam) in enumerate(found):
            amp, pct = characters(np.angle(lam[digits]))
            j = 1 + int(amp[1:].argmax())
            on = np.abs(lam[digits]).mean()
            off = [(shown.get(s, s), abs(lam[i])) for i, s in enumerate(symbols) if i not in digits and weight[i] > 0]
            turns = " ".join(f"{(np.angle(lam[i]) / (2 * np.pi) * 10) % 10:.1f}" for i in digits)
            print(f"CLOSURE {name} scope={scope} head={head} tick={tick} eigenvector={rank} modulus={abs(value):.3f} best_j={j} a_j={amp[j]:.3f} a_0={amp[0]:.3f} null_pct={pct:.3f} digits_modulus={on:.3f} others_modulus=" + ",".join(f"{s}:{m:.2f}" for s, m in off) + f" digits_keys_in_tenths_of_a_turn={turns}", flush=True)


def release(d, head=0, ridge=1e-3):
    """What the located key delivers through the rows (see the module's text). The keys are located on the fitting half."""
    import hashlib

    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import tension_ruler as tr

    dims = dict(line.split("\t") for line in open(os.path.join(d, "dims.tsv")).read().splitlines())
    dw, ticks = int(dims["lambda"]), int(dims["ticks"])
    rows = [line.split("\t") for line in open(os.path.join(d, "rows.tsv")).read().splitlines()]
    n = len(rows)
    opened = np.flatnonzero(np.array([r[5] == "1" for r in rows]))
    lam_all = np.memmap(os.path.join(d, "lambda.i64"), dtype="<i8", mode="r", shape=(n, dw))
    read_all = np.memmap(os.path.join(d, "read.i32"), dtype="<i4", mode="r", shape=(n, dw))
    lam = np.asarray(lam_all[opened]).astype(np.float64) / 2.0**tr.MATERIAL
    read = np.asarray(read_all[opened]).astype(np.float64) / 2.0**tr.FACE
    label = [rows[i][0] for i in opened]
    place = np.array([int(rows[i][1]) for i in opened])
    tick = np.array([int(rows[i][2]) for i in opened])
    half_of = lambda lab: hashlib.sha256(f"half:{lab}".encode()).digest()[0] % 2
    fit = np.array([half_of(l) == 0 for l in label])
    test = ~fit
    # The keys: the closure of the fitting half's menu, one head's rows at tick 0, every answer place.
    # A sum may stand in the table more than once, so a shares line is matched to its open row by its order (every place and tick writes
    # one line a head, in the rows' order), never by its label.
    lines = [line.rstrip("\n").split("\t") for line in open(os.path.join(d, "shares.tsv"))]
    heads = len(lines) // len(opened)
    if heads * len(opened) != len(lines):
        sys.exit("shares.tsv does not hold one line a head for every open row")
    lines = [(i // heads, line) for i, line in enumerate(lines) if int(line[3]) == head]
    for i, line in lines:
        if (line[0], int(line[1]), int(line[2])) != (label[i], int(place[i]), int(tick[i])):
            sys.exit("shares.tsv is not in the rows' order")
    symbols = sorted({c for _, line in lines for c in text_of(line[0])})
    index = {c: i for i, c in enumerate(symbols)}
    m = len(symbols)
    menu = np.zeros((m, m, m))
    parsed = []
    for i, line in lines:
        lab, pl, tk, site = line[0], int(line[1]), int(line[2]), int(line[4])
        text = text_of(lab)
        src = [(index[text[int(j)]], int(p) / 1e6) for j, p, _ in (entry.split(":") for entry in line[5].split())] if len(line) > 5 and line[5] else []
        parsed.append((i, src))
        if tk == 0 and half_of(lab) == 0:
            xi = index[text[site]]
            for a_, (u, p1) in enumerate(src):
                for b_, (w, p2) in enumerate(src):
                    if a_ != b_:
                        menu[u, w, xi] += p1 * p2
    found, _ = closure(menu, symbols)
    keys = np.array([lam_u for _, lam_u in found])  # [eigenvector][symbol]
    e = len(keys)
    print(f"RELEASE_READ head={head} keys_on=fit_half,tick=0,every_place eigenvectors={e} places={len(opened) // ticks} ticks={ticks} ridge={ridge}")
    y = np.zeros((len(opened), e), dtype=complex)
    pair = np.zeros((len(opened), e), dtype=complex)
    for i, src in parsed:
        if not src:
            continue
        us = np.array([u for u, _ in src])
        ps = np.array([p_ for _, p_ in src])
        terms = keys[:, us] * ps[None, :]
        y[i] = terms.sum(axis=1)
        pair[i] = y[i] ** 2 - (terms**2).sum(axis=1)
    f_y = np.hstack([y.real, y.imag])
    f_pair = np.hstack([f_y, pair.real, pair.imag])
    kinds = [tr.place_kind(l, int(p_)) for l, p_ in zip(label, place)]
    part = np.array([tr.PARTS.index(tr.part_of(k)) for k in kinds])
    da, db, dv = (np.array([k[i] for k in kinds]) for i in (4, 5, 6))
    held = np.array([k[7] for k in kinds])
    wheel = (da + np.where(held == 2, db, 0)) % 10
    table = (tr.onehot(da)[:, :, None] * tr.onehot(db)[:, None, :]).reshape(len(opened), 100)
    centre = lambda x, sel: x - x[sel].mean(axis=0)
    print("RELEASE_HOLD part tick test_rows | written_digit: chart barycentre barycentre+pair | wheel_digit: chart barycentre barycentre+pair")
    print("RELEASE_TENSION part tick test_rows | covector share: chart chart+barycentre chart+barycentre+pair value_digit table")
    for pid, pname in enumerate(tr.PARTS):
        for k in range(ticks):
            sel = (tick == k) & (part == pid)
            f, t = sel & fit, sel & test
            if t.sum() < 200 or pname == "top":
                continue
            out = []
            for target in (tr.onehot(dv), tr.onehot(wheel)):
                tc = centre(target, sel)
                out.append([tr.removed(x, tc, f, t, ridge) for x in (read, f_y, f_pair)])
            print(f"RELEASE_HOLD {pname} tick={k} {t.sum()} | " + " ".join(f"{v:.4f}" for v in out[0]) + " | " + " ".join(f"{v:.4f}" for v in out[1]), flush=True)
            shares = [tr.removed(x, lam, f, t, ridge) for x in (read, np.hstack([read, f_y]), np.hstack([read, f_pair]), tr.onehot(dv), table)]
            print(f"RELEASE_TENSION {pname} tick={k} {t.sum()} | " + " ".join(f"{v:.4f}" for v in shares), flush=True)


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    d = sys.argv[1]
    if len(sys.argv) > 2 and sys.argv[2] == "release":
        release(d)
        return
    if len(sys.argv) > 2 and sys.argv[2] == "planes":
        for planted in ("aligned", "dealt") if len(sys.argv) > 3 and sys.argv[3] == "planted" else (None,):
            tables, symbols = menus_every(d, planted)
            print(f"CLOSURE_READ menu={planted or 'rows'} places=every symbols={len(symbols)} tables={len(tables)}")
            for tick in range(1 + max(k[2] for k in tables)):
                report_planes(planted or "rows", tables, symbols, 0, tick)
                if planted:
                    break
        return
    plants = ("aligned", "dealt") if len(sys.argv) > 2 and sys.argv[2] == "planted" else (None,)
    for planted in plants:
        tables, symbols = menus(d, planted)
        print(f"CLOSURE_READ menu={planted or 'rows'} symbols={len(symbols)} tables={len(tables)}")
        report(planted or "rows", tables, symbols)


if __name__ == "__main__":
    main()
