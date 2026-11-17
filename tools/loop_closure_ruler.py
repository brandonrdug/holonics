#!/usr/bin/env -S python3 -I
"""A ruler: a ring located by loop closure on the engine's own rows and the passage (the lead, November 17; atlas
`key.menu-loop-closure`, `hnn.contact-menu-closes`, `compression.located-transport`).

Usage: loop_closure_ruler.py DIR [planted]

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


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    d = sys.argv[1]
    plants = ("aligned", "dealt") if len(sys.argv) > 2 and sys.argv[2] == "planted" else (None,)
    for planted in plants:
        tables, symbols = menus(d, planted)
        print(f"CLOSURE_READ menu={planted or 'rows'} symbols={len(symbols)} tables={len(tables)}")
        report(planted or "rows", tables, symbols)


if __name__ == "__main__":
    main()
