"""Read a tower's circuit mode by mode (the read-tower-modes command) over a text of equation lines.
An exterior reading of the machine's own exact quantities; nothing here enters the machine.

  cells TEXT ROLES        print the cells (ascending, one a line) whose coded class has one of
                          ROLES (comma-separated): the roles of tower_circuit.py, plus A (the cell
                          that has heard the first operand's units and codes the operation), B (has
                          heard the second operand's units, codes `=`), E (has heard `=`, codes the
                          result's first digit) and U (codes the result's units).
  flux TEXT MODES         per level and role of a sum, difference or product, mode by mode, from a
                          `full` reading: the mode's move (|λ| and its turn a tick in degrees, at
                          the role's cells), its share of the level's stored energy, of what the
                          level loses (|before|² − |carried|²) and of the power the push brings
                          (|after|² − |carried|²), the share of its own energy the moves keep
                          (`kept`, Σ|carried|² / Σ|before|²), and the push's orientation against the carried
                          phase: `R = 2 Re(c̄ d)` drives the mode along its phase (a boost, negative
                          where the push cancels what the mode carries), `Q = 2 Im(c̄ d)` across it
                          (a turn), `N = |d|²`, with `d = after − carried` and power = R + N. Each
                          share is the mode's part of its level's total at that role, so a uniform
                          load or a changed clock leaves it unchanged; the totals are given beside.
  turns TEXT MODES        per level, from a `full` reading, the move each mode makes where the
                          second operand's units digit arrives (B), by that digit: the share of
                          the move that depends on the digit (where it is 0 the arriving digit
                          moves the carried one alike whatever it is, and cannot cross it), and how
                          near its turn (arg λ) and its pump's axis (arg β) come to a character of
                          the ring of ten, d ↦ 2π m d/10.
  probe TEXT:MODES... -- TEXT:MODES...
                          from `after` readings (each reading beside the text it read; the
                          training readings before `--`, the held-out after it) at A, B, E and U: whether the operands' units (a0,
                          b0) and the result's units (c0) can be read linearly from the state, per
                          operation and role, from the lower level or the upper level. The fit
                          is least squares on the training cells by the exact Gram (each coordinate
                          released to 2^(−SHIFT) of the state's unit, one unit of ridge on the
                          diagonal so the Gram is positive definite, Bareiss elimination in
                          integers); the reading is the held-out share whose largest fitted class
                          is the true one, beside the share of the commonest class.

usage: python3 -I tower_modes.py cells TEXT ROLES
       python3 -I tower_modes.py flux TEXT MODES
       python3 -I tower_modes.py turns TEXT MODES
       python3 -I tower_modes.py probe [--shift S] [--ops +-*] TEXT:MODES... -- TEXT:MODES...
"""
import collections
import importlib.util
import math
import os
import sys

_spec = importlib.util.spec_from_file_location("tower_circuit", os.path.join(os.path.dirname(os.path.abspath(__file__)), "tower_circuit.py"))
tower_circuit = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(tower_circuit)

STATE_BITS = 24
MOVE_BITS = 30


def probe_roles(text):
    """Each position's probe role (A, B, E, U, or several for a one-digit result) and its line's
    (operation, a0, b0, c0), for whole true equation lines."""
    role, info, start = collections.defaultdict(list), {}, 0
    for line in text.split(b"\n"):
        m = tower_circuit.EQ.match(line)
        if m:
            a, op, b, c = m.groups()
            op = op.decode()
            t = int(a) + int(b) if op == "+" else int(a) - int(b) if op == "-" else int(a) * int(b)
            if t == int(c):
                facts = (op, int(a[-1:]), int(b[-1:]), int(c[-1:]))
                coded = {"A": len(a), "B": len(a) + 1 + len(b), "E": len(a) + 2 + len(b), "U": len(line) - 1}
                for r, k in coded.items():
                    role[start + k].append(r)
                    info[start + k] = facts
        start += len(line) + 1
    return role, info


def cells(text_path, roles):
    text = open(text_path, "rb").read()
    wanted = set(roles.split(","))
    circuit_role, _ = tower_circuit.roles(text)
    probe_role, _ = probe_roles(text)
    for p in range(1, len(text)):
        if circuit_role[p] in wanted or wanted.intersection(probe_role.get(p, ())):
            print(p - 1)


def parse(path, full):
    """Each MODES line: (cell, class, code, levels), a level a list of its modes' integers."""
    for line in open(path):
        if not line.startswith("MODES "):
            continue
        parts = line.split()
        levels = []
        for x in parts[4:]:
            modes = [tuple(int(v) for v in m.split(",")) for m in x.split("=", 1)[1].split(";")]
            if any(len(m) != (10 if full else 2) for m in modes):
                raise SystemExit(f"{path}: a mode has the wrong fields for a {'full' if full else 'after'} reading")
            levels.append(modes)
        yield int(parts[1]), int(parts[2]), int(parts[3]), levels


def flux(text_path, paths):
    text = open(text_path, "rb").read()
    role, info = tower_circuit.roles(text)
    groups = collections.defaultdict(list)
    for path in paths:
        for i, _cls, code, levels in parse(path, True):
            r = role[i + 1] if i + 1 < len(role) else None
            if r is not None:
                groups[(info[i + 1][0], r)].append((code, levels))
    for op in "+-*":
        for r in tower_circuit.ORDER:
            xs = groups.get((op, r))
            if not xs:
                continue
            n = len(xs)
            print(f"== {op}/{r} n={n} bits={sum(x[0] for x in xs) / n / 2**20:.2f}")
            for l in range(len(xs[0][1])):
                k_modes = len(xs[0][1][l])
                acc = [[0] * 7 for _ in range(k_modes)]  # E, loss, power, R, Q, N, cancels
                lam = [[0, 0, 0] for _ in range(k_modes)]  # Σ|λ| as re, im sums and |β| sum
                for _code, levels in xs:
                    for k, (br, bi, cr, ci, ar, ai, lr, li, gr, gi) in enumerate(levels[l]):
                        e0, ec, ea = br * br + bi * bi, cr * cr + ci * ci, ar * ar + ai * ai
                        dr, di = ar - cr, ai - ci
                        R, Q, N = 2 * (cr * dr + ci * di), 2 * (cr * di - ci * dr), dr * dr + di * di
                        a = acc[k]
                        a[0] += e0
                        a[1] += e0 - ec
                        a[2] += ea - ec
                        a[3] += R
                        a[4] += Q
                        a[5] += N
                        a[6] += ea < ec
                        lam[k][0] += lr
                        lam[k][1] += li
                        lam[k][2] += math.isqrt(gr * gr + gi * gi)
                tot = [sum(a[j] for a in acc) for j in range(6)]
                print(
                    f"L{l} totals per cell (state unit²): E={tot[0] / n / 2**48:.0f} lost={tot[1] / n / 2**48:.0f} "
                    f"power={tot[2] / n / 2**48:+.0f} R={tot[3] / n / 2**48:+.0f} Q={tot[4] / n / 2**48:+.0f} N={tot[5] / n / 2**48:.0f} "
                    f"kept={(tot[0] - tot[1]) / tot[0] if tot[0] else 0:.2f}"
                )
                print(f"L{l} mode |λ| turn° |β| kept E% lost% power% R% |Q|% N% cancel")
                order = sorted(range(k_modes), key=lambda k: -acc[k][0])
                for k in order:
                    a = acc[k]
                    lr, li = lam[k][0] / n / 2**MOVE_BITS, lam[k][1] / n / 2**MOVE_BITS
                    share = lambda j: 100 * a[j] / tot[j] if tot[j] else 0.0
                    absq = sum(abs(b[4]) for b in acc)
                    print(
                        f"L{l} {k:4d} {math.hypot(lr, li):.5f} {math.degrees(math.atan2(li, lr)):+8.2f} {lam[k][2] / n / 2**MOVE_BITS:.4f} {(a[0] - a[1]) / a[0] if a[0] else 0:.2f} "
                        f"{share(0):5.1f} {share(1):5.1f} {share(2):+6.1f} {share(3):+6.1f} {100 * abs(a[4]) / absq if absq else 0:5.1f} {share(5):5.1f} {a[6] / n:4.2f}"
                    )


def turns(text_path, paths):
    """Per level, the move each mode makes where the second operand's units digit arrives (the B
    cells of `probe`), by that digit. A mode's move is real-linear, `h ↦ λ h + β h̄`, the real 2×2
    `M = [[Re λ + Re β, Im β − Im λ], [Im λ + Im β, Re λ − Re β]]`. Printed per mode: its share of the
    level's stored energy before the move at those cells; the share of its move that depends on the
    digit, `mean_d ‖M(d) − M̄‖² / mean_d ‖M(d)‖²` (0 where every digit moves the carried strand
    alike, so the arriving digit cannot act on it); and how near its turn `arg λ(d)` and its pump's
    axis `arg β(d)` come to a character of the ring of ten, `d ↦ 2π m d/10`, by the fit
    `|Σ_d e^(i(θ(d) − 2π m d/10))| / 10` at its best `m ≠ 0` (1 for an exact character, an offset
    common to the digits free; `m = 0`, a turn every digit gives alike, apart). `spread` is the
    largest distance of one cell's move from its digit's mean: 0 where the move is the digit's
    alone. The level's line gives the energy-weighted share of the move that depends on the digit
    and the number of modes that hold the energy in effect, `1 / Σ_k share_k²`."""
    text = open(text_path, "rb").read()
    role, _info = probe_roles(text)
    acc, energy, cells = {}, collections.Counter(), 0
    for path in paths:
        for i, _cls, _code, levels in parse(path, True):
            if "B" not in role.get(i + 1, ()):
                continue
            cells += 1
            d = text[i] - 48
            for l, modes in enumerate(levels):
                for k, (br, bi, _cr, _ci, _ar, _ai, lr, li, gr, gi) in enumerate(modes):
                    acc.setdefault((l, k, d), []).append((lr, li, gr, gi))
                    energy[(l, k)] += br * br + bi * bi
    for l in sorted({l for l, _k, _d in acc}):
        k_modes = 1 + max(k for ll, k, _d in acc if ll == l)
        level_energy = sum(energy[(l, k)] for k in range(k_modes))
        rows, num, den = [], 0.0, 0.0
        for k in range(k_modes):
            digits = sorted(d for ll, kk, d in acc if ll == l and kk == k)
            lam, beta, moves, spread = [], [], [], 0.0
            for d in digits:
                xs = acc[(l, k, d)]
                n = len(xs)
                mr, mi = sum(x[0] for x in xs) / n, sum(x[1] for x in xs) / n
                br, bi = sum(x[2] for x in xs) / n, sum(x[3] for x in xs) / n
                spread = max(spread, max(math.hypot(x[0] - mr, x[1] - mi) + math.hypot(x[2] - br, x[3] - bi) for x in xs))
                lam.append(complex(mr, mi))
                beta.append(complex(br, bi))
                moves.append((mr + br, bi - mi, mi + bi, mr - br))
            mean = [sum(m[j] for m in moves) / len(moves) for j in range(4)]
            var = sum(sum((m[j] - mean[j]) ** 2 for j in range(4)) for m in moves) / len(moves)
            sq = sum(sum(m[j] ** 2 for j in range(4)) for m in moves) / len(moves)
            w = energy[(l, k)] / level_energy if level_energy else 0.0
            num += w * var
            den += w * sq

            def fit(zs):
                th = [math.atan2(z.imag, z.real) for z in zs]
                f = [abs(sum(complex(math.cos(t - 2 * math.pi * m * d / 10), math.sin(t - 2 * math.pi * m * d / 10)) for d, t in zip(digits, th))) / len(th) for m in range(10)]
                m = max(range(1, 10), key=lambda m: f[m])
                return m, f[m], f[0]

            rows.append((w, k, var / sq if sq else 0.0, *fit(lam), *fit(beta), spread / 2**MOVE_BITS))
        print(
            f"== L{l}: B cells {cells}, digits {len({d for ll, _k, d in acc if ll == l})}; the share of the move that depends on the digit, "
            f"weighted by the stored energy, {num / den if den else 0:.3f}; the energy is held by "
            f"{1 / sum(r[0] ** 2 for r in rows) if rows else 0:.1f} modes in effect (1/Σ share²); turn a character (fit ≥ 0.9) in {sum(r[4] >= 0.9 for r in rows)} modes, pump axis in {sum(r[7] >= 0.9 for r in rows)}"
        )
        print(f"L{l} mode energy digit_share  m_turn fit_turn fit0_turn  m_axis fit_axis fit0_axis  spread")
        for w, k, share, ml, fl, f0l, mb, fb, f0b, sp in sorted(rows, reverse=True):
            print(f"L{l} {k:4d} {w:6.3f} {share:11.3f}  {ml:6d} {fl:8.3f} {f0l:9.3f}  {mb:6d} {fb:8.3f} {f0b:9.3f}  {sp:.2e}")


def bareiss_solve(g, rhs):
    """Solve g w = rhs exactly for a symmetric positive definite integer g: returns (det, y) with
    w = y / det, y integer (Cramer), by fraction-free elimination without pivoting."""
    n, m = len(g), len(rhs[0])
    a = [list(g[i]) + list(rhs[i]) for i in range(n)]
    prev = 1
    for k in range(n - 1):
        pk = a[k][k]
        if pk == 0:
            raise SystemExit("a zero pivot: the Gram is not positive definite")
        rk = a[k]
        for i in range(k + 1, n):
            ri, f = a[i], a[i][k]
            for j in range(k + 1, n + m):
                ri[j] = (pk * ri[j] - f * rk[j]) // prev
            ri[k] = 0
        prev = pk
    det = a[n - 1][n - 1]
    y = [[0] * m for _ in range(n)]
    for i in range(n - 1, -1, -1):
        for c in range(m):
            s = det * a[i][n + c] - sum(a[i][j] * y[j][c] for j in range(i + 1, n))
            q, r = divmod(s, a[i][i])
            if r:
                raise SystemExit("an inexact quotient: the elimination is not Cramer's")
            y[i][c] = q
    return det, y


def probe(args):
    import numpy as np

    shift, ops = 14, "+-*"
    while args[:1] in (["--shift"], ["--ops"]):
        if args[0] == "--shift":
            shift = int(args[1])
        else:
            ops = args[1]
        args = args[2:]
    cut = args.index("--")
    sides = []
    for pairs in (args[:cut], args[cut + 1:]):
        rows = collections.defaultdict(list)  # (op, probe role) -> [(coordinates by level, facts)]
        for pair in pairs:
            text_path, path = pair.split(":", 1)
            role, info = probe_roles(open(text_path, "rb").read())
            for i, _cls, _code, levels in parse(path, False):
                p = i + 1
                for r in role.get(p, ()):
                    rows[(info[p][0], r)].append(([np.array([v >> shift for m in lv for v in m], dtype=np.int64) for lv in levels], info[p][1:]))
        sides.append(rows)
    train, dev = sides
    names = ["a0", "b0", "c0"]
    print(f"probe: coordinates released to 2^-{STATE_BITS - shift} of the state's unit, ridge 1", flush=True)
    for op in ops:
        for r in "ABEU":
            tr, dv = train.get((op, r), []), dev.get((op, r), [])
            if not tr or not dv:
                continue
            for which, pick in (("lower", [0]), ("upper", [1])):
                x = np.stack([np.concatenate([np.ones(1, dtype=np.int64)] + [c[l] for l in pick]) for c, _ in tr])
                top = int(np.abs(x).max())
                if top >= 1 << 20 or top * top * len(tr) >= 1 << 62:
                    raise SystemExit(f"a coordinate of {top} would overflow the Gram's 64-bit sum: raise --shift")
                d = x.shape[1]
                gram = x.T @ x
                facts = np.array([f for _c, f in tr], dtype=np.int64)
                hot = np.zeros((len(tr), 30), dtype=np.int64)
                for t in range(3):
                    hot[np.arange(len(tr)), 10 * t + facts[:, t]] = 1
                rhs = x.T @ hot
                g = [[int(v) for v in row] for row in gram]
                for i in range(1, d):
                    g[i][i] += 1
                det, y = bareiss_solve(g, [[int(v) for v in row] for row in rhs])
                sign = 1 if det > 0 else -1
                xd = [[1] + [int(v) for l in pick for v in c[l]] for c, _ in dv]
                out = []
                for t in range(3):
                    right, common = 0, collections.Counter(f[t] for _c, f in dv)
                    for xv, (_c, f) in zip(xd, dv):
                        scores = [sign * sum(xv[i] * y[i][10 * t + v] for i in range(d)) for v in range(10)]
                        right += max(range(10), key=lambda v: scores[v]) == f[t]
                    out.append(f"{names[t]}={right}/{len(dv)} (commonest {common.most_common(1)[0][1]})")
                print(f"{op}/{r} {which:5s} train={len(tr)} dim={d} " + " ".join(out), flush=True)


def main():
    if len(sys.argv) < 2:
        raise SystemExit(__doc__)
    if sys.argv[1] == "cells":
        cells(sys.argv[2], sys.argv[3])
    elif sys.argv[1] == "flux":
        flux(sys.argv[2], sys.argv[3:])
    elif sys.argv[1] == "turns":
        turns(sys.argv[2], sys.argv[3:])
    elif sys.argv[1] == "probe":
        probe(sys.argv[2:])
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main()
