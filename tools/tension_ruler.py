#!/usr/bin/env -S python3 -I
"""A ruler for the tension at the strand's return (`athena host complete-language read-tension`; atlas `contact.effective-tension`,
`contact.pool-founding`, `code.triad-character-of-composition`). It reads, on the host and outside the machine, how much of the covector
that reaches a place the present faces leave unbridged and a product of the place's own faces removes, and it locates the triads' legs
where that tension leads. Floats are a ruler's (CLAUDE.md, a ruler is an instrument); what it writes for the machine is integers on the
material's grain.

  tension_ruler.py table OUT KEY MET FAR        writes OUT, a table for `read-tension`: MET fresh sums and differences of two operands
                                                of one to six digits and FAR of seven to nine, as the arithmetic world writes them
                                                (`a + b = ` and the value with its line feed), each with its value's digit places named.
                                                The draw is keyed (SHA-256 of `KEY:tension:k`). Labels are
                                                `tension:<met|far>:<op>:<a>:<b>:<value>`.
  tension_ruler.py read DIR [--half H]          reads `read-tension`'s DIR: by the kind of place (a sum's or a difference's digit, whether a
                                                carry or a borrow enters its column, the units place) the place's code, the share of the
                                                covector's power a linear face of the pair chart removes, the share the triads' products as
                                                they stand remove, and the share products located on one half of the records remove on
                                                the other half.
  tension_ruler.py found DIR STATE_DIMS OUT     locates the legs on every row of DIR and writes OUT.legs and OUT.return for
                                                `found-crossing` (32-bit little-endian integers on the material's grain).

The world is synthetic (tools/arithmetic_world.py), so its records are printed freely."""
import hashlib
import os
import sys

import numpy as np

MATERIAL = 24  # the material's grain, 2^(-24)
FACE = 16  # the faces' grain, 2^(-16)


def draw(key, k):
    seed = hashlib.sha256(f"{key}:tension:{k}".encode()).digest()
    return int.from_bytes(seed, "big")


def operand(r, low, high):
    length = low + r % (high - low + 1)
    r //= 16
    first = 0 if length == 1 else 10 ** (length - 1)
    return first + r % (10**length - first)


def table(out, key, met, far):
    rows = []
    for kind, n, (low, high) in (("met", met, (1, 6)), ("far", far, (7, 9))):
        for k in range(n):
            r = draw(f"{key}:{kind}", k)
            op = "+" if r % 2 == 0 else "-"
            a = operand(r >> 8, low, high)
            b = operand(r >> 120, low, high)
            v = a + b if op == "+" else a - b
            run = f"{v}\n"
            digits = [j for j, c in enumerate(run) if c.isdigit()]
            rows.append((f"tension:{kind}:{op}:{a}:{b}:{v}", f"{a} {op} {b} = ", run.replace("\n", "\\n"), ",".join(map(str, digits))))
    with open(out, "x") as f:
        for row in rows:
            f.write("\t".join(row) + "\n")
    print(f"TENSION_TABLE rows={len(rows)} places={sum(len(r[3].split(',')) for r in rows)}")


def place_kind(label, place):
    """A value digit's kind: (lengths, op, k from the value's last digit, whether a carry or a borrow enters its column, a_k, b_k, digit)."""
    _, kind, op, a, b, v = label.split(":")
    a, b, v = int(a), int(b), int(v)
    text = str(v)
    digits = text.lstrip("-")
    k = len(text) - 1 - place
    da, db = (a // 10**k) % 10, (b // 10**k) % 10
    if op == "+":
        enters = (a % 10**k + b % 10**k) >= 10**k
    else:
        hi, lo = (a, b) if a >= b else (b, a)
        enters = (hi % 10**k) < (lo % 10**k)
        da, db = (hi // 10**k) % 10, (lo // 10**k) % 10
    return kind, op, k, bool(enters) and k > 0, da, db, int(digits[len(digits) - 1 - k])


def load(d):
    dims = dict(line.split("\t") for line in open(os.path.join(d, "dims.tsv")).read().splitlines())
    dw, m2, j2, ticks = int(dims["lambda"]), int(dims["current"]), int(dims["products"]), int(dims["ticks"])
    rows = [line.split("\t") for line in open(os.path.join(d, "rows.tsv")).read().splitlines()]
    n = len(rows)
    lam = np.fromfile(os.path.join(d, "lambda.i64"), dtype="<i8").reshape(n, dw).astype(np.float64) / 2.0**MATERIAL
    read = np.fromfile(os.path.join(d, "read.i32"), dtype="<i4").reshape(n, dw).astype(np.float64) / 2.0**FACE
    cur = np.fromfile(os.path.join(d, "current.i64"), dtype="<i8").reshape(n, m2).astype(np.float64) / 2.0**FACE
    prod = np.fromfile(os.path.join(d, "products.i64"), dtype="<i8").reshape(n, j2).astype(np.float64) / 2.0**FACE if j2 else np.zeros((n, 0))
    return rows, lam, read, cur, prod, ticks


def removed(features, lam, fit, test, ridge=1e-6):
    """The share of the covector's power a linear map of `features` removes on `test`, fitted on `fit` (least squares with a small ridge)."""
    f = np.hstack([features, np.ones((len(features), 1))])
    h = f[fit].T @ f[fit]
    h += ridge * np.trace(h) / len(h) * np.eye(len(h))
    w = np.linalg.solve(h, f[fit].T @ lam[fit])
    res = lam[test] - f[test] @ w
    return 1.0 - (res**2).sum() / (lam[test] ** 2).sum()


def locate(read, lam, triads, sweeps=40, seed=0, ridge=1e-3):
    """Located legs: complex forms α = a·r̄, β = b·r̄ (r̄ the pair chart with a one) whose products α β the covector follows, one triad after
    another on the remainder the earlier ones leave (alternating least squares on `Σ_t |λ_t − w Re/Im(α_t β_t)|²`, each leg's solve a
    regression of the remainder's projection on the other leg's weighted chart). Returns `a`, `b` (`[J][D + 1]` complex) and the features'
    regression onto the covector."""
    rng = np.random.default_rng(seed)
    n, dw = read.shape
    rb = np.hstack([read, np.ones((n, 1))])
    rem = lam.copy()
    legs_a, legs_b = [], []
    for _ in range(triads):
        a = (rng.standard_normal(dw + 1) + 1j * rng.standard_normal(dw + 1)) / np.sqrt(dw)
        b = (rng.standard_normal(dw + 1) + 1j * rng.standard_normal(dw + 1)) / np.sqrt(dw)
        for _ in range(sweeps):
            for which in (0, 1):
                other = rb @ (b if which == 0 else a)
                p = (rb @ a) * (rb @ b)
                feats = np.stack([p.real, p.imag], axis=1)
                # The output side: the covector's regression on the product, then its projection back as a complex target per place.
                h = feats.T @ feats + ridge * n * np.eye(2)
                w = np.linalg.solve(h, feats.T @ rem)  # [2][D]
                # target_t = (w_re + i w_im) · λ_t, so that Re(conj(target) α β) is the removed part's alignment.
                target = rem @ w[0] + 1j * (rem @ w[1])
                # Solve the leg: minimize Σ |target_t − (leg·r̄_t) other_t|² over the complex leg.
                x = rb * other[:, None]
                g = x.conj().T @ x + ridge * n * np.eye(dw + 1)
                leg = np.linalg.solve(g, x.conj().T @ target)
                if which == 0:
                    a = leg
                else:
                    b = leg
            # Balance the legs' norms (the gauge's scale is free).
            na, nb = np.linalg.norm(a), np.linalg.norm(b)
            s = np.sqrt(nb / na) if na > 0 and nb > 0 else 1.0
            a, b = a * s, b / s
        p = (rb @ a) * (rb @ b)
        feats = np.hstack([np.stack([p.real, p.imag], axis=1), np.ones((n, 1))])
        w = np.linalg.lstsq(feats, rem, rcond=None)[0]
        rem = rem - feats @ w
        legs_a.append(a)
        legs_b.append(b)
    return np.array(legs_a), np.array(legs_b)


def products_of(read, a, b):
    rb = np.hstack([read, np.ones((len(read), 1))])
    p = (rb @ a.T) * (rb @ b.T)
    return np.hstack([p.real, p.imag])


def read_dir(d, half_key="half"):
    rows, lam, read, cur, prod, ticks = load(d)
    n = len(rows)
    kinds = [place_kind(r[0], int(r[1])) for r in rows]
    tick = np.array([int(r[2]) for r in rows])
    code = np.array([int(r[3]) for r in rows]) / 2.0**20 * np.log(2.0)
    # Records split in two halves by a hash of the label: legs located on one, read on the other.
    half = np.array([hashlib.sha256(f"{half_key}:{r[0]}".encode()).digest()[0] % 2 for r in rows])
    fit, test = half == 0, half == 1
    print(f"TENSION_READ rows={n} places={n // ticks} ticks={ticks} fit_rows={fit.sum()} test_rows={test.sum()}")
    groups = {}
    for i, (kind, op, k, enters, da, db, dv) in enumerate(kinds):
        part = "units" if k == 0 else ("carry" if enters else "clear")
        groups.setdefault((kind, op, part), []).append(i)
    print("TENSION_CODE lengths op part places nats_a_digit")
    for key in sorted(groups):
        idx = np.array(groups[key])
        idx = idx[tick[idx] == 0]
        print(f"TENSION_CODE {key[0]} {key[1]} {key[2]} {len(idx)} {code[idx].mean():.4f}")
    met = np.array([k[0] == "met" for k in kinds])
    plus = np.array([k[1] == "+" for k in kinds])
    print("TENSION_SHARE scope tick rows power linear_chart standing_products linear_current")
    for scope, mask in (("met", met), ("met+", met & plus), ("far", ~met)):
        for k in range(ticks):
            sel = mask & (tick == k)
            f, t = sel & fit, sel & test
            if t.sum() == 0:
                continue
            power = (lam[t] ** 2).sum() / t.sum()
            lin = removed(read, lam, f, t)
            standing = removed(prod, lam, f, t) if prod.shape[1] else float("nan")
            lin_cur = removed(cur, lam, f, t)
            print(f"TENSION_SHARE {scope} {k} {t.sum()} {power:.6e} {lin:.4f} {standing:.4f} {lin_cur:.4f}")
    return rows, lam, read, cur, prod, ticks, kinds, tick, code, fit, test, met, plus


def located_shares(d, triads=10):
    rows, lam, read, cur, prod, ticks, kinds, tick, code, fit, test, met, plus = read_dir(d)
    print("TENSION_LOCATED scope tick triads fit_rows test_rows share_fit share_test share_test_after_linear")
    for scope, mask in (("met", met), ("met+", met & plus)):
        for k in range(ticks):
            sel = mask & (tick == k)
            f, t = sel & fit, sel & test
            # The linear face's part is taken out first (what the present faces could bridge), so the located share is the pool's own.
            fb = np.hstack([read, np.ones((len(read), 1))])
            w = np.linalg.lstsq(fb[f], lam[f], rcond=None)[0]
            rem = lam - fb @ w
            for j in (1, 2, 5, triads):
                a, b = locate(read[f], rem[f], j)
                feats = products_of(read, a, b)
                print(f"TENSION_LOCATED {scope} {k} {j} {f.sum()} {t.sum()} {removed(feats, rem, f, f):.4f} {removed(feats, rem, f, t):.4f} {removed(np.hstack([read, feats]), lam, f, t):.4f}")


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    cmd = sys.argv[1]
    if cmd == "table":
        table(sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5]))
    elif cmd == "read":
        read_dir(sys.argv[2])
    elif cmd == "located":
        located_shares(sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 10)
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()
