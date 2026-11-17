#!/usr/bin/env -S python3 -I
"""A ruler for the tension at the strand's return (`athena host complete-language read-tension`; atlas `contact.effective-tension`,
`contact.pool-founding`, `code.triad-character-of-composition`). It reads, on the host and outside the machine, how much of the covector
that reaches a place the present faces leave unbridged and a product of the place's own faces removes, and it locates the triads' legs
where that tension leads. Floats are a ruler's (CLAUDE.md, a ruler is an instrument); what it writes for the machine is integers on the
material's grain.

  tension_ruler.py table OUT KEY MET FAR [PER]  writes OUT, a table for `read-tension`: MET fresh sums and differences of two operands
                                                of one to six digits and FAR of seven to nine, as the arithmetic world writes them
                                                (`a + b = ` and the value with its line feed), each with its value's digit places named.
                                                The draw is keyed (SHA-256 of `KEY:tension:k`). Labels are
                                                `tension:<met|far>:<op>:<a>:<b>:<value>`.
  tension_ruler.py read DIR [--half H]          reads `read-tension`'s DIR: by the kind of place (a sum's or a difference's digit, whether a
                                                carry or a borrow enters its column, the units place) the place's code, the share of the
                                                covector's power a linear face of the pair chart removes, the share the triads' products as
                                                they stand remove, and the share products located on one half of the records remove on
                                                the other half.
  tension_ruler.py oracle DIR                   the premise and the ceiling: how well a linear read of the pair chart and of the gathered
                                                current gives the aligned operand digits, and what an additive reading of the two
                                                digits, their table and the value's own digit remove of the covector's power.
  tension_ruler.py located DIR [J]              legs located on one half of the records (J triads, ten by default), their products' share
                                                read on the other half, by tick and by the kind of place.
  tension_ruler.py links DIR                    on a `read-tension … all` directory: an operand digit's way to the answer's place, link by
                                                link (a site's own digit and its place from its chart, the open row's share on its
                                                aligned digits by tick and head, and what each head's current brings).
  tension_ruler.py closed DIR                   what a closed lock would open: the two aligned digits as a lock closed on their column
                                                would bring them, summed and unordered, read linearly (a copy) and through located
                                                products (a junction), by part, beside the pair's table.
  tension_ruler.py circles DIR [planted]        on a `read-tension … all` directory with the carry circles' rows (`charge.i64`,
                                                `gate.i64`): whether a circle holds a digit's phase. The gate's turn at a written
                                                digit's site by the digit, as the characters of ℤ/10 of the ten mean turns, against a
                                                permutation of the digits; at an open answer place, the share of the value's digit, the
                                                wheel's digit (a_k + b_k mod 10) and the aligned digits' unordered sum that the charges
                                                give read linearly and by their phases' five harmonics; and what each adds to the
                                                chart's share of the covector's power. With `planted`, one circle's gate is turned by
                                                2π(3d + 2)/10 at the digits' sites and one circle's charge is set to the wheel digit's
                                                phase at the answer place, each with noise: the instrument's own check.
  tension_ruler.py junction DIR [J]             products located on the answer site's gathered current in place of its chart: each
                                                head's current alone (its 2n coordinates and a one) and every head's, the linear chart's
                                                part taken out first, legs located on one half of the records and read on the other, by
                                                part and tick, beside the pair's table.
  tension_ruler.py temper STORE_DIR             the premise of a row's own temperature: each open row's temperature covector beside its
                                                opening chart, by head (how nearly the rows cancel, what the chart removes on the held
                                                section) and by slice (each slice's mean ask).
  tension_ruler.py found STORE_DIR OUT [DIR]    legs located on a `read-tension-store` directory's sections (all ticks together, the last
                                                section held out to score them), written as OUT.legs for `found-crossing` (32-bit
                                                little-endian integers: the charts on the material's grain, the biases on the faces');
                                                with DIR, the same legs read on a `read-tension` directory's places by part.

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


def table(out, key, met, far, per=None):
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
            if per is not None and len(digits) > per:
                # `per` of the value's digit places, drawn by the key.
                order = sorted(digits, key=lambda j: hashlib.sha256(f"{key}:{kind}:place:{k}:{j}".encode()).digest())
                digits = sorted(order[:per])
            rows.append((f"tension:{kind}:{op}:{a}:{b}:{v}", f"{a} {op} {b} = ", run.replace("\n", "\\n"), ",".join(map(str, digits))))
    with open(out, "x") as f:
        for row in rows:
            f.write("\t".join(row) + "\n")
    print(f"TENSION_TABLE rows={len(rows)} places={sum(len(r[3].split(',')) for r in rows)}")


def sums_table(out, key, n, weights):
    """A table of `n` plain sums, a record a region, every value digit opened alone, the operands' lengths drawn with the given
    weights (the lengths one, two, three, … digits), as `tools/arithmetic_world.py` draws them for the redrawn slice. Labelled `met`."""
    weights = [int(w) for w in weights.split(",")]
    rows = []
    for k in range(n):
        r = draw(f"{key}:sums", k)
        nums = []
        for shift in (8, 120):
            u, length = (r >> shift) % sum(weights), 1
            for i, w in enumerate(weights):
                if u < w:
                    length = i + 1
                    break
                u -= w
            first = 0 if length == 1 else 10 ** (length - 1)
            nums.append(first + (r >> (shift + 40)) % (10**length - first))
        a, b = nums
        run = f"{a + b}\n"
        rows.append((f"tension:met:+:{a}:{b}:{a + b}", f"{a} + {b} = ", run.replace("\n", "\\n"), ",".join(str(j) for j, c in enumerate(run) if c.isdigit())))
    with open(out, "x") as f:
        for row in rows:
            f.write("\t".join(row) + "\n")
    print(f"TENSION_TABLE rows={len(rows)} places={sum(len(r[3].split(',')) for r in rows)}")


def place_kind(label, place):
    """A value digit's kind: (lengths, op, k from the value's last digit, whether a carry or a borrow enters its column, a_k, b_k, the
    digit, how many of the two operands hold a digit in the column)."""
    _, kind, op, a, b, v = label.split(":")
    a, b, v = int(a), int(b), int(v)
    text = str(v)
    digits = text.lstrip("-")
    k = len(text) - 1 - place
    hi, lo = (a, b) if (op == "+" or a >= b) else (b, a)
    da, db = (hi // 10**k) % 10, (lo // 10**k) % 10
    if op == "+":
        enters = (a % 10**k + b % 10**k) >= 10**k
    else:
        enters = (hi % 10**k) < (lo % 10**k)
    held = int(len(str(hi)) > k) + int(len(str(lo)) > k)
    return kind, op, k, bool(enters) and k > 0, da, db, int(digits[len(digits) - 1 - k]), held


def part_of(kind):
    """A place's part: the units place; a column both operands hold, clear or carried into; a column one operand holds (the value's
    digit is that operand's, or its neighbour by a carry); a column neither holds (the carry out)."""
    _, _, k, enters, _, _, _, held = kind
    if held == 0:
        return "top"
    if held == 1:
        return "one-carry" if enters else "one-clear"
    if k == 0:
        return "units"
    return "both-carry" if enters else "both-clear"


PARTS = ("units", "both-clear", "both-carry", "one-clear", "one-carry", "top")


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
    ff = f[fit]
    h = grams(ff, [np.ones(len(ff))])[0] if len(ff) > 50000 else ff.T @ ff
    h += ridge * np.trace(h) / len(h) * np.eye(len(h))
    w = np.linalg.solve(h, ff.T @ lam[fit])
    res = lam[test] - f[test] @ w
    return 1.0 - (res**2).sum() / (lam[test] ** 2).sum()


def locate(read, lam, triads, sweeps=12, starts=1, seed=0, ridge=1e-4, weight=None, log=None):
    """Located legs: complex forms α = a·r̄, β = b·r̄ (r̄ the pair chart with a one) whose product p = α β the covector follows,
    `λ_t ≈ w_re Re p_t + w_im Im p_t`, one triad after another on the remainder the earlier ones leave. Alternating least squares, each
    half-step the exact solve of its block (the return `w` given the legs; one leg given the return and the other leg, as a real system
    of 2(D + 1) unknowns in the return's own Gram), so the remainder's power never rises. Returns `a`, `b` (`[J][D + 1]` complex)."""
    rng = np.random.default_rng(seed)
    n, dw = read.shape
    rb = np.hstack([read, np.ones((n, 1))])
    rem = lam.copy()
    if weight is not None:
        # A row read once for several of its kind counts as that many: both sides of every least-squares sum take its root.
        root = np.sqrt(weight)[:, None]
        rem = rem * root
        rb_w = rb * np.sqrt(root)  # a product of two legs takes the root once
    else:
        rb_w = rb
    rb, rb_plain = rb_w, rb
    legs_a, legs_b = [], []

    def fit_return(p, rem):
        feats = np.stack([p.real, p.imag], axis=1)
        h = feats.T @ feats + ridge * (feats**2).sum() / 2 * np.eye(2)
        return np.linalg.solve(h, feats.T @ rem)  # [2][D]

    def fit_leg(other, w, rem):
        # With R(v) = r̄ᵀ diag(v) r̄, the leg's normal system is three weighted Grams of the chart (the product is real-linear in the leg's
        # real and imaginary parts), so no row is copied: A = R(o_r²), B = R(o_r o_i), C = R(o_i²).
        o_r, o_i = other.real, other.imag
        a_, b_, c_ = grams(rb, [o_r * o_r, o_r * o_i, o_i * o_i])
        g11, g12, g22 = w[0] @ w[0], w[0] @ w[1], w[1] @ w[1]
        top = np.hstack([g11 * a_ + 2 * g12 * b_ + g22 * c_, (g22 - g11) * b_ + g12 * (a_ - c_)])
        bottom = np.hstack([top[:, dw + 1 :].T, g11 * c_ - 2 * g12 * b_ + g22 * a_])
        g = np.vstack([top, bottom])
        g += ridge * np.trace(g) / len(g) * np.eye(len(g))
        t_re, t_im = rem @ w[0], rem @ w[1]
        rhs = np.concatenate([rb.T @ (o_r * t_re + o_i * t_im), rb.T @ (o_r * t_im - o_i * t_re)])
        z = np.linalg.solve(g, rhs)
        return z[: dw + 1] + 1j * z[dw + 1 :]

    for _ in range(triads):
        best = None
        for _ in range(starts):
            a = (rng.standard_normal(dw + 1) + 1j * rng.standard_normal(dw + 1)) / np.sqrt(dw)
            b = (rng.standard_normal(dw + 1) + 1j * rng.standard_normal(dw + 1)) / np.sqrt(dw)
            for _ in range(sweeps):
                w = fit_return((rb @ a) * (rb @ b), rem)
                a = fit_leg(rb @ b, w, rem)
                w = fit_return((rb @ a) * (rb @ b), rem)
                b = fit_leg(rb @ a, w, rem)
                na, nb = np.linalg.norm(a), np.linalg.norm(b)
                if na > 0 and nb > 0:
                    a, b = a * np.sqrt(nb / na), b * np.sqrt(na / nb)
            p = (rb @ a) * (rb @ b)
            w = fit_return(p, rem)
            left = ((rem - np.stack([p.real, p.imag], axis=1) @ w) ** 2).sum()
            if best is None or left < best[0]:
                best = (left, a, b, p, w)
        _, a, b, p, w = best
        before = (rem**2).sum()
        rem = rem - np.stack([p.real, p.imag], axis=1) @ w
        if log:
            log(len(legs_a), 1.0 - (rem**2).sum() / before)
        legs_a.append(a)
        legs_b.append(b)
    del rb_plain
    return np.array(legs_a), np.array(legs_b)


def grams(x, weights, threads=12, chunk=8192):
    """`xᵀ diag(v) x` for each `v` of `weights`, by blocks of rows on the host's threads (this host's BLAS is the reference one, one
    thread; the blocks' products release the interpreter)."""
    from concurrent.futures import ThreadPoolExecutor

    def block(lo):
        xs = x[lo : lo + chunk]
        return [xs.T @ (xs * v[lo : lo + chunk, None]) for v in weights]

    with ThreadPoolExecutor(threads) as pool:
        parts = list(pool.map(block, range(0, len(x), chunk)))
    return [sum(p[i] for p in parts) for i in range(len(weights))]


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
    for i, kind in enumerate(kinds):
        groups.setdefault((kind[0], kind[1], part_of(kind)), []).append(i)
    print("TENSION_CODE lengths op part places nats_a_digit")
    for key in sorted(groups):
        idx = np.array(groups[key])
        idx = idx[tick[idx] == 0]
        print(f"TENSION_CODE {key[0]} {key[1]} {key[2]} {len(idx)} {code[idx].mean():.4f}")
    met = np.array([k[0] == "met" for k in kinds])
    plus = np.array([k[1] == "+" for k in kinds])
    print("TENSION_SHARE scope tick rows power constant linear_chart standing_products linear_current")
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
            const = removed(np.zeros((len(lam), 0)), lam, f, t)
            print(f"TENSION_SHARE {scope} {k} {t.sum()} {power:.6e} {const:.4f} {lin:.4f} {standing:.4f} {lin_cur:.4f}")
    return rows, lam, read, cur, prod, ticks, kinds, tick, code, fit, test, met, plus


def onehot(values, n=10):
    out = np.zeros((len(values), n))
    out[np.arange(len(values)), values] = 1.0
    return out


def oracle(d):
    """The premise and the law's ceiling, by ruler: how well the pair chart and the gathered current give the aligned operand digits
    (a linear read's R² on the held half), and what an additive reading of the two digits, their table and the value's own digit
    remove of the covector's power."""
    rows, lam, read, cur, prod, ticks, kinds, tick, code, fit, test, met, plus = read_dir(d)
    da, db, dv = (np.array([k[i] for k in kinds]) for i in (4, 5, 6))
    part = np.array([PARTS.index(part_of(k)) for k in kinds])
    a1, b1, v1 = onehot(da), onehot(db), onehot(dv)
    pair = (a1[:, :, None] * b1[:, None, :]).reshape(len(rows), 100)
    centre = lambda x, sel: x - x[sel].mean(axis=0)
    none = np.zeros((len(rows), 0))
    print("TENSION_PRESENCE scope tick rows a_from_chart b_from_chart a_from_current b_from_current")
    for scope, mask in (("met", met), ("met+", met & plus), ("met+both", met & plus & (part <= 2)), ("far", ~met)):
        for k in range(ticks):
            sel = mask & (tick == k)
            f, t = sel & fit, sel & test
            ac, bc = centre(a1, sel), centre(b1, sel)
            print(f"TENSION_PRESENCE {scope} {k} {t.sum()} {removed(read, ac, f, t):.4f} {removed(read, bc, f, t):.4f} {removed(cur, ac, f, t):.4f} {removed(cur, bc, f, t):.4f}")
    print("TENSION_ORACLE scope part tick rows nats constant additive table value_digit linear_chart standing_products")
    for scope, mask in (("met+", met & plus), ("met-", met & ~plus), ("far+", ~met & plus)):
        for pid, pname in enumerate(PARTS):
            for k in range(ticks):
                sel = mask & (tick == k) & (part == pid)
                f, t = sel & fit, sel & test
                if t.sum() < 200:
                    continue
                print(f"TENSION_ORACLE {scope} {pname} {k} {t.sum()} {code[t].mean():.3f} {removed(none, lam, f, t):.4f} {removed(np.hstack([a1, b1]), lam, f, t):.4f} {removed(pair, lam, f, t):.4f} {removed(v1, lam, f, t):.4f} {removed(read, lam, f, t):.4f} {removed(prod, lam, f, t):.4f}")


def located_shares(d, triads=10):
    rows, lam, read, cur, prod, ticks, kinds, tick, code, fit, test, met, plus = read_dir(d)
    part = np.array([PARTS.index(part_of(k)) for k in kinds])
    da, db = (np.array([k[i] for k in kinds]) for i in (4, 5))
    pair = (onehot(da)[:, :, None] * onehot(db)[:, None, :]).reshape(len(rows), 100)
    j2 = prod.shape[1] // 2
    print("TENSION_LOCATED scope tick triads fit_rows test_rows share_fit share_test standing_test")
    print("TENSION_LOCATED_PART scope tick part test_rows located standing table")
    fb = np.hstack([read, np.ones((len(read), 1))])
    for scope, mask in (("met+", met & plus), ("met", met)):
        for k in range(ticks):
            sel = mask & (tick == k)
            f, t = sel & fit, sel & test
            # The linear chart's part is taken out first (what a present face could bridge), so the located share is the pool's own.
            w = np.linalg.lstsq(fb[f], lam[f], rcond=None)[0]
            rem = lam - fb @ w
            standing = removed(prod, rem, f, t) if prod.shape[1] else float("nan")
            a, b = locate(read[f], rem[f], triads)
            for j in sorted({1, 2, 5, triads}):
                feats = products_of(read, a[:j], b[:j])
                print(f"TENSION_LOCATED {scope} {k} {j} {f.sum()} {t.sum()} {removed(feats, rem, f, f):.4f} {removed(feats, rem, f, t):.4f} {standing:.4f}", flush=True)
            feats = products_of(read, a, b)
            for pid, pname in enumerate(PARTS):
                fp, tp = f & (part == pid), t & (part == pid)
                if tp.sum() < 200:
                    continue
                # The legs located on the scope's fit half; the return fitted on the part's fit half, read on the part's held half.
                print(f"TENSION_LOCATED_PART {scope} {k} {pname} {tp.sum()} {removed(feats, rem, fp, tp):.4f} {removed(prod, rem, fp, tp):.4f} {removed(pair, rem, fp, tp):.4f}", flush=True)
            np.save(os.path.join(d, f"legs_{scope.replace('+', 'plus')}_{k}.npy"), np.stack([a, b]))


def load_store(d, dtype=np.float32):
    dims = dict(line.split("\t") for line in open(os.path.join(d, "dims.tsv")).read().splitlines())
    dw, m2, j2, ticks = int(dims["lambda"]), int(dims["current"]), int(dims["products"]), int(dims["ticks"])
    rows = [line.split("\t") for line in open(os.path.join(d, "rows.tsv")).read().splitlines()]
    n = len(rows)
    lam = (np.fromfile(os.path.join(d, "lambda.i64"), dtype="<i8").reshape(n, dw) / 2.0**MATERIAL).astype(dtype)
    read = (np.fromfile(os.path.join(d, "read.i32"), dtype="<i4").reshape(n, dw) / 2.0**FACE).astype(dtype)
    prod = (np.fromfile(os.path.join(d, "products.i64"), dtype="<i8").reshape(n, j2) / 2.0**FACE).astype(dtype) if j2 else np.zeros((n, 0), dtype)
    return rows, lam, read, prod, ticks


def found(d, out, held_section=None, sweeps=12, every=4, forms=None):
    """Legs located on the sections of a `read-tension-store` directory, all ticks together (the legs are every tick's), and written for
    `found-crossing`. The last section is held out: its rows score each located product (the share of its covector's power the products
    remove, the return fitted on the other sections). A written site was kept one in `every`, so it counts `every` times. With `forms`, a
    `read-tension` directory, the same legs are read on its places by part (the return fitted on one half, read on the other)."""
    rows, lam, read, prod, ticks = load_store(d, np.float64)
    section = np.array([int(r[1]) for r in rows])
    opened = np.array([r[5] == "1" for r in rows])
    slices = np.array([r[0] for r in rows])
    held = section == (section.max() if held_section is None else held_section)
    fit = ~held
    weight = np.where(opened, 1.0, float(every))
    j = prod.shape[1] // 2
    print(f"FOUND_READ rows={len(rows)} fit_rows={fit.sum()} held_rows={held.sum()} open_share={opened.mean():.3f} triads={j} sections={section.max() + 1}", flush=True)
    root = np.sqrt(weight)[:, None]

    def share(features, f, t):
        return removed(features * root, lam * root, f, t)

    print(f"FOUND_BASE constant={share(np.zeros((len(rows), 0)), fit, held):.4f} linear_chart={share(read, fit, held):.4f} standing_products={share(prod, fit, held):.4f}", flush=True)
    steps = []
    def step(k, drop):
        steps.append(drop)
        print(f"FOUND_STEP triad={k} step_fit={drop:.4f}", flush=True)

    a, b = locate(read[fit], lam[fit], j, sweeps=sweeps, weight=weight[fit], log=step)
    for k in range(1, j + 1):
        feats = products_of(read, a[:k], b[:k])
        print(f"FOUND_LOCATED triads={k} step_fit={steps[k - 1]:.4f} share_fit={share(feats, fit, fit):.4f} share_held={share(feats, fit, held):.4f}", flush=True)
    feats = products_of(read, a, b)
    print("FOUND_SLICE slice kind held_rows power_share located standing linear_chart")
    total = (weight[held, None] * lam[held] ** 2).sum()
    for name in sorted(set(slices)):
        for kind, mask in (("open", opened), ("written", ~opened)):
            t = held & (slices == name) & mask
            f = fit & (slices == name) & mask
            if t.sum() < 500:
                continue
            print(f"FOUND_SLICE {name} {kind} {t.sum()} {(weight[t, None] * lam[t] ** 2).sum() / total:.4f} {share(feats, f, t):.4f} {share(prod, f, t):.4f} {share(read, f, t):.4f}")
    # The legs at the drawn founding's power (a drawn chart's real and imaginary parts have unit variance on a unit chart), the third leg
    # a constant of the same power, so the products stand at the scale the drawn products stood at.
    rb = np.hstack([read, np.ones((len(read), 1))])
    for legs in (a, b):
        power = (np.abs(rb[fit] @ legs.T) ** 2 * weight[fit, None]).sum(axis=0) / weight[fit].sum()
        legs *= np.sqrt(2.0 / power)[:, None]
    dw = read.shape[1]
    chart = np.zeros((6 * j, dw))
    bias = np.zeros(6 * j)
    chart[0:j], chart[j : 2 * j], chart[2 * j : 3 * j], chart[3 * j : 4 * j] = a.real[:, :dw], a.imag[:, :dw], b.real[:, :dw], b.imag[:, :dw]
    bias[0:j], bias[j : 2 * j], bias[2 * j : 3 * j], bias[3 * j : 4 * j] = a.real[:, dw], a.imag[:, dw], b.real[:, dw], b.imag[:, dw]
    bias[4 * j : 5 * j] = np.sqrt(2.0)
    words = np.concatenate([np.rint(chart * 2.0**MATERIAL).ravel(), np.rint(bias * 2.0**FACE)])
    assert np.abs(words).max() < 2**31, "a located leg past its 32-bit word"
    words.astype("<i4").tofile(out + ".legs")
    np.save(out + ".npy", np.stack([a, b]))
    print(f"FOUND_WRITTEN legs={out}.legs entries={len(words)} largest_chart={np.abs(chart).max():.3f} largest_bias={np.abs(bias).max():.3f}")
    if forms:
        apply_legs(forms, a, b)


def apply_legs(forms, a, b):
    """Legs read on a `read-tension` directory's places, by part: the share of the covector's power their products remove (the return
    fitted on one half of the records, read on the other), beside the standing products' and the pair's table's."""
    rows, lam, read, cur, prod, ticks, kinds, tick, code, fit, test, met, plus = read_dir(forms)
    part = np.array([PARTS.index(part_of(k)) for k in kinds])
    da, db = (np.array([k[i] for k in kinds]) for i in (4, 5))
    pair = (onehot(da)[:, :, None] * onehot(db)[:, None, :]).reshape(len(rows), 100)
    feats = products_of(read, a, b)
    print("FOUND_FORMS scope part tick test_rows nats located standing table linear_chart")
    for scope, mask in (("met+", met & plus), ("met-", met & ~plus)):
        for pid, pname in enumerate(PARTS):
            for k in range(ticks):
                sel = mask & (tick == k) & (part == pid)
                f, t = sel & fit, sel & test
                if t.sum() < 200:
                    continue
                print(f"FOUND_FORMS {scope} {pname} {k} {t.sum()} {code[t].mean():.3f} {removed(feats, lam, f, t):.4f} {removed(prod, lam, f, t):.4f} {removed(pair, lam, f, t):.4f} {removed(read, lam, f, t):.4f}")


def site_role(label, site):
    """A site's role in `a op b = value\\n`: ("a" | "b" | "v", its place counted from its number's last digit, its digit), or (None, …)."""
    _, _, op, a, b, v = label.split(":")
    at_b = len(a) + 3
    at_v = at_b + len(b) + 3
    for name, start, text in (("a", 0, a), ("b", at_b, b), ("v", at_v, v)):
        if start <= site < start + len(text) and text[site - start].isdigit():
            return name, start + len(text) - 1 - site, int(text[site - start])
    return None, -1, -1


def links(d, heads=4):
    """An operand digit's way to the answer's place, link by link, on a `read-tension … all` directory: (1) purity: how well a site's own
    chart gives its own digit; (2) place: how well a site's chart gives its place counted from its number's end, at the operands' digits
    and at the open place; (3) the lock: the open row's share on its aligned operand digits against the rest, by tick and head; (4) what
    arrives: how well each head's current at the open place gives the aligned digits. Every fit on one half of the records, read on the
    other."""
    dims = dict(line.split("\t") for line in open(os.path.join(d, "dims.tsv")).read().splitlines())
    dw, m2, ticks = int(dims["lambda"]), int(dims["current"]), int(dims["ticks"])
    rows = [line.split("\t") for line in open(os.path.join(d, "rows.tsv")).read().splitlines()]
    n = len(rows)
    chart = (np.fromfile(os.path.join(d, "chart.i32"), dtype="<i4").reshape(n, dw) / 2.0**FACE).astype(np.float32)
    cur = (np.fromfile(os.path.join(d, "current.i64"), dtype="<i8").reshape(n, m2) / 2.0**FACE).astype(np.float32)
    label = [r[0] for r in rows]
    tick = np.array([int(r[2]) for r in rows])
    site = np.array([int(r[4]) for r in rows])
    opened = np.array([r[5] == "1" for r in rows])
    met = np.array([l.split(":")[1] == "met" for l in label])
    plus = np.array([l.split(":")[2] == "+" for l in label])
    roles = [site_role(l, s) for l, s in zip(label, site)]
    role = np.array([{"a": 0, "b": 1, "v": 2, None: 3}[r[0]] for r in roles])
    k_end = np.array([r[1] for r in roles])
    digit = np.array([r[2] for r in roles])
    half = np.array([hashlib.sha256(f"half:{l}".encode()).digest()[0] % 2 for l in label])
    fit, test = half == 0, half == 1
    centre = lambda x, sel: x - x[sel].mean(axis=0)
    print(f"LINKS_READ rows={n} regions={int(opened.sum()) // ticks} ticks={ticks}")
    value_path = os.path.join(d, "value.i64")
    if os.path.exists(value_path):
        # What a source offers: its own digit read from its value word, every head's and each head's part (the head's 2n coordinates).
        val = (np.fromfile(value_path, dtype="<i8").reshape(n, m2) / 2.0**FACE).astype(np.float32)
        n_modes = m2 // (2 * heads)
        print("LINKS_VALUE scope role tick rows own_digit_from_value_all_heads head0 head1 head2 head3")
        for scope, mask in (("met+", met & plus),):
            for rname, rid in (("a", 0), ("b", 1)):
                for k in range(ticks):
                    sel = mask & (role == rid) & (tick == k) & ~opened
                    f, t = sel & fit, sel & test
                    if t.sum() < 300:
                        continue
                    target = centre(onehot(np.clip(digit, 0, 9)), sel)
                    by_head = []
                    for h in range(heads):
                        cols = np.r_[h * n_modes : (h + 1) * n_modes, m2 // 2 + h * n_modes : m2 // 2 + (h + 1) * n_modes]
                        by_head.append(removed(val[:, cols], target, f, t))
                    print(f"LINKS_VALUE {scope} {rname} {k} {t.sum()} {removed(val, target, f, t):.4f} " + " ".join(f"{x:.4f}" for x in by_head), flush=True)
    print("LINKS_PURITY scope role tick rows own_digit_from_chart place_from_chart")
    for scope, mask in (("met+", met & plus), ("far+", ~met & plus)):
        for rname, rid in (("a", 0), ("b", 1), ("v-known", 2), ("v-open", 2)):
            for k in range(ticks):
                sel = mask & (role == rid) & (tick == k) & (opened if rname == "v-open" else ~opened)
                f, t = sel & fit, sel & test
                if t.sum() < 300:
                    continue
                own = removed(chart, centre(onehot(np.clip(digit, 0, 9)), sel), f, t) if rname != "v-open" else float("nan")
                place = removed(chart, centre(onehot(np.clip(k_end, 0, 9)), sel), f, t)
                print(f"LINKS_PURITY {scope} {rname} {k} {t.sum()} {own:.4f} {place:.4f}", flush=True)
    # The lock: the open row's shares, from shares.tsv (label, place, tick, head, site, "j:share …" in millionths).
    acc, score_acc = {}, {}
    for line in open(os.path.join(d, "shares.tsv")):
        lab, place, k, h, i, *rest = line.rstrip("\n").split("\t")
        _, kind, op, a, b, v = lab.split(":")
        if op != "+":
            continue
        i = int(i)
        _, kv, _ = site_role(lab, i)
        at_b = len(a) + 3
        ak = len(a) - 1 - kv if kv < len(a) else None
        bk = at_b + len(b) - 1 - kv if kv < len(b) else None
        if ak is None or bk is None:
            continue
        cells = [x.split(":") for x in (rest[0].split(" ") if rest and rest[0] else [])]
        shares = dict((int(c[0]), int(c[1])) for c in cells)
        scores = dict((int(c[0]), int(c[2]) / 2.0**FACE) for c in cells if len(c) > 2)
        others = [j for j in list(range(len(a))) + list(range(at_b, at_b + len(b))) if j not in (ak, bk)]
        value_sites = [j for j in shares if j >= at_b + len(b) + 3]
        if scores:
            sc = score_acc.setdefault((kind, int(k), int(h)), [0, 0.0, 0.0, 0.0, 0, 0.0, 0])
            if ak in scores and bk in scores:
                sc[0] += 1
                sc[1] += scores[ak]
                sc[2] += scores[bk]
            rest_scores = [scores[j] for j in others if j in scores]
            if rest_scores:
                sc[3] += sum(rest_scores)
                sc[4] += len(rest_scores)
            vs = [scores[j] for j in value_sites if j in scores]
            if vs:
                sc[5] += sum(vs)
                sc[6] += len(vs)
        e = acc.setdefault((kind, int(k), int(h)), [0, 0.0, 0.0, 0.0, 0.0, 0.0])
        e[0] += 1
        e[1] += shares.get(ak, 0)
        e[2] += shares.get(bk, 0)
        e[3] += sum(shares.get(j, 0) for j in others) / max(len(others), 1)
        e[4] += sum(shares.get(j, 0) for j in value_sites)
        e[5] += sum(shares.values())
    print("LINKS_LOCK lengths tick head rows share_a_k share_b_k share_other_operand_digit share_value_sites share_all (millionths of the row)")
    for key in sorted(acc):
        e = acc[key]
        print(f"LINKS_LOCK {key[0]} {key[1]} {key[2]} {e[0]} {e[1] / e[0]:.0f} {e[2] / e[0]:.0f} {e[3] / e[0]:.0f} {e[4] / e[0]:.0f} {e[5] / e[0]:.0f}")
    if score_acc:
        print("LINKS_SCORE lengths tick head rows lock_a_k lock_b_k lock_other_operand_digit lock_value_site (the lock at unit gain, before the temperature and the falloff)")
        for key in sorted(score_acc):
            sc = score_acc[key]
            if sc[0]:
                print(f"LINKS_SCORE {key[0]} {key[1]} {key[2]} {sc[0]} {sc[1] / sc[0]:.3f} {sc[2] / sc[0]:.3f} {sc[3] / max(sc[4], 1):.3f} {sc[5] / max(sc[6], 1):.3f}")
    # What arrives: the aligned operand digits read from each head's current at the open place (columns both operands hold).
    by_region = {}
    for idx in np.nonzero(opened)[0]:
        lab = label[idx]
        _, kv, _ = site_role(lab, site[idx])
        _, _, op, a, b, v = lab.split(":")
        if kv < len(a) and kv < len(b):
            hi, lo = (int(a), int(b)) if (op == "+" or int(a) >= int(b)) else (int(b), int(a))
            by_region[idx] = ((hi // 10**kv) % 10, (lo // 10**kv) % 10)
    keep = np.array(sorted(by_region))
    da = np.array([by_region[i][0] for i in keep])
    db = np.array([by_region[i][1] for i in keep])
    n_modes = m2 // (2 * heads)
    print("LINKS_ARRIVES scope tick rows head a_from_current b_from_current (head -1: every head)")
    for scope, mask in (("met+", met & plus), ("far+", ~met & plus)):
        for k in range(ticks):
            sel = mask[keep] & (tick[keep] == k)
            f, t = sel & fit[keep], sel & test[keep]
            if t.sum() < 300:
                continue
            a1, b1 = centre(onehot(da), sel), centre(onehot(db), sel)
            c = cur[keep]
            print(f"LINKS_ARRIVES {scope} {k} {t.sum()} -1 {removed(c, a1, f, t):.4f} {removed(c, b1, f, t):.4f}")
            for h in range(heads):
                cols = np.r_[h * n_modes : (h + 1) * n_modes, m2 // 2 + h * n_modes : m2 // 2 + (h + 1) * n_modes]
                print(f"LINKS_ARRIVES {scope} {k} {t.sum()} {h} {removed(c[:, cols], a1, f, t):.4f} {removed(c[:, cols], b1, f, t):.4f}", flush=True)


def closed_lock(d, triads=10):
    """What a closed lock would open, by ruler arithmetic on a `read-tension` directory: in place of what the open row gathered, the two
    aligned operand digits as a lock closed on their column would bring them through a pure value, summed and unordered
    (`e(a_k) + e(b_k)`, ten coordinates; one digit alone where one operand holds the column). The covector's share that a linear read of
    that sum removes (a copy), and that products located on one half of the records remove on the other (a junction), by part, beside the
    pair's table. Nothing of the machine is changed: it says what the next founding could reach once the lock closes."""
    rows, lam, read, cur, prod, ticks, kinds, tick, code, fit, test, met, plus = read_dir(d)
    part = np.array([PARTS.index(part_of(k)) for k in kinds])
    da, db = (np.array([k[i] for k in kinds]) for i in (4, 5))
    held = np.array([k[7] for k in kinds])
    hi_only = (held == 1)[:, None]
    gathered = onehot(da) + np.where(hi_only, 0.0, onehot(db))
    gathered = np.where((held == 0)[:, None], 0.0, gathered)
    pair = (onehot(da)[:, :, None] * onehot(db)[:, None, :]).reshape(len(rows), 100)
    print("CLOSED_LOCK scope part tick test_rows nats linear_of_sum located_1 located_5 located_all table")
    for scope, mask in (("met+", met & plus), ("met-", met & ~plus)):
        for pid, pname in enumerate(PARTS):
            for k in (0, ticks - 1):
                sel = mask & (tick == k) & (part == pid)
                f, t = sel & fit, sel & test
                if t.sum() < 200 or pname == "top":
                    continue
                a, b = locate(gathered[f], lam[f], triads, sweeps=20, starts=3)
                shares = [removed(np.hstack([gathered, products_of(gathered, a[:j], b[:j])]), lam, f, t) for j in (1, 5, triads)]
                print(f"CLOSED_LOCK {scope} {pname} {k} {t.sum()} {code[t].mean():.3f} {removed(gathered, lam, f, t):.4f} {shares[0]:.4f} {shares[1]:.4f} {shares[2]:.4f} {removed(pair, lam, f, t):.4f}", flush=True)


def midpoint(d, triads=10):
    """One located midpoint (the lead, November 17; atlas `contact.row-barycentre-sum-outside-simplex`): on a `read-tension` directory,
    how much of the aligned digits' unordered sum `s = e(a_k) + e(b_k)` the answer site's pair chart holds, and what a junction could
    carry from it. The chart is 128 wide and a product's two legs on it are 256 numbers a product, more than a few thousand places can
    locate; a junction needs only the ten coordinates of `s`. So `ŝ = W r̂'` is the least-squares read of `s` from the chart, fitted on one
    half of the records, and products are located on `ŝ`'s ten coordinates (twenty numbers a product). By part and tick: the share of `s`
    the chart holds on the held half; the covector's share removed on the held half by a linear read of `ŝ`, by `ŝ` with five and with
    ten located products, by the true `s` with ten located products (a lock closed on the column), and by the pair's table."""
    rows, lam, read, cur, prod, ticks, kinds, tick, code, fit, test, met, plus = read_dir(d)
    part = np.array([PARTS.index(part_of(k)) for k in kinds])
    da, db = (np.array([k[i] for k in kinds]) for i in (4, 5))
    held = np.array([k[7] for k in kinds])
    s_true = onehot(da) + np.where((held == 1)[:, None], 0.0, onehot(db))
    s_true = np.where((held == 0)[:, None], 0.0, s_true)
    pair = (onehot(da)[:, :, None] * onehot(db)[:, None, :]).reshape(len(rows), 100)
    print("TENSION_MIDPOINT scope part tick test_rows nats sum_in_chart linear_of_read read_5_products read_10_products true_sum_10_products table")
    for scope, mask in (("met+", met & plus),):
        for pid, pname in enumerate(PARTS):
            for k in range(ticks):
                sel = mask & (tick == k) & (part == pid)
                f, t = sel & fit, sel & test
                if t.sum() < 200 or pname == "top":
                    continue
                target = s_true - s_true[sel].mean(axis=0)
                x = np.hstack([read, np.ones((len(read), 1))])
                w = np.linalg.solve(x[f].T @ x[f] + 1e-6 * np.eye(x.shape[1]), x[f].T @ target[f])
                s_hat = x @ w
                present = 1.0 - ((target[t] - s_hat[t]) ** 2).sum() / (target[t] ** 2).sum()
                out = []
                a, b = locate(s_hat[f], lam[f], triads, sweeps=20, starts=3)
                for j in (0, 5, triads):
                    out.append(removed(np.hstack([s_hat, products_of(s_hat, a[:j], b[:j])]) if j else s_hat, lam, f, t))
                a2, b2 = locate(s_true[f], lam[f], triads, sweeps=20, starts=3)
                closed = removed(np.hstack([s_true, products_of(s_true, a2, b2)]), lam, f, t)
                print(f"TENSION_MIDPOINT {scope} {pname} {k} {t.sum()} {code[t].mean():.3f} {present:.4f} " + " ".join(f"{v:.4f}" for v in out) + f" {closed:.4f} {removed(pair, lam, f, t):.4f}", flush=True)


def modes(d, triads=10):
    """The junction located on leading modes, with no label (the lead, November 17; the Demeter record §7: "a crossing's legs founded
    on the leading modes of the heads' gathered currents", a form for every stream that leaves the assignment to the field). On a
    `read-tension` directory, by part and tick: the pair chart and the gathered current are each reduced to their m leading principal
    coordinates on the fit half of the places (no digit is read), products are located on those coordinates from the covector alone
    (2m numbers a product in place of 256), and the share they remove is read on the held half, beside the pair's table. Against
    `midpoint`, whose ten coordinates are fitted to the digits' labels and which is a ruler's gate, never a founding."""
    rows, lam, read, cur, prod, ticks, kinds, tick, code, fit, test, met, plus = read_dir(d)
    part = np.array([PARTS.index(part_of(k)) for k in kinds])
    da, db = (np.array([k[i] for k in kinds]) for i in (4, 5))
    pair = (onehot(da)[:, :, None] * onehot(db)[:, None, :]).reshape(len(rows), 100)
    print("TENSION_MODES scope part tick test_rows source m linear products_5 products_all table")
    for scope, mask in (("met+", met & plus),):
        for pid, pname in enumerate(PARTS):
            for k in range(ticks):
                sel = mask & (tick == k) & (part == pid)
                f, t = sel & fit, sel & test
                if t.sum() < 200 or pname == "top":
                    continue
                for sname, x in (("chart", read), ("current", cur)):
                    centred = x - x[f].mean(axis=0)
                    _, _, vt = np.linalg.svd(centred[f], full_matrices=False)
                    for m in (8, 16):
                        z = centred @ vt[:m].T
                        a, b = locate(z[f], lam[f], triads, sweeps=20, starts=3)
                        out = [removed(z, lam, f, t)] + [removed(np.hstack([z, products_of(z, a[:j], b[:j])]), lam, f, t) for j in (5, triads)]
                        print(f"TENSION_MODES {scope} {pname} {k} {t.sum()} {sname} {m} " + " ".join(f"{v:.4f}" for v in out) + f" {removed(pair, lam, f, t):.4f}", flush=True)


def registers(d, codec):
    """A value digit's code read by its registers (the lead, November 17; Brandon's reminder of 00:44Z on radix and registers; atlas
    `radix.trailing-unit-rings`, `radix.carry-cascade-consumer`, `radix.carry-section-flux`). On a `read-tension` directory with
    `faces.i64` (the open place's whole face), the ten digits' shares of the face, taken among the digits, are split as the ring of
    ten splits: the bit (the digit modulo 2) and the five-residue given the bit, and the other way round; and, at a column both
    operands hold, the release of the redundant digit `a_k + b_k`: the digit up to its carry (the face's share on the pair sum's
    last digit and on the next digit together) and the carry's bit given that. Beside each stands a register that knows nothing:
    ln 2 for a bit, ln 5 for a five-residue or for a digit up to its carry, ln 10 for the digit. By part, nats a place."""
    rows, lam, read, cur, prod, ticks, kinds, tick, code, fit, test, met, plus = read_dir(d)
    with open(codec) as f:
        void = int(f.readline().split()[2])
        units = [int(x) for x in f.readline().split()]
    cls = {b: (k if k < void else k + 1) for k, b in enumerate(units)}
    alphabet = len(units) + 1
    faces = np.fromfile(os.path.join(d, "faces.i64"), dtype="<i8").reshape(-1, alphabet).astype(np.float64) / 2.0**20 * np.log(2.0)
    first = np.arange(0, len(rows), ticks)
    assert len(first) == len(faces), (len(first), len(faces))
    p = np.exp(-faces[:, [cls[48 + k] for k in range(10)]])
    mass = p.sum(axis=1)
    q = p / mass[:, None]
    part = np.array([PARTS.index(part_of(kinds[i])) for i in first])
    digit = np.array([kinds[i][6] for i in first])
    da, db, held = (np.array([kinds[i][j] for i in first]) for j in (4, 5, 7))
    carried = np.array([kinds[i][3] for i in first])
    sel_plus = np.array([kinds[i][1] == "+" and kinds[i][0] == "met" for i in first])
    n = np.arange(len(first))
    same_bit = np.array([[c % 2 == dd % 2 for c in range(10)] for dd in digit])
    same_five = np.array([[c % 5 == dd % 5 for c in range(10)] for dd in digit])
    whole = -np.log(q[n, digit])
    bit = -np.log((q * same_bit).sum(axis=1))
    five = -np.log((q * same_five).sum(axis=1))
    s = (da + db) % 10
    upto = -np.log(q[n, s] + q[n, (s + 1) % 10])
    print(f"TENSION_REGISTERS chance: bit {np.log(2):.3f}  five {np.log(5):.3f}  digit {np.log(10):.3f}")
    print("TENSION_REGISTERS part places off_the_digits digit bit five_given_bit five bit_given_five")
    for pid, pname in enumerate(PARTS):
        m = sel_plus & (part == pid)
        if m.sum() < 100:
            continue
        print(f"TENSION_REGISTERS {pname} {m.sum()} {(-np.log(mass[m])).mean():.4f} {whole[m].mean():.4f} {bit[m].mean():.4f} {(whole[m] - bit[m]).mean():.4f} {five[m].mean():.4f} {(whole[m] - five[m]).mean():.4f}")
    # The nine-ring (the digit sum's ring, 10 ≡ 1): a digit's three-residue, and its nine-residue (0 and 9 one class). A reader that
    # cast out nines would know an answer digit's nine-residue from the operands and the value's other digits.
    three = -np.log(np.array([[c % 3 == dd % 3 for c in range(10)] for dd in digit]).__mul__(q).sum(axis=1))
    nine = -np.log(np.array([[c % 9 == dd % 9 for c in range(10)] for dd in digit]).__mul__(q).sum(axis=1))
    chance9 = -np.mean([np.log(0.2 if dd % 9 == 0 else 0.1) for dd in digit[sel_plus]])
    print(f"TENSION_NINES part places three_residue(ln 3 = {np.log(3):.3f} less the uneven classes) nine_residue (a register that knows nothing: {chance9:.3f})")
    for pid, pname in enumerate(PARTS):
        m = sel_plus & (part == pid)
        if m.sum() < 100:
            continue
        flat3 = -np.mean([np.log(0.4 if dd % 3 == 0 else 0.3) for dd in digit[m]])
        flat9 = -np.mean([np.log(0.2 if dd % 9 == 0 else 0.1) for dd in digit[m]])
        print(f"TENSION_NINES {pname} {m.sum()} {three[m].mean():.4f} ({flat3:.4f}) {nine[m].mean():.4f} ({flat9:.4f})")
    print("TENSION_RELEASE columns places digit digit_up_to_its_carry carry_bit_given_that")
    for name, m in (("both hold, no carry in", sel_plus & (held == 2) & ~carried), ("both hold, a carry in", sel_plus & (held == 2) & carried)):
        if m.sum() < 100:
            continue
        print(f"TENSION_RELEASE {name.replace(' ', '_')} {m.sum()} {whole[m].mean():.4f} {upto[m].mean():.4f} {(whole[m] - upto[m]).mean():.4f}")


def circles(d, planted=False, harmonics=5, ridge=1e-3, shuffles=1000):
    """Whether a carry circle holds a digit's phase (the lead, November 17; the wheel record §9, October's face of harmonics). The circles'
    one face is `a(t) · Qm(t)`, linear in the arriving charge, so a phase of `2πd/10` reaches it through the first harmonic alone. Three
    reads on a `read-tension … all` directory, every fit on one half of the records and read on the other:

    - `CIRCLES_TURN`: by tick, over the written (definite) digits' sites, each circle's mean turn a digit `θ_d = arg mean(γ/|γ|)` and its
      characters `a_j = |Σ_d e^(iθ_d) e^(−2πijd/10)|/10` (`Σ_j a_j² = 1`): a wheel is one `a_j` near one at `j ≠ 0`, digits turning alike is
      `a_0` near one. The null is the same statistic under `shuffles` permutations of the ten digits.
    - `CIRCLES_HOLD`: by part and tick at the open place, the share of the value's digit, the wheel's digit and the unordered sum (each
      centred one-hots) given by the chart, by the charges read linearly, by the harmonics of all circles' phases, and by the harmonics of
      the one circle that reads the wheel's digit best on the fitting half.
    - `CIRCLES_TENSION`: the covector's share removed by the chart, the chart with the charges, the chart with their harmonics, beside the
      pair's table."""
    dims = dict(line.split("\t") for line in open(os.path.join(d, "dims.tsv")).read().splitlines())
    dw, ticks, c2 = int(dims["lambda"]), int(dims["ticks"]), int(dims["charge"])
    cn = c2 // 2
    rows = [line.split("\t") for line in open(os.path.join(d, "rows.tsv")).read().splitlines()]
    n = len(rows)
    label = [r[0] for r in rows]
    place = np.array([int(r[1]) for r in rows])
    tick = np.array([int(r[2]) for r in rows])
    code = np.array([int(r[3]) for r in rows]) / 2.0**20 * np.log(2.0)
    site = np.array([int(r[4]) for r in rows])
    opened = np.array([r[5] == "1" for r in rows])
    charge = np.memmap(os.path.join(d, "charge.i64"), dtype="<i8", mode="r", shape=(n, c2))
    gate = np.memmap(os.path.join(d, "gate.i64"), dtype="<i8", mode="r", shape=(n, c2))
    roles = [site_role(l, s_) for l, s_ in zip(label, site)]
    digit = np.array([r[2] for r in roles])
    half = np.array([hashlib.sha256(f"half:{l}".encode()).digest()[0] % 2 for l in label])
    fit, test = half == 0, half == 1
    rng = np.random.default_rng(17)
    print(f"CIRCLES_READ rows={n} regions={int(opened.sum()) // ticks} ticks={ticks} circles={cn} planted={int(planted)} ridge={ridge}")

    # (1) The gate's turn at a written digit's site, by the digit.
    omega = np.exp(-2j * np.pi * np.outer(np.arange(10), np.arange(10)) / 10)  # [j][d]
    perms = np.array([rng.permutation(10) for _ in range(shuffles)])
    print("CIRCLES_TURN tick digit_sites wheels_over_0.6 wheels_over_0.9 past_null_99 | best: circle= j= a_j= a_0= null_pct= within_digit_concentration= turn_range_rad= | median over circles: a_0= top_other=")
    for k in range(ticks):
        sel = np.flatnonzero((tick == k) & ~opened & (digit >= 0))
        g = np.asarray(gate[sel]).astype(np.float64) / 2.0**30
        z = g[:, :cn] + 1j * g[:, cn:]
        dsel = digit[sel]
        if planted:
            z[:, 0] = np.exp(1j * (2 * np.pi * (3 * dsel + 2) / 10 + 0.2 * rng.standard_normal(len(sel))))
        unit = z / np.maximum(np.abs(z), 1e-12)
        mean = np.array([unit[dsel == v].mean(axis=0) for v in range(10)])  # [d][circle]
        theta = np.angle(mean)
        conc = np.abs(mean).mean(axis=0)
        phase = np.exp(1j * theta)  # [d][circle]
        amp = np.abs(omega @ phase) / 10  # [j][circle]
        other = amp[1:].max(axis=0)
        null = np.array([(np.abs(omega @ phase[p]) / 10)[1:].max(axis=0) for p in perms])  # [shuffle][circle]
        pct = (null < other[None, :]).mean(axis=0)
        best = int(other.argmax())
        spread = np.array([np.ptp(np.unwrap(np.sort(theta[:, c]))) for c in range(cn)])
        print(f"CIRCLES_TURN {k} {len(sel)} {(other > 0.6).sum()} {(other > 0.9).sum()} {(pct > 0.99).sum()} | best: circle={best} j={1 + int(amp[1:, best].argmax())} a_j={other[best]:.3f} a_0={amp[0, best]:.3f} null_pct={pct[best]:.3f} within_digit_concentration={conc[best]:.3f} turn_range_rad={spread[best]:.3f} | median over circles: a_0={np.median(amp[0]):.3f} top_other={np.median(other):.3f}", flush=True)

    # (2), (3) At the open place.
    o = np.flatnonzero(opened)
    kinds = [place_kind(label[i], int(place[i])) for i in o]
    part = np.array([PARTS.index(part_of(kd)) for kd in kinds])
    da, db, dv = (np.array([kd[i] for kd in kinds]) for i in (4, 5, 6))
    held = np.array([kd[7] for kd in kinds])
    plus = np.array([kd[1] == "+" for kd in kinds])
    lam = np.fromfile(os.path.join(d, "lambda.i64"), dtype="<i8").reshape(n, dw)[o].astype(np.float64) / 2.0**MATERIAL
    read = np.fromfile(os.path.join(d, "read.i32"), dtype="<i4").reshape(n, dw)[o].astype(np.float64) / 2.0**FACE
    q = np.asarray(charge[o]).astype(np.float64) / 2.0**FACE
    zq = q[:, :cn] + 1j * q[:, cn:]
    wheel = (da + np.where(held == 2, db, 0)) % 10
    if planted:
        radius = np.median(np.abs(zq[:, 0])) + 1e-3
        zq[:, 0] = radius * np.exp(1j * (2 * np.pi * wheel / 10 + 0.15 * rng.standard_normal(len(o))))
    modulus = np.abs(zq)
    unit = np.where(modulus > 2.0**-FACE, zq / np.maximum(modulus, 1e-12), 0)
    q_lin = np.hstack([zq.real, zq.imag])
    harm = [np.hstack([(unit[:, c : c + 1] ** m).real for m in range(1, harmonics + 1)] + [(unit[:, c : c + 1] ** m).imag for m in range(1, harmonics + 1)]) for c in range(cn)]
    q_harm = np.hstack(harm)
    s_sum = np.where((held == 0)[:, None], 0.0, onehot(da) + np.where((held == 1)[:, None], 0.0, onehot(db)))
    pair = (onehot(da)[:, :, None] * onehot(db)[:, None, :]).reshape(len(o), 100)
    tk, fo, to, co = tick[o], fit[o], test[o], code[o]
    centre = lambda x, sel: x - x[sel].mean(axis=0)
    print(f"CIRCLES_CHARGE median_modulus_by_circle_on_2^-16_units " + " ".join(f"{v:.2f}" for v in np.median(modulus, axis=0)))
    print("CIRCLES_HOLD part tick test_rows nats | value_digit: chart charges harmonics | wheel_digit: chart charges harmonics best_circle=c:share | unordered_sum: chart charges harmonics")
    print("CIRCLES_TENSION part tick test_rows | covector share: chart chart+charges chart+harmonics value_digit table")
    for pid, pname in enumerate(PARTS):
        for k in range(ticks):
            sel = plus & (tk == k) & (part == pid)
            f, t = sel & fo, sel & to
            if t.sum() < 200:
                continue
            out = []
            for target in (onehot(dv), onehot(wheel), s_sum):
                tc = centre(target, sel)
                out.append([removed(x, tc, f, t, ridge) for x in (read, q_lin, q_harm)])
            wc = centre(onehot(wheel), sel)
            inside = [removed(h, wc, f, f, ridge) for h in harm]
            best = int(np.argmax(inside))
            best_share = removed(harm[best], wc, f, t, ridge)
            print(f"CIRCLES_HOLD {pname} {k} {t.sum()} {co[t].mean():.3f} | " + " ".join(f"{v:.4f}" for v in out[0]) + " | " + " ".join(f"{v:.4f}" for v in out[1]) + f" best_circle={best}:{best_share:.4f} | " + " ".join(f"{v:.4f}" for v in out[2]), flush=True)
            shares = [removed(x, lam, f, t, ridge) for x in (read, np.hstack([read, q_lin]), np.hstack([read, q_harm]), onehot(dv), pair)]
            print(f"CIRCLES_TENSION {pname} {k} {t.sum()} | " + " ".join(f"{v:.4f}" for v in shares), flush=True)


def junction(d, triads=10, heads=4):
    """The junction located on a head's current (the lead, November 17; atlas `contact.row-barycentre-sum-outside-simplex`,
    `contact.pool-founding`). A row brings its sources as a barycentre of their value words, and that barycentre is the head's gathered
    current before the return spreads it into the chart. So products are located with their legs on the current: each head's `2n`
    coordinates alone and every head's together, with no label. As `located` does, the linear chart's part is taken out of the covector
    first, the legs are located on one half of the records and their products' share is read on the other, by part and tick."""
    rows, lam, read, cur, prod, ticks, kinds, tick, code, fit, test, met, plus = read_dir(d)
    part = np.array([PARTS.index(part_of(k)) for k in kinds])
    da, db = (np.array([k[i] for k in kinds]) for i in (4, 5))
    pair = (onehot(da)[:, :, None] * onehot(db)[:, None, :]).reshape(len(rows), 100)
    m2 = cur.shape[1]
    n_modes = m2 // (2 * heads)
    cols = lambda h: np.r_[h * n_modes : (h + 1) * n_modes, m2 // 2 + h * n_modes : m2 // 2 + (h + 1) * n_modes]
    spaces = [(f"head={h}", cur[:, cols(h)]) for h in range(heads)] + [("heads=all", cur)]
    fb = np.hstack([read, np.ones((len(read), 1))])
    print(f"JUNCTION_READ products={triads} coordinates_a_head={2 * n_modes} heads={heads}")
    print("JUNCTION scope tick legs_on fit_rows test_rows share_fit share_test")
    print("JUNCTION_PART scope tick legs_on part test_rows located table")
    for scope, mask in (("met+", met & plus),):
        for k in range(ticks):
            sel = mask & (tick == k)
            f, t = sel & fit, sel & test
            w = np.linalg.lstsq(fb[f], lam[f], rcond=None)[0]
            rem = lam - fb @ w
            for name, x in spaces:
                a, b = locate(x[f], rem[f], triads, sweeps=20, starts=2)
                feats = products_of(x, a, b)
                print(f"JUNCTION {scope} tick={k} {name} {f.sum()} {t.sum()} {removed(feats, rem, f, f):.4f} {removed(feats, rem, f, t):.4f}", flush=True)
                for pid, pname in enumerate(PARTS):
                    fp, tp = f & (part == pid), t & (part == pid)
                    if tp.sum() < 200:
                        continue
                    print(f"JUNCTION_PART {scope} tick={k} {name} {pname} {tp.sum()} {removed(feats, rem, fp, tp):.4f} {removed(pair, rem, fp, tp):.4f}", flush=True)


def temper(d, heads=4):
    """The premise of a row's own temperature, on a `read-tension-store` directory: each open row's temperature covector `δℓ` (as the
    reverse forms it before the rows are summed into the head's one entry) beside the row's opening chart. By head: how nearly the rows'
    covectors cancel, what a linear read of the row's chart removes of their power on the held section, and each slice's mean ask (below
    zero: the code falls as the lock sharpens)."""
    dims = dict(line.split("\t") for line in open(os.path.join(d, "dims.tsv")).read().splitlines())
    dw, ticks = int(dims["lambda"]), int(dims["ticks"])
    rows = [line.split("\t") for line in open(os.path.join(d, "rows.tsv")).read().splitlines()]
    n = len(rows)
    chart = (np.fromfile(os.path.join(d, "chart.i32"), dtype="<i4").reshape(n, dw) / 2.0**FACE).astype(np.float64)
    at = {(r[0], int(r[1]), int(r[2]), int(r[3]), int(r[4])): k for k, r in enumerate(rows)}
    asks = [line.rstrip("\n").split("\t") for line in open(os.path.join(d, "temper.tsv"))]
    idx = np.array([at[(a[0], int(a[1]), int(a[2]), int(a[3]), int(a[4]))] for a in asks])
    head = np.array([int(a[5]) for a in asks])
    tick = np.array([int(a[4]) for a in asks])
    section = np.array([int(a[1]) for a in asks])
    slices = np.array([a[0] for a in asks])
    dl = np.array([int(a[6]) for a in asks], dtype=np.float64) / 2.0**40
    held = section == section.max()
    print(f"TEMPER_READ rows={len(asks)} fit_rows={(~held).sum()} held_rows={held.sum()} sections={section.max() + 1}")
    print("TEMPER_HEAD head held_rows sum_over_abs chart_share chart_share_by_tick…")
    for h in range(heads):
        sel = head == h
        f, t = sel & ~held, sel & held
        y = dl[:, None]
        balance = abs(dl[t].sum()) / np.abs(dl[t]).sum()
        share = removed(chart[idx], y, f, t)
        by_tick = [removed(chart[idx], y, f & (tick == k), t & (tick == k)) for k in range(ticks)]
        print(f"TEMPER_HEAD {h} {t.sum()} {balance:.4f} {share:.4f} " + " ".join(f"{x:.4f}" for x in by_tick), flush=True)
    print("TEMPER_SLICE head slice held_rows mean_ask rms_ask share_of_power")
    for h in range(heads):
        sel = (head == h) & held
        total = (dl[sel] ** 2).sum()
        for name in sorted(set(slices)):
            t = sel & (slices == name)
            if t.sum() == 0:
                continue
            print(f"TEMPER_SLICE {h} {name} {t.sum()} {dl[t].mean():+.3e} {np.sqrt((dl[t] ** 2).mean()):.3e} {(dl[t] ** 2).sum() / total:.4f}")


def heat(d):
    """The row's heat against its sources' spread (the lead, November 16; Brandon's lens of 23:00Z on barycentric location and basins
    on saddles; atlas `compression.anneal-split-temperature`, `contact.crowd-slip-bound`). A ruler on a `read-tension … all` directory's
    `shares.tsv`: an open row's shares are a Gibbs face over its sources, a point of their simplex, and the row stands at its crowd's
    barycentre while it is hot against the spread of its log-weights. For each open answer place of a sum whose column both operands
    hold, by tick and head: the row's entropy in nats beside the logarithm of its count of sources, the variance of its log-weights
    under its own shares (the square of its gain times the spread of its slips: under one, the row cannot tell its sources apart), how
    far the two aligned sources' log-weights stand above the row's mean in units of that spread, and the share the two aligned sources
    would hold with the row's gain raised by 2, 4, 8 and 16 at the same keys (p ∝ p^κ). Where the cooled row closes on the aligned
    pair the keys locate and the gain is short of its critical value; where it does not, the keys do not single the pair out. The
    power scales a row's whole log-weight: for a turned head that includes its falloff by distance, which no temperature scales, and
    at a later tick the keys themselves move with what arrived, so the engine's own answer is a read of a ruler's state
    (`athena … ruler-temper`). Each line names its tick and its head: on November 17 the lines of head 0 at ticks 1 to 3 were read
    as heads 1 to 3 at tick 0, and a message and a guess stood on the mislabel until a ruler's state showed it."""
    acc, off = {}, {}
    for line in open(os.path.join(d, "shares.tsv")):
        lab, place, k, h, i, *rest = line.rstrip("\n").split("\t")
        _, kind, op, a, b, v = lab.split(":")
        if op != "+" or not rest or not rest[0]:
            continue
        _, kv, _ = site_role(lab, int(i))
        if kv >= len(a) or kv >= len(b):
            continue
        at_b = len(a) + 3
        ak, bk = len(a) - 1 - kv, at_b + len(b) - 1 - kv
        cells = [x.split(":") for x in rest[0].split(" ")]
        js = np.array([int(c[0]) for c in cells])
        p = np.array([max(int(c[1]), 1) for c in cells], dtype=float)
        p /= p.sum()
        lw = np.log(p)
        mean = float((p * lw).sum())
        var = float((p * (lw - mean) ** 2).sum())
        pair = (js == ak) | (js == bk)
        if pair.sum() != 2:
            continue
        # Where the row's weight stands: by a source digit's place from its number's end, less the answer place's (0 the aligned
        # column, +1 the next higher place), beside the expression's other sites and the value's own.
        o = off.setdefault((kind, int(k), int(h)), [0] + [0.0] * 9)
        o[0] += 1
        for j, pj in zip(js, p):
            if j < len(a):
                delta = (len(a) - 1 - j) - kv
            elif at_b <= j < at_b + len(b):
                delta = (at_b + len(b) - 1 - j) - kv
            else:
                o[8 if j < at_b + len(b) + 3 else 9] += pj
                continue
            o[1 + min(max(delta, -3), 3) + 3] += pj
        e = acc.setdefault((kind, int(k), int(h)), [0] + [0.0] * 9)
        e[0] += 1
        e[1] += -mean
        e[2] += np.log(len(js))
        e[3] += var
        e[4] += float((lw[pair].mean() - mean) / np.sqrt(var)) if var > 0 else 0.0
        for n, kappa in enumerate((1, 2, 4, 8, 16)):
            q = p**kappa
            e[5 + n] += float(q[pair].sum() / q.sum())
    print("TENSION_HEAT lengths tick head rows entropy_nats log_sources log_weight_variance aligned_above_mean_in_spreads aligned_pair_share_at_gain_x1 x2 x4 x8 x16")
    for key in sorted(acc):
        e = acc[key]
        print(f"TENSION_HEAT {key[0]} tick={key[1]} head={key[2]} {e[0]} " + " ".join(f"{x / e[0]:.4f}" for x in e[1:]))
    print("TENSION_PLACE lengths tick head rows share_at_offset_-3_or_less -2 -1 0 +1 +2 +3_or_more other_expression_sites value_sites")
    for key in sorted(off):
        o = off[key]
        print(f"TENSION_PLACE {key[0]} tick={key[1]} head={key[2]} {o[0]} " + " ".join(f"{x / o[0]:.4f}" for x in o[1:]))


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    cmd = sys.argv[1]
    if cmd == "table":
        table(sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6]) if len(sys.argv) > 6 else None)
    elif cmd == "sums":
        sums_table(sys.argv[2], sys.argv[3], int(sys.argv[4]), sys.argv[5])
    elif cmd == "read":
        read_dir(sys.argv[2])
    elif cmd == "oracle":
        oracle(sys.argv[2])
    elif cmd == "located":
        located_shares(sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 10)
    elif cmd == "temper":
        temper(sys.argv[2])
    elif cmd == "closed":
        closed_lock(sys.argv[2])
    elif cmd == "midpoint":
        midpoint(sys.argv[2])
    elif cmd == "modes":
        modes(sys.argv[2])
    elif cmd == "registers":
        registers(sys.argv[2], sys.argv[3])
    elif cmd == "heat":
        heat(sys.argv[2])
    elif cmd == "junction":
        junction(sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 10)
    elif cmd == "circles":
        circles(sys.argv[2], planted=len(sys.argv) > 3 and sys.argv[3] == "planted")
    elif cmd == "links":
        links(sys.argv[2])
    elif cmd == "found":
        found(sys.argv[2], sys.argv[3], forms=sys.argv[4] if len(sys.argv) > 4 else None)
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()
