#!/usr/bin/env python3
"""Cold exact-rational receiver over the public alpha_contextual_lift history export.

This is an observer, not a learner. It never opens the exposure dataset, changes a model,
chooses a current from an enclosure, or supplies an application answer. The declared
receiver is the existing 18-port, grain-72 text study, bilinear source chart version 2.
Pair bounds concern exact fitting of these observed points, not a demand for perfect
prediction or identification. Display decimals are explicitly exterior measurements.
Run with `python -P` in an environment containing SymPy; the sibling historical
`inspect.py` must not shadow Python's standard-library module.
"""

import json
import math
from fractions import Fraction as F
from pathlib import Path

G = 72
S = 1 << G
N = 18
R = 36
D = 108
BETA = 22 * (R + 1)
OUT = 52 * N + 22
IN = 68 * N + 34
CTX = 84 * N + 46
META = 150 * N + 68
EXTRA = META + 4


def wide(w, i):
    z = (w[i] % (1 << 64)) + (w[i + 1] % (1 << 64)) * (1 << 64)
    return z - (1 << 128) if z >= (1 << 127) else z


def big(w, i):
    return sum((w[i + j] % (1 << 64)) << (64 * j) for j in range(4)) * (
        -1 if w[i + 4] else 1
    )


def vec(w, i, n):
    return [wide(w, i + 2 * j) for j in range(n)]


def dot(a, b):
    return (
        sum(a[j] * b[j] + a[j + 1] * b[j + 1] for j in range(0, len(a), 2)),
        sum(a[j] * b[j + 1] - a[j + 1] * b[j] for j in range(0, len(a), 2)),
    )


def profile(w):
    q = CTX
    return dict(
        out=vec(w, q, D),
        prefix=vec(w, q + 2 * D, D),
        image=vec(w, q + 4 * D, D),
        offset=(big(w, q + 6 * D), big(w, q + 6 * D + 5)),
        norm=big(w, q + 6 * D + 10),
        error=wide(w, q + 6 * D + 16),
        upper=wide(w, q + 6 * D + 20),
    )


def kernel(a, b, i, j):
    if j < i:
        a, b, i, j = b, a, j, i
    re, im = dot(a["image"], b["prefix"])
    re -= a["offset"][0]
    im += a["offset"][1]
    sg = 1 if (i + j) % 2 == 0 else -1
    ro, io = dot(a["out"], b["out"])
    re = sg * re + ro
    im = sg * im + io
    z = F((S * S + re) ** 2 + im * im, (S * S + a["norm"]) * (S * S + b["norm"]))
    assert 0 <= z <= 1, (i, j, float(z))
    return z


def qerror(a):
    lower = max(S, a["upper"] - a["error"] - 1)
    return min(F(2), F(2 * a["error"], lower))


def ball(w, i):
    return vec(w, 2 * i * (R + 1), R), wide(w, 2 * (i * (R + 1) + R))


def code(v, e):
    diffs = [v[4 * b + 2] - v[4 * b] for b in range(9)]
    pos = sum((d > 0) << b for b, d in enumerate(diffs))
    unres = sum((d * d <= 2 * e * e) << b for b, d in enumerate(diffs))
    return pos, unres


def pair(a, b, i, j):
    if j < i:
        re, im = pair(b, a, j, i)
        return re, -im
    re, im = dot(a["image"], b["prefix"])
    re -= a["offset"][0]
    im += a["offset"][1]
    sg = 1 if (i + j) % 2 == 0 else -1
    ro, io = dot(a["out"], b["out"])
    return F(sg * re + ro, S * S), F(sg * im + io, S * S)


def norm_upper(q):
    z = (q.numerator * S * S) // q.denominator
    r = math.isqrt(z)
    if r * r * q.denominator < q.numerator * S * S:
        r += 1
    return F(r, S)


def ksource(wa, wb):
    a = vec(wa, IN + 8 * N + 2, 4 * N)
    b = vec(wb, IN + 8 * N + 2, 4 * N)
    re, im = dot(a, b)
    return F(
        (S * S + re) ** 2 + im * im,
        (S * S + sum(x * x for x in a)) * (S * S + sum(x * x for x in b)),
    )


def derivative(query, reference, at):
    c = rows[query - 1]["c"]
    d = rows[reference - 1]["c"]
    v = rows[at - 1]["c"]
    cv = pair(c, v, query - 1, at - 1)
    dv = pair(d, v, reference - 1, at - 1)
    cd = pair(c, d, query - 1, reference - 1)
    z = (1 + cv[0], cv[1])
    dz = (cv[0] - dv[0], cv[1] - dv[1])
    a = 1 + F(c["norm"], S * S)
    b = 1 + F(v["norm"], S * S)
    dn = 2 * (F(c["norm"], S * S) - cd[0])
    k = (z[0] ** 2 + z[1] ** 2) / (a * b)
    return 2 * (z[0] * dz[0] + z[1] * dz[1]) / (a * b) - k * dn / a


def tangent(query):
    # This receipt uses the actual producing operator and condition without a delayed-cut
    # translation: the queried material source is immediately preceding reception.
    assert rows[query]["source"] == query - 1
    reference = rows[query]["reference"]
    assert 0 < reference < query
    c = rows[query - 1]["c"]
    r = rows[reference - 1]["c"]
    delta2 = (
        F(c["norm"] + r["norm"], S * S) - 2 * pair(c, r, query - 1, reference - 1)[0]
    )
    result = [F(0) for _ in range(R)]
    forward = [F(0) for _ in range(R)]
    for j in range(1, query):
        row = rows[j]
        w = row["w"]
        if row["source"] < 0:
            continue
        bj = vec(w, BETA, R)
        bt = vec(w, BETA + 2 * R, R)
        kd = ksource(rows[query]["w"], w) * derivative(query, reference, j)
        ref = row["reference"]
        kr = (
            ksource(rows[query]["w"], rows[ref]["w"])
            * derivative(query, reference, ref)
            if ref < j
            else 0
        )
        kj = ksource(rows[query]["w"], w) * kernel(
            c, rows[j - 1]["c"], query - 1, j - 1
        )
        kref = (
            ksource(rows[query]["w"], rows[ref]["w"])
            * kernel(c, rows[ref - 1]["c"], query - 1, ref - 1)
            if ref < j
            else 0
        )
        for o in range(R):
            result[o] += F(bj[o] + bt[o], S) * kd - F(bt[o], S) * kr
            forward[o] += F(bj[o] + bt[o], S) * kj - F(bt[o], S) * kref
    presented, _ = ball(rows[query]["w"], 1)
    eval_error = F(wide(rows[query]["w"], EXTRA + 10), S)
    assert sum((a - F(b, S)) ** 2 for a, b in zip(forward, presented)) <= eval_error**2
    residual, er = ball(rows[query]["w"], 6)
    residual = [F(v, S) for v in residual]
    g = sum(a * b for a, b in zip(residual, result))
    energy = sum(v * v for v in result)
    E = F(wide(rows[query - 1]["w"], EXTRA), S)
    Nm = F(wide(rows[query - 1]["w"], EXTRA + 2), S)
    ec = F(c["error"], S)
    eref = F(r["error"], S)
    ev = (2 * E + 20 * Nm * ec) * norm_upper(delta2) + 2 * (Nm + E) * (ec + eref)
    eg = (
        F(er, S) * (norm_upper(energy) + ev)
        + norm_upper(sum(x * x for x in residual)) * ev
    )
    assert wide(rows[query]["w"], IN + 16 * N + 8) == 0
    return dict(
        receiving=query,
        reference=reference,
        context=[query - 1, reference - 1],
        numerical_direction_norm_squared=delta2,
        numerical_directional_return=result,
        numerical_cotangent_on_direction=g,
        cotangent_error_upper=eg,
        cotangent_interval=[g - eg, g + eg],
        native_recurrence_changed=False,
    )


def explicit_context(at, last):
    # Reconstruct the numerical born-current coordinates independently of prefix pairing.
    current = rows[at]["c"]
    values = list(current["out"])
    for birth in range(last + 1):
        w = rows[birth]["w"]
        if rows[birth]["source"] < 0:
            continue
        if birth > at:
            values.extend([0, 0])
            continue
        raw = vec(w, IN, 4 * N + 1)
        den = raw[-1]
        source = raw[:-1]
        target, _ = ball(w, 2)
        assert all(x % den == 0 for x in source) and all(x % S == 0 for x in target)
        drive = [x // den for x in source] + [-x // S for x in target]
        before = rows[birth - 1]["c"]["prefix"]
        difference = [x - y for x, y in zip(current["prefix"], before)]
        re, im = dot(drive, difference)
        sg = 1 if (at - birth) % 2 == 0 else -1
        values.extend([sg * re, sg * im])
    return values


def verify_prefix_and_derivative(query):
    reference = rows[query]["reference"]
    last = query - 1
    actual = [explicit_context(at, last) for at in range(query)]
    c = actual[query - 1]
    base = actual[reference - 1]
    direction = [x - y for x, y in zip(c, base)]
    from sympy import I, Rational, Symbol, conjugate, diff, simplify

    t = Symbol("t", real=True)

    def zpair(a, b):
        re, im = dot(a, b)
        return Rational(re, S * S) + I * Rational(im, S * S)

    for at in range(query):
        v = actual[at]
        assert sum(x * x for x in v) == rows[at]["c"]["norm"]
        re, im = dot(c, v)
        assert pair(rows[query - 1]["c"], rows[at]["c"], query - 1, at) == (
            F(re, S * S),
            F(im, S * S),
        )
        z = 1 + zpair(c, v) + t * zpair(direction, v)
        norm = (
            1
            + zpair(c, c)
            + 2 * t * zpair(c, direction).as_real_imag()[0]
            + t * t * zpair(direction, direction)
        )
        value = z * conjugate(z) / (norm * (1 + zpair(v, v)))
        d = simplify(diff(value, t).subs(t, 0))
        assert F(int(d.p), int(d.q)) == derivative(query, reference, at + 1)
    return dict(
        explicit_born_coordinate_pairings=query,
        symbolic_kernel_directional_derivatives=query,
    )


def scalar_adjoint_control():
    # Independent matrix differential: arbitrary complex phase and Hermitian covector.
    from sympy import I, Matrix, Rational, Symbol, simplify, trace

    t = Symbol("t", real=True)
    c = Matrix([Rational(2, 3) + I / 5, -Rational(1, 4) + I / 2])
    d = Matrix([I / 3, Rational(3, 7) - I / 2])
    u = Matrix([1, *c])
    v = Matrix([0, *d])
    a = (u.conjugate().T * u)[0]
    A = Matrix(
        [[2, 1 + I, I / 3], [1 - I, -1, Rational(2, 5)], [-I / 3, Rational(2, 5), 3]]
    )
    Q = u * u.conjugate().T / a
    ut = u + t * v
    Qt = ut * ut.conjugate().T / (ut.conjugate().T * ut)[0]
    dQ = Qt.diff(t).subs(t, 0)
    g = 2 * (A * u - trace(A * Q) * u) / a
    left = trace(A * dQ)
    right = (g.conjugate().T * v)[0].as_real_imag()[0]
    assert simplify(left - right) == 0
    return dict(exact_complex_adjoint_duality=True)


def encode(value):
    if isinstance(value, F):
        return dict(numerator=str(value.numerator), denominator=str(value.denominator))
    raise TypeError(type(value).__name__)


if __name__ == "__main__":
    import argparse, time

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("history", type=Path)
    parser.add_argument("--receiving", type=int, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    started = time.monotonic()
    if args.report.exists():
        parser.error("report already exists")
    rows = []
    for l in open(args.history):
        x = json.loads(l)
        w = x["words"]
        assert x["occurrence"] == len(rows) and len(w) == 2796 and w[META + 3] == 2
        assert x["rows"] == 1 and x["width"] == 2796 and x["grain"] == 0
        assert w[CTX + 6 * D + 15] == G
        rows.append(dict(w=w, c=profile(w), reference=w[META + 2], source=w[META + 1]))
    last = {}
    pairs = []
    counts = {}
    correct = bits = linked = unresolved = 0
    for i, row in enumerate(rows):
        w = row["w"]
        ref = row["reference"]
        p, e = ball(w, 1)
        y, ey = ball(w, 2)
        if row["source"] < 0:
            continue
        linked += 1
        pc, pu = code(p, e)
        yc, yu = code(y, ey)
        assert yu == 0
        correct += pc == yc and pu == 0
        bits += sum(
            not (pu >> b & 1) and (pc >> b & 1) == (yc >> b & 1) for b in range(9)
        )
        unresolved += bool(pu)
        group = counts.setdefault(i // 512, dict(count=0, correct=0, unresolved=0))
        group["count"] += 1
        group["correct"] += pc == yc and pu == 0
        group["unresolved"] += bool(pu)
        if ref in last:
            j = last[ref]
            other = rows[j]
            assert w[IN : IN + 8 * N + 2] == other["w"][IN : IN + 8 * N + 2]
            assert wide(w, IN + 16 * N + 8) == 0
            z = kernel(row["c"], row["c"], i, i)
            assert z == 1
            k = kernel(rows[i - 1]["c"], rows[j - 1]["c"], i - 1, j - 1)
            err = min(F(2), qerror(rows[i - 1]["c"]) + qerror(rows[j - 1]["c"]))
            upper_distance = min(F(2), 2 * (1 - k + err))
            yj, _ = ball(other["w"], 2)
            target = F(sum((a - b) ** 2 for a, b in zip(y, yj)), S * S)
            lower_norm2 = target / upper_distance if upper_distance else None
            pairs.append(
                dict(
                    i=i,
                    j=j,
                    reference=ref,
                    k=k,
                    kerror=err,
                    target=target,
                    lower_norm2=lower_norm2,
                )
            )
        last[ref] = i
    norm = F(wide(rows[-1]["w"], EXTRA + 2) + wide(rows[-1]["w"], EXTRA), S)
    strong = sorted(
        [p for p in pairs if p["lower_norm2"] is not None],
        key=lambda p: p["lower_norm2"],
        reverse=True,
    )
    controls = verify_prefix_and_derivative(args.receiving) | scalar_adjoint_control()
    returned = tangent(args.receiving)
    report = dict(
        truth_status="established-bounded",
        evidence_tags=["computational-witness"],
        history=str(args.history),
        native_recurrence_changed=False,
        observed_occurrences=len(rows),
        linked_receiving_occurrences=linked,
        correctly_predicted_codewords=correct,
        correctly_resolved_bits=bits,
        unresolved_codewords=unresolved,
        native_reference_families=len(last),
        chronological_512_occurrence_batches=counts,
        consecutive_family_pairs=len(pairs),
        final_operator_norm_upper=norm,
        pairs_requiring_larger_operator_for_exact_fit=sum(
            p["lower_norm2"] > norm * norm for p in strong
        ),
        strongest_pair_bounds=strong[:8],
        cotangent_return=returned,
        verification=controls,
        no_language_quality_claim=True,
        whole_wall_seconds=time.monotonic() - started,
    )
    with args.report.open("x") as f:
        json.dump(report, f, default=encode, indent=2)
        f.write("\n")
    print(
        json.dumps(
            dict(
                report=str(args.report),
                receiving=args.receiving,
                correct_codewords=correct,
                linked=linked,
                cotangent_display=float(returned["numerical_cotangent_on_direction"]),
                cotangent_error_display=float(returned["cotangent_error_upper"]),
                verification=controls,
                whole_wall_seconds=report["whole_wall_seconds"],
            )
        )
    )
