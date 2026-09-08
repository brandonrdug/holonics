#!/usr/bin/env python3
"""Exact paired-producer adjoint on an actual contextual material return.

Cold observer only. Run Python with -P in a SymPy environment. The native checkpoint
owner supplies the history export; no cultivation or model mutation takes place here.
"""

import argparse
import importlib.util
import json
from pathlib import Path
import time
from fractions import Fraction as F
from sympy import I, Matrix, Rational, eye, simplify

spec = importlib.util.spec_from_file_location(
    "contextual_return_observer",
    Path(__file__).with_name("inspect_contextual_return.py"),
)
c = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c)


def vector(values):
    def q(v):
        return Rational(v.numerator, v.denominator)

    return Matrix(
        [q(values[i]) + I * q(values[i + 1]) for i in range(0, len(values), 2)]
    )


def fractions(v):
    result = []
    for x in v:
        for a in x.expand(complex=True).as_real_imag():
            result.append(F(int(a.p), int(a.q)))
    return result


def norm2(v):
    return sum(x * x for x in fractions(v))


def assert_zero(v):
    assert all(simplify(x) == 0 for x in v)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("history", type=Path)
    parser.add_argument("--receiving", type=int, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    start = time.monotonic()
    if args.report.exists():
        parser.error("report already exists")
    q = args.receiving
    p = q - 1
    if q < 2:
        parser.error("an existing producer with a preceding current is required")
    c.rows = []
    with args.history.open() as f:
        for line in f:
            x = json.loads(line)
            w = x["words"]
            at = x["occurrence"]
            assert (
                at == len(c.rows)
                and len(w) == 2796
                and w[c.META + 3] == 2
                and w[c.CTX + 6 * c.D + 15] == c.G
            )
            c.rows.append(
                dict(w=w, c=c.profile(w), reference=w[c.META + 2], source=w[c.META + 1])
            )
            if at == q:
                break
    assert len(c.rows) == q + 1 and c.rows[q]["source"] == p
    g, error = c.full_context_cotangent(q)
    g = vector(g)
    current = vector([F(v, c.S) for v in c.explicit_context(p, p)])
    before = vector([F(v, c.S) for v in c.explicit_context(p - 1, p)])
    births = []
    contacts = []
    for birth in range(p + 1):
        w = c.rows[birth]["w"]
        if c.rows[birth]["source"] < 0:
            continue
        raw = c.vec(w, c.IN, 4 * c.N + 1)
        target, ey = c.ball(w, 2)
        assert ey == 0 and c.wide(w, c.IN + 16 * c.N + 8) == 0
        contacts.append(
            vector([F(v, raw[-1]) for v in raw[:-1]] + [-F(v, c.S) for v in target])
        )
        births.append(birth)
    # R is the actual row map d_i*. Woodbury uses the existing contact population.
    R = Matrix.vstack(*[d.conjugate().T for d in contacts])
    ports = c.D // 2
    go = g[:ports, 0]
    gb = g[ports:, 0]
    out = current[:ports, 0]
    b_out = current[ports:, 0]
    b_in = before[ports:, 0]
    raw = c.vec(c.rows[p]["w"], c.OUT, 4 * c.N + 1)
    u = vector([F(v, raw[-1]) for v in raw[:-1]] + [F(0)] * (2 * c.N))
    v = out + u
    assert_zero(R * v - b_in - b_out) # primal current identity
    A = eye(ports) + R.conjugate().T * R
    inv_small = (eye(len(births)) + R * R.conjugate().T).inv(method="DM")
    h = go + R.conjugate().T * gb
    lam = h - R.conjugate().T * (inv_small * (R * h))
    assert_zero(A * lam - h)
    reflected_source = 2 * lam - go
    reflected_internal = 2 * R * lam - gb
    assert norm2(reflected_source) + norm2(reflected_internal) == norm2(g)
    # All old internal rows are existing state. The just-born zero input is separate.
    old = [j for j, birth in enumerate(births) if birth < p]
    old_return = Matrix([reflected_internal[j] for j in old])
    k = b_in - b_out
    ell = gb - R * lam
    contact_return = lam * k.conjugate().T + v * ell.conjugate().T
    ec = F(c.rows[p]["c"]["error"], c.S)
    ep = F(c.rows[p - 1]["c"]["error"], c.S)
    ek = ep + ec
    morph_error = (
        error * (c.norm_upper(norm2(k)) + ek)
        + c.norm_upper(norm2(lam)) * ek
        + ec * (c.norm_upper(norm2(ell)) + error)
        + c.norm_upper(norm2(v)) * error
    )
    assert norm2(old_return) > error * error
    assert norm2(contact_return) > morph_error * morph_error
    # A concrete admitted old-current tangent returns nonzero under the material covector.
    z = Matrix.zeros(len(births), 1)
    for j in old:
        z[j] = reflected_internal[j]
    dv = 2 * (
        R.conjugate().T * z
        - R.conjugate().T * (inv_small * (R * (R.conjugate().T * z)))
    )
    tangent = Matrix.vstack(dv, R * dv - z)
    assert norm2(tangent) == norm2(z)
    assert simplify((g.conjugate().T * tangent)[0]).as_real_imag()[0] == Rational(
        norm2(z).numerator, norm2(z).denominator
    )
    report = dict(
        truth_status="established-bounded",
        evidence_tags=["computational-witness"],
        history=str(args.history),
        receiving=q,
        producer=p,
        producer_input=p - 1,
        contact_births=births,
        native_recurrence_changed=False,
        numerical_cotangent=fractions(g),
        cotangent_error_upper=error,
        numerical_source_return=fractions(reflected_source),
        numerical_internal_return=fractions(reflected_internal),
        old_internal_rows=old,
        old_internal_return_norm_squared=norm2(old_return),
        old_internal_return_certified_nonzero=True,
        newborn_constraint_reaction=fractions(
            Matrix(
                [reflected_internal[j] for j, birth in enumerate(births) if birth == p]
            )
        ),
        contact_port_factors=[fractions(lam), fractions(v)],
        contact_current_factors=[fractions(k), fractions(ell)],
        contact_return_norm_squared=norm2(contact_return),
        contact_return_error_upper=morph_error,
        contact_return_certified_nonzero=True,
        producer_cotangent_energy_identity=True,
        admitted_old_current_tangent_isometry=True,
        numerical_admitted_direction_receiver=norm2(z),
        no_language_quality_claim=True,
        whole_wall_seconds=time.monotonic() - start,
    )
    with args.report.open("x") as f:
        json.dump(report, f, default=c.encode, indent=2)
        f.write("\n")
    print(
        json.dumps(
            dict(
                report=str(args.report),
                old_internal_norm_squared_display=float(norm2(old_return)),
                cotangent_error_display=float(error),
                contact_norm_squared_display=float(norm2(contact_return)),
                contact_error_display=float(morph_error),
                whole_wall_seconds=report["whole_wall_seconds"],
            )
        )
    )


if __name__ == "__main__":
    main()
