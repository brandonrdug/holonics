"""Exact joint pressure receiver of two jet-preserving exterior directions.

Sparse Fourier vectors store u_hat(k)=i*A(k), with A in Q[rho,sigma].
All generated modes are retained. No coefficient interpolation or root quotient
is used in the source; the old quotient is used only for specialization checks.
"""

import contextlib
import io
import json
import math
import runpy
import sys
import time
from pathlib import Path

import flint
import sympy as sp
from flint import fmpq as Q, fmpq_mpoly_ctx

BASE = Path(__file__).parent
START = time.monotonic()


def progress(message):
    print(f"{time.monotonic() - START:.1f}s {message}", file=sys.stderr, flush=True)


with contextlib.redirect_stdout(io.StringIO()):
    src = runpy.run_path(str(BASE.parent / "mfr3_viscous_strain_source" / "source_spectrum.py"))
rho, sigma = sp.symbols("rho sigma", real=True)
x, y, z = src["x"], src["y"], src["z"]
ctx = fmpq_mpoly_ctx.get(("rho", "sigma"))
ZERO = ctx.constant(0)
ZV = (ZERO, ZERO, ZERO)
ORIGIN = (0, 0, 0)


def polynomial(value):
    return ctx.from_dict({powers: Q(str(coefficient)) for powers, coefficient
                          in sp.Poly(sp.expand(value), rho, sigma).terms()})


def symbolic(value):
    return sum((sp.Rational(str(c)) * rho**i * sigma**j
                for (i, j), c in value.to_dict().items()), sp.Integer(0))


def vadd(a, b):
    return tuple(a[i] + b[i] for i in range(3))


def dot(k, a):
    return k[0] * a[0] + k[1] * a[1] + k[2] * a[2]


def norm2(k):
    return sum(n * n for n in k)


def trim(field):
    return {k: v for k, v in field.items() if any(v)}


def real_odd(field):
    return all(field.get(tuple(-n for n in k), ZV) == tuple(-v for v in a)
               for k, a in field.items())


def real_even(field):
    return all(field.get(tuple(-n for n in k), ZERO) == a for k, a in field.items())


def matrix(field):
    return [[sum((-k[j] * a[i] for k, a in field.items()), ZERO)
             for j in range(3)] for i in range(3)]


def scalar_derivative(field, powers):
    order = sum(powers)
    assert order % 2 == 0
    sign = (-1) ** (order // 2)
    return sum((sign * math.prod(k[i] ** powers[i] for i in range(3)) * v
                for k, v in field.items()), ZERO)


def scalar_hessian(field):
    return [[scalar_derivative(field, tuple(int(k == i) + int(k == j) for k in range(3)))
             for j in range(3)] for i in range(3)]


def quartic(field):
    return {(i, j, 4 - i - j): scalar_derivative(field, (i, j, 4 - i - j)) /
            (math.factorial(i) * math.factorial(j) * math.factorial(4 - i - j))
            for i in range(5) for j in range(5 - i)}


def pressure_from_q(field):
    return {k: dot(k, v) / norm2(k) for k, v in field.items() if norm2(k) and dot(k, v)}


def source_step(field, nonlinear, pressure):
    return trim({k: tuple(-norm2(k) * field.get(k, ZV)[i]
                          + nonlinear.get(k, ZV)[i] - k[i] * pressure.get(k, ZERO)
                          for i in range(3))
                 for k in set(field) | set(nonlinear) | set(pressure)})


# Compose the new potential with the existing source constructor.
one_minus_cos2 = src["add"]({0: sp.Integer(1)}, {k: -v for k, v in src["cos2"].items()})
cutoff2 = src["mul1"](src["mul1"](one_minus_cos2, one_minus_cos2), one_minus_cos2)
delta_potential = src["mul"](src["embed"]({k: sigma * v for k, v in cutoff2.items()}, 2), src["psi"])
delta_u = [src["deriv"](delta_potential, 1),
           {k: -v for k, v in src["deriv"](delta_potential, 0).items()}, {}]
u = [src["add"](src["u"][i], delta_u[i]) for i in range(3)]
expected_delta = [src["mul"](src["embed"]({k: sigma * v for k, v in cutoff2.items()}, 2), src[name])
                  for name in ("Vx", "Vy")] + [{}]
assert all(src["add"](delta_u[i], {k: -v for k, v in expected_delta[i].items()}) == {} for i in range(3))
assert u[2] == src["u"][2]
A = {}
for i in range(3):
    for k, v in u[i].items():
        real_amplitude = sp.expand(v / sp.I)
        assert real_amplitude.is_real
        A.setdefault(k, [ZERO, ZERO, ZERO])[i] = polynomial(real_amplitude)
A = {k: tuple(v) for k, v in A.items()}
assert real_odd(A) and all(not dot(k, v) for k, v in A.items())
# The complete derivative population through six of either parameter variation is zero.
for param_index in (0, 1):
    direction = {k: tuple(ctx.constant(v.to_dict().get(tuple(int(j == param_index) for j in range(2)), Q(0)))
                           for v in vector) for k, vector in A.items()}
    for degree in range(7):
        for i in range(degree + 1):
            for j in range(degree + 1 - i):
                powers = (i, j, degree - i - j)
                for component in range(3):
                    assert not sum((math.prod(k[d] ** powers[d] for d in range(3)) * v[component]
                                    for k, v in direction.items()), ZERO)
progress(f"source and full jet fibre verified: {len(A)} modes")

Q0, poisson0, poisson_viscous_time = {}, {}, {}
for p, ap in A.items():
    for q, aq in A.items():
        k = tuple(p[i] + q[i] for i in range(3))
        d = dot(k, ap)
        Q0[k] = vadd(Q0.get(k, ZV), tuple(d * v for v in aq))
        trace_term = dot(p, aq) * dot(q, ap)
        poisson0[k] = poisson0.get(k, ZERO) + trace_term
        poisson_viscous_time[k] = (poisson_viscous_time.get(k, ZERO)
                                  - (norm2(p) + norm2(q)) * trace_term)
Q0 = trim(Q0)
assert Q0.get(ORIGIN, ZV) == ZV and not poisson0.get(ORIGIN, ZERO)
assert all(dot(k, Q0.get(k, ZV)) == v for k, v in poisson0.items())
P0 = pressure_from_q(Q0)
V = source_step(A, Q0, P0)
assert real_odd(V) and all(not dot(k, v) for k, v in V.items())
assert real_even(P0)
h = scalar_derivative(P0, (0, 0, 2))
assert not poisson_viscous_time.get(ORIGIN, ZERO)
Pt_viscous = {k: v / norm2(k) for k, v in poisson_viscous_time.items() if norm2(k) and v}
assert real_even(Pt_viscous)
progress(f"initial pressure and full velocity source verified: {len(V)} generated modes")

# Both ordered convection terms, and the independent two ordered trace terms.
Q1, poisson_t = {}, {}
for number, (p, vp) in enumerate(V.items()):
    for q, aq in A.items():
        k = tuple(p[i] + q[i] for i in range(3))
        dv, da = dot(k, vp), dot(k, aq)
        term = tuple(dv * aq[i] + da * vp[i] for i in range(3))
        Q1[k] = vadd(Q1.get(k, ZV), term)
        trace_term = dot(p, aq) * dot(q, vp)
        poisson_t[k] = poisson_t.get(k, ZERO) + 2 * trace_term
    if number % 500 == 0:
        progress(f"ordered pressure-time source {number}/{len(V)}")
Q1 = trim(Q1)
assert Q1.get(ORIGIN, ZV) == ZV and not poisson_t.get(ORIGIN, ZERO)
Pt = {k: v / norm2(k) for k, v in poisson_t.items() if norm2(k) and v}
assert Pt == pressure_from_q(Q1)
assert real_even(Pt)
ht = scalar_derivative(Pt, (0, 0, 2))
ht_viscous = scalar_derivative(Pt_viscous, (0, 0, 2))
assert h.total_degree() <= 2 and ht.total_degree() <= 2
(BASE / "axial_receivers.json").write_text(json.dumps({"pzz": str(symbolic(h)), "p_tzz": str(symbolic(ht)),
    "scope": "Exact axial polynomials; complete source audit is recorded in source_receipt.json"}, indent=2) + "\n")
progress("axial receivers available; finishing full second source and parent checks")
W = source_step(V, Q1, Pt)
assert real_odd(W) and all(not dot(k, v) for k, v in W.items())
Du, Dv, Dw = matrix(A), matrix(V), matrix(W)
H, Ht = scalar_hessian(P0), scalar_hessian(Pt)
P4, Pt4 = quartic(P0), quartic(Pt)

# Independent local Taylor/Poisson reduction, not inferred from the Fourier output.
local = json.loads((BASE / "local_jet_receipt.json").read_text())
def local_sub(value):
    return polynomial(sp.sympify(value, locals={"h": symbolic(h), "ht": symbolic(ht)}))
for name, actual in (("Du", Du), ("Dv", Dv), ("Dw", Dw), ("pressure_hessian", H)):
    assert actual == [[local_sub(value) for value in row] for row in local[name]]
assert matrix({k: tuple(-norm2(k) * value for value in v) for k, v in V.items()}) == [
    [local_sub(value) for value in row] for row in local["laplacian_Dv"]]

parent = json.loads((BASE.parent / "mfr3_viscous_strain_source" / "source_order3_receipt.json").read_text())
old_time = json.loads((BASE.parent / "mfr3_pressure_evolution" / "time_jet_receipt.json").read_text())
old_target = sp.Poly(sp.sympify(parent["pressure_hessian"]["target_polynomial"], locals={"rho": rho}), rho)

def remainder(value):
    return sp.Poly(sp.expand(value).subs(sigma, 0), rho).rem(old_target).as_expr()


def old_pair(value):
    return sum(sp.Rational(c) * rho**int(i) for i, c in value.items())


assert sp.expand(symbolic(h).subs(sigma, 0) - sp.sympify(parent["pressure_hessian"]["pzz"], locals={"rho": rho})) == 0
for powers, value in P4.items():
    assert sp.expand(symbolic(value).subs(sigma, 0) - sp.sympify(parent["pressure_degree4"]["p4_actual_coefficients"][str(powers)], locals={"rho": rho})) == 0
for name, actual in (("Du", Du), ("Dv", Dv), ("Dw", Dw), ("p_t_hessian", Ht)):
    for i in range(3):
        for j in range(3):
            assert remainder(symbolic(actual[i][j]) - old_pair(old_time["matrices_at_origin"][name][i][j])) == 0
for powers, value in Pt4.items():
    assert remainder(symbolic(value) - sp.sympify(old_time["quartic_p_t"]["coefficients_by_monomial"][str(powers)], locals={"rho": rho})) == 0

# The complete quartics reconstruct in the declared symmetry family.
def split_quartic(coeffs):
    av, bv, cv, dv, ev = (coeffs[p] for p in ((4,0,0),(2,2,0),(2,0,2),(0,0,4),(3,1,0)))
    L, M, b = (6*av+bv-3*dv)/8, cv+3*dv, (2*av-bv)/8
    sx = x*x+y*y
    shape = symbolic(L)*sx**2+symbolic(M)*sx*z*z+symbolic(dv)*(z**4-3*sx*z*z+sp.Rational(3,8)*sx**2)
    shape += symbolic(b)*(x**4-6*x*x*y*y+y**4)+symbolic(ev)*x*y*(x*x-y*y)
    expected = sum(symbolic(v)*x**p[0]*y**p[1]*z**p[2] for p,v in coeffs.items())
    assert sp.expand(shape-expected) == 0
    return {name: str(symbolic(value)) for name,value in zip(("L","M","D","b","c"),(L,M,dv,b,ev))}


def matrix_strings(matrix):
    return [[str(symbolic(v)) for v in row] for row in matrix]


receipt = {
    "scope": "Exact full finite source in Q[rho,sigma]; no positive-time or continuation claim",
    "arithmetic": "FLINT rational multivariate polynomials; no parameter interpolation or source quotient",
    "versions": {"sympy": sp.__version__, "python_flint": flint.__version__},
    "cutoff": "1+rho*(1-cos z)^3+sigma*(1-cos(2*z))^3",
    "checks": {"curl_reconstruction": True, "full_velocity_jet_through_six_preserved": True,
        "full_A_V_W_divergence_and_reality": True, "source_zero_modes": True,
        "initial_pressure_trace_equals_Q_projection": True,
        "pressure_time_ordered_trace_equals_Q_projection": True, "full_local_matrix_reduction": True,
        "initial_pressure_and_all_15_quartics_exact_parent_specialization": True,
        "all_time_matrices_and_15_quartics_parent_quotient_specialization": True,
        "full_quartic_symmetry_reconstruction": True, "axial_velocity_unchanged": True},
    "supports": {"u": len(A), "v": len(V), "w": len(W), "pressure": len(P0), "p_t": len(Pt)},
    "pzz": str(symbolic(h)), "p_tzz": str(symbolic(ht)),
    "p_tzz_viscous": str(symbolic(ht_viscous)),
    "p_tzz_convective": str(symbolic(ht - ht_viscous)),
    "Du": matrix_strings(Du), "Dv": matrix_strings(Dv), "Dw": matrix_strings(Dw),
    "pressure_hessian": matrix_strings(H), "pressure_time_hessian": matrix_strings(Ht),
    "initial_pressure_quartic": {str(k):str(symbolic(v)) for k,v in P4.items()},
    "pt_quartic": {str(k):str(symbolic(v)) for k,v in Pt4.items()},
    "initial_quartic_split": split_quartic(P4), "time_quartic_split": split_quartic(Pt4),
    "exit_status": 0,
}
progress("complete exact audit passed")
print(json.dumps(receipt, indent=2))
