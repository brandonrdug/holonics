"""Exact phase-sensitive fluid receiver and a nonsampled Euler generator.

Exterior symbolic research only. This is neither an HNA learner nor a blowup
candidate. Run with Python + SymPy; stdout is the portable JSON receipt.
"""
import json

import sympy as sp


x, y, z, t = sp.symbols("x y z t", real=True)
nu = sp.symbols("nu", positive=True)
xyz = (x, y, z)
k, ell = (2, 1, 0), (-1, -1, 0)
a, b = sp.Matrix([0, 0, 1]), sp.Matrix([1, -1, 0])
A, B = 2*x + y, -x - y
zero = sp.zeros(3, 1)


def neg(q):
    return tuple(-v for v in q)


def source(sign):
    return {k: sign*a/2, neg(k): sign*a/2, ell: b/2, neg(ell): b/2}


def projected_nonlinearity(coefficients):
    """All ordered Fourier products of -P[(u . grad)u], with exact Leray P."""
    result = {}
    for p, up in coefficients.items():
        for q, uq in coefficients.items():
            m = tuple(p[i] + q[i] for i in range(3))
            result[m] = result.get(m, zero) - sp.I*up.dot(sp.Matrix(q))*uq
    for m, value in result.items():
        mv = sp.Matrix(m)
        if m != (0, 0, 0):
            value -= mv * (mv.dot(value) / mv.dot(mv))
        result[m] = sp.simplify(value)
    return {m: value for m, value in result.items() if value != zero}


def covariance(coefficients):
    return sum((v*coefficients[neg(q)].T for q, v in coefficients.items()), sp.zeros(3))


plus, minus = source(1), source(-1)
for coefficients in (plus, minus):
    assert all(sp.Matrix(q).dot(v) == 0 for q, v in coefficients.items())
    assert (1, 0, 0) not in coefficients
assert {q: v.dot(v.conjugate()) for q, v in plus.items()} == {
    q: v.dot(v.conjugate()) for q, v in minus.items()
}
assert covariance(plus) == covariance(minus) == (a*a.T + b*b.T)/2
outputs = [projected_nonlinearity(c) for c in (plus, minus)]
for sign, output in zip((1, -1), outputs):
    expected = {}
    for m in ((1, 0, 0), (3, 2, 0)):
        expected[m], expected[neg(m)] = -sign*sp.I*a/4, sign*sp.I*a/4
    assert output == expected

# A whole all-time Euler solution, verified independently in physical coordinates.
# A - t*cos(B) is the phase transported by the actual horizontal shear.
u = b*sp.cos(B) + a*sp.cos(A - t*sp.cos(B))
assert sp.simplify(sum(sp.diff(u[i], xyz[i]) for i in range(3))) == 0
assert (sp.diff(u, t) + u.jacobian(xyz)*u).applyfunc(sp.simplify) == zero
assert u.subs(t, 0) == b*sp.cos(B) + a*sp.cos(A)

# First positive-viscosity Duhamel response, retaining BOTH generated mode pairs.
# h = exp(-nu*|k|^2*t)*a*cos(A) + exp(-nu*|ell|^2*t)*b*cos(B).
responses = {}
for rho in (1, 13):
    F = (sp.exp(-nu*rho*t) - sp.exp(-7*nu*t)) / (nu*(7-rho))
    assert sp.simplify(sp.diff(F, t) + nu*rho*F - sp.exp(-7*nu*t)) == 0
    assert F.subs(t, 0) == 0
    assert sp.limit(F, nu, 0, dir="+") == t
    responses[str(rho)] = str(F)

print(json.dumps({
    "scope": "exact finite Fourier source; all-time explicit Euler solution; first NS Duhamel response",
    "chart": "dimensionless R^3/(2*pi*Z)^3; fixed spatial frame; nu>0 for NS formulas",
    "initial_fields": "u_plus/minus = b*cos(B) +/- a*cos(A)",
    "k": k, "ell": ell, "a": list(map(str, a)), "b": list(map(str, b)),
    "same_modal_energy": True,
    "same_mean_covariance": [[str(v) for v in row] for row in covariance(plus).tolist()],
    "initial_low_mode": ["0", "0", "0"],
    "plus_low_time_derivative": list(map(str, outputs[0][(1, 0, 0)])),
    "minus_low_time_derivative": list(map(str, outputs[1][(1, 0, 0)])),
    "all_generated_modes": sorted(outputs[0]),
    "exact_euler_generator": "b*cos(B) + a*cos(A-t*cos(B)); p=0",
    "euler_divergence_and_momentum_residual": "exactly zero",
    "first_duhamel_sine_amplitudes": {rho: f"({F})/2" for rho, F in responses.items()},
    "viscosity_zero_limit_of_each_sine_amplitude": "t/2",
    "claims_excluded": ["NS blowup", "HNA learning", "finite closure of the nonlinear spectral ladder"],
}, indent=2))
