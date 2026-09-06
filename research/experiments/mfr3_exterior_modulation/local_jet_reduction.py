"""Local source reduction, independent of the global Fourier calculation.

The input is the accepted fifth-order velocity jet and the C4-invariant pressure
Hessians. The pressure Poisson equation determines Laplacian(Dv) locally, even
though neither pressure Hessian is determined by this velocity jet.
"""

import json

import sympy as sp


x, y, z, h, ht = sp.symbols("x y z h ht", real=True)
coordinates = (x, y, z)
a = sp.Rational(10, 3)
s = x**2 + y**2
omega = 1 - s / 6 + s**2 / 54
u = sp.Matrix([-a * x / 2 - omega * y, -a * y / 2 + omega * x, a * z])
J = u.jacobian(coordinates)


def laplacian(vector):
    return vector.applyfunc(lambda value: sum(sp.diff(value, c, 2) for c in coordinates))


def at_origin(value):
    return sp.simplify(value.subs({x: 0, y: 0, z: 0}))


def gradient(value):
    return sp.Matrix([sp.diff(value, c) for c in coordinates])


def matrix_strings(matrix):
    return [[str(value) for value in row] for row in matrix.tolist()]


J0 = at_origin(J)
poisson_source = sp.trace(J * J)
trace_H = -at_origin(poisson_source)
H = sp.diag((trace_H - h) / 2, (trace_H - h) / 2, h)
assert trace_H == -sp.Rational(44, 3)
V0 = sp.simplify(at_origin(laplacian(u).jacobian(coordinates)) - J0 * J0 - H)
# v = Lap(u) - (u.grad)u - grad(p), with -Lap(p) = tr(Du^2).
lap_V0 = at_origin((laplacian(laplacian(u)) - laplacian(J * u)
                   + gradient(poisson_source)).jacobian(coordinates))
assert lap_V0 == sp.Matrix([[0, sp.Rational(16, 3), 0],
                           [-sp.Rational(16, 3), 0, 0], [0, 0, 0]])
trace_Ht = -sp.trace(V0 * J0 + J0 * V0)
Ht = sp.diag((trace_Ht - ht) / 2, (trace_Ht - ht) / 2, ht)
W0 = sp.simplify(lap_V0 - V0 * J0 - J0 * V0 - Ht)
spin_second = sp.simplify((W0[1, 0] - W0[0, 1]) / 2)
assert spin_second == -h - sp.Rational(88, 9)
assert sp.simplify(W0[2, 2] - (2 * a**3 + 2 * a * h - ht)) == 0
pressure_match = -sp.Rational(160, 9)
assert V0.subs(h, pressure_match) == 2 * J0
assert spin_second.subs(h, pressure_match) == 8
ratio_second_on_match = sp.simplify((W0[2, 2] - 8 * a).subs(h, pressure_match))
assert ratio_second_on_match == -sp.Rational(640, 9) - ht

print(json.dumps({
    "scope": "Exact local polynomial source identities for the accepted velocity jet and C4-invariant pressure Hessians",
    "symbols": {"h": "p_zz(0)", "ht": "p_tzz(0)"},
    "input_velocity_jet": [str(value) for value in u],
    "pressure_hessian": matrix_strings(H),
    "Du": matrix_strings(J0), "Dv": matrix_strings(V0),
    "laplacian_Dv": matrix_strings(lap_V0), "Dw": matrix_strings(W0),
    "spin_second": str(spin_second),
    "pressure_match": str(pressure_match),
    "ratio_second_on_match": str(ratio_second_on_match),
    "checks": {"local_poisson_trace_retained": True, "laplacian_source_reduced": True,
               "first_gradient_match": True, "spin_second_on_match": True,
               "relative_strain_second_reduced": True},
    "sympy_version": sp.__version__, "exit_status": 0,
}, indent=2))
