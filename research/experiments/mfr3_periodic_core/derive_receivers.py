"""Exact symbolic receivers for two specified periodic concentrating core attempts.

Run with Python and sympy==1.14.0. The assertions check derivative algebra, not a PDE
existence theorem. The research record states the analytic limiting and sign arguments.
"""

import json

import sympy as sp


x, y, z = sp.symbols("x y z", real=True)
b = sp.symbols("b", positive=True)
alpha, beta, mu, lam, lam_jet = sp.symbols("alpha beta mu lam lam_jet", real=True)
coordinates = (x, y, z)
position = sp.Matrix(coordinates)
origin = dict.fromkeys(coordinates, 0)


def curl(field):
    return sp.Matrix([
        sp.diff(field[2], y) - sp.diff(field[1], z),
        sp.diff(field[0], z) - sp.diff(field[2], x),
        sp.diff(field[1], x) - sp.diff(field[0], y),
    ])


def laplacian(field):
    return field.applyfunc(lambda entry: sum(sp.diff(entry, q, 2) for q in coordinates))


def check_equal(left, right):
    difference = left - right
    if isinstance(difference, sp.MatrixBase):
        assert all(sp.simplify(entry) == 0 for entry in difference), difference
    else:
        assert sp.simplify(difference) == 0, difference


eta = sp.exp(sum(sp.cos(b * q) - 1 for q in coordinates) / b**2)
v = sp.Matrix([sp.sin(b * q) / b for q in coordinates])
cosine = sp.Matrix([sp.cos(b * q) for q in coordinates])
transverse = cosine[0] + cosine[1] - v[0]**2 - v[1]**2
toroidal = eta * sp.Matrix([-v[1], v[0], 0])
even_poloidal = eta * sp.Matrix([v[0] * v[2], v[1] * v[2], transverse])
odd_poloidal = eta * sp.Matrix([
    v[0] * (v[2]**2 - cosine[2]),
    v[1] * (v[2]**2 - cosine[2]),
    v[2] * transverse,
])

check_equal(curl(sp.Matrix([0, 0, eta])), toroidal)
check_equal(curl(toroidal), even_poloidal)
check_equal(curl(curl(sp.Matrix([0, 0, v[2] * eta]))), odd_poloidal)

centre_receipts = {}
for name, poloidal in (("even", even_poloidal), ("odd", odd_poloidal)):
    field = toroidal + lam * poloidal
    vorticity = curl(field)
    check_equal(sum(sp.diff(field[i], coordinates[i]) for i in range(3)), 0)
    check_equal(toroidal.dot(poloidal), 0)
    # b_s = -beta*b. The modulation derivative is retained before evaluation.
    vorticity_time_jet = -beta * b * sp.diff(vorticity, b) + lam_jet * sp.diff(vorticity, lam)
    # curl(Du[u]) = Domega[u] - Du[omega] for the checked divergence-free field.
    nonlinear_curl = vorticity.jacobian(coordinates) * field - field.jacobian(coordinates) * vorticity
    residual_curl = (
        vorticity_time_jet + nonlinear_curl - mu * laplacian(vorticity)
        + beta * vorticity.jacobian(coordinates) * position
        + (alpha + beta) * vorticity
    )
    centre = sp.simplify(residual_curl[2].subs(origin))
    expected = 2 * (alpha + beta) + 2 * mu * (5 + b**2)
    if name == "odd":
        expected -= 4 * lam
    check_equal(centre, expected)
    centre_receipts[name] = sp.sstr(centre)

g = sp.exp(-(x**2 + y**2 + z**2) / 2)
gaussian_toroidal = curl(sp.Matrix([0, 0, g]))
gaussian_odd_poloidal = curl(curl(sp.Matrix([0, 0, z * g])))
check_equal(gaussian_odd_poloidal, g * sp.Matrix([
    x * (z**2 - 1), y * (z**2 - 1), z * (2 - x**2 - y**2),
]))
gaussian_field = gaussian_toroidal + lam * gaussian_odd_poloidal
gaussian_advection = gaussian_field.jacobian(coordinates) * gaussian_field
gaussian_residual = (
    gaussian_advection + beta * gaussian_field.jacobian(coordinates) * position
    + alpha * gaussian_field + lam_jet * gaussian_odd_poloidal
)
axis = sp.simplify(curl(gaussian_residual)[2].subs({x: 0, y: 0}))
expected_axis = 2 * (alpha + beta - beta * z**2) * sp.exp(-z**2 / 2) - 4 * lam * sp.exp(-z**2)
check_equal(axis, expected_axis)
second = sp.simplify(axis.subs({
    alpha: sp.Rational(3, 2) * beta,
    lam: sp.Rational(5, 4) * beta,
    z: sp.sqrt(sp.Rational(5, 2)),
}))
check_equal(second, -5 * beta * sp.exp(-sp.Rational(5, 2)))
general_second = sp.simplify(axis.subs({
    lam: (alpha + beta) / 2,
    z: sp.sqrt((alpha + beta) / beta),
}))
check_equal(general_second, -2 * (alpha + beta) * sp.exp(-(alpha + beta) / beta))

# A constructive axis relation, retaining the positive-vorticity denominator explicitly.
f_axis = sp.Function("F")(z)
primitive = sp.Function("I")(z)
constant = sp.symbols("C", real=True)
w_axis = -beta * z + f_axis * (constant + (alpha + 2 * beta) * primitive)
axis_balance = (w_axis + beta * z) * sp.diff(f_axis, z) + (
    alpha + beta - sp.diff(w_axis, z)
) * f_axis
check_equal(axis_balance.subs(sp.diff(primitive, z), 1 / f_axis), 0)

print(json.dumps({
    "scope": "Exact derivative algebra for the specified periodic cores and Gaussian limit; no existence or stability claim",
    "sympy_version": sp.__version__,
    "periodic_scale": "b = 2*pi*ell; b_s = -beta*b",
    "third_curl_residual_at_centre": centre_receipts,
    "odd_centre_required_modulation": "lam = (alpha + beta + mu*(5 + b**2))/2",
    "gaussian_axis_third_curl_residual": sp.sstr(expected_axis),
    "energy_critical_modulation": "alpha = 3*beta/2; lam = 5*beta/4",
    "second_receiver": "(0, 0, sqrt(5/2))",
    "second_receiver_third_curl_residual": sp.sstr(second),
    "general_second_receiver": "(0, 0, sqrt((alpha+beta)/beta)); alpha,beta > 0",
    "general_second_receiver_third_curl_residual": sp.sstr(general_second),
    "coupled_axis_balance": "(W+beta*z)*F' + (alpha+beta-W')*F = 0",
    "constructed_axis_velocity": "W=-beta*z+F*(C+(alpha+2*beta)*I); I'=1/F; F>0",
}, indent=2))
