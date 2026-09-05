"""Exact full second-resonance source in the reflection-symmetric radial jet.

Coefficients are affine in Y=W15[z] and polynomial in X=a^2. Storing J=X*G
keeps every coefficient polynomial through radial mode 28. FLINT performs only
rational polynomial arithmetic; no root approximation or floating coefficient
enters the recurrence. Actual A, B, C products independently recompute all rows.
"""

import json
import sys
from pathlib import Path

import flint
from flint import fmpq as Q, fmpq_poly as Poly

BASE = Path(__file__).parent
X = Poly([0, 1])
ALPHA, BETA, KAPPA = Q(3, 2), Q(1), Q(7, 2)
MAX_MODE = 28
NW = lambda m: 61 - 2 * m
NJ = lambda m: 60 - 2 * m


class Affine:
    """An exact c(X)+Y*d(X), with every discarded quadratic term forbidden."""
    __slots__ = ("c", "d")

    def __init__(self, c=0, d=0):
        self.c = c if isinstance(c, Poly) else Poly([c])
        self.d = d if isinstance(d, Poly) else Poly([d])

    def __bool__(self):
        return bool(self.c) or bool(self.d)

    def __add__(self, other):
        return Affine(self.c + other.c, self.d + other.d)

    def __neg__(self):
        return Affine(-self.c, -self.d)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        assert not (self.d and other.d), "A Y^2 product has entered the declared aperture"
        return Affine(self.c * other.c, self.c * other.d + self.d * other.c)

    def scale(self, scalar):
        return Affine(self.c * scalar, self.d * scalar)

    def divide_X(self):
        assert self.c[0] == self.d[0] == 0, "J product not divisible by X"
        return Affine(self.c.right_shift(1), self.d.right_shift(1))


ZERO = Affine()


def trim(series, degree):
    return {n: v for n, v in series.items() if n <= degree and v}


def add(*series):
    result = {}
    for item in series:
        for n, value in item.items():
            result[n] = result.get(n, ZERO) + value
    return {n: v for n, v in result.items() if v}


def scale(series, scalar):
    return {n: v.scale(scalar) for n, v in series.items() if v}


def derivative(series):
    return {n - 1: v.scale(Q(n)) for n, v in series.items() if n > 0}


def times_z(series):
    return {n + 1: v for n, v in series.items()}


def product(left, right, degree):
    result = {}
    for i, a in left.items():
        for j, b in right.items():
            if i + j <= degree:
                result[i + j] = result.get(i + j, ZERO) + a * b
    return {n: v for n, v in result.items() if v}


def binomial_axis(exponent, degree):
    coefficients = [Q(0)] * (degree + 1)
    current = Q(1)
    for j in range(degree // 2 + 1):
        if j:
            current *= (exponent - j + 1) / j
        coefficients[2 * j] = current
    return Poly(coefficients)


def scalar_series(poly):
    return {n: Affine(c) for n, c in enumerate(poly.coeffs()) if c}


G0z = binomial_axis(Q(-5, 4), NJ(0))
I0z = binomial_axis(Q(5, 4), NJ(0)).integral()
W0z = KAPPA * G0z.mul_low(I0z, NW(0) + 1) - Poly([0, 1])
W = [scalar_series(W0z)]
J = [{n: Affine(X * c) for n, c in enumerate(G0z.coeffs()) if c}]
V = [scale(derivative(W[0]), Q(-1, 2))]
Gamma = dict(W[0])
Gamma = add(Gamma, {1: Affine(BETA)})
Gamma_scalar = {n: a.c[0] for n, a in Gamma.items()}
W0prime = {n: a.c[0] for n, a in derivative(W[0]).items()}
assert all(not a.d and a.c.degree() <= 0 for a in Gamma.values())


def radial_A(m, degree):
    out = add(scale(V[m], ALPHA + BETA + 2 * BETA * m),
              scale(times_z(derivative(V[m])), BETA))
    for i in range(m + 1):
        j = m - i
        out = add(out, product(W[i], derivative(V[j]), degree),
                  scale(product(V[i], V[j], degree), Q(2 * j + 1)))
        jj = product(J[i], J[j], degree)
        out = add(out, {n: -a.divide_X() for n, a in jj.items()})
    return trim(out, degree)


def axial_B(m, degree):
    out = add(scale(W[m], ALPHA + 2 * BETA * m),
              scale(times_z(derivative(W[m])), BETA))
    for i in range(m + 1):
        j = m - i
        out = add(out, product(W[i], derivative(W[j]), degree),
                  scale(product(V[i], W[j], degree), Q(2 * j)))
    return trim(out, degree)


def swirl_CJ(m, degree):
    out = add(scale(J[m], ALPHA + BETA + 2 * BETA * m),
              scale(times_z(derivative(J[m])), BETA))
    for i in range(m + 1):
        j = m - i
        out = add(out, product(W[i], derivative(J[j]), degree),
                  scale(product(V[i], J[j], degree), Q(2 * (j + 1))))
    return trim(out, degree)


def solve_transport(m, rhs, degree, parity, kind):
    # Both matrices come from the actual axis Gamma and W0'; they have rational
    # entries independent of X and Y. No resonant diagonal is divided by zero.
    if kind == "W":
        d = {n: (1 - m) * c for n, c in W0prime.items()}
        d[0] = d.get(0, Q(0)) + ALPHA + 2 * m * BETA
    else:
        d = {n: -(m + 1) * c for n, c in W0prime.items()}
        d[0] = d.get(0, Q(0)) + ALPHA + (2 * m + 1) * BETA
    solution, resonances = {}, {}
    for n in range(parity, degree + 1, 2):
        lower = ZERO
        for j, c in Gamma_scalar.items():
            target = n - j + 1
            if j > 1 and target >= 0:
                lower = lower + solution.get(target, ZERO).scale(c * target)
        for j, c in d.items():
            if j > 0 and n >= j:
                lower = lower + solution.get(n - j, ZERO).scale(c)
        diagonal = Gamma_scalar[1] * n + d[0]
        unpaid = rhs.get(n, ZERO) - lower
        if diagonal:
            value = unpaid.scale(1 / diagonal)
        else:
            resonances[n] = -unpaid
            if kind == "W":
                assert (m, n) == (15, 1) and not unpaid
                value = Affine(0, 1)
            else:
                assert (m, n) in ((14, 2), (28, 4))
                value = ZERO
        if value:
            solution[n] = value
    return solution, resonances


assert not swirl_CJ(0, NJ(0)), "Axis construction failed its actual swirl row"
rows = []
J14_parameter = None
for m in range(1, MAX_MODE + 1):
    W.append({})
    V.append({})
    J.append({})
    pressure_rhs = add(derivative(radial_A(m - 1, NW(m) + 1)),
                       scale(axial_B(m, NW(m)), Q(-2 * m)))
    pressure_rhs = trim(pressure_rhs, NW(m))
    if m == 15:
        # The W15[z] multiplier is zero. Pressure reads the previous J14[z^2]
        # fibre with coefficient -4; J=XG removed the superficial X divisor.
        J14_parameter = pressure_rhs.get(1, ZERO).scale(Q(1, 4))
        assert not J14_parameter.d
        homogeneous = G0z.pow_trunc(15, NJ(14) + 1).mul_low(
            I0z.mul_low(I0z, NJ(14) + 1), NJ(14) + 1)
        assert homogeneous[2] == 1
        J[14] = add(J[14], {n: J14_parameter.scale(c)
                           for n, c in enumerate(homogeneous.coeffs()) if c})
        pressure_rhs = add(derivative(radial_A(14, NW(m) + 1)),
                           scale(axial_B(m, NW(m)), Q(-2 * m)))
        assert not pressure_rhs.get(1, ZERO), "Pressure did not determine the prior fibre"
    W[m], wres = solve_transport(m, scale(pressure_rhs, Q(1, 2 * m)), NW(m), 1, "W")
    V[m] = scale(derivative(W[m]), Q(-1, 2 * (m + 1)))
    jrhs = scale(swirl_CJ(m, NJ(m)), Q(-1))
    J[m], jres = solve_transport(m, jrhs, NJ(m), 0, "J")
    rows.append({"mode": m, "axial_resonant_powers": list(wres),
                 "swirl_resonant_powers": list(jres),
                 "max_degree_X_W": max((a.c.degree() for a in W[m].values()), default=-1),
                 "max_degree_X_J": max((a.c.degree() for a in J[m].values()), default=-1)})
    print(f"progress full_mode={m} W_resonances={list(wres)} J_resonances={list(jres)}",
          file=sys.stderr, flush=True)

# Independently recompute the actual nonlinear products after the J14 fibre update.
pressure_rows, swirl_rows = {}, {}
for m in range(1, MAX_MODE + 1):
    pressure_rows[m] = trim(add(derivative(radial_A(m - 1, NW(m) + 1)),
                                scale(axial_B(m, NW(m)), Q(-2 * m))), NW(m))
    swirl_rows[m] = swirl_CJ(m, NJ(m))
    assert not pressure_rows[m], ("pressure residual", m)
    if m not in (14, 28):
        assert not swirl_rows[m], ("swirl residual", m)
    # Complete incompressibility at every retained coefficient, not a count check.
    assert not add(scale(V[m], Q(2 * (m + 1))), derivative(W[m]))
    print(f"progress recomputed_mode={m}", file=sys.stderr, flush=True)
assert set(swirl_rows[14]) == {2}
assert set(swirl_rows[28]) == {4}
first = swirl_rows[14][2]
second = swirl_rows[28][4]
# The zero representative does not settle the resonant J28[z^4] fibre. This
# coefficient enters every retained source linearly; a unit perturbation is
# invisible to its entire retained swirl row and cannot enter earlier modes.
representative_J28 = J[28]
J[28] = add(J[28], {4: Affine(1)})
free_fibre_difference = add(swirl_CJ(28, NJ(28)), scale(swirl_rows[28], Q(-1)))
assert not free_fibre_difference
J[28] = representative_J28

prior = json.loads((BASE / "family_receipt.json").read_text())
sensitivity = json.loads((BASE / "next_resonance_sensitivity_receipt.json").read_text())
P = Poly([Q(prior["resonance"]["coefficients_by_X_power"][str(i)]) for i in range(15)])
R = Poly([Q(sensitivity["sensitivity"]["coefficients_by_X_power"][str(i)]) for i in range(14)])
R *= Q(1) / Q(sensitivity["sensitivity"]["denominator"])
assert first.c == X * P and not first.d, "Prior source polynomial mismatch"
assert second.d == X * R, "Independently derived next sensitivity mismatch"
assert second.c, "Unexpected identically zero next constant forcing"
assert second.c[0] == 0
Q28 = second.c.right_shift(1)
# Selecting Y=-Q28/R leaves a univariate numerator. Every retained residual
# vanishes modulo the actual first compatibility polynomial P, with R nonzero
# on the certified positive-root bracket.
for residual in list(pressure_rows.values()) + list(swirl_rows.values()):
    for value in residual.values():
        selected_numerator = value.c * R - value.d * Q28
        assert not divmod(selected_numerator, P)[1]
root_lo, root_hi = Q(5625, 2236), Q(1366, 543)
q_lower = sum(c * (root_lo if c >= 0 else root_hi) ** n for n, c in enumerate(Q28.coeffs()))
q_upper = sum(c * (root_hi if c >= 0 else root_lo) ** n for n, c in enumerate(Q28.coeffs()))
r_lower = sum(c * (root_lo if c >= 0 else root_hi) ** n for n, c in enumerate(R.coeffs()))
r_upper = sum(c * (root_hi if c >= 0 else root_lo) ** n for n, c in enumerate(R.coeffs()))
assert q_upper < 0 < r_lower
y_lower, y_upper = -q_upper / r_upper, -q_lower / r_lower
g1_constant = J[1][0].c.right_shift(1)
g1_quadratic = J[1][2].c.right_shift(1)
assert J[1][0].c[0] == J[1][2].c[0] == 0 and not J[1][0].d and not J[1][2].d
assert g1_constant == Q(-5, 14) * X - Q(35, 8)
assert g1_quadratic == Q(15, 16) * X + Q(3885, 416)
axis_diffusion_constant = 8 * g1_constant + 2 * G0z[2]
axis_diffusion_quadratic = 8 * g1_quadratic + 12 * G0z[4]
axis_shape_mismatch = axis_diffusion_quadratic - G0z[2] * axis_diffusion_constant
assert axis_shape_mismatch == Q(55, 14) * X + Q(2325, 52)


def coefficients(poly):
    return {str(i): str(c) for i, c in enumerate(poly.coeffs())}


receipt = {
    "scope": "Full exact reflection-class finite radial jet through mode28; no radial convergence, global profile, viscosity or stability claim",
    "python_flint_version": flint.__version__,
    "flint_version": flint.__FLINT_VERSION__,
    "command": "python research/experiments/mfr3_periodic_core/derive_full_second_resonance.py",
    "parameters": {"alpha": "3/2", "beta": "1", "p": "5/2", "X": "a^2>0", "Y": "W15[z^1]"},
    "representation": "J=X*G; every stored z coefficient is c(X)+Y*d(X), and every Y^2 product is rejected",
    "budgets": {"N_W(m)": "61-2*m", "N_J(m)": "60-2*m", "max_radial_mode": MAX_MODE},
    "axis": {"G0": "(1+z^2)^(-5/4)", "I0": "integral_0^z (1+t^2)^(5/4)dt", "W0": "(7/2)*G0*I0-z"},
    "rows": rows,
    "residual_recompute": {
        "pressure_modes_1_to_28_zero": True,
        "swirl_except_14_and_28_zero": True,
        "incompressibility_all_modes_zero": True,
        "swirl14": "C_J14=X*P(X)*z^2",
        "swirl28": "C_J28=(Q_J28(X)+X*R(X)*Y)*z^4",
        "prior_P_match": True,
        "independent_R_match": True,
        "all_selected_residual_numerators_zero_mod_P": True,
        "J28_z4_unit_perturbation_preserves_full_retained_row": True,
    },
    "J14_fibre": coefficients(J14_parameter.c),
    "leading_viscous_axis_receivers": {
        "G1_z0": coefficients(g1_constant),
        "G1_z2": coefficients(g1_quadratic),
        "diffusion_z0_divided_by_a": coefficients(axis_diffusion_constant),
        "diffusion_z2_divided_by_a": coefficients(axis_diffusion_quadratic),
        "amplitude_only_shape_mismatch": coefficients(axis_shape_mismatch),
        "source": "8*G1+G0'' on s=0; subtract G0[z2] times constant receiver from quadratic receiver",
        "scope": "Two axis receivers of the instantaneous Euler-jet family, not a full viscous profile",
    },
    "second_resonance": {
        "constant_forcing_degree": second.c.degree(),
        "Q_J28_coefficients": coefficients(second.c),
        "Q28_coefficients": coefficients(Q28),
        "Y_slope_coefficients": coefficients(second.d),
        "selected_Y": "-Q28(X)/R(X), with Q_J28=X*Q28",
        "root_bracket": [str(root_lo), str(root_hi)],
        "Q28_interval": [str(q_lower), str(q_upper)],
        "R_interval": [str(r_lower), str(r_upper)],
        "selected_Y_interval": [str(y_lower), str(y_upper)],
        "selected_Y_outer_integers": [int(y_lower), int(y_upper) + 1],
        "domain": "Prior positive root P(X)=0; X>0 and R(X)>0 on its certified bracket",
        "remaining_free_fibre": "J28[z^4] is set to its representative zero here and remains free until the next pressure row",
    },
    "exit_status": 0,
}
print(json.dumps(receipt, indent=2))
