"""Independent fixed-alpha radial resonance sensitivity replay.

The finite solver below replays the original Cartesian coefficient formulas with independent
Taylor polynomials.  It retains the resonant F14,z^2 fibre and differentiates its forcing with
respect to the c30 perturbation; no sensitivity value is accepted merely because it was inserted
as a formula.
"""

import json

import sympy as sp


z, rho, epsilon = sp.symbols("z rho epsilon", real=True)
alpha = sp.Rational(3, 2)
beta = sp.Integer(1)
p = sp.Rational(5, 2)
kappa = sp.Rational(7, 2)
MAX_M = 14
NF = lambda m: 30 - 2 * m
NW = lambda m: 31 - 2 * m


def trunc(expr, degree):
    return sp.series(expr, z, 0, degree + 1).removeO().expand()


def solve_rows(equation, unknowns, degree):
    equations = [sp.expand(equation).coeff(z, jj) for jj in range(degree + 1)]
    equations = [eq for eq in equations if eq != 0]
    if not equations:
        return {}, []
    matrix, rhs = sp.linear_eq_to_matrix(equations, unknowns)
    rows = []
    for row in range(matrix.rows):
        if all(matrix[row, col] == 0 for col in range(matrix.cols)):
            rows.append(sp.expand(rhs[row]))
    # Solve the non-resonant rows and retain variables whose coefficient column is zero.
    substitutions = {}
    for equation in equations:
        current = sp.expand(equation.subs(substitutions))
        candidates = [u for u in unknowns if current.coeff(u) != 0]
        if candidates:
            substitutions[candidates[0]] = sp.solve(current, candidates[0], dict=False)[0]
    return {u: sp.simplify(v) for u, v in substitutions.items()}, rows


def build_replay(c30):
    F0 = trunc((1 + z**2) ** (-p / 2), NF(0)) + c30 * z**30
    I0 = sp.integrate(trunc((1 + z**2) ** (p / 2), NW(0) + 2), (z, 0, z))
    W0 = trunc(kappa * trunc((1 + z**2) ** (-p / 2), NF(0)) * I0 - z, NW(0))
    W0 += kappa * sp.Rational(30, 31) * c30 * z**31
    F = [F0]
    W = [W0]
    V = [-sp.diff(W0, z) / 2]

    def radial_A(rmode):
        out = (alpha + beta) * V[rmode]
        out += sum(W[i] * sp.diff(V[rmode - i], z) for i in range(rmode + 1))
        out += beta * z * sp.diff(V[rmode], z)
        if rmode >= 1:
            out += 2 * sum((V[i] + (beta if i == 0 else 0)) *
                           (rmode - i) * V[rmode - i] for i in range(rmode))
        out += sum(V[i] * V[rmode - i] for i in range(rmode + 1))
        out -= sum(F[i] * F[rmode - i] for i in range(rmode + 1))
        return sp.expand(out)

    def axial_B(rmode):
        out = alpha * W[rmode]
        out += sum(W[i] * sp.diff(W[rmode - i], z) for i in range(rmode + 1))
        out += beta * z * sp.diff(W[rmode], z)
        if rmode >= 1:
            out += 2 * sum((V[i] + (beta if i == 0 else 0)) *
                           (rmode - i) * W[rmode - i] for i in range(rmode))
        return sp.expand(out)

    def swirl_C(rmode):
        out = (alpha + beta) * F[rmode]
        out += 2 * sum(V[i] * F[rmode - i] for i in range(rmode + 1))
        out += sum(W[i] * sp.diff(F[rmode - i], z) for i in range(rmode + 1))
        out += beta * z * sp.diff(F[rmode], z)
        if rmode >= 1:
            out += 2 * sum((V[i] + (beta if i == 0 else 0)) *
                           (rmode - i) * F[rmode - i] for i in range(rmode))
        return sp.expand(out)

    pressure_rows = []
    swirl_rows = []
    for mm in range(1, MAX_M + 1):
        wvars = [sp.Symbol(f"W{mm}_{jj}") for jj in range(1, NW(mm) + 1, 2)]
        fvars = [sp.Symbol(f"F{mm}_{jj}") for jj in range(0, NF(mm) + 1, 2)]
        W.append(sum(v * z**jj for v, jj in zip(wvars, range(1, NW(mm) + 1, 2))))
        V.append(-sp.diff(W[mm], z) / (2 * (mm + 1)))
        F.append(sum(v * z**jj for v, jj in zip(fvars, range(0, NF(mm) + 1, 2))))
        wsol, wcompat = solve_rows(
            trunc(sp.diff(radial_A(mm - 1), z) - 2 * mm * axial_B(mm), NW(mm) + 1),
            wvars, NW(mm) + 1)
        W[mm] = sp.expand(W[mm].subs(wsol))
        V[mm] = sp.expand(V[mm].subs(wsol))
        pressure_rows.extend(wcompat)
        fsol, fcompat = solve_rows(trunc(swirl_C(mm), NF(mm)), fvars, NF(mm))
        F[mm] = sp.expand(F[mm].subs(fsol))
        swirl_rows.extend(fcompat)

    pressure_residuals = [
        sp.factor(trunc(sp.diff(radial_A(mm - 1), z) - 2 * mm * axial_B(mm), NW(mm) + 1))
        for mm in range(1, MAX_M + 1)
    ]
    swirl_residuals = [sp.factor(trunc(swirl_C(mm), NF(mm)))
                       for mm in range(1, MAX_M + 1)]
    forcing = sp.expand(swirl_residuals[MAX_M - 1]).coeff(z, 2)
    return forcing, pressure_residuals, swirl_residuals, sp.Symbol("F14_2")


forcing, pressure_residuals, swirl_residuals, free_F14_2 = build_replay(epsilon)
Q = sp.factor(forcing.subs(epsilon, 0))
S = sp.factor(sp.diff(forcing, epsilon).subs(epsilon, 0))
S_expected = sp.Rational(
    -2196278537437716503986872527655349099000236898596401,
    4325956700507885082543750000000000000000000000000,
)
assert S == S_expected
assert sp.expand(forcing - (Q + S * epsilon)) == 0
assert all(sp.simplify(residual) == 0 for residual in pressure_residuals)
assert all(sp.simplify(residual) == 0 for residual in swirl_residuals[:13])
swirl14_expected = sp.expand((Q + S * epsilon) * z**2)
assert sp.simplify(swirl_residuals[13] - swirl14_expected) == 0
assert not swirl_residuals[13].has(free_F14_2)
epsilon_repair = sp.factor(-Q / S)
assert epsilon_repair < 0
assert epsilon_repair > -32768
assert all(sp.simplify(residual.subs(epsilon, epsilon_repair)) == 0
           for residual in pressure_residuals + swirl_residuals)

# The repaired positive axis profile has a rational perturbation factor.  Its exact absolute
# ratio maximum is 15^15/(2^15*16^16), so epsilon > -2^15*16^16/15^15 implies positivity.
g = (1 + z**2) ** (-sp.Rational(5, 4))
ratio = z**30 / (1 + 2 * z**2) ** 16
ratio_derivative = sp.factor(sp.diff(ratio, z))
critical_ratio = sp.simplify(ratio.subs(z, sp.sqrt(sp.Rational(15, 2))))
ratio_bound = sp.Rational(2**15 * 16**16, 15**15)
assert sp.simplify(critical_ratio * ratio_bound - 1) == 0
assert epsilon_repair > -ratio_bound
simple_bound = sp.Integer(32768)
simple_gap = sp.Poly(sp.expand((1 + 2 * z**2)**16 - simple_bound * z**30), z)
assert all(coefficient >= 0 for coefficient in simple_gap.all_coeffs())
assert simple_gap.coeff_monomial(1) > 0
F_repaired = g * (1 + epsilon_repair * ratio)
assert sp.simplify(F_repaired.subs(z, 0) - 1) == 0

receipt = {
    "scope": "Finite exact alpha=3/2,beta=1 sensitivity replay through radial mode 14; no PDE existence or stability claim",
    "sympy_version": sp.__version__,
    "command": "/tmp/holonics-mfr3-symbolic/bin/python research/experiments/mfr3_periodic_core/derive_radial_axis_repair.py",
    "parameters": {"alpha": "3/2", "beta": "1", "p": "5/2", "kappa": "7/2", "max_radial_mode": 14},
    "replay": {
        "independent_baseline": "F0=(1+z^2)^(-5/4), W0=(7/2)*F0*integral(1/F0)-z",
        "perturbation": "F0 -> F0+epsilon*z^30; W0 -> W0+(7/2)*(30/31)*epsilon*z^31",
        "tested_pressure_orders": "m=1..14",
        "tested_swirl_orders": "m=1..14 with F14_z2 retained as resonant fibre",
        "forcing_affine": True,
        "pressure_residuals_all_zero": True,
        "swirl_residuals_m1_to_m13_zero": True,
        "swirl_m14_residual": "(Q+S*epsilon)*z^2, independent of free F14_2",
        "all_rows_zero_after_epsilon_repair": True,
        "free_fibre": "F14_2 retained and absent from the resonant forcing",
    },
    "sensitivity": {
        "Q": sp.sstr(Q),
        "S": sp.sstr(S),
        "S_expected": sp.sstr(S_expected),
        "epsilon": sp.sstr(epsilon_repair),
        "epsilon_negative": True,
        "epsilon_range": "-32768 < epsilon < 0",
    },
    "positivity": {
        "profile": "(1+z^2)^(-5/4)*(1+epsilon*z^30/(1+2*z^2)^16)",
        "ratio_derivative": sp.sstr(ratio_derivative),
        "ratio_max": "15^15/(2^15*16^16)",
        "epsilon_bound": "> -2^15*16^16/15^15",
        "simple_epsilon_bound": "-32768 < epsilon < 0",
        "verified": True,
    },
    "exit_status": 0,
}
print(json.dumps(receipt, indent=2))
