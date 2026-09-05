"""Exact finite sensitivity of the next mirror-class swirl resonance.

The accepted amplitude-family recurrence is used only to obtain baseline modes
0..13.  A unit Y=W15[z] perturbation is then propagated linearly through the
actual A, B, C coefficient formulas to mode 28.  This is a finite jet test;
it makes no claim about a PDE solution, convergence, or continuation.
"""

import contextlib
import io
import json
import runpy
import sys
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).parent
FAMILY = ROOT / "derive_radial_resonance_family.py"

# The family script emits the accepted exact baseline receipt and progress.  Its
# stdout is captured so this script's stdout remains one machine-readable receipt;
# progress remains visible on stderr for supervision.
with contextlib.redirect_stdout(io.StringIO()):
    family = runpy.run_path(str(FAMILY), run_name="mfr3_family_for_sensitivity")

alpha = family["alpha"]
beta = family["beta"]
X = family["X"]
z = family["z"]
G0 = family["G0"]
I0 = family["_fixed"].I0
base_W = family["W"][:14]
base_G = family["G"][:14]
base_V = family["V"][:14]

MAX_BASE = 13
START = 15
END = 28
dNW = lambda m: 61 - 2 * m
dNG = lambda m: 60 - 2 * m


def trunc(expr, degree):
    poly = sp.Poly(expr, z, domain="EX")
    return sp.Add(*(sp.expand(c) * z**j for (j,), c in poly.terms() if j <= degree))


def mul_trunc(left, right, degree):
    left_poly = sp.Poly(left, z, domain="EX")
    right_poly = sp.Poly(right, z, domain="EX")
    coefficients = {}
    for (i,), left_coefficient in left_poly.terms():
        for (j,), right_coefficient in right_poly.terms():
            if i + j <= degree:
                coefficients[i + j] = coefficients.get(i + j, 0) + left_coefficient * right_coefficient
    return sp.Add(*(sp.expand(c) * z**j for j, c in coefficients.items()))


def normalize_z(expr):
    poly = sp.Poly(sp.expand(expr), z, domain="EX")
    return sp.Add(*(sp.simplify(c) * z**j for (j,), c in poly.terms()))


def base(arr, i):
    return arr[i] if 0 <= i <= MAX_BASE else sp.Integer(0)


# dW, dG, dV are derivatives with respect to Y, with dW15[z]=1.
H15 = sp.Integer(1)
for _ in range(14):
    H15 = mul_trunc(H15, G0, dNW(START))
H15 = mul_trunc(H15, I0, dNW(START))
H15 = sp.expand(H15 / sp.expand(H15).coeff(z, 1))
assert sp.expand(H15).coeff(z, 1) == 1
assert all(sp.expand(H15).coeff(z, j) == 0 for j in range(0, dNW(START) + 1, 2))

dW = [sp.Integer(0)] * START + [H15]
dG = [sp.Integer(0)] * START
dV = [sp.Integer(0)] * START + [-sp.diff(H15, z) / (2 * (START + 1))]
rows = []


def dA(rmode):
    out = (alpha + beta) * dV[rmode]
    out += sum(dW[i] * sp.diff(base(base_V, rmode - i), z) +
               base(base_W, i) * sp.diff(dV[rmode - i], z)
               for i in range(rmode + 1))
    out += beta * z * sp.diff(dV[rmode], z)
    if rmode >= 1:
        out += 2 * sum((dV[i] * base(base_V, rmode - i) +
                        (base(base_V, i) + (beta if i == 0 else 0)) * dV[rmode - i]) *
                       (rmode - i) for i in range(rmode))
    out += sum(dV[i] * base(base_V, rmode - i) +
               base(base_V, i) * dV[rmode - i] for i in range(rmode + 1))
    out -= X * sum(dG[i] * base(base_G, rmode - i) +
                   base(base_G, i) * dG[rmode - i] for i in range(rmode + 1))
    return sp.expand(out)


def dB(rmode):
    out = alpha * dW[rmode]
    out += sum(dW[i] * sp.diff(base(base_W, rmode - i), z) +
               base(base_W, i) * sp.diff(dW[rmode - i], z)
               for i in range(rmode + 1))
    out += beta * z * sp.diff(dW[rmode], z)
    if rmode >= 1:
        out += 2 * sum((dV[i] * base(base_W, rmode - i) +
                        (base(base_V, i) + (beta if i == 0 else 0)) * dW[rmode - i]) *
                       (rmode - i) for i in range(rmode))
    return sp.expand(out)


def dC(rmode):
    out = (alpha + beta) * dG[rmode]
    out += 2 * sum(dV[i] * base(base_G, rmode - i) +
                   base(base_V, i) * dG[rmode - i]
                   for i in range(rmode + 1))
    out += sum(dW[i] * sp.diff(base(base_G, rmode - i), z) +
               base(base_W, i) * sp.diff(dG[rmode - i], z)
               for i in range(rmode + 1))
    out += beta * z * sp.diff(dG[rmode], z)
    if rmode >= 1:
        out += 2 * sum((dV[i] * base(base_G, rmode - i) +
                        (base(base_V, i) + (beta if i == 0 else 0)) * dG[rmode - i]) *
                       (rmode - i) for i in range(rmode))
    return sp.expand(out)


def solve_rows(equation, unknowns, degree, label):
    equations = [sp.expand(equation).coeff(z, j) for j in range(degree + 1)]
    equations = [e for e in equations if e != 0]
    assert equations, label
    result = sp.linsolve(equations, unknowns)
    if result == sp.EmptySet:
        partial = {}
        residual = []
        for equation in equations:
            equation = sp.expand(equation.subs(partial))
            free = [u for u in unknowns if u not in partial and equation.coeff(u) != 0]
            if free:
                partial[free[0]] = sp.simplify(sp.solve(equation, free[0], dict=False)[0])
            elif equation != 0:
                residual.append(sp.simplify(equation))
        rows.append({"label": label, "status": "incompatible", "free_unknowns": [str(u) for u in unknowns if u not in partial],
                     "forcing_rows": [sp.sstr(e) for e in residual]})
        return partial
    solution = next(iter(result))
    solved = {u: sp.simplify(v) for u, v in zip(unknowns, solution) if v != u}
    for variable, value in solved.items():
        denominator = sp.denom(sp.cancel(value))
        assert not denominator.has(X), ("X-dependent nonresonant solve denominator", label, variable, denominator)
    rows.append({"label": label, "status": "solved", "free_unknowns": [str(u) for u in unknowns if u not in solved]})
    return solved


# The prescribed mode-15 axial perturbation is a pressure-homogeneous source.
assert normalize_z(trunc(dA(14).diff(z) - 30 * dB(15), dNW(START))) == 0
g15_vars = [sp.Symbol(f"dG15_{j}") for j in range(0, dNG(START) + 1, 2)]
dG.append(sum(v * z**j for v, j in zip(g15_vars, range(0, dNG(START) + 1, 2))))
g15_eq = trunc(dC(15), dNG(START))
g15_solution = solve_rows(g15_eq, g15_vars, dNG(START), "dG15 swirl")
dG[15] = sp.expand(dG[15].subs(g15_solution))
assert not any(dG[15].has(v) for v in g15_vars)
print("progress sensitivity_mode=15 pressure=homogeneous swirl=solved", file=sys.stderr, flush=True)


for m in range(16, END + 1):
    wvars = [sp.Symbol(f"dW{m}_{j}") for j in range(1, dNW(m) + 1, 2)]
    gvars = [sp.Symbol(f"dG{m}_{j}") for j in range(0, dNG(m) + 1, 2)]
    dW.append(sum(v * z**j for v, j in zip(wvars, range(1, dNW(m) + 1, 2))))
    dV.append(-sp.diff(dW[m], z) / (2 * (m + 1)))
    dG.append(sum(v * z**j for v, j in zip(gvars, range(0, dNG(m) + 1, 2))))

    pressure_eq = trunc(dA(m - 1).diff(z) - 2 * m * dB(m), dNW(m))
    w_solution = solve_rows(pressure_eq, wvars, dNW(m), f"dW{m} pressure")
    dW[m] = sp.expand(dW[m].subs(w_solution))
    dV[m] = sp.expand(dV[m].subs(w_solution))

    swirl_eq = trunc(dC(m), dNG(m))
    g_solution = solve_rows(swirl_eq, gvars, dNG(m), f"dG{m} swirl")
    dG[m] = sp.expand(dG[m].subs(g_solution))
    print(f"progress sensitivity_mode={m} pressure={rows[-2]['status']} swirl={rows[-1]['status']}",
          file=sys.stderr, flush=True)


# Recompute every linearized row after all prior substitutions.  Mode 28 may
# retain its resonant dG28_4 fibre, so its z^4 coefficient is extracted below.
pressure_residuals = [
    normalize_z(trunc(dA(m - 1).diff(z) - 2 * m * dB(m), dNW(m)))
    for m in range(15, END + 1)
]
swirl_residuals = [normalize_z(trunc(dC(m), dNG(m))) for m in range(15, END + 1)]
for m, residual in zip(range(15, END + 1), pressure_residuals):
    assert residual == 0, ("linearized pressure residual", m, residual)
for m, residual in zip(range(15, END + 1), swirl_residuals):
    if m != END:
        assert residual == 0, ("linearized swirl residual", m, residual)

dG28_4 = sp.Symbol("dG28_4")
R = sp.factor(sp.expand(swirl_residuals[-1]).coeff(z, 4))
assert not R.has(dG28_4)
R = sp.cancel(R)
R_num, R_den = sp.fraction(R)
assert normalize_z(swirl_residuals[-1] - R * z**4) == 0
R_poly = sp.Poly(R_num, X)
prior = json.loads((ROOT / "family_receipt.json").read_text())
P = sum(sp.Rational(c) * X**int(power)
        for power, c in prior["resonance"]["coefficients_by_X_power"].items())
quotient, remainder = sp.div(sp.Poly(R_num, X), sp.Poly(P, X))
remainder = sp.Poly(remainder, X)
root_lo = sp.Rational(5625, 2236)
root_hi = sp.Rational(1366, 543)
interval_lower_bound = sp.factor(sum(
    coefficient * (root_hi**power if coefficient < 0 else root_lo**power)
    for (power,), coefficient in R_poly.terms()
))
assert interval_lower_bound > 0

receipt = {
    "scope": "Finite linear sensitivity of the mirror-class C28[z^4] row to Y=W15[z]; baseline modes 0..13 only; no PDE, convergence, or continuation claim",
    "sympy_version": sp.__version__,
    "command": "/tmp/holonics-mfr3-symbolic/bin/python research/experiments/mfr3_periodic_core/derive_next_resonance_sensitivity.py",
    "parameters": {"alpha": sp.sstr(alpha), "beta": sp.sstr(beta), "X": "a^2>0"},
    "baseline_scope": {"modes": "0..13", "source": "derive_radial_resonance_family.py", "variation_start": 15},
    "budgets": {"dNW(m)": "61-2*m", "dNG(m)": "60-2*m", "modes": "15..28"},
    "perturbation": {"dW15": "G0^14*I0 normalized by dW15[z]=1", "dV_m": "-dW_m'/(2*(m+1))", "dW_m_dG_m": "0 for m<15"},
    "linearized_residuals": {"pressure_m15": "0", "pressure_m15_to_28": True, "swirl_m15_to_27": True},
    "row_summary": rows,
    "sensitivity": {
        "coefficient": "R(X)=dC28[z^4]/dY",
        "numerator_degree": R_poly.degree(),
        "denominator": sp.sstr(R_den),
        "denominator_has_X": R_den.has(X),
        "coefficients_by_X_power": {str(power): sp.sstr(R_poly.coeff_monomial(X**power)) for power in range(R_poly.degree() + 1)},
        "coefficient_signs_low_to_high": [int(sp.sign(R_poly.coeff_monomial(X**power))) for power in range(R_poly.degree() + 1)],
        "divisible_by_prior_P": remainder.is_zero,
        "remainder_mod_prior_P": {str(power): sp.sstr(remainder.coeff_monomial(X**power)) for power in range(remainder.degree() + 1)} if not remainder.is_zero else {},
        "prior_P_degree": sp.Poly(P, X).degree(),
        "prior_P_positive_root_bracket": [sp.sstr(root_lo), sp.sstr(root_hi)],
        "interval_sign_lower_bound": sp.sstr(interval_lower_bound),
        "interval_sign_lower_bound_positive": True,
    },
    "exit_status": 0,
}
print(json.dumps(receipt, indent=2))
