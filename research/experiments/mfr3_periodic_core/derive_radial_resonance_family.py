"""Exact rational amplitude-family recurrence through radial mode 14 and its mode-15 junction.

The amplitude is F = a G with X = a^2 > 0.  This finite computation keeps the
reflection-symmetric class G even and W odd and reports the first resonant swirl
forcing as an exact polynomial P(X).  It makes no PDE existence or stability claim.
"""

import contextlib
import importlib.util
import io
import json
import sys
from pathlib import Path

import sympy as sp


# Reuse the exact truncation and compatibility-preserving row solver from the
# fixed-witness script without running its default JSON-producing main block.
_fixed_path = Path(__file__).with_name("derive_radial_resonance.py")
_fixed_spec = importlib.util.spec_from_file_location("mfr3_fixed_resonance", _fixed_path)
_fixed = importlib.util.module_from_spec(_fixed_spec)
with contextlib.redirect_stdout(io.StringIO()):
    _fixed_spec.loader.exec_module(_fixed)

trunc = _fixed.trunc
solve_rows = _fixed.solve_rows
alpha = _fixed.alpha
beta = _fixed.beta
p = _fixed.p
kappa = _fixed.kappa
NF = _fixed.NF
NW = _fixed.NW
G0 = _fixed.F0
W0 = _fixed.W0

z = sp.symbols("z", real=True)
X = sp.symbols("X", positive=True)
MAX_M = 14

G = [G0]
W = [W0]
V = [-sp.diff(W0, z) / 2]
rows = []


def radial_A(rmode):
    out = (alpha + beta) * V[rmode]
    out += sum(W[i] * sp.diff(V[rmode - i], z) for i in range(rmode + 1))
    out += beta * z * sp.diff(V[rmode], z)
    if rmode >= 1:
        out += 2 * sum((V[i] + (beta if i == 0 else 0)) *
                       (rmode - i) * V[rmode - i] for i in range(rmode))
    out += sum(V[i] * V[rmode - i] for i in range(rmode + 1))
    out -= X * sum(G[i] * G[rmode - i] for i in range(rmode + 1))
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
    # This is the nonlinear swirl coefficient after division by a; it uses G.
    out = (alpha + beta) * G[rmode]
    out += 2 * sum(V[i] * G[rmode - i] for i in range(rmode + 1))
    out += sum(W[i] * sp.diff(G[rmode - i], z) for i in range(rmode + 1))
    out += beta * z * sp.diff(G[rmode], z)
    if rmode >= 1:
        out += 2 * sum((V[i] + (beta if i == 0 else 0)) *
                       (rmode - i) * G[rmode - i] for i in range(rmode))
    return sp.expand(out)


def x_degree(expr):
    expr = sp.cancel(expr)
    denominator = sp.denom(expr)
    assert not denominator.has(X), ("non-polynomial X denominator", denominator)
    return -1 if expr == 0 else sp.Poly(expr, X).degree()


def normalize_z(expr):
    """Collect exact cancelling z-coefficients while retaining symbolic X."""
    poly = sp.Poly(sp.expand(expr), z, domain="EX")
    return sp.Add(*(sp.simplify(c) * z**j for (j,), c in poly.terms()))


for m in range(1, MAX_M + 1):
    wvars = [sp.Symbol(f"W{m}_{j}") for j in range(1, NW(m) + 1, 2)]
    gvars = [sp.Symbol(f"G{m}_{j}") for j in range(0, NF(m) + 1, 2)]
    W.append(sum(v * z**j for v, j in zip(wvars, range(1, NW(m) + 1, 2))))
    V.append(-sp.diff(W[m], z) / (2 * (m + 1)))
    G.append(sum(v * z**j for v, j in zip(gvars, range(0, NF(m) + 1, 2))))

    pressure_eq = trunc(sp.diff(radial_A(m - 1), z) - 2 * m * axial_B(m), NW(m) + 1)
    wsol = solve_rows(pressure_eq, wvars, NW(m), f"W{m} pressure", rows)
    W[m] = sp.expand(W[m].subs(wsol))
    V[m] = sp.expand(V[m].subs(wsol))
    assert all(x_degree(c) <= m for c in sp.Poly(W[m], z).all_coeffs())

    swirl_eq = trunc(swirl_C(m), NF(m))
    gsol = solve_rows(swirl_eq, gvars, NF(m), f"G{m} swirl", rows)
    G[m] = sp.expand(G[m].subs(gsol))
    assert all(x_degree(c) <= m for c in sp.Poly(G[m], z).all_coeffs())
    print(f"progress radial_mode={m} pressure={rows[-2]['status']} swirl={rows[-1]['status']}",
          file=sys.stderr, flush=True)


# The next source junction uses the still-free G14_2 fibre.  Its pressure row
# has W15(z)=w15_1*z and G15(z)=g15_0; the former must remain free.
w15_1 = sp.Symbol("W15_1")
g14_2 = sp.Symbol("G14_2")
g15_0 = sp.Symbol("G15_0")
W.append(w15_1 * z)
V.append(-sp.diff(W[MAX_M + 1], z) / (2 * (MAX_M + 2)))
G.append(g15_0)

junction_pressure = trunc(sp.diff(radial_A(MAX_M), z) - 2 * (MAX_M + 1) * axial_B(MAX_M + 1), NW(MAX_M + 1) + 1)
junction_solution = solve_rows(
    junction_pressure, [w15_1, g14_2], NW(MAX_M + 1), "W15 pressure / G14_2 junction", rows
)
assert w15_1 not in junction_solution
assert g14_2 in junction_solution
G[MAX_M] = sp.expand(G[MAX_M].subs(junction_solution))
assert W[MAX_M + 1].has(w15_1)

junction_row = rows[-1]
junction_scalar = junction_row["scalar_rows"]
assert len(junction_scalar) == 1 and junction_scalar[0]["power"] == 1
junction_coefficients = junction_scalar[0]["linear_coefficients"]
assert sp.simplify(sp.sympify(junction_coefficients[str(w15_1)], locals={"X": X})) == 0
assert sp.simplify(sp.sympify(junction_coefficients[str(g14_2)], locals={"X": X}) + 4 * X) == 0

g15_equation = trunc(swirl_C(MAX_M + 1), NF(MAX_M + 1))
g15_solution = solve_rows(g15_equation, [g15_0], NF(MAX_M + 1), "G15 swirl", rows)
assert g15_0 in g15_solution
G[MAX_M + 1] = sp.expand(G[MAX_M + 1].subs(g15_solution))
assert not G[MAX_M + 1].has(g15_0)
print("progress radial_mode=15 pressure=solved swirl=solved", file=sys.stderr, flush=True)


# Recompute all residuals after every prior row substitution.  The m=14
# divided-swirl row is retained as P(X)*z^2; all other rows close exactly.
pressure_residuals = [
    normalize_z(trunc(sp.diff(radial_A(m - 1), z) - 2 * m * axial_B(m), NW(m) + 1))
    for m in range(1, MAX_M + 2)
]
swirl_residuals = [normalize_z(trunc(swirl_C(m), NF(m))) for m in range(1, MAX_M + 1)]
swirl_residuals.append(normalize_z(trunc(swirl_C(MAX_M + 1), NF(MAX_M + 1))))
for m, residual in enumerate(pressure_residuals, 1):
    assert residual == 0, ("pressure residual", m, residual)
for m, residual in enumerate(swirl_residuals, 1):
    if m != MAX_M:
        assert residual == 0, ("swirl residual", m, residual)

forcing = sp.factor(sp.expand(swirl_residuals[MAX_M - 1]).coeff(z, 2))
assert normalize_z(swirl_residuals[MAX_M - 1] - forcing * z**2) == 0
forcing_poly = sp.Poly(forcing, X)
coefficients = {
    str(power): sp.sstr(forcing_poly.coeff_monomial(X**power))
    for power in range(forcing_poly.degree() + 1)
}
nonzero_coefficients = [c for c in forcing_poly.all_coeffs() if c != 0]
coefficient_signs = [sp.sign(c) for c in nonzero_coefficients]
all_nonzero_one_sign = len(set(coefficient_signs)) <= 1
positive_root_count = int(forcing_poly.count_roots(0, sp.oo))
positive_root_intervals = [
    {"interval": [sp.sstr(left), sp.sstr(right)], "multiplicity": int(multiplicity)}
    for (left, right), multiplicity in forcing_poly.intervals(eps=sp.Rational(1, 10)**6)
    if left > 0
]

fixed_receipt = json.loads((_fixed_path.with_name("resonance_receipt.json")).read_text())
fixed_forcing = sp.Rational(fixed_receipt["resonance"]["forcing"])
assert sp.simplify(forcing.subs(X, 1) - fixed_forcing) == 0

receipt = {
    "scope": "Finite exact amplitude family through radial mode 14 and the mode-15 pressure/swirl junction; F=a*G, X=a^2>0; G even and W odd; no PDE existence or stability claim",
    "sympy_version": sp.__version__,
    "command": "/tmp/holonics-mfr3-symbolic/bin/python research/experiments/mfr3_periodic_core/derive_radial_resonance_family.py",
    "parameters": {"alpha": sp.sstr(alpha), "beta": sp.sstr(beta), "p": sp.sstr(p), "kappa": sp.sstr(kappa)},
    "amplitude": {"X": "a^2", "domain": "X>0", "fixed_witness": "X=1"},
    "budgets": {"N_F(m)": "30-2*m", "N_W(m)": "31-2*m", "max_radial_mode": MAX_M},
    "baseline": {"G0": "(1+z^2)^(-5/4)", "W0": "(7/2)*G0*integral(1/G0)-z"},
    "assertions": {
        "divergence": "2*V+2*s*V_s+W_z",
        "pressure_equation": "A_(m-1)'=2*m*B_m with -X*sum(G_i*G_j) in A",
        "divided_swirl_equation": "C_m=0 with G in place of F",
        "V_m": "-W_m'/(2*(m+1))",
        "degree_bound": "For m=1..14, W_m and G_m coefficients are polynomials in X of degree <=m before the mode-15 junction",
        "scalar_row_control": "Exact linear coefficients, zero compatibility forcing, and free symbols are retained by the reused solver",
        "next_source_junction": "[z^1](A14'-30*B15) has W15_1 coefficient 0 and G14_2 coefficient -4*X; [z^0]C15 solves G15_0",
    },
    "row_summary": [
        {"label": row["label"], "status": row["status"], "rank": row.get("rank"),
         "unknown_count": row.get("unknown_count"), "free_unknowns": row.get("free_unknowns", [])}
        for row in rows
    ],
    "next_source_junction": {
        "pressure_row": "[z^1](A14'-30*B15)",
        "linear_coefficients": junction_coefficients,
        "required_domain": "X>0 implies X!=0",
        "free_unknowns": junction_row["free_unknowns"],
        "solution": {str(k): sp.sstr(v) for k, v in junction_solution.items()},
        "retained_W15": "W15_1 remains an explicit free coefficient",
        "swirl_row": "[z^0]C15",
        "G15_solution": {str(k): sp.sstr(v) for k, v in g15_solution.items()},
    },
    "residual_recompute": {
        "pressure_all_zero": True,
        "swirl_m1_to_m13_zero": True,
        "swirl_m15_zero": True,
        "only_remaining_residual": "C14=P(X)*z^2",
        "forcing_coefficient": "z^2",
        "forcing_degree_in_X": forcing_poly.degree(),
    },
    "resonance": {
        "row": MAX_M,
        "polynomial": "P(X)=C14[z^2]",
        "coefficients_by_X_power": coefficients,
        "coefficient_signs": [int(s) for s in coefficient_signs],
        "all_nonzero_coefficients_one_sign": all_nonzero_one_sign,
        "positive_root_count": positive_root_count,
        "positive_root_intervals": positive_root_intervals,
        "positive_root_obstruction": "exact Sturm count and rational isolating intervals; no floating root estimate",
        "P_at_1": sp.sstr(forcing.subs(X, 1)),
        "matches_fixed_witness": True,
    },
    "exit_status": 0,
}
print(json.dumps(receipt, indent=2))
