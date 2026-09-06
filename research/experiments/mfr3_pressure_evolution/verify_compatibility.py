"""Exact compatibility certificate for the complete initial-pressure root fibre.

Consumes the already verified source jets; no Fourier convolution is repeated.
The certificate concerns this one-parameter family and the fixed strain/spin
ratio trajectory, not all modulated Navier--Stokes solutions.
"""
import json
from pathlib import Path

import sympy as sp
from flint import fmpq as Q, fmpq_poly as Poly

base = Path(__file__).parent
time = json.loads((base / "time_jet_receipt.json").read_text())
parent = json.loads((base.parent / "mfr3_viscous_strain_source" / "source_order3_receipt.json").read_text())
rho = sp.Symbol("rho", real=True)
symbolic = sp.Poly(sp.sympify(parent["pressure_hessian"]["target_polynomial"], locals={"rho": rho}), rho)
P = Poly([Q(str(symbolic.nth(i))) for i in range(symbolic.degree() + 1)])
assert P.degree() == 2


def read_pair(pair):
    assert set(pair) <= {"0", "1"}
    return Poly([Q(pair.get(str(i), "0")) for i in range(2)])


def evaluate(poly, point):
    return sum(poly[i] * point**i for i in range(poly.degree() + 1))


def coefficients(poly):
    return [str(poly[i]) for i in range(poly.degree() + 1)]


def enclosure(poly, lo, hi):
    assert poly.degree() <= 1
    lower, upper = sorted([evaluate(poly, lo), evaluate(poly, hi)])
    lower_grid = sp.floor(sp.Rational(str(lower)) * 1000) / 1000
    upper_grid = sp.ceiling(sp.Rational(str(upper)) * 1000) / 1000
    return {"exact": [str(lower), str(upper)], "grid_1e3": [str(lower_grid), str(upper_grid)]}


matrices = time["matrices_at_origin"]
a_initial = read_pair(matrices["Du"][2][2])
a_first = read_pair(matrices["Dv"][2][2])
a_second = read_pair(matrices["Dw"][2][2])
spin_initial = (read_pair(matrices["Du"][1][0]) - read_pair(matrices["Du"][0][1])) / 2
spin_first = (read_pair(matrices["Dv"][1][0]) - read_pair(matrices["Dv"][0][1])) / 2
spin_second = (read_pair(matrices["Dw"][1][0]) - read_pair(matrices["Dw"][0][1])) / 2
assert a_initial == Poly([Q(10, 3)]) and a_first == 2 * a_initial
assert spin_initial == Poly([1]) and spin_first == Poly([2]) and spin_second == Poly([8])
pressure_rate = read_pair(time["matrices_at_origin"]["p_t_hessian"][2][2])
R = a_second - a_initial * spin_second
assert R.degree() == 1 and R[1] != 0
# Exact division by the affine second-condition polynomial.
H = Poly([(P[1] - (P[2] / R[1]) * R[0]) / R[1], P[2] / R[1]])
remainder = P[0] - H[0] * R[0]
assert P == H * R + Poly([remainder]) and remainder != 0
bezout_P = Poly([1 / remainder])
bezout_R = -H / remainder
assert bezout_P * P + bezout_R * R == Poly([1])

branches = []
for interval, multiplicity in parent["strain_current"]["all_real_root_intervals"]:
    lo, hi = map(Q, interval)
    assert lo < hi and multiplicity == 1 and evaluate(P, lo) * evaluate(P, hi) < 0
    curvature = enclosure(R, lo, hi)
    assert Q(curvature["exact"][1]) < 0
    branches.append({
        "rho_interval": interval,
        "branch": "positive" if lo > 0 else "negative",
        "a_second": enclosure(a_second, lo, hi),
        "pressure_time_curvature": enclosure(pressure_rate, lo, hi),
        "relative_strain_curvature": curvature,
    })
assert sorted(branch["branch"] for branch in branches) == ["negative", "positive"]

print(json.dumps({
    "scope": "Complete matching fibre of the declared one-parameter initial family; fixed strain/spin ratio through second order",
    "arithmetic": "Exact rational polynomial identity and affine endpoint enclosures",
    "pressure_condition_coefficients": coefficients(P),
    "second_condition_coefficients": coefficients(R),
    "bezout": {
        "multiplier_P": coefficients(bezout_P),
        "multiplier_R": coefficients(bezout_R),
        "identity": "multiplier_P * P + multiplier_R * R = 1",
        "verified": True,
    },
    "matching_branches": branches,
    "conclusion": "No real or complex parameter satisfies both polynomial conditions; both real matching branches have negative initial ratio curvature",
    "exit_status": 0,
}, indent=2))
