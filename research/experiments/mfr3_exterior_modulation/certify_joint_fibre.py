"""Exact quadratic-form certificate for the complete two-parameter fibre.

The source is the full finite Fourier audit. This script neither samples the
parameter plane nor repeats the Fourier calculation. It retains an exact
square completion and the entire initial-pressure matching ellipse.
"""

import json
from pathlib import Path

import sympy as sp

BASE = Path(__file__).parent
source = json.loads((BASE / "source_receipt.json").read_text())
parent = json.loads((BASE.parent / "mfr3_viscous_strain_source" / "source_order3_receipt.json").read_text())
rho, sigma = sp.symbols("rho sigma", real=True)
variables = (rho, sigma)
v = sp.Matrix(variables)
zero = {rho: 0, sigma: 0}

def read(value):
    return sp.sympify(value, locals={"rho": rho, "sigma": sigma})


def grid(value, denominator=1000):
    assert value.is_Rational
    return [str(sp.floor(denominator * value) / denominator),
            str(sp.ceiling(denominator * value) / denominator)]


def matrix_strings(matrix):
    return [[str(value) for value in row] for row in matrix.tolist()]


def quadratic_parts(expression):
    assert sp.Poly(expression, *variables).total_degree() == 2
    form = sp.hessian(expression, variables) / 2
    linear = sp.Matrix([sp.diff(expression, t).subs(zero) for t in variables])
    constant = expression.subs(zero)
    assert sp.expand(expression - ((v.T * form * v)[0] + (linear.T * v)[0] + constant)) == 0
    return form, linear, constant


h, ht = read(source["pzz"]), read(source["p_tzz"])
P = h + sp.Rational(160, 9)
T = ht + sp.Rational(640, 9)
form, linear, constant = quadratic_parts(T)
centre = -form.inv() * linear / 2
minimum = sp.factor(T.subs(dict(zip(variables, centre))))
eta = v - centre
pivot0 = form[0, 0]
coupling = form[0, 1] / pivot0
pivot1 = form[1, 1] - form[0, 1]**2 / pivot0
squares = pivot0 * (eta[0] + coupling * eta[1])**2 + pivot1 * eta[1]**2
assert sp.expand(T - squares - minimum) == 0
assert pivot0 > 0 and pivot1 > 0 and minimum > 64

# Retain the complete matching fibre, not a chosen parameter sign or branch.
pressure_form, pressure_linear, pressure_constant = quadratic_parts(P)
pressure_centre = -pressure_form.inv() * pressure_linear / 2
pressure_height = sp.factor(P.subs(dict(zip(variables, pressure_centre))))
K = -pressure_form
assert K[0, 0] > 0 and K.det() > 0 and pressure_height > 0
pressure_eta = v - pressure_centre
assert sp.expand(P - (pressure_height - (pressure_eta.T * K * pressure_eta)[0])) == 0

# The second direction actually changes the joint receiver, also on the retained
# positive matching branch at sigma=0. Quotient reduction is only a certificate
# on that branch and never changes the source calculation.
jacobian = sp.expand(sp.det(sp.Matrix([[sp.diff(f, t) for t in variables] for f in (h, ht)])))
jacobian_origin = jacobian.subs(zero)
assert jacobian_origin > 0
old_target = sp.Poly(read(parent["pressure_hessian"]["target_polynomial"]), rho)
jacobian_branch = sp.Poly(jacobian.subs(sigma, 0), rho).rem(old_target).as_expr()
assert sp.Poly(jacobian_branch, rho).degree() <= 1
positive_interval = next(interval for interval, multiplicity in parent["strain_current"]["all_real_root_intervals"]
                         if sp.Rational(interval[0]) > 0 and multiplicity == 1)
lo, hi = map(sp.Rational, positive_interval)
assert old_target.eval(lo) * old_target.eval(hi) < 0
branch_values = sorted([jacobian_branch.subs(rho, lo), jacobian_branch.subs(rho, hi)])
assert branch_values[0] > 0

# This identifies the competing source terms without attributing the whole
# obstruction to dissipation. The convective quadratic is indefinite.
viscous, convective = read(source["p_tzz_viscous"]), read(source["p_tzz_convective"])
assert sp.expand(viscous + convective - ht) == 0
viscous_form, _, _ = quadratic_parts(viscous)
convective_form, _, _ = quadratic_parts(convective)
assert viscous_form[0, 0] > 0 and viscous_form.det() > 0
assert convective_form.det() < 0
assert viscous_form[1, 1] > 0 and convective_form[1, 1] < 0
assert viscous_form[1, 1] + convective_form[1, 1] == form[1, 1] > 0

receipt = {
    "scope": "All real rho,sigma in the declared periodic exterior family; fixed relative-strain target only",
    "arithmetic": "Exact rational polynomial reconstruction, positive pivots and root-interval enclosure",
    "pressure_matching_ellipse": {
        "centre": [str(c) for c in pressure_centre], "positive_matrix": matrix_strings(K),
        "height": str(pressure_height), "height_grid": grid(pressure_height),
        "identity": "P = height - (parameter - centre)^T K (parameter - centre)",
        "K_positive_definite_and_height_positive": True,
    },
    "second_condition_square_completion": {
        "centre": [str(c) for c in centre], "first_pivot": str(pivot0),
        "coupling": str(coupling), "second_pivot": str(pivot1), "minimum": str(minimum),
        "minimum_grid": grid(minimum), "strict_rational_lower_bound": "64",
        "identity": "T = first_pivot*(eta_rho + coupling*eta_sigma)^2 + second_pivot*eta_sigma^2 + minimum",
        "polynomial_identity_and_positive_pivots_verified": True,
    },
    "joint_receiver_jacobian": {
        "at_origin": str(jacobian_origin), "origin_grid": grid(jacobian_origin),
        "positive_pressure_branch_interval": positive_interval,
        "on_branch_affine_remainder": str(jacobian_branch),
        "on_branch_exact_enclosure": [str(value) for value in branch_values],
        "on_branch_grid": [grid(branch_values[0])[0], grid(branch_values[1])[1]],
        "strictly_positive_on_branch": True,
    },
    "pressure_time_source_decomposition": {
        "viscous_quadratic_form": matrix_strings(viscous_form),
        "convective_quadratic_form": matrix_strings(convective_form),
        "viscous_form_positive_definite": True, "convective_form_indefinite": True,
        "sigma_squared_coefficients": {
            name: {"exact": str(value), "grid": grid(value)}
            for name, value in (("viscous", viscous_form[1, 1]),
                                ("convective", convective_form[1, 1]),
                                ("total", form[1, 1]))
        },
        "source_sum_verified": True,
    },
    "conclusion": "No real parameter pair pays both target equations. On the entire initial-pressure matching ellipse the initial ratio curvature is less than -64.",
    "boundary": "Other trajectories, exterior velocity directions and positive-time continuation are not excluded",
    "exit_status": 0,
}
print(json.dumps(receipt, indent=2))
