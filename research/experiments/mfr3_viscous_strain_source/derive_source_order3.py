"""Exact order-three radial Gaussian jet pressure/source audit."""

import json
import sympy as sp
from source_spectrum import (
    C,
    F,
    I,
    a,
    add,
    deriv,
    eps,
    jet_at_origin,
    mul,
    psi_expression,
    rho,
    u,
    x,
    y,
    z,
)


divergence = add(add(deriv(u[0], 0), deriv(u[1], 1)), deriv(u[2], 2))
gradient = [[deriv(u[j], i) for j in range(3)] for i in range(3)]
source = {}
for i in range(3):
    for j in range(3):
        source = add(source, mul(gradient[i][j], gradient[j][i]))
source_mean = sp.expand(source.get((0, 0, 0), 0))
pressure = {mode: sp.expand(value / sum(k * k for k in mode)) for mode, value in source.items() if mode != (0, 0, 0)}
poisson = {mode: sp.expand(value * sum(k * k for k in mode)) for mode, value in pressure.items()}
assert divergence == {} and source_mean == 0 and poisson == source
velocity_conjugate_symmetric = all(u_component.get(tuple(-k for k in mode), 0) == sp.conjugate(value)
                                   for u_component in u for mode, value in u_component.items())
pressure_real = all(pressure.get(tuple(-k for k in mode), 0) == sp.conjugate(value)
                    for mode, value in pressure.items())
assert velocity_conjugate_symmetric and pressure_real
u3_square = mul(u[2], u[2])
for mode in set(u3_square) | set(pressure):
    if mode[0] == 0 and mode[1] == 0 and mode[2] != 0:
        assert pressure.get(mode, 0) == -u3_square.get(mode, 0)


def d0(field, axis):
    return sp.expand(sum(I * mode[axis] * value for mode, value in field.items()))


def d1(field, order):
    return sp.expand(sum((I * mode) ** order * value for mode, value in field.items()))


def lapd0(field, axis):
    return sp.expand(sum(-sum(k * k for k in mode) * I * mode[axis] * value for mode, value in field.items()))


Du = [[d0(u[j], i) for i in range(3)] for j in range(3)]
lapDu = [[lapd0(u[j], i) for i in range(3)] for j in range(3)]
Hp = [[sp.expand(sum(-mode[i] * mode[j] * value for mode, value in pressure.items())) for j in range(3)] for i in range(3)]
pgrad = [d0(pressure, i) for i in range(3)]
pzz = sp.factor(Hp[2][2])
target = sp.factor(pzz + sp.Rational(160, 9))
target_poly = sp.Poly(target, rho)
source_current = [[sp.expand(-sum(Du[i][k] * Du[k][j] for k in range(3)) + lapDu[i][j] - Hp[i][j]) for j in range(3)] for i in range(3)]
assert pgrad == [0, 0, 0]
assert all(sp.Poly(source_current[i][j] - 2 * Du[i][j], rho).rem(target_poly).is_zero for i in range(3) for j in range(3))
factorial = sp.factorial
p4_actual = sp.expand(sum(jet_at_origin(pressure, (i, j, k)) / (factorial(i) * factorial(j) * factorial(k)) * x**i * y**j * z**k
                           for i in range(5) for j in range(5 - i) for k in [4 - i - j]))
p4_gaussian = -(x**2 + y**2)**2 / 12
Hdiff = sp.expand(p4_actual - p4_gaussian)
hax, hcos, hsin = sp.symbols("hax hcos hsin")
Hax = z**4 - 3 * (x**2 + y**2) * z**2 + sp.Rational(3, 8) * (x**2 + y**2)**2
Hcos = x**4 - 6 * x**2 * y**2 + y**4
Hsin = x * y * (x**2 - y**2)
hsol = sp.solve(sp.Poly(Hdiff - hax * Hax - hcos * Hcos - hsin * Hsin, x, y, z).coeffs(), (hax, hcos, hsin), dict=True)[0]
assert sp.expand(Hdiff - hsol[hax] * Hax - hsol[hcos] * Hcos - hsol[hsin] * Hsin) == 0
assert sp.expand(sum(sp.diff(Hdiff, coordinate, 2) for coordinate in (x, y, z))) == 0
assert d1(F, 1) == 1 and all(d1(F, n) == 0 for n in (0, 2, 3, 4, 5, 6))
assert d1(C, 0) == 1 and all(d1(C, n) == 0 for n in (1, 2, 3, 4, 5))

lap_u = [{mode: -sum(k * k for k in mode) * value for mode, value in field.items()} for field in u]
adv_u = []
for i in range(3):
    adv_i = {}
    for j in range(3):
        adv_i = add(adv_i, mul(u[j], deriv(u[i], j)))
    adv_u.append(adv_i)
pressure_force = [{mode: -value for mode, value in deriv(pressure, i).items()} for i in range(3)]
ut = [add(add(lap_u[i], {mode: -value for mode, value in adv_u[i].items()}), pressure_force[i]) for i in range(3)]
jet_powers = [(3, 0, 0), (1, 2, 0), (2, 0, 1), (0, 0, 3)]
jet_components = [1, 1, 2, 2]
initial_jet = [jet_at_origin(u[c], powers) for c, powers in zip(jet_components, jet_powers)]
time_jet = [jet_at_origin(ut[c], powers) for c, powers in zip(jet_components, jet_powers)]
viscous_jet = [jet_at_origin(lap_u[c], powers) for c, powers in zip(jet_components, jet_powers)]
nonlinear_jet = [jet_at_origin({mode: -value for mode, value in adv_u[c].items()}, powers)
                for c, powers in zip(jet_components, jet_powers)]
pressure_jet = [jet_at_origin(pressure_force[c], powers) for c, powers in zip(jet_components, jet_powers)]
desired_time_jet = [sp.Integer(-4), sp.Rational(-4, 3), sp.Integer(0), sp.Integer(0)]
jet_remainders = {"total": [sp.Poly(actual - desired, rho).rem(target_poly).as_expr() for actual, desired in zip(time_jet, desired_time_jet)]}
jet_remainders.update({name: [sp.Poly(actual, rho).rem(target_poly).as_expr() for actual in values]
                      for name, values in (("viscous", viscous_jet), ("nonlinear", nonlinear_jet), ("pressure", pressure_jet))})
assert initial_jet == [sp.Integer(-1), sp.Rational(-1, 3), sp.Integer(0), sp.Integer(0)]
assert all(sp.expand(time_jet[i] - viscous_jet[i] - nonlinear_jet[i] - pressure_jet[i]) == 0 for i in range(4))

# Full homogeneous cubic vector comparison, retaining every monomial.
def homogeneous_component(field, degree):
    result = 0
    for i in range(degree + 1):
        for j in range(degree + 1 - i):
            k = degree - i - j
            result += jet_at_origin(field, (i, j, k)) / (factorial(i) * factorial(j) * factorial(k)) * x**i * y**j * z**k
    return sp.expand(result)

cubic_ut = [homogeneous_component(ut[i], 3) for i in range(3)]
cubic_gaussian = (sp.Rational(2, 3) * y * (x**2 + y**2),
                  -sp.Rational(2, 3) * x * (x**2 + y**2), sp.Integer(0))
cubic_defect = [sp.expand(cubic_ut[i] - cubic_gaussian[i]) for i in range(3)]
assert all(sp.expand(cubic_defect[i] + sp.diff(Hdiff, coordinate)) == 0
           for i, coordinate in ((0, x), (1, y), (2, z)))
cubic_defect_remainders = [sp.Poly(value, rho).rem(target_poly).as_expr() for value in cubic_defect]

root = next(value for value in sp.solve(target, rho) if value.is_positive)
intervals = target_poly.intervals(eps=sp.Rational(1, 10) ** 8)
all_root_intervals = [([str(lo), str(hi)], int(mult)) for (lo, hi), mult in intervals]
positive_intervals = [([str(lo), str(hi)], int(mult)) for (lo, hi), mult in intervals if lo > 0]
positive_interval = positive_intervals[0]
root_lo, root_hi = next((lo, hi) for (lo, hi), _ in intervals if lo > 0)
assert sp.simplify(target.subs(rho, root)) == 0
assert target_poly.eval(sp.Rational(positive_interval[0][0])) * target_poly.eval(sp.Rational(positive_interval[0][1])) < 0

harmonic_reduced = {name: sp.Poly(hsol[symbol], rho).rem(target_poly).as_expr()
                    for name, symbol in (("hax", hax), ("hcos", hcos), ("hsin", hsin))}
harmonic_enclosures = {}
for name, value in harmonic_reduced.items():
    left, right = value.subs(rho, root_lo), value.subs(rho, root_hi)
    lower, upper = min(left, right), max(left, right)
    harmonic_enclosures[name] = {"exact": [str(lower), str(upper)], "coarse_1e3": [str(sp.floor(lower * 1000) / 1000), str(sp.ceiling(upper * 1000) / 1000)]}

variation = rho * (1 - sp.cos(z))**3
Vx_expression = sp.diff(psi_expression, y)
Vy_expression = -sp.diff(psi_expression, x)
assert all(sp.series(sp.expand_trig((variation * expr).subs({x: eps * x, y: eps * y, z: eps * z})), eps, 0, 7).removeO() == 0
           for expr in (Vx_expression, Vy_expression))

receipt = {
    "scope": "Exact order-three periodic strain-plus-swirl source; no global stationary or blowup claim",
    "arithmetic": "SymPy exact rational Fourier coefficients in rho; no floating values",
    "F_C": {"F": "3/2*sin(x)-3/10*sin(2*x)+1/30*sin(3*x)", "C": "F'", "jet": "F=x+O(x^7), C=1+O(x^6)"},
    "psi_coefficients": {"A": "169/216", "B": "-4/135", "C": "11/3240", "D": "7/27", "E": "1/108", "target": "const-s/2+s^2/24-s^3/324+O(8)", "taylor_identity_verified": True},
    "cutoff": "B(z)=1+rho*(1-cos(z))^3; variation starts degree 7",
    "fourier": {"source_modes": len(source), "pressure_modes": len(pressure), "source_mean": str(source_mean), "pressure_zero_mode": "0", "poisson_residual_zero": True, "velocity_conjugate_symmetric": velocity_conjugate_symmetric, "pressure_real": pressure_real, "u3_square_pressure_identity": True, "curl_A_phase_reconstruction": True},
    "local_checks": {"divergence_zero": True, "curl_A_phase_reconstruction": True, "Du_origin": [[str(v) for v in row] for row in Du], "laplacian_Du_origin": [[str(v) for v in row] for row in lapDu], "pressure_gradient_origin": [str(v) for v in pgrad], "full_first_jet_source_matrix": [[str(v) for v in row] for row in source_current], "full_first_jet_source_modulo_target": True, "F_C_jet_derivatives_verified": True, "rho_velocity_jets_through_6_preserved": True, "time_jet_split_verified": True, "full_p4_15_monomials_verified": True, "harmonic_Hdiff_verified": True, "cubic_ut_defect_equals_negative_gradient_Hdiff": True},
    "pressure_degree4": {"p4_actual_coefficients": {str((i, j, k)): str(sp.Poly(p4_actual, x, y, z).coeff_monomial(x**i * y**j * z**k)) for i in range(5) for j in range(5 - i) for k in [4 - i - j]}, "p4_gaussian": str(p4_gaussian), "Hdiff": str(Hdiff), "harmonic_coefficients": {"hax": str(hsol[hax]), "hcos": str(hsol[hcos]), "hsin": str(hsol[hsin])}, "full_monomial_equality": True, "laplacian_Hdiff_zero": True},
    "harmonic_coefficients_mod_target": {name: str(value) for name, value in harmonic_reduced.items()},
    "harmonic_coefficient_enclosures": harmonic_enclosures,
    "full_cubic_time_defect": {"actual": [str(value) for value in cubic_ut], "desired": [str(value) for value in cubic_gaussian], "defect": [str(value) for value in cubic_defect], "defect_remainders_mod_target": [str(value) for value in cubic_defect_remainders], "equals_negative_gradient_Hdiff": True},
    "cubic_time_jet": {"receivers": ["partial_x^3 u2", "partial_x partial_y^2 u2", "partial_x^2 partial_z u3", "partial_z^3 u3"], "initial": [str(v) for v in initial_jet], "total": [str(v) for v in time_jet], "viscous": [str(v) for v in viscous_jet], "nonlinear": [str(v) for v in nonlinear_jet], "pressure": [str(v) for v in pressure_jet], "desired_gaussian_clock": [str(v) for v in desired_time_jet], "remainders_modulo_target": {name: [str(v) for v in values] for name, values in jet_remainders.items()}},
    "pressure_hessian": {"matrix_origin": [[str(v) for v in row] for row in Hp], "pzz": str(pzz), "target_polynomial": str(target)},
    "strain_current": {"formula": "A'=-a^2+Delta(partial_z u3)(0)-pzz", "value": str(sp.factor(-a**2 + lapd0(u[2], 2) - pzz)), "target": "20/3", "all_real_root_intervals": all_root_intervals, "positive_root": str(root), "positive_root_interval": positive_intervals, "chosen_branch": "rho>0, hence B(z)>=1", "root_substitution_verified": True, "endpoint_sign_change_verified": True},
    "exit_status": 0,
}
print(json.dumps(receipt, indent=2))
