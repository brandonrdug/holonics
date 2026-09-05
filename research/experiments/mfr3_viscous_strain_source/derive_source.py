"""Exact Fourier pressure audit for a strain plus swirl periodic source."""

import json

import sympy as sp


I = sp.I
rho = sp.symbols("rho", real=True)
x, y, z = sp.symbols("x y z", real=True)
a = sp.Rational(10, 3)
nu = sp.Integer(1)
q = sp.Rational(1, 3)
assert a == 2 + 4 * nu * q


def add1(left, right):
    out = dict(left)
    for mode, value in right.items():
        out[mode] = sp.expand(out.get(mode, 0) + value)
        if out[mode] == 0:
            del out[mode]
    return out


def mul1(left, right):
    out = {}
    for i, left_value in left.items():
        for j, right_value in right.items():
            out[i + j] = out.get(i + j, 0) + left_value * right_value
    return {mode: sp.expand(value) for mode, value in out.items() if sp.expand(value) != 0}


def deriv1(field):
    return {mode: I * mode * value for mode, value in field.items() if mode}


def embed(field, axis):
    return {tuple(mode if i == axis else 0 for i in range(3)): value for mode, value in field.items()}


def mul3(left, right):
    out = {}
    for i, left_value in left.items():
        for j, right_value in right.items():
            mode = tuple(i[q] + j[q] for q in range(3))
            out[mode] = out.get(mode, 0) + left_value * right_value
    return {mode: sp.expand(value) for mode, value in out.items() if sp.expand(value) != 0}


def deriv3(field, axis):
    return {mode: I * mode[axis] * value for mode, value in field.items() if mode[axis]}


def product3(*fields):
    out = {(0, 0, 0): sp.Integer(1)}
    for field in fields:
        out = mul3(out, field)
    return out


def eval_origin(field):
    return sp.expand(sum(field.values()))


sin = {1: -I / 2, -1: I / 2}
cos = {1: sp.Rational(1, 2), -1: sp.Rational(1, 2)}
sin2 = {2: -I / 2, -2: I / 2}
F = add1({mode: sp.Rational(4, 3) * value for mode, value in sin.items()},
         {mode: sp.Rational(-1, 6) * value for mode, value in sin2.items()})
C = deriv1(F)
cutoff = add1({0: sp.Integer(1)}, {mode: rho * value for mode, value in mul1(add1({0: sp.Integer(1)}, {mode: -value for mode, value in cos.items()}),
                                                                            add1({0: sp.Integer(1)}, {mode: -value for mode, value in cos.items()})).items()})
Vx = add1(embed({mode: -sp.Rational(2, 3) * value for mode, value in sin.items()}, 1),
         {mode: -sp.Rational(1, 3) * value for mode, value in product3(embed(cos, 0), embed(sin, 1)).items()})
Vy = add1(embed({mode: sp.Rational(2, 3) * value for mode, value in sin.items()}, 0),
         {mode: sp.Rational(1, 3) * value for mode, value in product3(embed(sin, 0), embed(cos, 1)).items()})
S = [
    {mode: -a * sp.Rational(1, 2) * value for mode, value in product3(embed(F, 0), embed(C, 1), embed(C, 2)).items()},
    {mode: -a * sp.Rational(1, 2) * value for mode, value in product3(embed(C, 0), embed(F, 1), embed(C, 2)).items()},
    {mode: a * value for mode, value in product3(embed(C, 0), embed(C, 1), embed(F, 2)).items()},
]
u = [add1(S[0], mul3(embed(cutoff, 2), Vx)), add1(S[1], mul3(embed(cutoff, 2), Vy)), S[2]]

psi = add1(add1({mode: sp.Rational(2, 3) * value for mode, value in embed(cos, 0).items()},
                {mode: sp.Rational(2, 3) * value for mode, value in embed(cos, 1).items()}),
             {mode: sp.Rational(1, 3) * value for mode, value in product3(embed(cos, 0), embed(cos, 1)).items()})
A_phase = [
    {mode: -a * sp.Rational(1, 2) * value for mode, value in product3(embed(C, 0), embed(F, 1), embed(F, 2)).items()},
    {mode: a * sp.Rational(1, 2) * value for mode, value in product3(embed(F, 0), embed(C, 1), embed(F, 2)).items()},
    mul3(embed(cutoff, 2), psi),
]
curl_A = [
    add1(deriv3(A_phase[2], 1), {mode: -value for mode, value in deriv3(A_phase[1], 2).items()}),
    add1(deriv3(A_phase[0], 2), {mode: -value for mode, value in deriv3(A_phase[2], 0).items()}),
    add1(deriv3(A_phase[1], 0), {mode: -value for mode, value in deriv3(A_phase[0], 1).items()}),
]
assert all(sp.expand(curl_A[i].get(mode, 0) - u[i].get(mode, 0)) == 0
           for i in range(3) for mode in set(curl_A[i]) | set(u[i]))

divergence = add1(add1(deriv3(u[0], 0), deriv3(u[1], 1)), deriv3(u[2], 2))
gradient = [[deriv3(u[j], i) for j in range(3)] for i in range(3)]
source = {}
for i in range(3):
    for j in range(3):
        source = add1(source, mul3(gradient[i][j], gradient[j][i]))
source_mean = sp.expand(source.get((0, 0, 0), 0))
pressure = {mode: sp.expand(value / sum(k * k for k in mode))
            for mode, value in source.items() if mode != (0, 0, 0)}
poisson = {mode: sp.expand(value * sum(k * k for k in mode)) for mode, value in pressure.items()}
assert divergence == {}
assert source_mean == 0
assert poisson == source


def derivative_origin(field, axis):
    return sp.expand(sum(I * mode[axis] * value for mode, value in field.items()))


def derivative_origin_1d(field, order):
    return sp.expand(sum((I * mode) ** order * value for mode, value in field.items()))


def derivative_origin_multi(field, powers):
    return sp.expand(sum((I * mode[0]) ** powers[0] * (I * mode[1]) ** powers[1]
                         * (I * mode[2]) ** powers[2] * value for mode, value in field.items()))


def laplacian(field):
    return {mode: -sum(k * k for k in mode) * value for mode, value in field.items()}


def laplacian_derivative_origin(field, derivative_axis):
    return sp.expand(sum((-sum(k * k for k in mode)) * I * mode[derivative_axis] * value
                         for mode, value in field.items()))


local_Du = [[derivative_origin(u[j], i) for i in range(3)] for j in range(3)]
lap_Du_origin = [[laplacian_derivative_origin(u[j], i) for i in range(3)] for j in range(3)]
p_hessian = [[sp.expand(sum(-mode[i] * mode[j] * value for mode, value in pressure.items())) for j in range(3)] for i in range(3)]
pressure_gradient_origin = [derivative_origin(pressure, i) for i in range(3)]
assert pressure_gradient_origin == [0, 0, 0]
pzz = sp.factor(sum(-mode[2] ** 2 * value for mode, value in pressure.items()))
target_polynomial = sp.factor(pzz + sp.Rational(160, 9))
target_poly = sp.Poly(target_polynomial, rho)
source_current = [[sp.expand(-sum(local_Du[i][k] * local_Du[k][j] for k in range(3))
                              + nu * lap_Du_origin[i][j] - p_hessian[i][j]) for j in range(3)] for i in range(3)]
assert all(sp.Poly(source_current[i][j] - 2 * local_Du[i][j], rho).rem(target_poly).is_zero
           for i in range(3) for j in range(3))
ut = []
for i in range(3):
    adv_i = add1(add1(mul3(u[0], deriv3(u[i], 0)), mul3(u[1], deriv3(u[i], 1))),
                 mul3(u[2], deriv3(u[i], 2)))
    ut.append(add1(add1(laplacian(u[i]), {mode: -value for mode, value in adv_i.items()}),
                   {mode: -value for mode, value in deriv3(pressure, i).items()}))
jet_powers = [(3, 0, 0), (1, 2, 0), (2, 0, 1), (0, 0, 3)]
jet_components = [1, 1, 2, 2]
initial_jet = [derivative_origin_multi(u[component], powers).subs(rho, 0)
               for component, powers in zip(jet_components, jet_powers)]
time_jet = [derivative_origin_multi(ut[component], powers)
            for component, powers in zip(jet_components, jet_powers)]
desired_time_jet = [sp.Integer(-4), sp.Rational(-4, 3), sp.Integer(0), sp.Integer(0)]
jet_remainders = [sp.Poly(actual - desired, rho).rem(target_poly).as_expr()
                  for actual, desired in zip(time_jet, desired_time_jet)]
assert initial_jet == [sp.Integer(-1), sp.Rational(-1, 3), sp.Integer(0), sp.Integer(0)]
strain_current = sp.factor(-a**2 + nu * laplacian_derivative_origin(u[2], 2) - pzz)
target_roots = sp.solve(target_polynomial, rho)
target_integer = target_poly.primitive()[1]
target_intervals = target_integer.intervals(eps=sp.Rational(1, 10) ** 8)
positive_target_intervals = [([str(left), str(right)], int(multiplicity))
                             for (left, right), multiplicity in target_intervals if left > 0]
positive_root = next(root for root in target_roots if root.is_positive)
positive_interval = next(interval for interval in positive_target_intervals)
assert sp.simplify(target_integer.as_expr().subs(rho, positive_root)) == 0
assert target_integer.eval(sp.Rational(positive_interval[0][0])) * target_integer.eval(sp.Rational(positive_interval[0][1])) < 0
velocity_conjugate_symmetric = all(u_component.get(tuple(-k for k in mode), 0) == sp.conjugate(value)
                                   for u_component in u for mode, value in u_component.items())
assert velocity_conjugate_symmetric
u3_square = mul3(u[2], u[2])
for mode in set(u3_square) | set(pressure):
    if mode[0] == 0 and mode[1] == 0 and mode[2] != 0:
        assert pressure.get(mode, 0) == -u3_square.get(mode, 0)
pressure_real = all(pressure.get(tuple(-k for k in mode), 0) == sp.conjugate(value)
                    for mode, value in pressure.items())
assert pressure_real

assert derivative_origin_1d(F, 0) == 0 and derivative_origin_1d(F, 1) == 1
assert all(derivative_origin_1d(F, n) == 0 for n in range(2, 5))
assert derivative_origin_1d(C, 0) == 1
assert all(derivative_origin_1d(C, n) == 0 for n in range(1, 4))

epsilon = sp.symbols("epsilon", real=True)
variation_exprs = (rho * (1 - sp.cos(z))**2 * (-(sp.Rational(2, 3) + sp.cos(x) / 3) * sp.sin(y)),
                   rho * (1 - sp.cos(z))**2 * ((sp.Rational(2, 3) + sp.cos(y) / 3) * sp.sin(x)),
                   sp.Integer(0))
for variation in variation_exprs:
    assert sp.series(sp.expand_trig(variation.subs({x: epsilon * x, y: epsilon * y, z: epsilon * z})),
                     epsilon, 0, 5).removeO() == 0

receipt = {
    "scope": "Exact smooth periodic strain-plus-swirl initial source and pressure; no global stationary profile or blowup claim",
    "arithmetic": "SymPy exact rational Fourier coefficients in rho; no floating values",
    "torus": "[0,2*pi]^3 with nu=1",
    "field": "S=(-a/2*F(x)C(y)C(z),-a/2*C(x)F(y)C(z),a*C(x)C(y)F(z)); u=S+B(z)*V",
    "definitions": {"F": "4/3*sin(x)-1/6*sin(2*x)", "C": "F'", "a": "10/3", "q": "1/3", "B": "1+rho*(1-cos(z))^2", "psi": "2/3*(cos(x)+cos(y))+1/3*cos(x)*cos(y)"},
    "fourier": {"source_modes": len(source), "pressure_modes": len(pressure), "source_mean": str(source_mean), "poisson_residual_zero": True, "pressure_zero_mode": "0", "harmonic_labels": {"F_C": "modes ±1,±2", "B": "0,±1,±2"}, "source_samples": {str(mode): str(source[mode]) for mode in sorted(source)[:4]}, "velocity_conjugate_symmetric": velocity_conjugate_symmetric, "pressure_real": pressure_real, "u3_square_pressure_identity": True},
    "local_checks": {"divergence_zero": True, "curl_A_phase_reconstruction": True, "Du_origin": [[str(value) for value in row] for row in local_Du], "laplacian_Du_origin": [[str(value) for value in row] for row in lap_Du_origin], "pressure_gradient_origin": [str(value) for value in pressure_gradient_origin], "velocity_origin": [str(eval_origin(field).subs(rho, 0)) for field in u], "F_jet": "F=x+O(x^5), C=1+O(x^4)", "F_jet_derivatives_verified": True, "rho_variation_starts_degree": 5, "velocity_jets_through_4_preserved": True, "full_first_jet_source": "-J*J+nu*DeltaJ-Hessian(p)", "full_first_jet_source_matrix": [[str(value) for value in row] for row in source_current], "full_first_jet_source_equals_2J_modulo_target": True},
    "pressure_hessian": {"full_hessian_origin": [[str(value) for value in row] for row in p_hessian], "pzz_origin": str(pzz), "pzz_degree_rho": sp.Poly(pzz, rho).degree(), "pzz_negative_at_rho0": bool(pzz.subs(rho, 0) < 0), "pxx_equals_pyy": sp.simplify(p_hessian[0][0] - p_hessian[1][1]) == 0, "off_diagonal_zero": all(p_hessian[i][j] == 0 for i in range(3) for j in range(3) if i != j)},
    "strain_current": {"formula": "A'=-a^2+nu*Delta(partial_z u3)(0)-pzz", "value": str(strain_current), "target": "2*a=20/3", "target_equation": "pzz=-160/9", "target_polynomial": str(target_polynomial), "target_integer_primitive": str(target_integer.as_expr()), "target_roots": [str(root) for root in target_roots], "positive_root_intervals": positive_target_intervals, "positive_root_exists": bool(positive_target_intervals), "positive_root_substitution_verified": True, "endpoint_sign_change_verified": True},
    "next_time_jet": {"receivers": ["partial_x^3 u2", "partial_x partial_y^2 u2", "partial_x^2 partial_z u3", "partial_z^3 u3"], "initial_jet": [str(value) for value in initial_jet], "actual_time_jet": [str(value) for value in time_jet], "desired_gaussian_clock_jet": [str(value) for value in desired_time_jet], "remainders_modulo_target": [str(value) for value in jet_remainders], "scope": "Exact initial PDE jet comparison; nonzero shape remainders retained as exterior current"},
    "phase_physical_scaling": {"k": "2*pi", "u_phys": "k*u(kX,k^2*t)", "p_phys": "k^2*p", "nu": "unchanged", "A_phys": "k^2*A", "A_prime_phys": "k^4*A'"},
    "exit_status": 0,
}
print(json.dumps(receipt, indent=2))
