"""Exact first and second time jets of the extracted periodic source spectrum."""

import contextlib
import io
import json
import runpy
from pathlib import Path

import sympy as sp
import flint
from flint import fmpq as Q, fmpq_poly as Poly


BASE = Path(__file__).parent
with contextlib.redirect_stdout(io.StringIO()):
    source = runpy.run_path(str(BASE.parent / "mfr3_viscous_strain_source" / "source_spectrum.py"), run_name="mfr3_time_jet_spectrum")
rho = source["rho"]
I = sp.I
parent_receipt = json.loads((BASE.parent / "mfr3_viscous_strain_source" / "source_order3_receipt.json").read_text())
target_sympy = sp.Poly(sp.sympify(parent_receipt["pressure_hessian"]["target_polynomial"], locals={"rho": rho}), rho)
P = Poly([Q(str(target_sympy.nth(i))) for i in range(target_sympy.degree() + 1)])
ROOT_LO = Q(str(sp.Rational(parent_receipt["strain_current"]["positive_root_interval"][0][0][0])))
ROOT_HI = Q(str(sp.Rational(parent_receipt["strain_current"]["positive_root_interval"][0][0][1])))


def qp(value):
    if isinstance(value, Poly):
        return value % P
    return Poly([Q(str(value))]) % P


def from_sympy(value):
    polynomial = sp.Poly(sp.expand(value), rho)
    # Reduce the complete polynomial: dropping high powers before reduction changes
    # their lower-order remainder in the matching-root quotient algebra.
    return Poly([Q(str(value)) for value in reversed(polynomial.all_coeffs())]) % P


def add(a, b):
    return (a + b) % P


def neg(a):
    return (-a) % P


def mul(a, b):
    return (a * b) % P


def scale(a, n):
    return (a * n) % P


ZERO = Poly([0])


def vadd(a, b):
    return [add(a[i], b[i]) for i in range(3)]


def vscale(a, n):
    return [scale(value, n) for value in a]


def dot(k, a):
    return add(add(scale(a[0], k[0]), scale(a[1], k[1])), scale(a[2], k[2]))


def zero_vector():
    return [ZERO, ZERO, ZERO]


def component_field(field, component):
    return {mode: value[component] for mode, value in field.items() if value[component]}


def conjugate_symmetric(field):
    return all(field.get(tuple(-k for k in mode), zero_vector()) ==
               [value.conjugate() if hasattr(value, "conjugate") else value for value in vector]
               for mode, vector in field.items())


def amplitude_field():
    result = {}
    spectrum = {}
    for component, field in enumerate(source["u"]):
        for mode, value in field.items():
            spectrum.setdefault(mode, [0, 0, 0])[component] = value
    for mode, vector in spectrum.items():
        values = [sp.simplify(component / I) for component in vector]
        assert all(value.is_real for value in values)
        result[mode] = [from_sympy(value) for value in values]
    return result


A = amplitude_field()
assert all(tuple(-k for k in mode) in A for mode in A)


def nonlinear_Q(left, right):
    result = {}
    for p_mode, p_vec in left.items():
        for q_mode, q_vec in right.items():
            mode = tuple(p_mode[i] + q_mode[i] for i in range(3))
            term = vscale(q_vec, dot(mode, p_vec))
            result[mode] = vadd(result.get(mode, zero_vector()), term)
    return {mode: vector for mode, vector in result.items() if any(value for value in vector)}


def pressure_from_Q(Qfield):
    result = {}
    for mode, vector in Qfield.items():
        norm = sum(value * value for value in mode)
        if norm:
            result[mode] = scale(dot(mode, vector), Q(1, norm))
    return result


Q0 = nonlinear_Q(A, A)
P0 = pressure_from_Q(Q0)
assert not any(value for value in Q0.get((0, 0, 0), zero_vector()))

V = {}
for mode in set(A) | set(Q0) | set(P0):
    avec = A.get(mode, zero_vector())
    norm = sum(value * value for value in mode)
    pressure_value = P0.get(mode, ZERO)
    V[mode] = [add(add(scale(avec[i], -norm), Q0.get(mode, zero_vector())[i]), scale(pressure_value, -mode[i])) for i in range(3)]
    if not any(V[mode]):
        del V[mode]

assert all(any(value for value in vector) for vector in V.values())
assert all(dot(mode, vector) == ZERO for mode, vector in A.items())
assert all(dot(mode, vector) == ZERO for mode, vector in V.items())


# Ordered trace(Dv Du)+trace(Du Dv), accumulated independently in both orders.
Pt_source = {}
for p_mode, v_p in V.items():
    for q_mode, a_q in A.items():
        mode = tuple(p_mode[i] + q_mode[i] for i in range(3))
        first = mul(dot(p_mode, a_q), dot(q_mode, v_p))
        second = mul(dot(p_mode, a_q), dot(q_mode, v_p))
        Pt_source[mode] = add(Pt_source.get(mode, ZERO), add(first, second))
assert Pt_source.get((0, 0, 0), ZERO) == ZERO
Pt = {mode: scale(value, Q(1, sum(k * k for k in mode)))
      for mode, value in Pt_source.items() if mode != (0, 0, 0)}
assert Pt.get((0, 0, 0), ZERO) == ZERO

Qvu = nonlinear_Q(V, A)
Quv = nonlinear_Q(A, V)
Pt_independent = pressure_from_Q({mode: vadd(Qvu.get(mode, zero_vector()), Quv.get(mode, zero_vector()))
                                 for mode in set(Qvu) | set(Quv)})
assert Pt == Pt_independent
W = {}
for mode in set(A) | set(V) | set(Qvu) | set(Quv) | set(Pt):
    norm = sum(value * value for value in mode)
    pressure_value = Pt.get(mode, ZERO)
    W[mode] = [add(add(add(scale(V.get(mode, zero_vector())[i], -norm), Qvu.get(mode, zero_vector())[i]),
                       Quv.get(mode, zero_vector())[i]), scale(pressure_value, -mode[i])) for i in range(3)]
    if not any(W[mode]):
        del W[mode]


def modewise_conjugate(field):
    return all(field.get(tuple(-k for k in mode), zero_vector()) == [-value for value in vector]
               for mode, vector in field.items())


assert modewise_conjugate(A) and modewise_conjugate(V) and modewise_conjugate(W)
assert all(dot(mode, vector) == ZERO for mode, vector in W.items())


def scalar_derivative(field, powers):
    result = ZERO
    for mode, value in field.items():
        factor = 1
        total_order = sum(powers)
        for axis in range(3):
            factor *= mode[axis] ** powers[axis]
        factor *= 1 if total_order % 4 == 0 else -1 if total_order % 4 == 2 else 0
        assert total_order % 2 == 0
        result = add(result, scale(value, factor))
    return result


def v_scalar_derivative(field, powers):
    """Real derivative of a velocity field stored as its imaginary amplitude V (u=iV)."""
    total_order = sum(powers)
    assert total_order % 2 == 1
    sign = 1 if (total_order + 1) % 4 == 0 else -1
    result = ZERO
    for mode, value in field.items():
        factor = sign
        for axis in range(3):
            factor *= mode[axis] ** powers[axis]
        result = add(result, scale(value, factor))
    return result


def first_matrix(field):
    return [[sum_field_scale(component_field(field, j), i) for i in range(3)] for j in range(3)]


def sum_field_scale(field, axis):
    result = ZERO
    for mode, value in field.items():
        result = add(result, scale(value, -mode[axis]))
    return result


Du = first_matrix(A)
Dv = first_matrix(V)
Dw = first_matrix(W)
Dv_minus_2Du = [[add(Dv[i][j], scale(Du[i][j], -2)) for j in range(3)] for i in range(3)]
Dw_minus_8Du = [[add(Dw[i][j], scale(Du[i][j], -8)) for j in range(3)] for i in range(3)]
assert all(value == ZERO for row in Dv_minus_2Du for value in row)

def pressure_hessian(field):
    return [[scalar_derivative(field, tuple(2 if k == i == j else 1 if k in (i, j) else 0 for k in range(3))) for j in range(3)] for i in range(3)]


Pt_hessian = pressure_hessian(Pt)
assert all(Pt.get(tuple(-mode[i] for i in range(3)), ZERO) == value for mode, value in Pt.items())

def qp_sympy(value):
    return sum(sp.Rational(str(value[i])) * rho**i for i in range(2))


def homogeneous_pressure(field, degree):
    polynomial = 0
    vars_ = (source["x"], source["y"], source["z"])
    for i in range(degree + 1):
        for j in range(degree + 1 - i):
            k = degree - i - j
            polynomial += qp_sympy(scalar_derivative(field, (i, j, k))) / (sp.factorial(i) * sp.factorial(j) * sp.factorial(k)) * vars_[0]**i * vars_[1]**j * vars_[2]**k
    return sp.expand(polynomial)


def reduce_parent(value):
    return from_sympy(sp.sympify(value, locals={"rho": rho}))


initial_pzz = qp_sympy(scalar_derivative(P0, (0, 0, 2)))
parent_pzz = parent_receipt["pressure_hessian"]["pzz"]
assert reduce_parent(parent_pzz) == qp(scalar_derivative(P0, (0, 0, 2)))
parent_p4 = parent_receipt["pressure_degree4"]["p4_actual_coefficients"]
initial_p4 = homogeneous_pressure(P0, 4)
for monomial, value in parent_p4.items():
    i, j, k = (int(part) for part in monomial.strip("()").split(", "))
    assert from_sympy(sp.Poly(initial_p4, source["x"], source["y"], source["z"]).coeff_monomial(source["x"]**i * source["y"]**j * source["z"]**k)) == reduce_parent(value)

selected_powers = [(3, 0, 0), (1, 2, 0), (2, 0, 1), (0, 0, 3)]
selected_components = [1, 1, 2, 2]
v_cubic = [qp_sympy(v_scalar_derivative(component_field(V, component), powers))
            for component, powers in zip(selected_components, selected_powers)]
parent_v_cubic = [sp.sympify(value, locals={"rho": rho}) for value in parent_receipt["cubic_time_jet"]["total"]]
assert all(from_sympy(value) == from_sympy(parent) for value, parent in zip(v_cubic, parent_v_cubic))


def qp_string(value):
    return {str(i): str(value[i]) for i in range(2) if value[i]}


def eval_qp(value, point):
    return sum(value[i] * point**i for i in range(2))


def enclosure(value):
    left, right = eval_qp(value, ROOT_LO), eval_qp(value, ROOT_HI)
    return [str(min(left, right)), str(max(left, right))]


def grid_enclosure(value):
    left, right = eval_qp(value, ROOT_LO), eval_qp(value, ROOT_HI)
    lower, upper = min(left, right), max(left, right)
    return {"exact": [str(lower), str(upper)], "grid_1e3": [str(sp.floor(lower * 1000) / 1000), str(sp.ceiling(upper * 1000) / 1000)]}


pt4 = homogeneous_pressure(Pt, 4)
sx, sy, sz = source["x"], source["y"], source["z"]
sxy = sx**2 + sy**2
A4 = sp.expand(pt4).coeff(sx, 4)
B4 = sp.expand(pt4).coeff(sx, 2).coeff(sy, 2)
C4 = sp.expand(pt4).coeff(sx, 2).coeff(sz, 2)
D4 = sp.expand(pt4).coeff(sz, 4)
E4 = sp.expand(pt4).coeff(sx, 3).coeff(sy, 1)
L4 = (6 * A4 + B4 - 3 * D4) / 8
M4 = C4 + 3 * D4
b4 = (2 * A4 - B4) / 8
Hax4 = sz**4 - 3 * sxy * sz**2 + sp.Rational(3, 8) * sxy**2
Hcos4 = sx**4 - 6 * sx**2 * sy**2 + sy**4
Hsin4 = sx * sy * (sx**2 - sy**2)
pt4_split = sp.expand(L4 * sxy**2 + M4 * sxy * sz**2 + D4 * Hax4 + b4 * Hcos4 + E4 * Hsin4)
assert sp.expand(pt4 - pt4_split) == 0
assert len([(i, j, k) for i in range(5) for j in range(5 - i) for k in [4 - i - j]]) == 15
parent_hax = sp.sympify(parent_receipt["harmonic_coefficients_mod_target"]["hax"], locals={"rho": rho})
parent_hcos = sp.sympify(parent_receipt["harmonic_coefficients_mod_target"]["hcos"], locals={"rho": rho})
parent_hsin = sp.sympify(parent_receipt["harmonic_coefficients_mod_target"]["hsin"], locals={"rho": rho})
assert from_sympy(L4 + sp.Rational(1, 2) + sp.Rational(15, 2) * parent_hax) == ZERO
assert from_sympy(M4 - 30 * parent_hax) == ZERO
assert add(Dw[1][0], scale(Dw[0][1], -1)) == qp(16)
assert target_sympy.degree() == 2
root_intervals = parent_receipt["strain_current"]["all_real_root_intervals"]
assert len(root_intervals) == 2
root_signs = []
for endpoints, multiplicity in root_intervals:
    left, right = (Q(str(sp.Rational(value))) for value in endpoints)
    assert left < right and multiplicity == 1
    p_left = sum(P[i] * left**i for i in range(P.degree() + 1))
    p_right = sum(P[i] * right**i for i in range(P.degree() + 1))
    assert p_left * p_right < 0
    assert right < 0 or left > 0
    root_signs.append(1 if left > 0 else -1)
assert sorted(root_signs) == [-1, 1]

quartic_rates = {"L": from_sympy(L4), "M": from_sympy(M4), "D": from_sympy(D4), "b": from_sympy(b4), "c": from_sympy(E4)}
normalized_rates = {"L": add(quartic_rates["L"], qp(sp.Rational(1, 2))), "M": quartic_rates["M"],
                    "kappa": add(quartic_rates["D"], scale(from_sympy(parent_hax), Q(-28, 5))),
                    "b": add(quartic_rates["b"], scale(from_sympy(parent_hcos), -6)),
                    "c": add(quartic_rates["c"], scale(from_sympy(parent_hsin), -6))}
diagnostic_enclosures = {"Dw22": grid_enclosure(Dw[2][2]), "Pt_zz": grid_enclosure(Pt_hessian[2][2]),
                       "Dw22_minus_8a": grid_enclosure(add(Dw[2][2], scale(qp(8 * sp.Rational(str(source["a"]))), -1)))}

key_rate_enclosures = {"Dv_00": enclosure(Dv[0][0]), "Dv_01": enclosure(Dv[0][1]),
                       "Dw_00": enclosure(Dw[0][0]), "p_t_hessian_22": enclosure(Pt_hessian[2][2])}


receipt = {
    "scope": "Exact finite phase Navier--Stokes time jets for the extracted order-three spectrum; no global evolution claim",
    "arithmetic": "FLINT fmpq_poly coefficients reduced modulo the exact rho target quadratic",
    "versions": {"sympy": sp.__version__, "python_flint": flint.__version__},
    "source": "source_spectrum.py; nu=1; p_t gauge zero mode=0",
    "checks": {"modewise_conjugacy": True, "full_divergence": True, "all_mode_dot_k_A_V_W_zero": True, "pressure_zero_modes": True, "p_t_source_zero_mode_verified": True, "ordered_p_t_trace_terms_verified": True, "p_t_equals_independent_pressure_from_Qvu_plus_Quv": True, "initial_pzz_parent_match": True, "initial_full_p4_parent_match": True, "initial_v_cubic_parent_match": True, "Dv_minus_2Du_zero_modulo_target": True, "Dw_antisymmetric_vorticity_rate_16": True, "both_parent_root_intervals_verified": True, "quartic_p_t_split_verified": True, "quartic_rate_consistency_verified": True},
    "modes": {"u": len(A), "v": len(V), "w": len(W), "p_t": len(Pt)},
    "matrices_at_origin": {"Du": [[qp_string(v) for v in row] for row in Du], "Dv": [[qp_string(v) for v in row] for row in Dv], "Dw": [[qp_string(v) for v in row] for row in Dw], "Dv_minus_2Du": [[qp_string(v) for v in row] for row in Dv_minus_2Du], "Dw_minus_8Du": [[qp_string(v) for v in row] for row in Dw_minus_8Du], "p_t_hessian": [[qp_string(v) for v in row] for row in Pt_hessian]},
    "quartic_p_t": {"coefficients_by_monomial": {str((i, j, k)): str(sp.Poly(pt4, sx, sy, sz).coeff_monomial(sx**i * sy**j * sz**k)) for i in range(5) for j in range(5 - i) for k in [4 - i - j]}, "split_formula": "L*s^2+M*s*z^2+D*Hax+b*Hcos+c*Hsin", "L": str(L4), "M": str(M4), "D": str(D4), "b": str(b4), "c": str(E4)},
    "positive_root_rate_enclosures": key_rate_enclosures,
    "diagnostic_enclosures": diagnostic_enclosures,
    "quartic_rate_enclosures": {name: grid_enclosure(value) for name, value in quartic_rates.items()},
    "normalized_frame": {"beta": "1", "gamma": "4/5", "K_equals_r_equals_z_equals_b1": True, "epsilon_prime": "-2/5", "initial_h_values": {"hax": str(parent_hax), "hcos": str(parent_hcos), "hsin": str(parent_hsin)}, "normalized_rates": {name: qp_string(value) for name, value in normalized_rates.items()}, "normalized_rate_enclosures": {name: grid_enclosure(value) for name, value in normalized_rates.items()}},
    "phase_to_physical": {"k": "2*pi", "u_phys": "k*u(kX,k^2*t)", "p_phys": "k^2*p", "nu": "unchanged"},
    "exit_status": 0,
}
print(json.dumps(receipt, indent=2))
