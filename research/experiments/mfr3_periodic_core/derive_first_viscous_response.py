"""Exact first-viscous response of the finite reflected radial jet.

The full second-resonance source supplies the accepted FLINT baseline.  This
file linearizes its actual A, B, C products for mu'=-mu/2.  The calculation is
finite and makes no claim about a finite-mu solution or convergence.
"""

import contextlib
import io
import json
import runpy
import sys
from pathlib import Path

import flint
from flint import fmpq as Q, fmpq_poly as Poly


BASE = Path(__file__).parent
with contextlib.redirect_stdout(io.StringIO()):
    full = runpy.run_path(str(BASE / "derive_full_second_resonance.py"), run_name="mfr3_first_viscous_baseline")

ALPHA, BETA, KAPPA, DELTA = Q(3, 2), Q(1), Q(7, 2), Q(1, 2)
X = full["X"]
NW = lambda m: 29 - 2 * m
NK = lambda m: 28 - 2 * m


class Parameter:
    """A c+E*e+Y*y+T*t+K*k carrier over Q[X]."""
    __slots__ = ("c", "e", "y", "t", "k")

    def __init__(self, c=0, e=0, y=0, t=0, k=0):
        self.c = c if isinstance(c, Poly) else Poly([c])
        self.e = e if isinstance(e, Poly) else Poly([e])
        self.y = y if isinstance(y, Poly) else Poly([y])
        self.t = t if isinstance(t, Poly) else Poly([t])
        self.k = k if isinstance(k, Poly) else Poly([k])

    def __bool__(self):
        return bool(self.c) or bool(self.e) or bool(self.y) or bool(self.t) or bool(self.k)

    def __add__(self, other):
        return Parameter(self.c + other.c, self.e + other.e, self.y + other.y,
                         self.t + other.t, self.k + other.k)

    def __neg__(self):
        return Parameter(-self.c, -self.e, -self.y, -self.t, -self.k)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        for i, left in enumerate((self.e, self.y, self.t, self.k)):
            for j, right in enumerate((other.e, other.y, other.t, other.k)):
                assert not (left and right), ("quadratic viscous parameter", i, j)
        return Parameter(self.c * other.c,
                         self.c * other.e + self.e * other.c,
                         self.c * other.y + self.y * other.c,
                         self.c * other.t + self.t * other.c,
                         self.c * other.k + self.k * other.c)

    def scale(self, scalar):
        return Parameter(self.c * scalar, self.e * scalar, self.y * scalar,
                         self.t * scalar, self.k * scalar)

    def divide_X(self):
        assert all(part == 0 or part[0] == 0 for part in (self.c, self.e, self.y, self.t, self.k))
        return Parameter(*(part.right_shift(1) if part else Poly([0])
                           for part in (self.c, self.e, self.y, self.t, self.k)))


ZERO = Parameter()


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


def integral(series):
    return {n + 1: v.scale(Q(1, n + 1)) for n, v in series.items()}


def scalar_series(poly):
    return {n: Parameter(c) for n, c in enumerate(poly.coeffs()) if c}


def affine_series(series):
    return {n: Parameter(value.c, y=value.d) for n, value in series.items() if value}


def second_derivative(series):
    return derivative(derivative(series))


def diffusion(series, m, factor, degree):
    return trim(add(scale(series[m + 1], factor), second_derivative(series[m])), degree)


base_W = [affine_series(series) for series in full["W"]]
base_J = [affine_series(series) for series in full["J"]]
base_V = [affine_series(series) for series in full["V"]]
G0 = scalar_series(full["G0z"])
I0 = scalar_series(full["I0z"])
# Derive every reciprocal and weight coefficient from the exact binomial rule.
# No manually supplied coefficient table is admitted as an axis inverse.
inv_G0_sq_poly = full["binomial_axis"](Q(5, 2), NW(0))
assert full["G0z"].pow_trunc(2, NK(0) + 1).mul_low(inv_G0_sq_poly, NK(0) + 1) == Poly([1])
inv_G0_sq = scalar_series(inv_G0_sq_poly)


def scaled_binomial(exponent, degree):
    poly = full["binomial_axis"](exponent, degree)
    return {n: Parameter(c * Q(2) ** (n // 2))
            for n, c in enumerate(poly.coeffs()) if c}


chi = product({2: Parameter(1)}, scaled_binomial(Q(-2), NW(0)), NW(0))
chi28 = product({28: Parameter(1)}, scaled_binomial(Q(-15), NW(0)), NW(0))
A = Poly([75, Q(40, 7)])
B = Poly([Q(-2325, 26), Q(-55, 7)])
f0_factor = add({0: Parameter(c=A)}, scale(chi, B), {n: Parameter(e=value.c) for n, value in chi28.items()})
f0 = product(G0, f0_factor, 29)
k0 = {n: Parameter(c=X) * value for n, value in f0.items()}
G1 = {n: Parameter(value.c.right_shift(1), y=value.d.right_shift(1))
      for n, value in full["J"][1].items() if value}
Phi = add(scale(G1, Q(8)), second_derivative(G0))
f0_over = product(f0, inv_G0_sq, 29)
w0 = add(scale(add(product(f0, I0, 29), scale(product(G0, integral(f0_over), 29), Q(-1))), KAPPA),
         scale(product(G0, integral(product(add(scale(f0, DELTA), Phi), inv_G0_sq, 29)), 29), Q(-1)))

W = [w0]
K = [k0]
V = [scale(derivative(w0), Q(-1, 2))]
Gamma_scalar = full["Gamma_scalar"]
W0prime = full["W0prime"]


def linear_A(m, degree):
    out = add(scale(V[m], ALPHA + BETA + 2 * BETA * m),
              scale(times_z(derivative(V[m])), BETA))
    for i in range(m + 1):
        j = m - i
        out = add(out, product(W[i], derivative(base_V[j]), degree),
                  product(base_W[i], derivative(V[j]), degree),
                  scale(product(V[i], base_V[j], degree), Q(2 * j + 1)),
                  scale(product(base_V[i], V[j], degree), Q(2 * j + 1)))
        out = add(out, {n: -a.divide_X() for n, a in product(base_J[i], K[j], degree).items()},
                  {n: -a.divide_X() for n, a in product(K[i], base_J[j], degree).items()})
    return trim(out, degree)


def linear_B(m, degree):
    out = add(scale(W[m], ALPHA + 2 * BETA * m),
              scale(times_z(derivative(W[m])), BETA))
    for i in range(m + 1):
        j = m - i
        out = add(out, product(W[i], derivative(base_W[j]), degree),
                  product(base_W[i], derivative(W[j]), degree),
                  scale(product(V[i], base_W[j], degree), Q(2 * j)),
                  scale(product(base_V[i], W[j], degree), Q(2 * j)))
    return trim(out, degree)


def linear_CJ(m, degree):
    out = add(scale(K[m], ALPHA + BETA + 2 * BETA * m),
              scale(times_z(derivative(K[m])), BETA))
    for i in range(m + 1):
        j = m - i
        out = add(out, product(W[i], derivative(base_J[j]), degree),
                  product(base_W[i], derivative(K[j]), degree),
                  scale(product(V[i], base_J[j], degree), Q(2 * (j + 1))),
                  scale(product(base_V[i], K[j], degree), Q(2 * (j + 1))))
    return trim(out, degree)


def linearized_A1(m, degree):
    return trim(add(linear_A(m, degree), scale(V[m], Q(-1, 2)),
                    scale(diffusion(base_V, m, 4 * (m + 1) * (m + 2), degree), Q(-1))), degree)


def linearized_B1(m, degree):
    return trim(add(linear_B(m, degree), scale(W[m], Q(-1, 2)),
                    scale(diffusion(base_W, m, 4 * (m + 1) ** 2, degree), Q(-1))), degree)


def linearized_C1(m, degree):
    return trim(add(linear_CJ(m, degree), scale(K[m], Q(-1, 2)),
                    scale(diffusion(base_J, m, 4 * (m + 1) * (m + 2), degree), Q(-1))), degree)


def solve_transport(m, rhs, degree, parity, kind):
    if kind == "W":
        d = {n: (1 - m) * c for n, c in W0prime.items()}
        d[0] = d.get(0, Q(0)) + ALPHA + 2 * m * BETA - DELTA
    else:
        d = {n: -(m + 1) * c for n, c in W0prime.items()}
        d[0] = d.get(0, Q(0)) + ALPHA + (2 * m + 1) * BETA - DELTA
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
            solution[n] = unpaid.scale(1 / diagonal)
        else:
            resonances[n] = -unpaid
            if kind == "W":
                assert (m, n) == (14, 1)
                solution[n] = Parameter(t=1)
            else:
                assert (m, n) == (13, 2)
                solution[n] = Parameter(k=1)
    return solution, resonances


# The prescribed axis itself is a source obligation, not a free initial port.
assert not linearized_C1(0, NK(0)), "Forced axis violates its first-viscous swirl equation"
assert not add(scale(V[0], Q(2)), derivative(W[0]))
rows = []
resonances = {}
for m in range(1, 14):
    W.append({})
    V.append({})
    K.append({})
    pressure_rhs = trim(add(derivative(linearized_A1(m - 1, NW(m) + 1)),
                             scale(linearized_B1(m, NW(m)), Q(-2 * m))), NW(m))
    W[m], wres = solve_transport(m, scale(pressure_rhs, Q(1, 2 * m)), NW(m), 1, "W")
    V[m] = scale(derivative(W[m]), Q(-1, 2 * (m + 1)))
    swirl_rhs = scale(linearized_C1(m, NK(m)), Q(-1))
    K[m], kres = solve_transport(m, swirl_rhs, NK(m), 0, "K")
    resonances[m] = {"W": wres, "K": kres}
    rows.append({"mode": m, "W_resonances": list(wres), "K_resonances": list(kres)})
    print(f"progress viscous_mode={m} W_resonances={list(wres)} K_resonances={list(kres)}",
          file=sys.stderr, flush=True)

# Mode 14 determines the prior K13[z^2] fibre while W14[z] remains T-free.
W.append({1: Parameter(t=1)})
V.append(scale(derivative(W[14]), Q(-1, 30)))
K.append({})
pressure14 = trim(add(derivative(linearized_A1(13, NW(14) + 1)),
                      scale(linearized_B1(14, NW(14)), Q(-28))), NW(14))
pressure14_z1 = pressure14.get(1, ZERO)
assert pressure14_z1.y == Poly([25200])
assert pressure14_z1.k == Poly([-4])
assert not pressure14_z1.t
k13_solution = pressure14_z1.scale(Q(1, 4))
K[13][2] = K[13][2] + k13_solution
assert K[13][2].y == Poly([6300]) and not K[13][2].k
pressure14_after = trim(add(derivative(linearized_A1(13, NW(14) + 1)),
                            scale(linearized_B1(14, NW(14)), Q(-28))), NW(14))
assert not pressure14_after

forcing_C14 = linearized_C1(14, NK(14)).get(0, ZERO)
unit_k14 = {0: Parameter(c=1)}
K[14] = unit_k14
unit_C14 = linearized_C1(14, NK(14)).get(0, ZERO) - forcing_C14
K[14] = {}
assert unit_C14.c.degree() == 0 and unit_C14.c[0] != 0 and not unit_C14.e and not unit_C14.y and not unit_C14.t and not unit_C14.k
K[14][0] = forcing_C14.scale(-1 / unit_C14.c[0])
assert not linearized_C1(14, NK(14))
rows.append({"mode": 14, "pressure_junction": "K13[z2]", "W14_free": "T", "K14": "solved"})
print("progress viscous_mode=14 pressure=K13[z2] solved swirl=K14[0] solved", file=sys.stderr, flush=True)


pressure_rows, swirl_rows = {}, {}
for m in range(1, 15):
    pressure_rows[m] = trim(add(derivative(linearized_A1(m - 1, NW(m) + 1)),
                                scale(linearized_B1(m, NW(m)), Q(-2 * m))), NW(m))
    swirl_rows[m] = linearized_C1(m, NK(m))
    assert not pressure_rows[m], ("viscous pressure residual", m, pressure_rows[m])
    if m != 13:
        assert not swirl_rows[m], ("viscous swirl residual", m, swirl_rows[m])
    assert not add(scale(V[m], Q(2 * (m + 1))), derivative(W[m]))

# Reconstruct the actual first-response pressure, including its last constant
# radial coefficient. The potential is anchored by P1(0,0)=0; its exterior is
# not prescribed by this local jet.
pressure_potential = [scale(integral(linearized_B1(0, NW(0))), Q(-1))]
for m in range(1, 16):
    pressure_potential.append(scale(linearized_A1(m - 1, 30 - 2 * m), Q(-1, 2 * m)))
for m in range(15):
    assert not add(scale(pressure_potential[m + 1], Q(2 * (m + 1))),
                   linearized_A1(m, 28 - 2 * m))
    assert not trim(add(derivative(pressure_potential[m]), linearized_B1(m, NW(m))), NW(m))

# The full affine-mu profile is not an exact finite-mu solution. Its quadratic
# swirl residual at the axis is -D_J(k0), because the actual v0 and w0 axis
# values vanish. This receiver is independent of the late resonant parameters.
assert not V[0].get(0, ZERO) and not W[0].get(0, ZERO)
quadratic_axis_swirl = -diffusion(K, 0, Q(8), NK(0) - 2).get(0, ZERO)
assert not quadratic_axis_swirl.e and not quadratic_axis_swirl.y and not quadratic_axis_swirl.t and not quadratic_axis_swirl.k


def coefficients(series):
    return {str(n): {
        name: {str(i): str(getattr(value, name)[i]) for i in range(getattr(value, name).degree() + 1)
               if getattr(value, name)}
        for name in ("c", "e", "y", "t", "k") if getattr(value, name)
    } for n, value in series.items() if value}


def poly_coefficients(poly):
    return {str(i): str(poly[i]) for i in range(poly.degree() + 1) if poly[i]}


compatibility_K13 = resonances[13]["K"][2]
assert set(swirl_rows[13]) == {2}
assert all(getattr(swirl_rows[13][2], name) == getattr(compatibility_K13, name)
           for name in ("c", "e", "y", "t", "k"))
assert not linearized_C1(0, NK(0))
assert not compatibility_K13.y and not compatibility_K13.t and not compatibility_K13.k
E_numerator = -compatibility_K13.c
E_denominator = compatibility_K13.e
assert E_denominator
root_lo, root_hi = Q(5625, 2236), Q(1366, 543)


def interval_bounds(poly, lo, hi):
    lower = sum(c * (lo if c >= 0 else hi) ** n for n, c in enumerate(poly.coeffs()))
    upper = sum(c * (hi if c >= 0 else lo) ** n for n, c in enumerate(poly.coeffs()))
    return lower, upper


e_num_lower, e_num_upper = interval_bounds(E_numerator, root_lo, root_hi)
e_den_lower, e_den_upper = interval_bounds(E_denominator, root_lo, root_hi)
if e_den_upper < 0:
    E_numerator, E_denominator = -E_numerator, -E_denominator
    e_num_lower, e_num_upper = -e_num_upper, -e_num_lower
    e_den_lower, e_den_upper = -e_den_upper, -e_den_lower
assert e_den_lower > 0, "No certified nonzero E divisor on the prior root bracket"
e_corners = [n / d for n in (e_num_lower, e_num_upper) for d in (e_den_lower, e_den_upper)]
e_root_lower, e_root_upper = min(e_corners), max(e_corners)
for residual in list(pressure_rows.values()) + list(swirl_rows.values()):
    for value in residual.values():
        assert not value.c * E_denominator + value.e * E_numerator
        assert not value.y and not value.t and not value.k


receipt = {
    "scope": "Finite first-viscous reflected jet through mode14; no finite-mu solution or convergence claim",
    "python_flint_version": flint.__version__,
    "flint_version": flint.__FLINT_VERSION__,
    "command": "python research/experiments/mfr3_periodic_core/derive_first_viscous_response.py",
    "parameters": {"alpha": "3/2", "beta": "1", "delta": "1/2", "X": "a^2", "E": "axis-high correction", "Y": "Euler W15[z]", "T": "viscous W14[z]"},
    "budgets": {"N_W(m)": "29-2*m", "N_K(m)": "28-2*m", "modes": "0..14"},
    "prescribed_axis": {"f0": "G0*(40*X/7+75+(-55*X/7-2325/26)*chi+E*chi28)", "k0": "X*f0", "chi": "z^2/(1+2*z^2)^2", "chi28": "z^28/(1+2*z^2)^15", "w0": "forced formula including -(G0)*integral((delta*f0+Phi)/G0^2)"},
    "linearized_source": {"A1": "linearized A-delta*v-D_V(V*)", "B1": "linearized B-delta*w-D_W(W*)", "C1": "linearized C_J-delta*k-D_J(J*)", "v_m": "-w_m'/(2*(m+1))", "D_V_D_J": "4*(m+1)*(m+2)*field_(m+1)+field_m''", "D_W": "4*(m+1)^2*W_(m+1)+W_m''"},
    "rows": rows,
    "residual_recompute": {"forced_axis_mode0_zero": True, "pressure_modes_1_to_14_zero": True, "swirl_modes_1_to_12_and_14_zero": True, "swirl_mode13_compatibility_retained": True, "incompressibility_modes_1_to_14_zero": True, "parameter_quadratics_rejected": True, "full_mode13_row_is_compatibility_z2": True, "all_rows_zero_after_selected_E": True, "pressure_potential_gradient_matches_radial_and_axial_rows": True},
    "mode14_junction": {"pressure_z1_W14_T_coefficient": "0", "pressure_z1_K13_z2_coefficient": "-4", "pressure_z1_Y_coefficient": "25200", "K13_z2_Y_coefficient": "6300", "W14_z1_free": "T", "K14_z0": "solved", "domain": "X>0"},
    "axis_response": {"w0": coefficients(w0), "f0": coefficients(f0)},
    "pressure_response": {"axis_potential": coefficients(pressure_potential[0]), "last_radial_constant": coefficients(pressure_potential[15]), "anchor": "P1(0,0)=0", "formula": "P1_0=-integral B1_0; P1_m=-A1_(m-1)/(2m), m1..15"},
    "quadratic_mu_remainder": {"axis_swirl_CJ": poly_coefficients(quadratic_axis_swirl.c), "source": "At (s,z)=(0,0), quadratic advection is zero and C2_J=-8*k1(0)-k0''(0)", "scope": "One exact receiver of the complete unclosed mu^2 source; not a remainder norm"},
    "K13_compatibility": {"forcing": {name: poly_coefficients(getattr(compatibility_K13, name)) for name in ("c", "e", "y", "t", "k") if getattr(compatibility_K13, name)}, "equation": "forcing_c(X)+E*forcing_e(X)=0"},
    "E_divisor": {"numerator": poly_coefficients(E_numerator), "denominator": poly_coefficients(E_denominator), "relation": "E=numerator/denominator", "denominator_nonzero_on_prior_P_bracket": True, "prior_P_root_bracket": [str(root_lo), str(root_hi)], "E_interval_on_bracket": [str(e_root_lower), str(e_root_upper)], "denominator_interval": [str(e_den_lower), str(e_den_upper)]},
    "exit_status": 0,
}
print(json.dumps(receipt, indent=2))
