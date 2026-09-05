"""Exact Cartesian audit of the radial/axisymmetric continuation equations.

This is derivative algebra only.  It does not assert existence, stability, or continuation of a
Navier--Stokes solution.  Run with the pinned SymPy 1.14 environment used by the MFR3 receipts.
"""

import json

import sympy as sp


x, y, z, s = sp.symbols("x y z s", real=True)
alpha, beta, mu = sp.symbols("alpha beta mu", real=True)
coordinates = (x, y, z)
position = sp.Matrix(coordinates)
sxy = x**2 + y**2

V = sp.Function("V")
Omega = sp.Function("Omega")
W = sp.Function("W")


def curl(field):
    return sp.Matrix([
        sp.diff(field[2], y) - sp.diff(field[1], z),
        sp.diff(field[0], z) - sp.diff(field[2], x),
        sp.diff(field[1], x) - sp.diff(field[0], y),
    ])


def laplacian(field):
    return field.applyfunc(lambda entry: sum(sp.diff(entry, q, 2) for q in coordinates))


def check_equal(left, right):
    difference = left - right
    if isinstance(difference, sp.MatrixBase):
        assert all(sp.simplify(entry) == 0 for entry in difference), difference
    else:
        assert sp.simplify(difference) == 0, difference


def dS(f, q):
    """Differentiate an S-expression and substitute S=x²+y² when requested."""
    return sp.diff(f, s).subs(s, q)


u = sp.Matrix([
    x * V(sxy, z) - y * Omega(sxy, z),
    y * V(sxy, z) + x * Omega(sxy, z),
    W(sxy, z),
])
J = u.jacobian(coordinates)

divergence = sp.simplify(sum(sp.diff(u[i], coordinates[i]) for i in range(3)))
divergence_expected = (
    2 * V(sxy, z) + 2 * sxy * dS(V(s, z), sxy) + sp.diff(W(sxy, z), z)
)
check_equal(divergence, divergence_expected)

# Exact stationary Euler/modulation residual coefficients.
Vs = sp.diff(V(s, z), s)
Os = sp.diff(Omega(s, z), s)
Ws = sp.diff(W(s, z), s)
A = (
    (alpha + beta) * V(s, z)
    + (W(s, z) + beta * z) * sp.diff(V(s, z), z)
    + 2 * s * (V(s, z) + beta) * Vs
    + V(s, z) ** 2
    - Omega(s, z) ** 2
)
C = (
    (alpha + beta + 2 * V(s, z)) * Omega(s, z)
    + (W(s, z) + beta * z) * sp.diff(Omega(s, z), z)
    + 2 * s * (V(s, z) + beta) * Os
)
B = (
    alpha * W(s, z)
    + (W(s, z) + beta * z) * sp.diff(W(s, z), z)
    + 2 * s * (V(s, z) + beta) * Ws
)
residual = sp.simplify(J * u + beta * J * position + alpha * u)
residual_expected = sp.Matrix([
    x * A.subs(s, sxy) - y * C.subs(s, sxy),
    y * A.subs(s, sxy) + x * C.subs(s, sxy),
    B.subs(s, sxy),
])
check_equal(residual, residual_expected)

# Cartesian Laplacian coefficients: planar radial/angular components carry 8 f_s,
# while the axial scalar carries 4 f_s.
lap = laplacian(u)
radial_lap = lambda f: 4 * s * sp.diff(f, s, 2) + 8 * sp.diff(f, s) + sp.diff(f, z, 2)
axial_lap = lambda f: 4 * s * sp.diff(f, s, 2) + 4 * sp.diff(f, s) + sp.diff(f, z, 2)
lap_expected = sp.Matrix([
    x * radial_lap(V(s, z)).subs(s, sxy) - y * radial_lap(Omega(s, z)).subs(s, sxy),
    y * radial_lap(V(s, z)).subs(s, sxy) + x * radial_lap(Omega(s, z)).subs(s, sxy),
    axial_lap(W(s, z)).subs(s, sxy),
])
check_equal(lap, lap_expected)

# A radial pressure P(s,z) has gradient (2x P_s, 2y P_s, P_z).  Its compatibility
# with residual + grad(P)=0 is C=0 and A_z=2 B_s.
Pressure = sp.Function("Pressure")
pressure_source = Pressure(sxy, z)
pressure_gradient = sp.Matrix([sp.diff(pressure_source, q) for q in coordinates])
pressure_expected = sp.Matrix([2 * x * sp.diff(Pressure(s, z), s).subs(s, sxy),
                              2 * y * sp.diff(Pressure(s, z), s).subs(s, sxy),
                              sp.diff(Pressure(s, z), z).subs(s, sxy)])
check_equal(pressure_gradient, pressure_expected)
check_equal(sp.diff(-2 * sp.diff(Pressure(s, z), s), z)
            - 2 * sp.diff(-sp.diff(Pressure(s, z), z), s), 0)

# First radial lift: W=W0+sH, Omega=F+sK, V=-W0'/2-sH'/4.
sigma = sp.symbols("sigma", real=True)
W0, H, F, K = (sp.Function(name) for name in ("W0", "H", "F", "K"))
V_lift = -sp.diff(W0(z), z) / 2 - sigma * sp.diff(H(z), z) / 4
Omega_lift = F(z) + sigma * K(z)
W_lift = W0(z) + sigma * H(z)
A_lift = (
    (alpha + beta) * V_lift
    + (W_lift + beta * z) * sp.diff(V_lift, z)
    + 2 * sigma * (V_lift + beta) * sp.diff(V_lift, sigma)
    + V_lift**2 - Omega_lift**2
)
C_lift = (
    (alpha + beta + 2 * V_lift) * Omega_lift
    + (W_lift + beta * z) * sp.diff(Omega_lift, z)
    + 2 * sigma * (V_lift + beta) * sp.diff(Omega_lift, sigma)
)
B_lift = (
    alpha * W_lift
    + (W_lift + beta * z) * sp.diff(W_lift, z)
    + 2 * sigma * (V_lift + beta) * sp.diff(W_lift, sigma)
)
check_equal(
    2 * V_lift + 2 * sigma * sp.diff(V_lift, sigma) + sp.diff(W_lift, z),
    0,
)
Gamma = W0(z) + beta * z
A0 = sp.simplify(A_lift.subs(sigma, 0))
H_equation = Gamma * sp.diff(H(z), z) + (alpha + 2 * beta) * H(z) - sp.diff(A0, z) / 2
check_equal(
    sp.diff(A_lift, z).subs(sigma, 0) / 2 - sp.diff(B_lift, sigma).subs(sigma, 0),
    -H_equation,
)
K_equation = (
    Gamma * sp.diff(K(z), z)
    + (alpha + 3 * beta - 2 * sp.diff(W0(z), z)) * K(z)
    - F(z) * sp.diff(H(z), z) / 2
    + H(z) * sp.diff(F(z), z)
)
check_equal(sp.diff(C_lift, sigma).subs(sigma, 0), K_equation)
check_equal(C_lift, C_lift.subs(sigma, 0) + sigma * K_equation
            + sigma**2 * (H(z) * sp.diff(K(z), z) - sp.diff(H(z), z) * K(z)))
check_equal(B_lift, B_lift.subs(sigma, 0)
            + sigma * (Gamma * sp.diff(H(z), z) + (alpha + 2 * beta) * H(z))
            + sigma**2 * H(z) * sp.diff(H(z), z) / 2)

# Axis jet audit. Taylor polynomials make evaluation at z=0 explicit. C(0)=0 determines W'_0,
# C'(0)=0 determines W''_0, and C''(0)=0 determines W'''_0.
p = sp.symbols("p", positive=True)
h = alpha + beta
kappa = alpha + 2 * beta
w1, w2, w3, w4 = sp.symbols("w1 w2 w3 w4", real=True)
f3, f4 = sp.symbols("f3 f4", real=True)
Fjet = 1 - p * z**2 / 2 + f3 * z**3 / 6 + f4 * z**4 / 24
Wjet = w1 * z + w2 * z**2 / 2 + w3 * z**3 / 6 + w4 * z**4 / 24
Cjet = (Wjet + beta * z) * sp.diff(Fjet, z) + (h - sp.diff(Wjet, z)) * Fjet
axis_data = {}
for order, unknown in enumerate((w1, w2, w3)):
    equation = sp.diff(Cjet, z, order).subs(z, 0).subs(axis_data)
    solutions = sp.solve(equation, unknown)
    assert len(solutions) == 1
    axis_data[unknown] = solutions[0]
check_equal(axis_data[w1], h)
check_equal(axis_data[w2], 0)
check_equal(axis_data[w3], -2 * kappa * p)

Vjet = -sp.diff(Wjet, z) / 2
Ajet = h * Vjet + (Wjet + beta * z) * sp.diff(Vjet, z) + Vjet**2 - Fjet**2
A0 = sp.simplify(Ajet.subs(axis_data))
check_equal(sp.diff(A0, z).subs(z, 0), 0)
A0_second = sp.factor(sp.diff(A0, z, 2).subs(z, 0))
check_equal(A0_second, 2 * p * (1 + kappa**2))

# Gamma(0)=0 and Gamma'(0)=kappa: the first pressure rows give H(0)=0 and
# H'(0)=p*(1+kappa**2)/(2*kappa).
h0, h1, k0, k1 = sp.symbols("h0 h1 k0 k1", real=True)
Hjet = h0 + h1 * z
pressure_jet_equation = ((Wjet + beta * z) * sp.diff(Hjet, z)
                         + kappa * Hjet - sp.diff(A0, z) / 2).subs(axis_data)
H0 = sp.solve(pressure_jet_equation.subs(z, 0), h0)[0]
H1 = sp.solve(sp.diff(pressure_jet_equation, z).subs(z, 0).subs(h0, H0), h1)[0]
check_equal(H0, 0)
check_equal(H1, p * (1 + kappa**2) / (2 * kappa))
Kjet = k0 + k1 * z
swirl_jet_equation = ((Wjet + beta * z) * sp.diff(Kjet, z)
                      + (alpha + 3 * beta - 2 * sp.diff(Wjet, z)) * Kjet
                      - Fjet * sp.diff(Hjet, z) / 2 + Hjet * sp.diff(Fjet, z))
K0 = sp.solve(swirl_jet_equation.subs(axis_data).subs(z, 0).subs({h0: H0, h1: H1}), k0)[0]
check_equal(K0, p * (1 + kappa**2) / (4 * kappa * (beta - alpha)))

# For Z=W+sH, Omega=F+sK, V=-W'/2-sH'/4, the quadratic swirl coefficient is
# H*K'-H'*K. At the axis the paid first rows leave the displayed positive coefficient.
D = sp.simplify(-H1 * K0)
D_expected = sp.simplify(p**2 * (1 + kappa**2)**2 /
    (8 * kappa**2 * (alpha - beta)))
check_equal(D, D_expected)
r = sp.symbols("r", nonnegative=True)
C_second_order = D * (x**2 + y**2)**2
swirl_horizontal = sp.Matrix([-y * C_second_order, x * C_second_order])
curl_third = sp.simplify(sp.diff(swirl_horizontal[1], x) - sp.diff(swirl_horizontal[0], y))
check_equal(curl_third, 6 * D * (x**2 + y**2)**2)

axis_receipt = {
    "assumptions": [
        "F(0)=1", "F'(0)=0", "F''(0)=-p", "W(0)=0",
        "p>0", "kappa=alpha+2*beta>0",
        "alpha>beta"
    ],
    "derived_axis_jets": {
        "W_prime_0": "alpha+beta",
        "W_second_0": "0 (from C'(0)=0 under F'(0)=0)",
        "W_third_0": "-2*(alpha+2*beta)*p"
    },
    "pressure_correction": {
        "H_0": "0",
        "H_prime_0": "p*(1+kappa**2)/(2*kappa)"
    },
    "swirl_correction": {
        "K_0": "p*(1+kappa**2)/(4*kappa*(beta-alpha))",
        "quadratic_swirl_coefficient": sp.sstr(D_expected),
        "radial_order": "C_second_order = D*r**4; horizontal swirl residual is O(r**5)",
        "curled_third_order": "6*D*r**4"
    }
}

receipt = {
    "scope": "Exact Cartesian radial derivative algebra; no PDE existence, stability, or continuation claim",
    "sympy_version": sp.__version__,
    "command": "/tmp/holonics-mfr3-symbolic/bin/python research/experiments/mfr3_periodic_core/derive_radial_continuation.py",
    "assertions": {
        "divergence": "2*V + 2*s*V_s + W_z",
        "residual": "(x*A-y*C, y*A+x*C, B)",
        "radial_angular_laplacian": "4*s*f_ss + 8*f_s + f_zz",
        "axial_laplacian": "4*s*W_ss + 4*W_s + W_zz",
        "pressure_compatibility": "C=0 and A_z=2*B_s",
        "pressure_gradient": "actual Cartesian gradient (2*x*P_s,2*y*P_s,P_z)",
        "radial_lift_divergence": "0",
        "radial_lift_pressure_equation": "Gamma*H' + (alpha+2*beta)*H = A0'/2",
        "radial_lift_swirl_equation": "Gamma*K' + (alpha+3*beta-2*W0')*K = F*H'/2 - H*F'",
        "axis_jet_receipt": axis_receipt,
    },
    "exit_status": 0,
}
print(json.dumps(receipt, indent=2))
