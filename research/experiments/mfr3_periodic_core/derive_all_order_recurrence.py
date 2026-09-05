"""All-order axisymmetric recurrence audit for the MFR3 radial core.

This is exact SymPy algebra only.  It checks the coefficient convolutions, indicial denominators,
the alpha=3 beta/2 resonance aperture, and the first pressure row coupling a symmetry-breaking
F_7 z mode to the W_8 constant mode.  It does not assert existence, parity, stability, or a PDE
continuation theorem.
"""

import json

import sympy as sp


m, n = sp.symbols("m n", integer=True, nonnegative=True)
alpha, beta = sp.symbols("alpha beta", real=True)
h = alpha + beta
kappa = alpha + 2 * beta

# Genuine finite Cauchy-product test.  Every W_j and F_j is an independent function of z;
# coefficients m=1,...,4 are extracted from the original rho-polynomials before comparison with
# the displayed all-order recurrence.
z, rho = sp.symbols("z rho", real=True)
Wj = [sp.Function(f"W{jj}")(z) for jj in range(5)]
Fj = [sp.Function(f"F{jj}")(z) for jj in range(5)]
Wpoly = sum(Wj[jj] * rho**jj for jj in range(5))
Fpoly = sum(Fj[jj] * rho**jj for jj in range(5))
Vpoly = sum(-sp.diff(Wj[jj], z) * rho**jj / (2 * (jj + 1)) for jj in range(5))
Bpoly = (alpha * Wpoly + (Wpoly + beta * z) * sp.diff(Wpoly, z)
         + 2 * rho * (Vpoly + beta) * sp.diff(Wpoly, rho))
Cpoly = ((alpha + beta + 2 * Vpoly) * Fpoly
         + (Wpoly + beta * z) * sp.diff(Fpoly, z)
         + 2 * rho * (Vpoly + beta) * sp.diff(Fpoly, rho))

finite_recurrence_orders = []
for mm in range(1, 5):
    Bm = sp.expand(Bpoly).coeff(rho, mm)
    Bm_expected = (Wj[0] + beta * z) * sp.diff(Wj[mm], z) + (
        alpha + 2 * mm * beta + (1 - mm) * sp.diff(Wj[0], z)
    ) * Wj[mm]
    Bm_expected += sum(
        Wj[ii] * sp.diff(Wj[mm - ii], z)
        - (mm - ii) * sp.diff(Wj[ii], z) * Wj[mm - ii] / (ii + 1)
        for ii in range(1, mm)
    )
    Cm = sp.expand(Cpoly).coeff(rho, mm)
    Cm_expected = (Wj[0] + beta * z) * sp.diff(Fj[mm], z) + (
        alpha + (2 * mm + 1) * beta - (mm + 1) * sp.diff(Wj[0], z)
    ) * Fj[mm]
    Cm_expected += Wj[mm] * sp.diff(Fj[0], z) - sp.diff(Wj[mm], z) * Fj[0] / (mm + 1)
    Cm_expected += sum(
        Wj[ii] * sp.diff(Fj[mm - ii], z)
        - (mm - ii + 1) * sp.diff(Wj[ii], z) * Fj[mm - ii] / (ii + 1)
        for ii in range(1, mm)
    )
    assert sp.simplify(Bm - Bm_expected) == 0, (mm, Bm - Bm_expected)
    assert sp.simplify(Cm - Cm_expected) == 0, (mm, Cm - Cm_expected)
    finite_recurrence_orders.append(mm)

# Indicial denominators after Gamma(z)=kappa*z+O(z^2), W0'(0)=alpha+beta.
W0p = h
W_den = sp.expand(n * kappa + alpha + 2 * m * beta + (1 - m) * W0p)
F_den = sp.expand(n * kappa + alpha + (2 * m + 1) * beta - (m + 1) * W0p)
assert sp.expand(W_den - (n * kappa + (2 - m) * alpha + (m + 1) * beta)) == 0
assert sp.expand(F_den - (n * kappa - m * (alpha - beta))) == 0

# Resonance table at alpha=3 beta/2, through the first requested orders.
resonance_alpha = sp.Rational(3, 2) * beta
W_den_resonant = sp.factor(W_den.subs(alpha, resonance_alpha))
F_den_resonant = sp.factor(F_den.subs(alpha, resonance_alpha))
assert sp.expand(W_den_resonant - beta * (sp.Rational(7, 2) * n + 4 - m / 2)) == 0
assert sp.expand(F_den_resonant - beta * (sp.Rational(7, 2) * n - m / 2)) == 0

W_resonances = [(mm, nn) for mm in range(16) for nn in range(3)
                if sp.simplify(W_den_resonant.subs({m: mm, n: nn})) == 0]
F_resonances = [(mm, nn) for mm in range(16) for nn in range(3)
                if sp.simplify(F_den_resonant.subs({m: mm, n: nn})) == 0]
assert W_resonances == [(8, 0), (15, 1)]
assert F_resonances == [(0, 0), (7, 1), (14, 2)]

# Pressure row audit.  Keep only the first axis data and the symmetry-breaking pair W8(0)=a,
# F7'(0)=b.  At m=8 the resonant W8 constant drops out of B8, while A7'(0)=-2*b.  Hence the
# pressure relation A7'=2*m*B8 forces b=0 in this paid lower-aperture slice.
a8, b7, p = sp.symbols("a8 b7 p", real=True)
W0 = h * z - kappa * p * z**3 / 3
F0 = 1 - p * z**2 / 2
W8 = a8
F7 = b7 * z
W_truncated = W0 + rho**8 * W8
F_truncated = F0 + rho**7 * F7
V_truncated = -sp.diff(W0, z) / 2 - rho**8 * sp.diff(W8, z) / 18
A_truncated = (
    h * V_truncated + (W_truncated + beta * z) * sp.diff(V_truncated, z)
    + 2 * rho * (V_truncated + beta) * sp.diff(V_truncated, rho)
    + V_truncated**2 - F_truncated**2
)
B_truncated = (
    alpha * W_truncated + (W_truncated + beta * z) * sp.diff(W_truncated, z)
    + 2 * rho * (V_truncated + beta) * sp.diff(W_truncated, rho)
)
A7_prime = sp.expand(sp.diff(A_truncated, z, rho, 7).subs({z: 0, rho: 0}) / sp.factorial(7))
B8_axis = sp.expand(sp.diff(B_truncated, rho, 8).subs({z: 0, rho: 0}) / sp.factorial(8))
A7_prime_paid = sp.expand(A7_prime.subs(alpha, resonance_alpha))
B8_axis_paid = sp.expand(B8_axis.subs(alpha, resonance_alpha))
assert sp.expand(A7_prime_paid + 2 * b7) == 0
assert sp.expand(B8_axis_paid) == 0
assert sp.expand(A7_prime_paid - 16 * B8_axis_paid + 2 * b7) == 0

receipt = {
    "scope": "Exact tests of the written all-order recurrence at modes 1..4, indicial multipliers, and a limited symmetry-breaking slice; no existence, stability, or continuation claim",
    "sympy_version": sp.__version__,
    "command": "/tmp/holonics-mfr3-symbolic/bin/python research/experiments/mfr3_periodic_core/derive_all_order_recurrence.py",
    "all_order_coefficients": {
        "B_linear": "Gamma*W_m' + [alpha+2*m*beta+(1-m)*W0']*W_m",
        "B_lower": "sum_(i+j=m,i,j>=1) [W_i*W_j' - j/(i+1)*W_i'*W_j]",
        "pressure_row": "A_(m-1)' = 2*m*B_m",
        "C_linear": "Gamma*F_m' + [alpha+(2*m+1)*beta-(m+1)*W0']*F_m",
        "C_known": "W_m*F0' - W_m'*F0/(m+1)",
        "C_lower": "sum_(i+j=m,i,j>=1) [W_i*F_j' - (j+1)/(i+1)*W_i'*F_j]",
    },
    "finite_recurrence_test": {
        "independent_fields": "W_j(z), F_j(z), j=0..4",
        "tested_orders": finite_recurrence_orders,
        "source": "coefficients extracted from original B(rho), C(rho) Cauchy products",
    },
    "indicial_denominators": {
        "W_m_z_n": "n*kappa+(2-m)*alpha+(m+1)*beta",
        "F_m_z_n": "n*kappa-m*(alpha-beta)",
        "kappa": "alpha+2*beta",
    },
    "resonance_aperture": {
        "alpha": "3*beta/2",
        "tested_m": "0..15",
        "tested_n": "0..2",
        "W_resonances": [[8, 0], [15, 1]],
        "F_resonances": [[0, 0], [7, 1], [14, 2]],
        "parity_reading": "W odd excludes W8,z0 and admits W15,z1; F even excludes F7,z1 and admits F14,z2",
        "symmetry_breaking_retained": ["F7,z1", "W8,z0"],
    },
    "pressure_symmetry_breaking_audit": {
        "paid_slice": "W0'=alpha+beta, W0''=0, W0'''=-2*kappa*p, F0=1-p*z^2/2, W8(0)=a8, F7'(0)=b7",
        "B8_axis": "0 at alpha=3*beta/2",
        "A7_prime_axis": "-2*b7",
        "pressure_row": "A7'=16*B8 therefore b7=0 in this paid lower-aperture slice",
    },
    "exit_status": 0,
}
print(json.dumps(receipt, indent=2))
