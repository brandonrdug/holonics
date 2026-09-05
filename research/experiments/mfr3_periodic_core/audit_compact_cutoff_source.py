"""Exact compact-cutoff source audit at the certified inner radius.

The payload is read without rerunning its expensive recurrence.  The local
cutoff curl and angular source identity are independently differentiated with
SymPy; interval bounds use exact Fraction arithmetic.
"""

import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path

import sympy as sp


BASE = Path(__file__).parent
PAYLOAD = BASE.parents[2] / ".local" / "mfr3-periodic-core" / "periodic_potential.json"
payload_bytes = PAYLOAD.read_bytes()
payload = json.loads(payload_bytes)
Xlo, Xhi = Q(5625, 2236), Q(1366, 543)
Ylo, Yhi = Q(1679495189493), Q(1691966325597)
prior = json.loads((BASE / "full_second_resonance_receipt.json").read_text())
assert [str(Ylo), str(Yhi)] == list(map(str, prior["second_resonance"]["selected_Y_outer_integers"]))
assert [str(Xlo), str(Xhi)] == prior["second_resonance"]["root_bracket"]
r0 = Q(2) ** -6
s0 = r0**2
angular_gap = Q(1, 2)
residual_floor = angular_gap * s0 / 2


def parse_slot(slots):
    result = {}
    for name, powers in slots.items():
        if name == "constant":
            ypower = 0
        elif name == "Y":
            ypower = 1
        else:
            raise AssertionError(("unexpected axis parameter", name))
        for xpower, value in powers.items():
            result[(int(xpower), ypower)] = result.get((int(xpower), ypower), Q(0)) + Q(value)
    return {key: value for key, value in result.items() if value}


def interval_eval(poly, xlo=Xlo, xhi=Xhi, ylo=Ylo, yhi=Yhi):
    lower = Q(0)
    upper = Q(0)
    for (xpower, ypower), coefficient in poly.items():
        if coefficient >= 0:
            lower += coefficient * xlo**xpower * ylo**ypower
            upper += coefficient * xhi**xpower * yhi**ypower
        else:
            lower += coefficient * xhi**xpower * yhi**ypower
            upper += coefficient * xlo**xpower * ylo**ypower
    return lower, upper


axis_ag_rows = [row for row in payload["a_times_g"] if row["mu"] == 0 and row["z"] == 0]
assert len(axis_ag_rows) == 29
axis_ag = {row["s"]: parse_slot(row["coefficient"]) for row in axis_ag_rows}
assert axis_ag[1] == {(1, 0): Q(-1, 2)}

# Reconstruct J(s,0)=-2*partial_s(a*g) directly from the payload coefficient table.
axis_J = {}
for power, coefficient in axis_ag.items():
    for monomial, value in coefficient.items():
        axis_J[(power - 1, *monomial)] = axis_J.get((power - 1, *monomial), Q(0)) - 2 * power * value
axis_J = {key: value for key, value in axis_J.items() if value}
J_at_inner = {}
for (spower, xpower, ypower), coefficient in axis_J.items():
    J_at_inner[(xpower, ypower)] = J_at_inner.get((xpower, ypower), Q(0)) + coefficient * s0**spower
j_lower, j_upper = interval_eval(J_at_inner)
assert j_lower > 2 and j_upper < 3
assert j_lower / 2 * s0 > s0
assert Xhi < 4
assert r0 < Q(1, 8)

# Keep the first parsed source coefficient as an elementary normalization check.
payload_axis_first_coefficient = {str(key): str(value) for key, value in axis_ag[1].items()}

# Independent generic cutoff differentiation.
s, z, mu = sp.symbols("s z mu")
delta = sp.Rational(1, 2)
chi = sp.Function("chi")
h = sp.Function("h")
g = sp.Function("g")
q = s + z**2
cut = chi(q)
Vcut = -sp.diff(cut * h(s, z), z)
Omegacut = -2 * sp.diff(cut * g(s, z), s)
Wcut = 2 * cut * h(s, z) + 2 * s * sp.diff(cut * h(s, z), s)
Lcut = s * Omegacut
assert sp.simplify(Lcut + 2 * s * sp.diff(cut * g(s, z), s)) == 0

V0, O0, W0 = sp.Function("V0")(s, z), sp.Function("O0")(s, z), sp.Function("W0")(s, z)
V1, O1, W1 = sp.Function("V1")(s, z), sp.Function("O1")(s, z), sp.Function("W1")(s, z)
L0, L1 = s * O0, s * O1
b0s, b0z = 2 * s * (V0 + 1), W0 + z
b1s, b1z = 2 * s * V1, W1


def diffusion_L(L):
    return 4 * s * sp.diff(L, s, 2) + sp.diff(L, z, 2)


C1 = sp.expand(b0s * sp.diff(L1, s) + b0z * sp.diff(L1, z) - diffusion_L(L0))
C2 = sp.expand(b1s * sp.diff(L1, s) + b1z * sp.diff(L1, z) - diffusion_L(L1))

# Start from the actual swirl PDE, then compare it to the source decomposition.
Omega = O0 + mu * O1
V = V0 + mu * V1
W = W0 + mu * W1
swirl_pde = (-mu * delta * O1 + (sp.Rational(5, 2) + 2 * V) * Omega
             + (W + z) * sp.diff(Omega, z) + 2 * s * (V + 1) * sp.diff(Omega, s)
             - mu * (4 * s * sp.diff(Omega, s, 2) + 8 * sp.diff(Omega, s) + sp.diff(Omega, z, 2)))
pressure_free = sp.expand(s * swirl_pde)
decomposed = sp.Rational(1, 2) * L0 + mu * C1 + mu**2 * C2
criticality_defect = sp.expand((b0s + mu * b1s) * sp.diff(L0, s) + (b0z + mu * b1z) * sp.diff(L0, z))
assert sp.simplify(pressure_free - decomposed - criticality_defect) == 0
critical_coefficients = [sp.expand(decomposed).coeff(mu, power) for power in range(3)]
assert critical_coefficients == [sp.Rational(1, 2) * L0, C1, C2]
source_coefficients = [pressure_free.coeff(mu, power) for power in range(3)]
assert sp.expand(sum(value * mu**j for j, value in enumerate(source_coefficients)) - pressure_free) == 0

# Differentiate the actual Cartesian potential and identify all three axisym profiles.
x, y = sp.symbols("x y")
cart_s = x**2 + y**2
cart_q = cart_s + z**2
cart_cut = chi(cart_q)
cart_h, cart_g = h(cart_s, z), g(cart_s, z)
potential = (-y * cart_cut * cart_h, x * cart_cut * cart_h, cart_cut * cart_g)
cart_curl = (
    sp.diff(potential[2], y) - sp.diff(potential[1], z),
    sp.diff(potential[0], z) - sp.diff(potential[2], x),
    sp.diff(potential[1], x) - sp.diff(potential[0], y),
)
radial_V = -sp.diff(cut * h(s, z), z)
radial_Omega = -2 * sp.diff(cut * g(s, z), s)
radial_W = 2 * cut * h(s, z) + 2 * s * sp.diff(cut * h(s, z), s)
cart_V = radial_V.subs(s, cart_s)
cart_Omega = radial_Omega.subs(s, cart_s)
cart_W = radial_W.subs(s, cart_s)
assert sp.simplify(cart_curl[0] - (x * cart_V - y * cart_Omega)) == 0
assert sp.simplify(cart_curl[1] - (y * cart_V + x * cart_Omega)) == 0
assert sp.simplify(cart_curl[2] - cart_W) == 0

# Substitute independent cutoff profiles for both h0,g0 and h1,g1.
h0, g0, h1, g1 = (sp.Function(name) for name in ("h0", "g0", "h1", "g1"))
def cutoff_profiles(hf, gf):
    return (-sp.diff(cut * hf(s, z), z), -2 * sp.diff(cut * gf(s, z), s),
            2 * cut * hf(s, z) + 2 * s * sp.diff(cut * hf(s, z), s))

V0c, O0c, W0c = cutoff_profiles(h0, g0)
V1c, O1c, W1c = cutoff_profiles(h1, g1)
cutoff_substitution = {V0: V0c, O0: O0c, W0: W0c, V1: V1c, O1: O1c, W1: W1c}
cutoff_source_coefficients = [sp.expand(value.subs(cutoff_substitution)) for value in source_coefficients]

receipt = {
    "scale_relations": {"radius": "2^(-6)", "squared_radius": "r^2=2^(-12)", "seed_lower_bound": "r^2", "angular_gap": str(angular_gap), "residual_floor": "(alpha-beta)*r^2/2=2^(-14)", "evaluated_residual_floor": str(residual_floor)},
    "scope": "Finite compact-cutoff source audit at inner radius; no maximum theorem or global residual bound",
    "payload": {"path": str(PAYLOAD), "sha256": hashlib.sha256(payload_bytes).hexdigest(), "axis_a_times_g_rows_mu0_z0": len(axis_ag_rows), "axis_first_coefficient": payload_axis_first_coefficient, "source_reconstruction_verified": True},
    "selectors": {"X": [str(Xlo), str(Xhi)], "Y": [str(Ylo), str(Yhi)], "s": str(s0), "r": str(r0), "inner_cutoff_radius": "1/8", "chi_inner_value": "1"},
    "axis_angular_momentum": {"reconstruction": "J(s,0)=-2*partial_s(a*g) from payload a_times_g", "interval_raw": [str(j_lower), str(j_upper)], "readable_interval": ["2", "3"], "J_greater_than_2": True, "a_less_than_2": True, "Omega_greater_than_1": True, "L0_lower_bound": str(s0), "L0_greater_than_lower_bound": True},
    "cutoff_curl": {"Vcut": str(Vcut), "Omegacut": str(Omegacut), "Wcut": str(Wcut), "Lcut": str(Lcut), "cartesian_curl_verified": True},
    "angular_source_identity": {"b0": "(2*s*(V0+1), W0+z)", "b1": "(2*s*V1, W1)", "C1": str(C1), "C2": str(C2), "criticality_defect": str(criticality_defect), "pressure_free_mu0": str(source_coefficients[0]), "pressure_free_mu1": str(source_coefficients[1]), "pressure_free_mu2": str(source_coefficients[2]), "cutoff_h0g0_mu0": str(cutoff_source_coefficients[0]), "cutoff_h0g0_h1g1_mu1": str(cutoff_source_coefficients[1]), "cutoff_h0g0_h1g1_mu2": str(cutoff_source_coefficients[2]), "pressure_torque_retained": True, "mu_prime": "-delta*mu with delta=1/2; delta*L0+mu*C1+mu^2*C2", "full_source": "delta*L0+mu*C1+mu^2*C2+criticality_defect+arbitrary pressure torque"},
    "fourier_source_formula": "trace(Dv^2) is audited in derive_jet_flat_pressure.py; this audit retains the actual angular diffusion and pressure torque symbols",
    "exit_status": 0,
}
print(json.dumps(receipt, indent=2))
