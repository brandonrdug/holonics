"""Exact full-support Lamb-current audit for the exterior source spectrum."""

import contextlib
import io
import json
import runpy
from pathlib import Path

from flint import fmpq as Q


BASE = Path(__file__).parent
with contextlib.redirect_stdout(io.StringIO()):
    ext = runpy.run_path(str(BASE.parent / "mfr3_exterior_modulation" / "derive_receivers.py"), run_name="mfr_lamb_exterior")

ZERO, ZV = ext["ZERO"], ext["ZV"]
dot, norm2, trim = ext["dot"], ext["norm2"], ext["trim"]
ctx = ext["ctx"]
A, V, P0 = ext["A"], ext["V"], ext["P0"]
rho, sigma = ext["rho"], ext["sigma"]


def vadd(a, b):
    return tuple(a[i] + b[i] for i in range(3))


def vscale(a, c):
    return tuple(c * a[i] for i in range(3))


def cross(a, b):
    return (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0])


def field_add(left, right):
    result = dict(left)
    for mode, value in right.items():
        result[mode] = vadd(result.get(mode, ZV), value)
    return trim(result)


def field_cross(left, right):
    result = {}
    for p, a_p in left.items():
        for q, b_q in right.items():
            mode = tuple(p[i] + q[i] for i in range(3))
            result[mode] = vadd(result.get(mode, ZV), cross(a_p, b_q))
    return trim(result)


def omega(field):
    return trim({mode: (-mode[1] * value[2] + mode[2] * value[1],
                         -mode[2] * value[0] + mode[0] * value[2],
                         -mode[0] * value[1] + mode[1] * value[0])
                 for mode, value in field.items()})


def lamb(left, right_omega):
    return field_cross(left, right_omega)


Omega = omega(A)
OmegaV = omega(V)
C = lamb(A, Omega)
Ct = field_add(lamb(V, Omega), lamb(A, OmegaV))

# (u · grad) C, in imaginary-amplitude convention u=iA and C=iC_amp.
advC = {}
for p, a_p in A.items():
    for q, c_q in C.items():
        mode = tuple(p[i] + q[i] for i in range(3))
        advC[mode] = vadd(advC.get(mode, ZV), vscale(c_q, -dot(mode, a_p)))
advC = trim(advC)
lapC_term = {mode: vscale(value, norm2(mode)) for mode, value in C.items()}
lhs = field_add(field_add(Ct, advC), lapC_term)

# Independently formed RHS stretching, pressure, and derivative-cross terms.
# First construct (omega.grad)u, then cross it with u; this retains all three
# Fourier inputs of the actual stretching term.
omega_grad_u = {}
for p, omega_p in Omega.items():
    for q, a_q in A.items():
        mode = tuple(p[i] + q[i] for i in range(3))
        omega_grad_u[mode] = vadd(omega_grad_u.get(mode, ZV), vscale(a_q, -dot(q, omega_p)))
omega_grad_u = trim(omega_grad_u)
stretch = field_cross(A, omega_grad_u)
pressure_cross = {}
for p, p_value in P0.items():
    for q, omega_q in Omega.items():
        mode = tuple(p[i] + q[i] for i in range(3))
        pressure_cross[mode] = vadd(pressure_cross.get(mode, ZV), vscale(cross((p[0] * p_value, p[1] * p_value, p[2] * p_value), omega_q), -1))
derivative_cross = {}
for p, a_p in A.items():
    for q, omega_q in Omega.items():
        mode = tuple(p[i] + q[i] for i in range(3))
        derivative_cross[mode] = vadd(derivative_cross.get(mode, ZV), vscale(cross(a_p, omega_q), 2 * sum(p[i] * q[i] for i in range(3))))
pressure_cross = trim(pressure_cross)
derivative_cross = trim(derivative_cross)
rhs = field_add(field_add(stretch, pressure_cross), derivative_cross)
assert lhs == rhs

# Full momentum identity u_t = Delta u + C - grad(p+|u|²/2).
kinetic = {}
for p, a_p in A.items():
    for q, a_q in A.items():
        mode = tuple(p[i] + q[i] for i in range(3))
        kinetic[mode] = kinetic.get(mode, ZERO) - sum(a_p[i] * a_q[i] for i in range(3)) / 2
total_pressure = dict(kinetic)
for mode, value in P0.items():
    total_pressure[mode] = total_pressure.get(mode, ZERO) + value
momentum_rhs = {}
for mode in set(A) | set(C) | set(total_pressure):
    momentum_rhs[mode] = tuple(-norm2(mode) * A.get(mode, ZV)[i] + C.get(mode, ZV)[i] - mode[i] * total_pressure.get(mode, ZERO) for i in range(3))
momentum_rhs = trim(momentum_rhs)
assert momentum_rhs == V

low = {mode: value for mode, value in A.items() if all(abs(k) <= 1 for k in mode)}
high = {mode: value for mode, value in A.items() if mode not in low}
C_decomp = field_add(field_add(lamb(low, omega(low)), lamb(low, omega(high))),
                     field_add(lamb(high, omega(low)), lamb(high, omega(high))))
assert C_decomp == C
assert high

def field_phase(field):
    result = [ZERO, ZERO, ZERO]
    for mode, value in field.items():
        phase = (0, -1, 0, 1)[mode[0] % 4]
        for i in range(3):
            result[i] = result[i] + phase * value[i]
    return [str(value) for value in result]


low_self = lamb(low, omega(low))
generated_raw = {mode: value for mode, value in low_self.items() if any(abs(k) > 1 for k in mode)}
assert all(all(abs(k) <= 2 for k in mode) for mode in low_self)
generated_projected = {}
for mode, value in generated_raw.items():
    norm = norm2(mode)
    assert norm > 0
    dot_value = sum(mode[i] * value[i] for i in range(3))
    projected = tuple(value[i] - mode[i] * dot_value / norm for i in range(3))
    if any(projected):
        generated_projected[mode] = projected
assert generated_projected
assert all(not dot(mode, value) for mode, value in generated_projected.items())
generated_mode, generated_value = next(iter(sorted(generated_projected.items())))
# Reality and the nonzero divergence of C are actual source checks, not a claim
# that a cross-current inherits the velocity's divergence constraint.
for field in (A,V,C,Ct,advC,lapC_term,stretch,pressure_cross,derivative_cross):
    assert ext["real_odd"](field)
assert all(Omega.get(tuple(-i for i in mode), ZV) == value for mode,value in Omega.items())
assert all(not dot(mode,value) for mode,value in Omega.items())
divC = {mode: -dot(mode,value) for mode,value in C.items() if dot(mode,value)}
assert divC
curlOmegaAmplitude = {mode: cross(mode,value) for mode,value in Omega.items()}
div_source = {}
for p,omega_p in Omega.items():
    for q,omega_q in Omega.items():
        mode=tuple(p[i]+q[i] for i in range(3))
        div_source[mode]=div_source.get(mode,ZERO)+sum(omega_p[i]*omega_q[i] for i in range(3))
for p,a_p in A.items():
    for q,curl_q in curlOmegaAmplitude.items():
        mode=tuple(p[i]+q[i] for i in range(3))
        div_source[mode]=div_source.get(mode,ZERO)+sum(a_p[i]*curl_q[i] for i in range(3))
assert divC == {mode:value for mode,value in div_source.items() if value}
assert generated_mode == (-2,-2,-1)
rvar,svar=ctx.gens()
factor=Q(35,768)*(2+5*(rvar+svar))
assert generated_value == (-factor,factor,ZERO)

phase = {"point": "(pi/2,0,0)", "C": field_phase(C), "Ct": field_phase(Ct), "advection": field_phase(advC), "minus_laplacian": field_phase(lapC_term), "stretching": field_phase(stretch), "minus_pressure_cross": field_phase(pressure_cross), "derivative_cross": field_phase(derivative_cross)}

receipt = {
    "scope": "Exact full-support nonlinear Lamb-current source audit for the two-parameter exterior family; no stability conclusion",
    "arithmetic": "FLINT fmpq_mpoly source carriers reused from verified exterior owner",
    "coefficient_convention": "A,V,C and current-source vectors are imaginary amplitudes; actual Fourier coefficients are i times these amplitudes; Omega is real",
    "supports": {"A": len(A), "V": len(V), "Omega": len(Omega), "C": len(C), "high_complement": len(high)},
    "checks": {"lamb_current_identity_full_modes": True, "momentum_identity_full_modes": True, "resolved_complement_decomposition": True, "nonzero_generated_raw_complement": True, "nonzero_generated_velocity_current_after_leray": True, "actual_phase_evaluation": True, "all_oriented_terms_reality": True, "actual_nonzero_Lamb_divergence_source": True, "generated_complement_uses_full_declared_cube": True, "generated_projected_modes_divergence_free": True},
    "lamb_identity": {"lhs": "C_t+(u.grad)C-Delta C", "rhs": "u cross ((omega.grad)u)-grad(p) cross omega-2 sum_a(partial_a u) cross(partial_a omega)", "term_supports": {"Ct": len(Ct), "advection": len(advC), "stretching": len(stretch), "pressure": len(pressure_cross), "derivative_cross": len(derivative_cross)}},
    "momentum": {"identity": "u_t=Delta u+C-grad(p+|u|^2/2)", "kinetic_pressure_included": True},
    "resolved_cutoff": {"condition": "|k_i|<=1", "low_modes": len(low), "high_modes": len(high), "all_four_products_retained": True, "full_Lamb_tail_separate": True, "selected_mode_zero_fibre": "rho+sigma=-2/5", "selected_mode_nonzero_on_rho_positive_sigma_zero": True, "generated_raw_mode": list(generated_mode), "generated_velocity_current_after_Leray_mode": list(generated_mode), "generated_velocity_current_after_Leray_coefficient": [str(value) for value in generated_value]},
    "phase_receiver": phase,
    "input_lineage": {"source_producer": "mfr3_exterior_modulation/derive_receivers.py", "existing_full_source_and_parent_specialization_assertions_executed": True},
    "phase_to_physical": {"k": "2*pi", "u_phys": "k*u(kX,k^2*t)", "p_phys": "k^2*p", "nu": "unchanged"},
    "exit_status": 0,
}
print(json.dumps(receipt, indent=2))
