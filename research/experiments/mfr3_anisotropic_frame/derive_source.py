"""Independent exact jet audit of the moving linear fluid chart.

Differentiate an arbitrary physical quadratic spatial jet and linear time jet
through a moving anisotropic, sheared map. The source is not assumed to solve
Navier--Stokes: the complete residual must transform by b^2 B. This exercises
the pressure metric, mixed diffusion, inverse derivative and centre current.
"""

import json
import sympy as S

r, z, b = S.symbols("r z b", positive=True)
shear, rdot, zdot, sdot, bdot, nu = S.symbols("shear rdot zdot sdot bdot nu", real=True)
tau = S.symbols("tau", real=True)
x = S.Matrix(S.symbols("x:3", real=True))
y = S.Matrix(S.symbols("y:3", real=True))
anchor = S.Matrix(S.symbols("Y:3", real=True))
cjet = S.Matrix(S.symbols("cdot:3", real=True))
v = S.Matrix(S.symbols("v:3", real=True))
time_jet = S.Matrix(S.symbols("vt:3", real=True))
pressure_jet = S.Matrix(S.symbols("p:3", real=True))
force = S.Matrix(S.symbols("f:3", real=True))
physical_time = S.symbols("physical_time", real=True)

A = S.Matrix([[r, shear, 0], [0, r, 0], [0, 0, z]])
Adot = S.Matrix([[rdot, sdot, 0], [0, rdot, 0], [0, 0, zdot]])
B = A.inv()
C = B * B.T
G = A.T * A
J = S.Matrix(3, 3, lambda i, j: S.Symbol(f"J{i}{j}", real=True))
H = []
for i in range(3):
    entries = {(j, k): S.Symbol(f"H{i}{j}{k}", real=True)
               for j in range(3) for k in range(j, 3)}
    H.append(S.Matrix(3, 3, lambda j, k: entries[min(j, k), max(j, k)]))

# The anchor is fixed while the independent y variables are differentiated.
dx = x - A * anchor
u = S.Matrix([v[i] + (J * dx)[i] + (dx.T * H[i] * dx)[0] / 2
              + time_jet[i] * physical_time for i in range(3)])
p = (pressure_jet.T * dx)[0]
At = A + tau * Adot
Bt = At.inv()
bt = b + tau * bdot
clock = b * tau + bdot * tau**2 / 2
position = At * y + tau * cjet
pull = {x[i]: position[i] for i in range(3)} | {physical_time: clock}
U = bt * Bt * u.subs(pull, simultaneous=True)
P = bt**2 * p.subs(pull, simultaneous=True)
at = {tau: 0} | {y[i]: anchor[i] for i in range(3)}


def zero_matrix(M):
    return all(S.cancel(entry) == 0 for entry in M)


U0 = U.subs(at, simultaneous=True)
DU = U.jacobian(y).subs(at, simultaneous=True)
Utime = U.diff(tau).subs(at, simultaneous=True)
gradP = S.Matrix([S.diff(P, variable) for variable in y]).subs(at, simultaneous=True)
lapU = S.Matrix([sum(C[j, k] * S.diff(U[i], y[j], y[k])
                    for j in range(3) for k in range(3)) for i in range(3)])
lapU = lapU.subs(at, simultaneous=True)
physical_lap = S.Matrix([S.trace(hessian) for hessian in H])
D = B * Adot

assert zero_matrix(A * B - S.eye(3))
assert zero_matrix(Bt.diff(tau).subs(tau, 0) + B * Adot * B)
assert zero_matrix(U0 - b * B * v)
assert zero_matrix(DU - b * B * J * A)
assert S.cancel(S.trace(DU) - b * S.trace(J)) == 0
assert zero_matrix(gradP - b**2 * A.T * pressure_jet)
assert zero_matrix(C * gradP - b**2 * B * pressure_jet)
assert zero_matrix(lapU - b * B * physical_lap)

physical_residual = time_jet + J * v + pressure_jet - nu * physical_lap - force
chart_residual = (Utime + DU * (U0 - D * anchor - B * cjet)
                  + D * U0 - bdot / b * U0 + C * gradP
                  - nu * b * lapU - b**2 * B * force)
assert zero_matrix(chart_residual - b**2 * B * physical_residual)

# The mismatched operators fail as symbolic identities, without tuning a solution.
assert not zero_matrix(gradP - b**2 * B * pressure_jet)
ordinary_lap = S.Matrix([sum(S.diff(U[i], variable, 2) for variable in y) for i in range(3)])
ordinary_lap = ordinary_lap.subs(at, simultaneous=True)
assert not zero_matrix(ordinary_lap - lapU)

V = S.Matrix(S.symbols("V:3", real=True))
assert S.cancel(((A * V / b).T * (A * V / b))[0] - (V.T * G * V)[0] / b**2) == 0
assert S.factor(A.det()) == r**2 * z
angular_factor = r**2 / b
physical_position = A * anchor
physical_velocity = A * V / b
physical_angular = physical_position[0] * physical_velocity[1] - physical_position[1] * physical_velocity[0]
assert S.cancel(physical_angular - angular_factor * (anchor[0] * V[1] - anchor[1] * V[0])) == 0
radial_viscosity = nu * b / r**2
assert S.cancel(angular_factor * radial_viscosity - nu) == 0
factor_derivative = S.diff(angular_factor, r) * rdot + S.diff(angular_factor, b) * bdot
assert S.cancel(factor_derivative - (2 * rdot / r - bdot / b) * angular_factor) == 0

# Retaining radial viscosity selects a coupled clock and reduced pressure metric.
k = S.symbols("k", positive=True)
radial_clock = r**2 / k
aspect = (r / z)**2
Cdiag = C.subs(shear, 0)
reduced_metric = S.diag(1, 1, aspect)
assert zero_matrix(nu * radial_clock * Cdiag - (nu / k) * reduced_metric)
assert zero_matrix(Cdiag * (r**2 * V) - reduced_metric * V)
assert S.cancel(r**2 / radial_clock - k) == 0
matched_energy = (r**2 * z / radial_clock**2) * (V.T * G.subs(shear, 0) * V)[0]
assert S.cancel(matched_energy - k**2 * (z * (V[0]**2 + V[1]**2) + z**3 / r**2 * V[2]**2)) == 0

receipt = {
    "grade": "established-bounded", "evidence": ["computational-witness"],
    "scope": "Exact arbitrary second spatial/first time jet under a symbolic anisotropic sheared frame; no PDE solution or stability claim",
    "sympy_version": S.__version__,
    "frame": {"A": str(A), "B": str(B), "pressure_metric_C": str(C), "energy_metric_G": str(G)},
    "source": {
        "physical": "u_t+Du[u]+grad(p)-nu*Laplacian(u)-f",
        "chart": "U_tau+DU[U-D*y-B*c_dot]+(D-b_dot/b*I)U+C*grad(P)-nu*b*L_B(U)-b^2*B*f",
        "relations": "U=b*B*u; P=b^2*p; x=c+A*y; t'=b; D=B*A_dot; C=B*B^T",
        "complete_residual_identity": "R_chart=b^2*B*R_physical",
    },
    "checks": {"inverse_derivative": True, "spatial_derivative": True, "divergence": True,
               "pressure_metric": True, "weighted_second_derivative": True,
               "complete_source": True, "ordinary_pressure_gradient_control_fails": True,
               "ordinary_laplacian_control_fails": True, "kinetic_metric": True, "jacobian": True,
               "relative_angular_reconstruction": True, "angular_viscosity_reciprocity": True, "actual_angular_factor_derivative": True},
    "radial_clock_regime": {"clock_rate": "r^2/k", "fixed_angular_reconstruction": "k",
                            "aspect": "epsilon=(r/z)^2", "diffusion": "(nu/k)*(horizontalSecond+epsilon*axialSecond)",
                            "reduced_pressure_metric": "diag(1,1,epsilon)",
                            "energy_weights": "k^2*z and k^2*z^3/r^2", "operator_and_energy_checks": True},
    "diagonal_specialization": {"shear": "0", "jacobian": "r^2*z", "angular_reconstruction": "r^2/b",
                                "radial_viscosity": "nu*b/r^2", "axial_viscosity": "nu*b/z^2",
                                "physical_energy_density": "abs(det A)/b^2 * U^T*(A^T*A)*U"},
}
print(json.dumps(receipt, indent=2))
