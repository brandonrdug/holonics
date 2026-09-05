"""Exact Taylor--Green pressure and transported horizontal-mean audit."""

import json

import sympy as sp


x, y, z, zeta = sp.symbols("x y z zeta", real=True)
a, adot, nu = sp.symbols("a adot nu", real=True)
r, zScale, K = sp.symbols("r zScale K", positive=True)
c0, c1, c2 = sp.symbols("c0 c1 c2", real=True)
k = 2 * sp.pi

u = (
    a * sp.sin(k * x) * sp.cos(k * z),
    sp.Integer(0),
    -a * sp.cos(k * x) * sp.sin(k * z),
)
p = a**2 / 4 * (sp.cos(2 * k * x) + sp.cos(2 * k * z))
adot_law = -2 * nu * k**2 * a
t = sp.symbols("t", real=True)
amplitude = sp.exp(-2 * nu * k**2 * t)
assert sp.simplify(sp.diff(amplitude, t) - adot_law.subs(a, amplitude)) == 0

variables = (x, y, z)
time_u = tuple(adot * sp.diff(component, a) for component in u)
advection = tuple(sum(u[j] * sp.diff(u[i], variables[j]) for j in range(3)) for i in range(3))
diffusion = tuple(sum(sp.diff(u[i], variable, 2) for variable in variables) for i in range(3))
pressure_gradient = tuple(sp.diff(p, variable) for variable in variables)
residual = tuple(sp.expand(time_u[i] + advection[i] - nu * diffusion[i] + pressure_gradient[i]).subs(adot, adot_law) for i in range(3))
residual_simplified = [sp.simplify(sp.trigsimp(sp.expand_trig(value))) for value in residual]
divergence = sp.expand(sum(sp.diff(u[i], variables[i]) for i in range(3)))
assert all(value == 0 for value in residual_simplified)
assert divergence == 0

physical_p_mean = sp.integrate(p, (x, 0, 1), (y, 0, 1))
physical_u3_sq_mean = sp.integrate(u[2]**2, (x, 0, 1), (y, 0, 1))
assert sp.trigsimp(physical_p_mean - a**2 / 4 * sp.cos(2 * k * z)) == 0
assert sp.trigsimp(physical_u3_sq_mean - a**2 / 2 * sp.sin(k * z)**2) == 0
mean_sum = sp.trigsimp(physical_p_mean + physical_u3_sq_mean)
assert mean_sum == a**2 / 4
assert sp.trigsimp(sp.diff(physical_p_mean, z) + sp.diff(physical_u3_sq_mean, z)) == 0

# The transported chart uses the full physical horizontal unit cell, whose
# chart coordinates have length 1/r in both horizontal directions.
chart_x = c0 + r * x
chart_z = c2 + zScale * zeta
clock_rate = r**2 / K
W = clock_rate / zScale * u[2].subs({x: chart_x, z: chart_z})
Pi = (r / K)**2 * p.subs({x: chart_x, z: chart_z})
cell_x = (-c0 / r, (1 - c0) / r)
cell_y = (-c1 / r, (1 - c1) / r)
physical_cell_mean = lambda expression: r**2 * sp.integrate(
    expression, (x, cell_x[0], cell_x[1]), (y, cell_y[0], cell_y[1]))
Pi_mean = sp.trigsimp(physical_cell_mean(Pi))
W_sq_mean = sp.trigsimp(physical_cell_mean(W**2))
W_mean = sp.trigsimp(physical_cell_mean(W))
Pi_mean_expected = a**2 * r**2 / (4 * K**2) * sp.cos(2 * k * (c2 + zScale * zeta))
W_sq_mean_expected = a**2 * r**4 / (4 * K**2 * zScale**2) * (1 - sp.cos(2 * k * (c2 + zScale * zeta)))
assert sp.trigsimp(Pi_mean - Pi_mean_expected) == 0
assert sp.trigsimp(W_sq_mean - W_sq_mean_expected) == 0
epsilon = (r / zScale)**2
transported_balance = sp.trigsimp(epsilon * sp.diff(Pi_mean, zeta) + sp.diff(W_sq_mean, zeta))
without_epsilon = sp.trigsimp(sp.diff(Pi_mean, zeta) + sp.diff(W_sq_mean, zeta), method="fu")
mean_before_square = sp.trigsimp(epsilon * sp.diff(Pi_mean, zeta) + sp.diff(W_mean**2, zeta), method="fu")
source_coefficient = sp.trigsimp(sp.diff(Pi_mean, zeta), method="fu")
assert transported_balance == 0
assert without_epsilon != 0
assert mean_before_square != 0
assert source_coefficient != 0

# Exact positive-parameter witnesses distinguish a genuinely nonzero control
# from an expression that the symbolic simplifier merely failed to reduce.
control_point = {a: 1, r: 1, zScale: 2, K: 1, c2: 0, zeta: sp.Rational(1, 16)}
control_without_epsilon = sp.simplify(without_epsilon.subs(control_point))
control_mean_before_square = sp.simplify(mean_before_square.subs(control_point))
assert control_without_epsilon == -3 * sp.pi / 2
assert control_mean_before_square == -sp.pi / 2

receipt = {
    "scope": "Exact smooth Taylor--Green source and transported horizontal physical-cell mean; no blowup or normalized-family claim",
    "arithmetic": "SymPy exact symbolic trigonometric identities; no floating values",
    "sympy_version": sp.__version__,
    "field": "u=a*(sin(2*pi*x)*cos(2*pi*z),0,-cos(2*pi*x)*sin(2*pi*z))",
    "pressure": "p=a^2/4*(cos(4*pi*x)+cos(4*pi*z))",
    "physical_harmonics": {"velocity": [[1, 0, 1], [1, 0, -1], [-1, 0, 1], [-1, 0, -1]], "pressure": [[2, 0, 0], [-2, 0, 0], [0, 0, 2], [0, 0, -2]]},
    "amplitude_law": "a_dot=-8*pi^2*nu*a",
    "actual_amplitude": str(amplitude),
    "physical_checks": {
        "divergence": str(divergence),
        "momentum_residual": [str(value) for value in residual_simplified],
        "horizontal_pressure_mean": str(physical_p_mean),
        "horizontal_u3_square_mean": str(physical_u3_sq_mean),
        "mean_sum": str(mean_sum),
        "mean_sum_z_derivative": str(sp.diff(mean_sum, z)),
    },
    "anisotropic_chart": {
        "map": "(x,z)=(c0+r*y0,c2+zScale*zeta)",
        "clock_rate": str(clock_rate),
        "W": "(r^2/(K*zScale))*u3(chart)",
        "Pi": "(r/K)^2*p(chart)",
        "epsilon": str(epsilon),
        "inverse_frame_periods": {"horizontal_chart_period": "1/r", "vertical_chart_period": "1/zScale"},
        "transported_cell_mean": "r^2*integral_[-c0/r,(1-c0)/r] integral_[-c1/r,(1-c1)/r]",
        "Pi_mean": str(Pi_mean_expected),
        "W_square_mean": str(W_sq_mean_expected),
        "W_mean": str(W_mean),
        "balance": str(transported_balance),
        "without_epsilon": str(without_epsilon),
        "mean_before_square": str(mean_before_square),
        "nonzero_source_coefficient": str(source_coefficient),
    },
    "exact_control_point": {
        "parameters": {str(key): str(value) for key, value in control_point.items()},
        "without_epsilon": str(control_without_epsilon),
        "mean_before_square": str(control_mean_before_square),
    },
    "exit_status": 0,
}
print(json.dumps(receipt, indent=2))
