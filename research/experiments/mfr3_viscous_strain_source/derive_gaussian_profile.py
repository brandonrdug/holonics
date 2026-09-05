"""Exact off-axis Cartesian audit of the Gaussian radial-clock comparison.

The Lean divided-difference owner supplies the smooth angular extension at the
axis. This script checks the actual Cartesian differential expressions away
from the axis, with the pressure written as a radial primitive. The comparison
has a prescribed linear strain and is not a periodic finite-energy solution.
"""
import json
import sympy as sp

x, y, z, v = sp.symbols('x y z v', real=True)
mu, q, epsilon = sp.symbols('mu q epsilon', positive=True)
beta, gamma, Gamma = sp.symbols('beta gamma Gamma', real=True)
a = 2 * beta + 4 * mu * q
s = x*x + y*y
omega = Gamma * (1 - sp.exp(-q*s)) / s
omega_v = Gamma * (1 - sp.exp(-q*v)) / v
U = sp.Matrix([-a*x/2 - omega*y, -a*y/2 + omega*x, a*z])
coordinates = (x, y, z)
pressure = (a*beta/2 - a*a/8)*s + sp.Integral(omega_v**2/2, (v, 0, s)) - a*(a+2*beta)*z*z/(2*epsilon)
gradient = sp.Matrix([sp.diff(pressure, coordinate) for coordinate in coordinates])
drift = U + sp.Matrix([beta*x, beta*y, gamma*z])
reaction = sp.diag(beta, beta, 2*beta-gamma)*U
diffusion = mu * sp.Matrix([sp.diff(f, x, 2) + sp.diff(f, y, 2) + epsilon*sp.diff(f, z, 2) for f in U])
residual = U.jacobian(coordinates)*drift + reaction - diffusion + sp.diag(1, 1, epsilon)*gradient
residual = [sp.factor(sp.simplify(f)) for f in residual]
assert residual == [0, 0, 0]
assert sp.simplify(sum(sp.diff(U[i], coordinates[i]) for i in range(3))) == 0
assert sp.simplify(x*U[1]-y*U[0] - Gamma*(1-sp.exp(-q*s))) == 0
omega_axis_series = sp.series(omega_v, v, 0, 3).removeO()
assert sp.expand(omega_axis_series - (Gamma*q - Gamma*q**2*v/2 + Gamma*q**3*v**2/6)) == 0
potential_axis_series = sp.integrate(-omega_axis_series/2, (v, 0, v)).subs({Gamma: 3, q: sp.Rational(1, 3)})
assert sp.expand(potential_axis_series - (-v/2 + v**2/24 - v**3/324)) == 0
print(json.dumps({
    'scope': 'Exact off-axis Cartesian Gaussian comparison with prescribed linear strain; no periodic exterior or stability claim',
    'sympy_version': sp.__version__,
    'parameters': {'strain': str(a), 'radial_viscosity': str(mu), 'aspect': str(epsilon)},
    'velocity': [str(f) for f in U],
    'pressure': str(pressure),
    'drift': [str(f) for f in drift],
    'reaction': [str(f) for f in reaction],
    'cartesian_residual': [str(f) for f in residual],
    'axial_pressure_curvature': str(sp.diff(pressure, z, 2)),
    'circulation': str(Gamma*(1-sp.exp(-q*s))),
    'angular_axis_series': str(omega_axis_series),
    'potential_axis_series_Gamma3_q1over3': str(potential_axis_series),
    'axis_scope': 'Smooth extension supplied separately by gaussianAngularVelocity_analyticAt in Lean',
    'exit_status': 0,
}, indent=2))
