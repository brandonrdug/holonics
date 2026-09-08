"""Exact research controls for complex projection and folded dynamical memory.

Python + SymPy; no native learner, sampling, or PDE blowup claim.
"""
import json

import sympy as sp

x, y, z, t, s = sp.symbols("x y z t s", real=True)
xyz = (x, y, z)
A, B = 2*x+y, -x-y
vertical = sp.Matrix([0, 0, 1])
horizontal = sp.Matrix([1, -1, 0])
v = horizontal*sp.cos(B) + vertical*sp.cos(A)
U = sp.I*v

assert sum(sp.diff(v[i], xyz[i]) for i in range(3)) == 0
assert U.applyfunc(sp.re) == sp.zeros(3, 1)
complex_source = -(U.jacobian(xyz)*U)
hidden_feedback = v.jacobian(xyz)*v
assert (complex_source-hidden_feedback).applyfunc(sp.simplify) == sp.zeros(3, 1)
expected = -vertical*sp.sin(A)*sp.cos(B)
assert (hidden_feedback-expected).applyfunc(sp.trigsimp) == sp.zeros(3, 1)
assert hidden_feedback != sp.zeros(3, 1)
# This z-directed, z-independent field is already solenoidal; Leray leaves it fixed.
assert sum(sp.diff(hidden_feedback[i], xyz[i]) for i in range(3)) == 0

# Full rotation versus the exact memory equation after folding the second coordinate.
r, hidden = sp.cos(t), -sp.sin(t)
assert sp.diff(r,t) == hidden and sp.diff(hidden,t) == -r
assert sp.simplify(sp.diff(r,t) + sp.integrate(sp.cos(s),(s,0,t))) == 0

# A normalized complex face can be singular while its ratio family is regular.
w1, w2 = sp.exp(0), sp.exp(sp.I*sp.pi)
assert w1+w2 == 0 and w1/w2 == -1

print(json.dumps({
    "scope": "exact initial complex NS/Euler source and linear folded-memory control",
    "chart": "dimensionless fixed 2*pi periodic spatial chart; complex velocity, real coordinates",
    "complex_velocity": "i*((1,-1,0)*cos(-x-y)+(0,0,1)*cos(2*x+y))",
    "real_projection": ["0", "0", "0"],
    "real_projected_nonlinear_source": [str(e) for e in expected],
    "source_is_solenoidal": True,
    "zero_real_field_source": ["0", "0", "0"],
    "folded_linear_system": "r'=h, h'=-r; r(0)=1, h(0)=0",
    "exact_memory_equation": "r'(t)=-integral_0^t r(s) ds",
    "solution": "r(t)=cos(t), h(t)=-sin(t)",
    "complex_normalization": {"weights": ["1", "-1"], "partition": "0", "ratio": "-1"},
    "claims_excluded": ["blowup", "defect in Clay statement", "HNN learning"],
}, indent=2))
