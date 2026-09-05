"""Independent symbolic expansion of the actual normalized meridional NS source.

The viscosity clock satisfies mu'=-delta*mu. The source is expanded before any
radial coefficient extraction, with independent smooth symbolic profile fields.
This checks the first-response formulas and retains the complete quadratic source.
"""

import json
import sympy as s

r, z, mu, alpha, beta, delta = s.symbols('s z mu alpha beta delta', real=True)
V, O, W, v, f, w = [s.Function(name)(r, z) for name in ('V', 'Omega', 'W', 'v', 'f', 'w')]

def A(V, O, W):
    return (alpha+beta)*V+(W+beta*z)*s.diff(V,z)+2*r*(V+beta)*s.diff(V,r)+V**2-O**2

def B(V, O, W):
    return alpha*W+(W+beta*z)*s.diff(W,z)+2*r*(V+beta)*s.diff(W,r)

def C(V, O, W):
    return (alpha+beta+2*V)*O+(W+beta*z)*s.diff(O,z)+2*r*(V+beta)*s.diff(O,r)

def D(field, radial_coefficient):
    return 4*r*s.diff(field,r,2)+radial_coefficient*s.diff(field,r)+s.diff(field,z,2)

full = [
    -delta*mu*v+A(V+mu*v,O+mu*f,W+mu*w)-mu*D(V+mu*v,8),
    -delta*mu*w+B(V+mu*v,O+mu*f,W+mu*w)-mu*D(W+mu*w,4),
    -delta*mu*f+C(V+mu*v,O+mu*f,W+mu*w)-mu*D(O+mu*f,8),
]
first = [
    (alpha+beta+2*V)*v+(W+beta*z)*s.diff(v,z)+w*s.diff(V,z)
    +2*r*((V+beta)*s.diff(v,r)+v*s.diff(V,r))-2*O*f-delta*v-D(V,8),
    alpha*w+(W+beta*z)*s.diff(w,z)+w*s.diff(W,z)
    +2*r*((V+beta)*s.diff(w,r)+v*s.diff(W,r))-delta*w-D(W,4),
    (alpha+beta+2*V)*f+2*v*O+(W+beta*z)*s.diff(f,z)+w*s.diff(O,z)
    +2*r*((V+beta)*s.diff(f,r)+v*s.diff(O,r))-delta*f-D(O,8),
]
second = [
    w*s.diff(v,z)+2*r*v*s.diff(v,r)+v**2-f**2-D(v,8),
    w*s.diff(w,z)+2*r*v*s.diff(w,r)-D(w,4),
    2*v*f+w*s.diff(f,z)+2*r*v*s.diff(f,r)-D(f,8),
]
for raw, base, linear, quadratic in zip(full, [A(V,O,W),B(V,O,W),C(V,O,W)], first, second):
    assert s.expand(raw-base-mu*linear-mu**2*quadratic) == 0

m, n, j = s.symbols('m n j', integer=True, nonnegative=True)
axial_indicial = n*(alpha+2*beta)+(2-m)*alpha+(m+1)*beta-j*(alpha-beta)
swirl_indicial = n*(alpha+2*beta)-m*(alpha-beta)-j*(alpha-beta)
critical = {alpha:s.Rational(3,2),beta:s.Integer(1)}
assert s.expand(axial_indicial.subs(critical)-(7*n+8-m-j)/2)==0
assert s.expand(swirl_indicial.subs(critical)-(7*n-m-j)/2)==0

print(json.dumps({
    'scope':'Exact symbolic coefficient identity in viscosity order0..2; no convergence or solution claim',
    'sympy_version':s.__version__,
    'clock':'mu_prime=-delta*mu',
    'first_order':{key:s.sstr(value) for key,value in zip(('A1','B1','C1'),first)},
    'second_order':{key:s.sstr(value) for key,value in zip(('A2','B2','C2'),second)},
    'indicial':{'axial':'(7*n+8-m-j)/2','angular':'(7*n-m-j)/2','scope':'critical rates, viscosity order j'},
    'pressure':'A_j,z=2*B_j,s for each retained viscosity coefficient',
    'exit_status':0,
},indent=2))
