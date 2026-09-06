"""Exact temporal realization of the existing oriented entropy/action cross-current.

The current sections are two complete unforced Navier--Stokes shear solutions.
The complex face retains their horizontal phase. No statistical closure is used.
"""
import json
import sympy as sp

x,y,z,t=sp.symbols('x y z t',real=True)
nu=sp.symbols('nu',nonnegative=True)
q=sp.symbols('q',positive=True)
coordinates=(x,y,z)
rate=nu*q*q
phase=q*z
J=sp.Matrix([sp.exp(-rate*t)*sp.cos(phase),sp.exp(-rate*t)*sp.sin(phase),0])
K=sp.Matrix([(1+sp.exp(-4*rate*t)*sp.cos(2*phase))/2,
             sp.exp(-4*rate*t)*sp.sin(2*phase)/2,0])

def clean(value):
    return sp.trigsimp(sp.expand_trig(sp.simplify(value)))

def lap(vector):
    return vector.applyfunc(lambda a:sum(sp.diff(a,c,2) for c in coordinates))

def cross(left,right):
    return left[0]*right[1]-left[1]*right[0]

def strings(vector):
    return [str(sp.simplify(v)) for v in vector]

for field in (J,K):
    assert clean(sum(sp.diff(field[i],coordinates[i]) for i in range(3)))==0
    advection=field.jacobian(coordinates)*field
    assert advection==sp.zeros(3,1)
    assert (sp.diff(field,t)+advection-nu*lap(field)).applyfunc(clean)==sp.zeros(3,1)
    assert (field.subs(z,z+2*sp.pi/q)-field).applyfunc(clean)==sp.zeros(3,1)
    assert sp.diff(field.subs(nu,0),t)==sp.zeros(3,1)
assert (K.subs(t,0)-sp.cos(phase)*J.subs(t,0)).applyfunc(clean)==sp.zeros(3,1)
C=clean(cross(J,K))
expected=sp.exp(-rate*t)*(sp.exp(-4*rate*t)-1)*sp.sin(phase)/2
assert clean(C-expected)==0
mixed=sum(cross(sp.diff(J,c),sp.diff(K,c)) for c in coordinates)
defect=clean(sp.diff(C,t)-nu*sum(sp.diff(C,c,2) for c in coordinates))
assert clean(defect+2*nu*mixed)==0
assert clean(defect+2*rate*sp.exp(-5*rate*t)*sp.sin(phase))==0
assert clean(C.subs(t,0))==0 and clean(C.subs(nu,0))==0
assert clean(sp.diff(C,t).subs(t,0)+2*rate*sp.sin(phase))==0

# Complex face and the same oriented receiver, retaining conjugation/hand.
j=J[0]+sp.I*J[1]
k=K[0]+sp.I*K[1]
assert clean(sp.im(sp.conjugate(j)*k)-C)==0
assert clean(j-sp.exp(-rate*t)*(sp.cos(phase)+sp.I*sp.sin(phase)))==0
assert clean(k-(1+sp.exp(-4*rate*t)*(sp.cos(2*phase)+sp.I*sp.sin(2*phase)))/2)==0

# The same complex second current has an entire continuation in its phase coordinate.
zeta=sp.symbols('zeta')
n=sp.symbols('n',integer=True)
H=(1+sp.exp(-4*rate*t)*sp.exp(2*sp.I*q*zeta))/2
assert sp.simplify(sp.diff(H,t)-nu*sp.diff(H,zeta,2))==0
zero_curve=sp.pi/(2*q)+sp.pi*n/q-2*sp.I*nu*q*t
assert sp.simplify(H.subs(zeta,zero_curve))==0
assert sp.simplify(sp.diff(H,zeta).subs(zeta,zero_curve))==-sp.I*q
logarithmic_field=sp.diff(H,zeta)/H
burgers_field=-2*nu*logarithmic_field
assert sp.simplify(sp.diff(burgers_field,t)+burgers_field*sp.diff(burgers_field,zeta)-nu*sp.diff(burgers_field,zeta,2))==0

# Full local kinetic-energy equation with pressure zero.
energies=[]
for field in (J,K):
    e=clean(field.dot(field)/2)
    dissipation=clean(nu*sum(sp.diff(field,c).dot(sp.diff(field,c)) for c in coordinates))
    local=sp.diff(e,t)+sum(sp.diff(e*field[i]-nu*sp.diff(e,coordinates[i]),coordinates[i]) for i in range(3))+dissipation
    assert clean(local)==0
    average_e=clean(sp.integrate(sp.expand_trig(e),(z,0,2*sp.pi/q))*q/(2*sp.pi))
    average_d=clean(sp.integrate(sp.expand_trig(dissipation),(z,0,2*sp.pi/q))*q/(2*sp.pi))
    assert clean(sp.diff(average_e,t)+average_d)==0
    energies.append({'average_kinetic_energy':str(average_e),'average_viscous_dissipation':str(average_d)})

# General one-axis product-Laplacian identity, independent of the selected modes.
a,b,c,d=[sp.Function(name)(z) for name in ('a','b','c','d')]
omega=a*d-b*c
heat_time=nu*(sp.diff(a,z,2)*d+a*sp.diff(d,z,2)-sp.diff(b,z,2)*c-b*sp.diff(c,z,2))
assert sp.expand(heat_time-nu*sp.diff(omega,z,2)+2*nu*(sp.diff(a,z)*sp.diff(d,z)-sp.diff(b,z)*sp.diff(c,z)))==0
# General induced exterior-square action of the stretching matrix in three axes.
A=sp.Matrix(3,3,sp.symbols('A0:9'))
l=sp.Matrix(sp.symbols('l0:3')); r=sp.Matrix(sp.symbols('r0:3'))
assert ((A*l).cross(r)+l.cross(A*r)-(sp.trace(A)*sp.eye(3)-A.T)*l.cross(r)).applyfunc(sp.expand)==sp.zeros(3,1)

print(json.dumps({
 'scope':'Exact periodic fluid solutions, oriented current and complex heat/logarithmic continuation; no fluid blowup or general closure conclusion',
 'coordinates':{'q':'positive spatial frequency; period 2*pi/q; q=2*pi gives a unit-period field','nu':'nonnegative viscosity','rate':'nu*q^2','pressure':'zero for both solutions'},
 'fields':{'J':strings(J),'K':strings(K)},
 'complex_faces':{'j':'exp(-rate*t)*exp(i*q*z)','k':'(1+exp(-4*rate*t)*exp(2*i*q*z))/2','cross':'Im(conjugate(j)*k)'},
 'complex_heat_continuation':{'H':str(H),'simple_zero_curve':str(zero_curve),'derivative_at_zero':str(-sp.I*q),'logarithmic_field':'H_zeta/H','Burgers_field':'-2*nu*H_zeta/H','regular_domain':'H != 0'},
 'cross_current':str(expected),
 'cross_heat_defect':str(-2*rate*sp.exp(-5*rate*t)*sp.sin(phase)),
 'initial_cross_rate':str(-2*rate*sp.sin(phase)),
 'energy_balances':energies,
 'checks':{'complete_NS_momentum':True,'divergence':True,'actual_periodicity':True,'Euler_specialization':True,
  'initial_pointwise_alignment':True,'complex_oriented_receiver':True,'mixed_gradient_heat_source':True,
  'local_energy_flux_and_dissipation':True,'periodic_energy_balance':True,'general_product_Laplacian':True,
  'general_stretching_exterior_action':True,'entire_complex_heat_source':True,
  'actual_simple_zero_trajectory':True,'complex_Burgers_source_on_regular_domain':True},
 'sympy_version':sp.__version__,'exit_status':0
},indent=2))
