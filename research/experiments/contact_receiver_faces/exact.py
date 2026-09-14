"""Exact local Lorentz / gyro / traction faces. No floating-point arithmetic.

Components are rational in an orthonormal tetrad with x^0=ct and velocity v/c.
T is expressed in a declared stress/energy-density unit E0. A tetrad metric equal
to eta at an event is not an assertion that the spacetime is globally flat.
"""
from fractions import Fraction as Q
from pathlib import Path
import json

N=4
I=[[Q(int(i==j)) for j in range(N)] for i in range(N)]
ETA=[[Q((-1 if i==0 else 1)*int(i==j)) for j in range(N)] for i in range(N)]
def transpose(a):return [list(x) for x in zip(*a)]
def mat(a,b):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def mv(a,v):return [sum(x*y for x,y in zip(row,v)) for row in a]
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def mdot(a,b):return dot(a,mv(ETA,b))
def sub(a,b):return [x-y for x,y in zip(a,b)]
def boost(v,gamma):
    assert gamma*gamma*(1-dot(v,v))==1 and gamma>0
    result=[r[:] for r in I]
    result[0][0]=gamma
    for i in range(3):
        result[0][i+1]=result[i+1][0]=gamma*v[i]
        for j in range(3):result[i+1][j+1]+=gamma*gamma/(gamma+1)*v[i]*v[j]
    assert mat(mat(transpose(result),ETA),result)==ETA
    return result

def einstein(u,v,gu):
    den=1+dot(u,v)
    return [(u[i]+v[i]/gu+gu/(1+gu)*dot(u,v)*u[i])/den for i in range(3)]

def lorentz_inverse(a):return mat(mat(ETA,transpose(a)),ETA)
def face(T,U,n):return -dot(mv(ETA,U),mv(T,mv(ETA,n)))
def energy(T,U):return dot(mv(ETA,U),mv(T,mv(ETA,U)))

def main():
    zero=[Q(0)]*3;u=[Q(3,5),Q(0),Q(0)];v=[Q(0),Q(4,5),Q(0)]
    gu,gv=Q(5,4),Q(5,3);Bu,Bv=boost(u,gu),boost(v,gv)
    scales=[Q(2),Q(3)]
    for k,velocity,gamma in zip(scales,[u,v],[gu,gv]):
        assert gamma==(k+1/k)/2
        assert gamma*sum(velocity)==(k-1/k)/2
    w=einstein(u,v,gu);reverse=einstein(v,u,gv);gw=gu*gv*(1+dot(u,v))
    R=mat(lorentz_inverse(boost(w,gw)),mat(Bu,Bv))
    assert R[0]==[Q(1),Q(0),Q(0),Q(0)] and [r[0] for r in R]==[Q(1),Q(0),Q(0),Q(0)]
    assert w!=reverse and w==[Q(3,5),Q(16,25),Q(0)]
    # Definition coadd(u,v)=u ⊕ gyr[u,-v]v, using the recovered gyrogroup law.
    minusv=[-x for x in v];wm=einstein(u,minusv,gu)
    Rm=mat(lorentz_inverse(boost(wm,gu*gv)),mat(Bu,boost(minusv,gv)))
    gyrv=mv([r[1:] for r in Rm[1:]],v)
    D=einstein(u,gyrv,gu)
    assert D==[Q(315,781),Q(560,781),Q(0)]
    gD=Q(781,444);assert gD*gD*(1-dot(D,D))==1
    middle=[(gu*u[i]+gv*v[i])/(gu+gv) for i in range(3)]
    assert middle==[gD*x/(1+gD) for x in D]
    U0=[Q(1),Q(0),Q(0),Q(0)];UA=mv(Bu,U0);UR=mv(Bv,U0);normal=[Q(0),Q(0),Q(0),Q(1)]
    T=[[Q(10),Q(0),Q(0),Q(2)], [Q(0),Q(2),Q(0),Q(1)], [Q(0),Q(0),Q(3),Q(0)], [Q(2),Q(1),Q(0),Q(4)]]
    readings=[face(T,U,normal) for U in [U0,UA,UR]]
    assert readings==[Q(2),Q(7,4),Q(10,3)]
    energies=[energy(T,U) for U in [U0,UA,UR]]
    frame=mat(Bu,Bv);Tp=mat(mat(frame,T),transpose(frame))
    # Same observer, same oriented face, changed components: invariant contractions.
    for U in [U0,UA,UR]:
        assert mdot(U,U)==-1 and mdot(U,normal)==0
        assert face(Tp,mv(frame,U),mv(frame,normal))==face(T,U,normal)
        assert energy(Tp,mv(frame,U))==energy(T,U)
    assert [face(T,U,[-x for x in normal])+face(T,U,normal) for U in [U0,UA,UR]]==[0,0,0]
    # Local tangential slip in U0's spatial face; constitutive traction & dissipation.
    slip=[Q(0),Q(3,5),Q(0),Q(0)];eta=Q(5,3)
    tractionA=[eta*x for x in slip];tractionB=[-x for x in tractionA]
    heat=eta*mdot(slip,slip)
    assert heat==Q(3,5) and sub(tractionA,[-x for x in tractionB])==[0]*4
    # Poincare coordinates are an exact type/geometry transition C(v)=gamma*v/(1+gamma).
    poincare=[[Q(0),Q(0)],[gu*u[i]/(1+gu) for i in range(2)], [gv*v[i]/(1+gv) for i in range(2)], [gD*D[i]/(1+gD) for i in range(2)]]
    out=dict(schema='holonics.exact-contact-receiver-faces.v1',component_domain='Q; units and tensor roles retained',metric=ETA,
        unit_convention=dict(position='(ct,x,y,z)/L0',velocity='v/c',stress='T/E0',face_flux='F/(c E0)',heat_flux='Qdot/(c E0)'),
        scale_faces=scales,scale_constraint="E(rapidity)=k; gamma=(k+k^-1)/2; xi=(k-k^-1)/2",velocities=[u,v],gammas=[gu,gv],boosts=[Bu,Bv],ordered_velocities=[w,reverse],gyration=R,
        gyroparallelogram=dict(origin=zero,left=u,right=v,fourth=D,midpoint=middle,poincare_vertices=poincare,closure='D=u ⊕ gyr[u,-v]v; diagonals share gyromidpoint'),
        stress=T,observers=[U0,UA,UR],normal=normal,face_fluxes=readings,energies=energies,
        transformed_stress=Tp,slip=slip,friction_coefficient=eta,tractions=[tractionA,tractionB],heat=heat,
        checks=dict(lorentz_isometries=True,gyro_diagonal_midpoint=True,same_observer_face_covariance=True,opposite_face_cancellation=True,friction_balance=True),
        scope='exact pointwise tetrad and local constitutive example; Einstein/Bianchi field conservation additionally uses its supplied geometric and stress laws')
    def wire(x):
        if isinstance(x,Q):return str(x)
        if isinstance(x,dict):return {k:wire(v) for k,v in x.items()}
        if isinstance(x,(list,tuple)):return [wire(v) for v in x]
        return x
    Path(__file__).with_name('receipt.json').write_text(json.dumps(wire(out),indent=2)+'\n')
    print('exact gyro fourth:',D,'gyration spatial:',[r[1:] for r in R[1:]])
    print('exact receiver fluxes:',readings,'energy faces:',energies,'heat:',heat)
if __name__=='__main__':main()
