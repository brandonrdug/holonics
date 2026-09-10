"""Exact exterior derivations for the Athena equational/world-tube review.
No model fitting from an evaluation target and no native learning implementation.
"""
from fractions import Fraction as Q
from itertools import product
from collections import defaultdict
from pathlib import Path
import json


def dot(a, b):
    return sum(x*y for x,y in zip(a,b))


def add(a, b):
    return tuple(x+y for x,y in zip(a,b))


def cross(a,b):
    return (a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])


def mv(a, x):
    return tuple(dot(row,x) for row in a)


def normal_return(p, h_inverse, x, y):
    """Exact Sherman-Morrison update of the normal reference P=B H^-1."""
    residual=y-dot(p,x)
    pullback=mv(h_inverse,x)
    return tuple(Q(v)+residual*w/(1+dot(x,pullback)) for v,w in zip(p,pullback))


def magma(x,y):
    if x%2==0 and y%2==0:
        return x^y
    if y%2==0:
        return y+2
    if x%2==0:
        return max(x-2,0)
    return 0


def ring_mesh(rect, r, plane):
    """Exact boundary of rectangular annulus times a normal interval."""
    x0,x1,y0,y1=map(Q,rect)
    vertices=[]
    def position(x,y,z):
        return (x,y,z) if plane=='xy' else (x,z,y)
    for z in (-r,r):
        for bounds in ((x0-r,x1+r,y0-r,y1+r),(x0+r,x1-r,y0+r,y1-r)):
            a,b,c,d=bounds
            vertices.extend(position(x,y,z) for x,y in ((a,c),(b,c),(b,d),(a,d)))
    faces=[]
    def quad(a,b,c,d):
        faces.extend(((a,b,c),(a,c,d)))
    for i in range(4):
        j=(i+1)%4
        quad(i,j,j+4,i+4)
        quad(i+8,i+12,j+12,j+8)
        quad(i,i+8,j+8,j)
        quad(i+4,j+4,j+12,i+12)
    if plane=='xy':
        faces=[tuple(reversed(f)) for f in faces]
    edges=defaultdict(list)
    for face in faces:
        for a,b in zip(face,face[1:]+face[:1]):
            e=tuple(sorted((a,b)))
            edges[e].append(1 if (a,b)==e else -1)
    assert all(len(signs)==2 and sum(signs)==0 for signs in edges.values())
    assert len(vertices)-len(edges)+len(faces)==0
    volume=sum(dot(vertices[a],cross(vertices[b],vertices[c])) for a,b,c in faces)/6
    assert volume==8*r*r*((x1-x0)+(y1-y0))
    return dict(vertices=vertices,faces=faces,V=len(vertices),E=len(edges),F=len(faces),volume=volume)


def boundary(simplex):
    out=defaultdict(int)
    for i in range(len(simplex)):
        face=simplex[:i]+simplex[i+1:]
        inversions=sum(face[a]>face[b] for a in range(len(face)) for b in range(a+1,len(face)))
        out[tuple(sorted(face))]+=(-1)**(i+inversions)
    return out


def main():
    # Commutative, idempotent mean is not associative. Retaining weight restores the join.
    mean=lambda a,b: (a+b)/2
    lhs=mean(mean(Q(0),Q(0)),Q(4)); rhs=mean(Q(0),mean(Q(0),Q(4)))
    assert (lhs,rhs)==(2,1)
    terms=((Q(0),1),(Q(0),1),(Q(4),1))
    assert add(add(terms[0],terms[1]),terms[2])==add(terms[0],add(terms[1],terms[2]))==(4,3)
    # ETP's infinite operation, tested at a declared finite assignment aperture only.
    for x,y,z in product(range(8),repeat=3):
        assert magma(x,y)==magma(magma(z,magma(x,y)),z)
    x=y=z=1
    counter=(magma(x,y),magma(z,magma(magma(x,y),z)))
    assert counter==(0,2)
    # Same scalar observation, different producing cut. This is a causal distinction,
    # not a defect in receive(v), whose contract is an actual NEXT current.
    # Reachable from the native unit prior using one source-plane-admissible
    # observation phi0=(1,1,0), eta0=3/2. H=I+phi0 phi0^T, B=eta0 phi0^T.
    h=((Q(2),Q(1),Q(0)),(Q(1),Q(2),Q(0)),(Q(0),Q(0),Q(1)))
    h_inverse=((Q(2,3),Q(-1,3),Q(0)),(Q(-1,3),Q(2,3),Q(0)),(Q(0),Q(0),Q(1)))
    prior_b=(Q(3,2),Q(3,2),Q(0))
    p=mv(h_inverse,prior_b)
    assert p==(Q(1,2),Q(1,2),Q(0))
    correct=normal_return(p,h_inverse,(1,1,0),Q(2))
    next_current=normal_return(p,h_inverse,(1,2,1),Q(1))
    assert correct==(Q(7,10),Q(7,10),Q(0))
    assert next_current==(Q(1,2),Q(3,8),Q(-1,8))
    # Fixed linear SSM equals its finite convolution including the initial-state term.
    a=((Q(1),Q(1)),(Q(0),Q(1)))
    b=(Q(0),Q(1)); c=(Q(1),Q(0)); initial=(Q(2),Q(-1))
    inputs=(Q(1),Q(2),Q(-1),Q(3))
    def power(k,x):
        for _ in range(k): x=mv(a,x)
        return x
    state=initial; outputs=[]
    for t,u in enumerate(inputs):
        state=add(mv(a,state),tuple(v*u for v in b))
        y=dot(c,state)
        conv=dot(c,power(t+1,initial))+sum(dot(c,power(t-s,b))*inputs[s] for s in range(t+1))
        assert y==conv
        outputs.append(y)
    # A selective recurrence is not in general one fixed linear convolution.
    selective=lambda us: __import__('functools').reduce(lambda h,u:(1+u)*h+u,us,Q(0))
    assert selective((1,1))==3 != selective((1,0))+selective((0,1))==2
    # Exact integral polygonal Hopf link, using oriented disk intersection.
    curve_a=((-2,-2,0),(2,-2,0),(2,2,0),(-2,2,0))
    curve_b=((0,0,-1),(3,0,-1),(3,0,1),(0,0,1))
    crossings=[]
    for u,v in zip(curve_b,curve_b[1:]+curve_b[:1]):
        if u[2]*v[2]<0:
            t=Q(-u[2],v[2]-u[2]); p0=tuple(Q(x)+t*(y-x) for x,y in zip(u,v))
            if -2<p0[0]<2 and -2<p0[1]<2:
                crossings.append(1 if v[2]>u[2] else -1)
    assert crossings==[-1]
    # Each pair of segments is at least one apart in l-infinity: A has y=+-2
    # or x=+-2; B has z=+-1 or a vertical edge at x=0 or x=3.
    clearance=Q(1); radius=clearance/4
    mesh_a=ring_mesh((-2,2,-2,2),radius,'xy')
    mesh_b=ring_mesh((0,3,-1,1),radius,'xz')
    def shear(p,t):
        x,y,z=map(Q,p)
        return (x+t*z,y,z)
    def circulation(curve):
        return sum(Q(u[2]+v[2],2)*(v[0]-u[0]) for u,v in zip(curve,curve[1:]+curve[:1]))
    circulation_rows=[]
    for t in (Q(0),Q(1,2),Q(1)):
        row=tuple(circulation(tuple(shear(p,t) for p in curve)) for curve in (curve_a,curve_b))
        assert row==(0,-6)
        circulation_rows.append((t,row))
    # A single triangular section swept through one exact clock interval consists
    # of three tetrahedra. Internal triangular faces cancel, boundary squared = 0.
    tetrahedra=((0,1,2,5),(0,1,5,4),(0,4,5,3))
    bd=defaultdict(int)
    for tet in tetrahedra:
        for f,n in boundary(tet).items(): bd[f]+=n
    bd={f:n for f,n in bd.items() if n}
    assert len(bd)==8
    bb=defaultdict(int)
    for f,n in bd.items():
        for e,k in boundary(f).items(): bb[e]+=n*k
    assert not any(bb.values())
    assert bd[(0,1,2)]==-1 and bd[(3,4,5)]==1
    # Same complex-torus topology does not identify an elliptic arithmetic source.
    elliptic=[]
    for prime in (3,5,7,11,13):  # declared good-prime observation aperture
        traces=[]
        for twist in (1,2):
            affine=sum((y*y-x*x*x+twist*twist*x)%prime==0
                       for x,y in product(range(prime),repeat=2))
            trace=prime-affine
            assert trace*trace<=4*prime
            traces.append(trace)
        elliptic.append((prime,tuple(traces)))
        character=pow(2,(prime-1)//2,prime)
        character=-1 if character==prime-1 else character
        assert traces[1]==character*traces[0]
    assert next(row for p,row in elliptic if p==5)==(-2,2)
    data=dict(mean=dict(left=lhs,right=rhs,weighted_join=(4,3)),
              etp=dict(assignment=(1,1,1),law3588_difference=counter,checked_assignment_extent=8),
              producing_cut=dict(prior_observation=dict(phi=(1,1,0),eta=Q(3,2)),
                                 H=h,B=prior_b,target_energy=Q(9,4),P=p,
                                 correction=correct,next_current=next_current),
              ssm=dict(inputs=inputs,outputs=outputs),
              link=dict(a=curve_a,b=curve_b,linking=-1,clearance=clearance,radius=radius,
                        mesh_a=mesh_a,mesh_b=mesh_b,circulation_rows=circulation_rows),
              prism=dict(tetrahedra=tetrahedra,boundary=[(f,n) for f,n in sorted(bd.items())]),
              elliptic=dict(curve='y^2=x^3-n^2*x',twists=(1,2),prime_traces=elliptic))
    def encode(v):
        if isinstance(v,Q): return [v.numerator,v.denominator]
        raise TypeError(type(v))
    Path(__file__).with_name('witness.json').write_text(json.dumps(data,default=encode,indent=2)+'\n')
    figure_path=Path(__file__).resolve().parents[2]/'papers/source/papers/hnn-information-chemistry/law-geometry.json'
    figure_path.write_text(json.dumps({k:data[k] for k in ('link','prism')},default=encode,separators=(',',':'))+'\n')
    print('Returned: nonassociative mean / weighted join; ETP infinite-model assignment; producing-cut normal updates; SSM convolution and selective counterexample; exact polygonal link, closed triangular shells, material shear and Kelvin circulation; swept prism boundary; distinct elliptic prime traces.')

if __name__=='__main__': main()
