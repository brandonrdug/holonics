"""Exact exterior witnesses for closed cartography and geometric differences.

No native learner is implemented here. Cubical state is recovered from the
existing calibration board; the remaining checks use fractions and Q(zeta_16).
"""
from fractions import Fraction as F
from collections import defaultdict
from itertools import product
from pathlib import Path
import json
import subprocess

ROOT = Path(__file__).resolve().parents[5]
OUT = Path(__file__).with_name('manifold-example.json')
N = 2**4
ZERO = (F(0),)*8
ONE = (F(1),)+(F(0),)*7

def add(a,b): return tuple(x+y for x,y in zip(a,b))
def neg(a): return tuple(-x for x in a)
def sub(a,b): return add(a,neg(b))
def scale(a,s): return tuple(x*s for x in a)
def mul(a,b):
    c=[F(0)]*8
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b):
                if y:
                    k=i+j
                    c[k%8] += x*y*(1 if k<8 else -1)
    return tuple(c)
def root(k):
    k%=16
    return tuple(F((1 if k<8 else -1) if i==k%8 else 0) for i in range(8))
def sigma(a,k=5):
    out=ZERO
    for i,x in enumerate(a): out=add(out,scale(root(k*i),x))
    return out
I=root(4)
C=[scale(add(root(k),root(-k)),F(1,2)) for k in range(N)]
S=[scale(mul(sub(root(k),root(-k)),neg(I)),F(1,2)) for k in range(N)]
for a in (root(k) for k in range(8)):
    assert sigma(sigma(sigma(sigma(a))))==a
    for b in (root(k) for k in range(8)): assert sigma(mul(a,b))==mul(sigma(a),sigma(b))
assert sigma(I)==I

weights={c:tuple(F(v,c+4) for v in (1,2,c,1)) for c in (2,3,4)}

def profile(c,i,j):
    a,b,d,r=weights[c]
    return add(add(scale(C[i],a),scale(C[j],b)),add(scale(C[(i+j)%N],d),scale(C[(i-j)%N],r)))
def shape(c,i,j,derivatives=False):
    a,b,d,s=weights[c]
    ci,si,cj,sj=C[i],S[i],C[j],S[j]
    f=profile(c,i,j)
    radius=add(ONE,scale(f,F(1,4)))
    t=add(scale(ONE,2),mul(radius,cj))
    X=(mul(t,ci),mul(t,si),mul(radius,sj))
    if not derivatives: return X
    ft=neg(add(scale(si,a),add(scale(S[(i+j)%N],d),scale(S[(i-j)%N],s))))
    fp=add(neg(add(scale(sj,b),scale(S[(i+j)%N],d))),scale(S[(i-j)%N],s))
    rt,rp=scale(ft,F(1,4)),scale(fp,F(1,4))
    normal=(mul(ci,cj),mul(si,cj),sj)
    tangent_t=(neg(mul(si,cj)),mul(ci,cj),ZERO)
    tangent_p=(neg(mul(ci,sj)),neg(mul(si,sj)),cj)
    base=(scale(si,-2),scale(ci,2),ZERO)
    Xt=tuple(add(base[k],add(mul(rt,normal[k]),mul(radius,tangent_t[k]))) for k in range(3))
    Xp=tuple(add(mul(rp,normal[k]),mul(radius,tangent_p[k])) for k in range(3))
    return X,(Xt,Xp)

def dot(a,b):
    z=ZERO
    for x,y in zip(a,b): z=add(z,mul(x,y))
    return z

for i,j in product(range(N),repeat=2):
    X2,X3,X4=(shape(c,i,j) for c in (2,3,4))
    for k in range(3):
        assert sub(X2[k],X3[k])==scale(sub(X4[k],X3[k]),F(-4,3))
        assert X3[k]==scale(add(scale(X2[k],6),scale(X4[k],8)),F(1,14))
        assert sigma(X3[k])==shape(3,5*i%N,5*j%N)[k]

_,d2=shape(2,1,2,True);_,d3=shape(3,1,2,True);_,d4=shape(4,1,2,True)
delta=tuple(tuple(sub(x,y) for x,y in zip(v,w)) for v,w in zip(d2,d3))
metric_remainder=[]
for a,b in product(range(2),repeat=2):
    g2,g3,g4=(dot(d[a],d[b]) for d in (d2,d3,d4))
    lhs=add(sub(g4,g3),scale(sub(g2,g3),F(3,4)))
    rhs=scale(dot(delta[a],delta[b]),F(21,16))
    assert lhs==rhs
    metric_remainder.append(lhs)
assert any(any(x) for x in metric_remainder)

# Periodic oriented triangles, all with explicit integer covering displacements.
vid=lambda i,j:(j%N)*N+(i%N)
edges=[]; edge_of={}; directions=[]
for j,i in product(range(N),repeat=2):
    for di,dj in ((1,0),(0,1),(1,1)):
        a,b=vid(i,j),vid(i+di,j+dj)
        edge_of[a,b]=(len(edges),1);edge_of[b,a]=(len(edges),-1)
        edges.append((a,b));directions.append((F(di,N),F(dj,N)))
faces=[]
for j,i in product(range(N),repeat=2):
    for tri in ((vid(i,j),vid(i+1,j),vid(i+1,j+1)),(vid(i,j),vid(i+1,j+1),vid(i,j+1))):
        faces.append([edge_of[tri[k],tri[(k+1)%3]] for k in range(3)])
assert N*N-len(edges)+len(faces)==0
for face in faces:
    boundary=defaultdict(int)
    for e,sign in face:
        a,b=edges[e];boundary[a]-=sign;boundary[b]+=sign
    assert not any(boundary.values())
assert all(sum(sign for face in faces for e2,sign in face if e2==e)==0 for e in range(len(edges)))

def curl(j): return [sum(sign*j[e] for e,sign in face) for face in faces]
def divergence(j):
    v=[F(0)]*(N*N)
    for x,(a,b) in zip(j,edges): v[a]-=x;v[b]+=x
    return v

def laplace(j):
    div=divergence(j);cr=curl(j)
    out=[div[b]-div[a] for a,b in edges]
    for value,face in zip(cr,faces):
        for e,sign in face: out[e]+=sign*value
    return out
wa=[d[0] for d in directions];wb=[d[1] for d in directions]
assert not any(curl(wa)) and not any(curl(wb))
assert not any(laplace(wa)) and not any(laplace(wb))
G=[[sum(x*y for x,y in zip(a,b)) for b in (wa,wb)] for a in (wa,wb)]
assert G==[[2,1],[1,2]]
cycle_a=[edge_of[vid(i,0),vid(i+1,0)] for i in range(N)]
cycle_b=[edge_of[vid(0,j),vid(0,j+1)] for j in range(N)]
assert [sum(sign*w[e] for e,sign in cyc) for w in (wa,wb) for cyc in (cycle_a,cycle_b)]==[1,0,0,1]
# kappa is the boundary of one face, viewed as a cochain under the unit metric.
f0=2*((N//4)*N+N//4)
kappa=[F(0)]*len(edges)
for e,sign in faces[f0]:kappa[e]=F(sign)
assert sorted(x for x in curl(kappa) if x)==[-1,-1,-1,3]
assert sum(x*y for x,y in zip(wa,kappa))==sum(x*y for x,y in zip(wb,kappa))==0
# Sparse Hodge matrix and a step derived from its row-sum bound.
L=[defaultdict(int) for _ in edges]
incident=[[] for _ in range(N*N)]
for e,(a,b) in enumerate(edges):incident[a].append((e,-1));incident[b].append((e,1))
for star in incident+faces:
    for e,s in star:
        for f,t in star:L[e][f]+=s*t
bound=max(sum(abs(v) for v in row.values()) for row in L)
time_step=F(1,bound)
heat=[kappa]
for _ in range(4):
    old=heat[-1]
    heat.append([old[e]-time_step*sum(v*old[f] for f,v in row.items()) for e,row in enumerate(L)])
    assert sum(x*y for x,y in zip(wa,heat[-1]))==0
    assert sum(x*y for x,y in zip(wb,heat[-1]))==0
    assert sum(x*x for x in heat[-1])<=sum(x*x for x in old)

# Two radius-2 octahedra centered at +/-e_x intersect in the unit octahedron.
# Outward area vector on face sigma is sigma/2, centroid sigma/3.
flux=[]
for signs in product((-1,1),repeat=3):
    n=tuple(F(s,2) for s in signs);c=tuple(F(s,3) for s in signs)
    jl=(c[0]+1,c[1],c[2]);jr=(c[0]-1,c[1],c[2])
    left=sum(a*b for a,b in zip(jl,n));right=sum(a*b for a,b in zip(jr,n))
    assert right-left==-signs[0]
    flux.append({'signs':signs,'left':int(left),'right':int(right),'difference':int(right-left)})
assert sum(f['left'] for f in flux)==sum(f['right'] for f in flux)==4
assert sum(f['difference'] for f in flux)==0
assert F(3)*F(4,3)==4
path=[(-1,0,0),(0,1,0),(1,0,0)]
assert sum(-2*(b[0]-a[0]) for a,b in zip(path,path[1:]))==-4

# Recover the user's original finite face state using its actual board source.
board=ROOT/'research/design/holonic-cad-2026-08-30/expression-manipulator/artboards/RubikBoard.dc.html'
js="const fs=require('fs'),vm=require('vm');const s=fs.readFileSync(process.argv[1],'utf8');const a=s.slice(s.indexOf('const U0='),s.indexOf('class Component extends'));console.log(vm.runInNewContext(a+';JSON.stringify({state:buildStorm(18).list[17],letters:FLETTER,colors:COLORS})'));"
cube=json.loads(subprocess.check_output(['node','-e',js,str(board)],text=True))
assert cube['state']['w']==['R',"U'"]
cube['face_word']=''.join(cube['letters'][k] for k in cube['state']['s'])
rename=[2,3,4,5,0,1]
assert [rename.index(ren) for ren in [rename[k] for k in cube['state']['s']]]==cube['state']['s']
cube['rename']=rename

def rat(x): return [x.numerator,x.denominator]
def poly(x):return [rat(c) for c in x]
def wire_seq(x):return [rat(v) for v in x]
result={
 'scope':'exact exterior finite chains, cyclotomic shape comparisons, and Euclidean flux calibration',
 'N':N,'cube':cube,'faces':faces,'edges':edges,'directions':[[rat(a),rat(b)] for a,b in directions],
 'curvature_face':f0,'kappa_heat':[wire_seq(x) for x in heat],
 'hodge_row_bound':bound,'edge_heat_step':rat(time_step),
 'torus_counts':{'vertices':N*N,'edges':len(edges),'faces':len(faces),'euler':0},
 'period_matrix':[[1,0],[0,1]],'harmonic_gram':[[2,1],[1,2]],'initial_curvature_nonzero':[-1,-1,-1,3],
 'shape_difference_ratio':[-4,3],'metric_remainder_factor':[21,16],
 'metric_remainder_at_1_2':[poly(x) for x in metric_remainder],
 'cyclotomic_modulus':'t^8+1','galois_power':5,'galois_order':4,
 'all_shape_samples_checked':N*N,'flux':flux,'volume':[4,3],
 'flux_totals':[4,4,0],'interior_and_surface_path_integral':-4,
}
OUT.write_text(json.dumps(result,indent=2)+'\n')
print(f'Returned: cube n=17 / R U-prime; torus {N*N}/{len(edges)}/{len(faces)}; nonzero periods and curvature; edge heat step {time_step}; {N*N} exact cyclotomic shape squares; metric remainder; octahedral flux and both path integrals.')
