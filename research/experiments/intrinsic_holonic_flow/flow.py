"""A coupled analytic phase field on a branched chain of interlinked tori.

Preserved exterior numerical survey/display evaluator.
The authoritative source is model_constraints.json and exact/; this evaluator
must not supply exact Holonic state or receiver verdicts. Two normalized phase-comparison
potentials act on ONE T^(2N), with incidence computed from exact solid-torus overlap
witnesses. The chosen symplectic split, parameters and detector are explicit.
This is not a new native HNN runtime or a reproduced trained reasoning model.
"""
from pathlib import Path
from fractions import Fraction as Q
import sys
import json,time
import numpy as np

HERE=Path(__file__).parent
N=6; R=2; FIELD_RADIUS=1; CORE_RADIUS=float(Q(13,50))
CENTERS=np.array([[-6,0,0],[-3,0,0],[0,0,0],[3,0,0],[6,0,0],[0,3,0]],dtype=float)
AXES=np.array([2,1,2,1,2,0])
KAPPA=float(Q(27,100)); GAMMA=float(Q(7,20)); BETAS=(1,4); CAP=96
# Clock and canonical phase have dimensionless reference units.

def torus_polynomial(points,i,minor=FIELD_RADIUS):
    v=np.asarray(points)-CENTERS[i];s=np.sum(v*v,axis=-1)
    plane=s-v[...,AXES[i]]**2
    return (s+R*R-minor*minor)**2-4*R*R*plane

def incidence():
    # Integer quarter-unit lattice and denominator-cleared quartic: exact int64.
    a=np.arange(-36,37);b=np.arange(-12,25);c=np.arange(-12,13)
    pts=np.stack(np.meshgrid(a,b,c,indexing='ij'),axis=-1).reshape(-1,3)
    polys=[]
    for center,axis in zip(CENTERS,AXES):
        v=pts-(4*center).astype(np.int64);s=np.sum(v*v,axis=1)
        polys.append((s+64-16)**2-256*(s-v[:,axis]**2))
    mask=np.eye(N,dtype=bool);witness=[]
    for i in range(N):
        for j in range(i+1,N):
            joint=np.maximum(polys[i],polys[j]);k=np.argmin(joint)
            if joint[k]<0:
                mask[i,j]=mask[j,i]=True
                witness.append(dict(edge=[i,j],point=(pts[k]/4).tolist(),quartics=[int(polys[i][k]),int(polys[j][k])]))
    return mask,witness

MASK,WITNESSES=incidence()
EDGE_LIST=[w['edge'] for w in WITNESSES]
# Antisymmetric oriented phase connection; self-comparison phase is zero.
PHASE=np.zeros((N,N))
for i,j in EDGE_LIST:PHASE[i,j]=1/8;PHASE[j,i]=-1/8

def head(q,beta):
    angle=2*np.pi*(q[..., :,None]-q[...,None,:]-PHASE)
    scores=beta*np.cos(angle)
    scores=np.where(MASK,scores,-np.inf)
    weights=np.exp(scores-np.max(scores,axis=-1,keepdims=True));weights/=weights.sum(axis=-1,keepdims=True)
    return weights,angle

def force(q):
    f=np.sin(2*np.pi*q)/(1+np.exp(np.cos(2*np.pi*q)))
    for beta in BETAS:
        a,angle=head(q,beta)
        # Derivative of every receiving row: includes inbound AND outbound terms.
        f+=GAMMA/len(BETAS)*np.sum((a+np.swapaxes(a,-1,-2))*np.sin(angle),axis=-1)
    return KAPPA*f

def potential(q):
    value=KAPPA/(2*np.pi)*np.sum(np.logaddexp(0,-np.cos(2*np.pi*q)),axis=-1)
    for beta in BETAS:
        scores=np.where(MASK,beta*np.cos(2*np.pi*(q[..., :,None]-q[...,None,:]-PHASE)),-np.inf)
        m=np.max(scores,axis=-1)
        value-=KAPPA*GAMMA/(2*np.pi*len(BETAS)*beta)*np.sum(m+np.log(np.exp(scores-m[...,None]).sum(axis=-1)),axis=-1)
    return value

def step(q,p):
    q1=q+KAPPA*np.sin(2*np.pi*p)
    p1=p-force(q1)
    return q1%1,p1%1

def inverse(q1,p1):
    p=p1+force(q1);q=q1-KAPPA*np.sin(2*np.pi*p)
    return q%1,p%1

def initialize(a,b):
    a,b=np.broadcast_arrays(a,b)
    q=np.broadcast_to((.07+.13*np.arange(N))%1,a.shape+(N,)).copy()
    p=np.broadcast_to((.11+.09*np.arange(N))%1,a.shape+(N,)).copy()
    q[...,0]=a;p[...,0]=b
    return q,p

def receiver(q,p):
    return (q[...,0]>=.20)&(q[...,0]<.34)&(p[...,0]>=.08)&(p[...,0]<.20)

def arrival(bounds,res=192):
    xmin,xmax,ymin,ymax=bounds
    aa=xmin+(np.arange(res)+.5)*(xmax-xmin)/res
    bb=ymin+(np.arange(res)+.5)*(ymax-ymin)/res
    a,b=np.meshgrid(aa,bb);q,p=initialize(a,b)
    times=np.full(a.shape,CAP+1,dtype=np.uint16)
    for k in range(CAP+1):
        times[(times==CAP+1)&receiver(q,p)]=k
        if k<CAP:q,p=step(q,p)
    return times

def torus_point(i,q,p,radius=CORE_RADIUS):
    q,p=np.broadcast_arrays(q,p);theta=2*np.pi*q;phi=2*np.pi*p
    axis=AXES[i];a=(axis+1)%3;b=(axis+2)%3
    out=np.zeros(q.shape+(3,));out[...,axis]=radius*np.sin(phi)
    out[...,a]=(R+radius*np.cos(phi))*np.cos(theta)
    out[...,b]=(R+radius*np.cos(phi))*np.sin(theta)
    return out+CENTERS[i]

def advect(points,t=1.,rate=1/8):
    """Exact analytic forced incompressible-flow map, numerically rendered.
    F_t(x,y,z)=(x, y cos(rate*x*t)-z sin(...), y sin(...)+z cos(...)).
    """
    pts=np.asarray(points);angle=rate*pts[...,0]*t;c=np.cos(angle);ss=np.sin(angle)
    return np.stack([pts[...,0],pts[...,1]*c-pts[...,2]*ss,pts[...,1]*ss+pts[...,2]*c],axis=-1)


def path(a,b,steps=14):
    q,p=initialize(np.asarray(a),np.asarray(b));qs=[q.copy()];ps=[p.copy()]
    for k in range(steps):
        qnew=q+KAPPA*np.sin(2*np.pi*p)
        for s in np.linspace(0,1,12)[1:]:qs.append((q+s*(qnew-q))%1);ps.append(p.copy())
        pnew=p-force(qnew)
        for s in np.linspace(0,1,12)[1:]:qs.append(qnew%1);ps.append((p+s*(pnew-p))%1)
        q,p=qnew%1,pnew%1
    return np.array(qs),np.array(ps)

def verify():
    rng=np.random.default_rng(19);q,p=rng.random((9,N)),rng.random((9,N))
    u,v=step(q,p);backq,backp=inverse(u,v)
    err=max(np.max(abs((backq-q+.5)%1-.5)),np.max(abs((backp-p+.5)%1-.5)))
    # Independent finite differences check the complete normalized-potential gradient.
    eps=1e-6;g=np.empty_like(q)
    for i in range(N):
        dq=np.zeros(N);dq[i]=eps
        g[:,i]=(potential(q+dq)-potential(q-dq))/(2*eps)
    gradient_error=np.max(abs(g-force(q)))
    assert err<1e-12 and gradient_error<1e-8
    # Full Jacobian of the unwrapped split checks determinant one and symplecticity.
    x=np.r_[q[0],p[0]]
    def unwrapped(x):
        q1=x[:N]+KAPPA*np.sin(2*np.pi*x[N:]);return np.r_[q1,x[N:]-force(q1)]
    jac=np.column_stack([(unwrapped(x+eps*np.eye(2*N)[i])-unwrapped(x-eps*np.eye(2*N)[i]))/(2*eps) for i in range(2*N)])
    omega=np.block([[np.zeros((N,N)),np.eye(N)],[-np.eye(N),np.zeros((N,N))]])
    symp=np.max(abs(jac.T@omega@jac-omega));det=np.linalg.det(jac)
    assert symp<1e-7 and abs(det-1)<1e-7
    return dict(inverse_phase_error=float(err),gradient_difference_error=float(gradient_error),symplectic_difference_error=float(symp),jacobian_determinant=float(det))

def main():
    start=time.perf_counter();checks=verify()
    coarse=arrival((0,1,0,1))
    # Choose a witnessed neighboring pair with a large DIFFERENCE in first arrival.
    # This is observer selection after evolution, never a fitted or supplied solution.
    diff=abs(coarse[:,1:].astype(int)-coarse[:,:-1].astype(int))
    eligible=(coarse[:,1:]>8)&(coarse[:,:-1]>8)&(coarse[:,1:]<=CAP)&(coarse[:,:-1]<=CAP)
    diff=np.where(eligible,diff,-1)
    row,col=np.unravel_index(np.argmax(diff),diff.shape)
    center=((col+1)/192,(row+.5)/192)
    width=.16;bounds=(center[0]-width/2,center[0]+width/2,center[1]-width/2,center[1]+width/2)
    zoom=arrival(bounds)
    small=.032;finebounds=(center[0]-small/2,center[0]+small/2,center[1]-small/2,center[1]+small/2)
    fine=arrival(finebounds)
    np.savez_compressed(HERE/'arrival.npz',coarse=coarse,zoom=zoom,fine=fine)
    pair=[[(col+.5)/192,(row+.5)/192],[(col+1.5)/192,(row+.5)/192]]
    paths=[path(*pt) for pt in pair]
    q0,p0=initialize(*map(np.asarray,pair[0]));weights=[head(q0,beta)[0].tolist() for beta in BETAS]
    late=coarse>24
    rates=[dict(pixel_separation=d,phase_separation=d/192,disagreement=float(np.mean(late[:,d:]!=late[:,:-d]))) for d in [1,2,4,8,16]]
    result=dict(scope='exterior floating-point analytic Hamiltonian reference; finite arrival field, not trained HNN evidence or an infinite-scale fractal theorem',
        phase_dimension=2*N,centers=CENTERS.tolist(),axes=AXES.tolist(),major_radius=R,field_radius=FIELD_RADIUS,core_radius=CORE_RADIUS,
        overlap_witnesses=WITNESSES,mask=MASK.astype(int).tolist(),phase_connection=PHASE.tolist(),
        kappa=KAPPA,gamma=GAMMA,betas=BETAS,cap=CAP,resolution=192,
        receiver='q0 in [0.20,0.34), p0 in [0.08,0.20)',
        bounds=[[0,1,0,1],list(bounds),list(finebounds)],
        selected_neighbor_pair=pair,arrival_pair=[int(coarse[row,col]),int(coarse[row,col+1])],
        observation_windows=[dict(arrived_fraction=float(np.mean(a<=CAP)),mean_arrival_on_arrived=float(np.mean(a[a<=CAP]))) for a in [coarse,zoom,fine]],
        finite_early_late_disagreement=rates,checks=checks,weights_at_selected_state=weights,
        paths=[dict(q=q.tolist(),p=p.tolist()) for q,p in paths],elapsed_seconds=time.perf_counter()-start)
    (HERE/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['phase_dimension','arrival_pair','observation_windows','checks','elapsed_seconds']},indent=2))
if __name__=='__main__':
    if '--exploratory-survey' not in sys.argv:
        raise SystemExit('For exact/enclosed execution use exact/Cargo.toml. The preserved numerical survey requires --exploratory-survey and supplies no exact Holonic verdict.')
    main()
