# Host rulers for the lens of 2026-11-10 20:45Z (rulers on text, never machinery; Witten-Bell chains fit on TRAIN):
#  split : four letters divided between the two sides of a place
#  prod  : the two sides read as separate branches whose messages multiply at the place, against the joint table
#  field : the field's own face (a locked visit's dump) multiplied into the branch product and into the joint table
#  stride: the text's code from letters at +-s only, and at +-s, +-3s
import numpy as np, time, sys, os
exec(open('yard.py').read().split("xT,sT=load")[0])
z=np.load('train.npz'); xT=z['x'].astype(np.int64); sT=z['seg']; xH,sH=load('HELD128.txt')
t0=time.time(); part=sys.argv[1]; A=100
uni=np.bincount(xT,minlength=B).astype(float)+0.5; uni/=uni.sum()
def dist(chain,idx=None):
    cs=[ctx(xH,sH,o) for o in chain]
    if idx is not None: cs=[c[idx] for c in cs]
    N=len(cs[0]); P=np.tile(uni,(N,1))
    for offs,cH in zip(chain,cs):
        M=fit(ctx(xT,sT,offs),xT); Q=np.empty_like(P)
        for a in range(B):
            n,m,d=look(M,cH,np.full(N,a,np.int64)); lam=np.maximum(d,1).astype(float)
            Q[:,a]=np.where(n>0,(m+lam*P[:,a])/(n+lam),P[:,a])
        P=Q; del M
    P=P[:,:A]; return P/P.sum(1,keepdims=True)
def pool(ls,ws):
    s=sum(w*l for w,l in zip(ws,ls)); m=s.max(1,keepdims=True); return s-m-np.log(np.exp(s-m).sum(1,keepdims=True))
if part=='split':
    run('3 LEFT 1 RIGHT (levels: 1L; 1L1R; 2L1R; 3L1R), HELD128',[(-1,),(-1,1),(-2,-1,1),(-3,-2,-1,1)],xT,sT,xH,sH)
    run('1 LEFT 3 RIGHT (levels: 1R; 1L1R; 1L2R; 1L3R), HELD128',[(1,),(-1,1),(-1,1,2),(-1,1,2,3)],xT,sT,xH,sH)
if part in('prod','field'):
    idx=None
    if part=='field':
        idx=np.load('gi_held.npy')
    let=xH if idx is None else xH[idx]; N=len(let); I=np.arange(N)
    f='cap_f_%s.npz'%part
    if os.path.exists(f): q=np.load(f); lL,lR,lJ,lL1,lR1,lJ1=[q[k] for k in ('lL','lR','lJ','lL1','lR1','lJ1')]
    else:
        lL1=np.log(dist([(-1,)],idx)); lL=np.log(dist([(-1,),(-2,-1)],idx)); lR1=np.log(dist([(1,)],idx)); lR=np.log(dist([(1,),(1,2)],idx))
        lJ1=np.log(dist([(-1,1)],idx)); lJ=np.log(dist([(-1,1),(-2,-1,1,2)],idx)); np.savez(f,lL=lL,lR=lR,lJ=lJ,lL1=lL1,lR1=lR1,lJ1=lJ1)
    lU=np.log(uni[:A]/uni[:A].sum())[None,:]+np.zeros((N,1))
    c=lambda l,s=slice(None): -l[I,let][s].mean()
    print('places',N,' %.0fs'%(time.time()-t0),flush=True)
if part=='prod':
    print('two each side: left %.4f right %.4f joint %.4f | one each side: left %.4f right %.4f joint %.4f'%(c(lL),c(lR),c(lJ),c(lL1),c(lR1),c(lJ1)))
    lB=pool([lL,lR,lU],[1,1,-1]); lB1=pool([lL1,lR1,lU],[1,1,-1])
    print('BRANCH PRODUCT P(x|L)P(x|R)/P(x): two each side %.4f (lacks %.4f against joint)   one each side %.4f (lacks %.4f)'%(c(lB),c(lB)-c(lJ),c(lB1),c(lB1)-c(lJ1)))
    print('one shared exponent a, weights (a,a,1-2a), chosen on the read itself:')
    for a in (0.5,0.6,0.7,0.8,0.9,1.0,1.1): print('   a=%.1f  two each side %.4f   one each side %.4f'%(a,c(pool([lL,lR,lU],[a,a,1-2*a])),c(pool([lL1,lR1,lU],[a,a,1-2*a]))))
    # by how often the joint context occurs in TRAIN
    M=fit(ctx(xT,sT,(-2,-1,1,2)),xT); cH=ctx(xH,sH,(-2,-1,1,2)); i=np.searchsorted(M[0],cH); i[i>=len(M[0])]=0; nH=np.where(M[0][i]==cH,M[1][i],0)
    cj=-lJ[I,let]; cb=-lB[I,let]
    print('by count of the joint context in TRAIN: share of places | joint table | branch product | share of the lack')
    for lo,hi in [(0,0),(1,1),(2,9),(10,99),(100,999),(1000,9999),(10000,10**9)]:
        s=(nH>=lo)&(nH<=hi); print('  %6d..%-10d %6.4f | %6.3f | %6.3f | %6.3f'%(lo,hi,s.mean(),cj[s].mean(),cb[s].mean(),(cb-cj)[s].sum()/(cb-cj).sum()))
    # synergy: joint against each branch alone and against both pooled with the joint
    print('joint x branch product (best of grid, on the read): %.4f'%min(c(pool([lJ,lB],[a,b])) for a in (0.6,0.8,1.0) for b in (0.0,0.1,0.2,0.3,0.4)))
if part=='field':
    V=os.environ.get('HOLONICS_ROOT','./')+'.local/wt/qgchgu-sampler/.local/run/2026-11-10-contacts/visit/'  # the visit dumps, private
    dt=np.dtype([('problem','<u4'),('place','<u4'),('stop','u1'),('letter','<u2'),('face','<u2',(100,)),('chart','<i4',(64,))])
    pr=sH[idx]; lB=pool([lL,lR,lU],[1,1,-1])
    grid=[(a,b) for a in np.arange(0.4,1.01,0.1) for b in np.arange(0.0,0.91,0.1)]
    def cs(lf,lt,a,b,sel):
        s=a*lf[sel]+b*lt[sel]; m=s.max(1,keepdims=True); lz=m[:,0]+np.log(np.exp(s-m).sum(1)); return lz-s[np.arange(len(lz)),let[sel]]
    def mult(lf,lt):
        out=np.zeros(N); w=[]
        for fold in (0,1):
            tr=(pr%2==fold); te=~tr
            _,a,b=min((cs(lf,lt,a,b,tr).mean(),a,b) for a,b in grid); out[te]=cs(lf,lt,a,b,te); w.append((round(float(a),1),round(float(b),1)))
        return out.mean(),w
    for nm in sys.argv[2:]:
        d=np.fromfile(V+nm+'/held.bin',dtype=dt); assert (d['letter']==let).all()
        f=np.maximum(d['face'].astype(np.float64),0.5); f/=f.sum(1,keepdims=True); lf=np.log(f); cf=c(lf)
        print(nm,'field %.4f | joint table %.4f | branch product %.4f | left pair %.4f | right pair %.4f | one each side joint %.4f'%(cf,c(lJ),c(lB),c(lL),c(lR),c(lJ1)),flush=True)
        for name,lt in (('joint table (two each side)',lJ),('branch product (two each side)',lB),('left pair',lL),('right pair',lR),('one each side joint',lJ1),('branch product (one each side)',pool([lL1,lR1,lU],[1,1,-1]))):
            p,w=mult(lf,lt); print('   field x %-32s %.4f  weights %s  THE FIELD LACKS %.4f   %.0fs'%(name,p,w,cf-p,time.time()-t0),flush=True)
if part=='stride':
    for s in (1,2,4,8,16):
        ch=[(-s,s)]+([(-3*s,-s,s,3*s)] if s<=8 else [])
        run('STRIDE %d: letters at +-%d%s, HELD128'%(s,s,' then +-%d,+-%d'%(s,3*s) if s<=8 else ''),ch,xT,sT,xH,sH); print('   %.0fs'%(time.time()-t0),flush=True)
print('done %.0fs'%(time.time()-t0))
