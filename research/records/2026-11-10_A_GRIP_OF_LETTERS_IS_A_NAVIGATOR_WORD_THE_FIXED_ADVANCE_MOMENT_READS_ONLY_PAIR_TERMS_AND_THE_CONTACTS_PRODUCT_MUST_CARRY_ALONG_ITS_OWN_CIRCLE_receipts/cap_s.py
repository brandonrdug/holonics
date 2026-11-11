# Host ruler: the field's stored locked faces multiplied into a count reader's law, renormalized (the guide's test before saying the field holds a ruler's law).
import numpy as np, os, sys, time
exec(open('cap_q.py').read().split("z=np.load('train.npz')")[0].replace("part=sys.argv[1]","part='t'"))
t0=time.time(); z=np.load('train.npz'); xT=z['x'].astype(np.int64); sT=z['seg']; xH,sH=load('HELD128.txt'); st,uid,pre,uh,useg,ulen,pos=units(xH,sH)
uni=np.bincount(xT,minlength=B).astype(float)+0.5; uni/=uni.sum()
def law(chain):
    P=np.tile(uni[:100],(len(xH),1)); P/=P.sum(1,keepdims=True)
    for offs in chain:
        M=fit(ctx(xT,sT,offs),xT); c=ctx(xH,sH,offs); cols=[]
        for a in range(100):
            n,m,d=look(M,c,np.full(len(xH),a,np.int64)); cols.append(m)
        m=np.stack(cols,1).astype(float); lam=np.maximum(d,1).astype(float)[:,None]; n=n.astype(float)[:,None]
        P=np.where(n>0,(m+lam*P)/(n+lam),P); del M
    return P/P.sum(1,keepdims=True)
root=os.environ['HOLONICS_VISIT']+'/'   # the directory that holds design's locked visits, ct8/ and rt4/
dt=np.dtype([('problem','<u4'),('place','<u4'),('stop','u1'),('letter','<u2'),('face','<u2',(100,)),('chart','<i4',(64,))])
idx=np.arange(len(xH)); y=np.minimum(xH,99)
def code(P): return -np.log(np.maximum(P[idx,y],1e-12))
for nm,chain in (('two letters each side',[(-1,1),(-2,-1,1,2)]),('four letters on the left',[(-1,),(-2,-1),(-3,-2,-1),(-4,-3,-2,-1)])):
    R=law(chain); cr=code(R)
    print('ruler, %s: mean %.4f; at unit starts %.4f (share %.3f), inside units %.4f   %.0fs'%(nm,cr.mean(),cr[st].mean(),cr[st].sum()/cr.sum(),cr[~st].mean(),time.time()-t0),flush=True)
    for arm in sys.argv[1:]:
        r=np.fromfile(root+arm+'/held.bin',dtype=dt); r=r[np.lexsort((r['place'],r['problem']))]
        F=(r['face'].astype(float)+0.5)/65536.0; F/=F.sum(1,keepdims=True); cf=code(F)
        for w in (0.5,1.0):
            G=F*R**w; G/=G.sum(1,keepdims=True); cg=code(G)
            print('   %s: field %.4f | field x ruler^%.1f %.4f (at unit starts %.4f, inside units %.4f) | half-and-half mixture %.4f'%(arm,cf.mean(),w,cg.mean(),cg[st].mean(),cg[~st].mean(),code(0.5*F+0.5*R).mean()),flush=True)
print('%.0fs'%(time.time()-t0))
