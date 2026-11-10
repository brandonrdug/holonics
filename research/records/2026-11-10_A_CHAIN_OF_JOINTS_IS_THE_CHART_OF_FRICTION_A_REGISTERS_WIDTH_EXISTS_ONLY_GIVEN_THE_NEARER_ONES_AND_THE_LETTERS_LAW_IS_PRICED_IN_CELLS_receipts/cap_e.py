# Register widths by distance, left only. For a distance D: the D-1 nearer letters kept letter for letter, the letter at -D read
# only as one of K classes (one class map for every context). Classes are located on TRAIN: weighted k-means on the square roots
# of the distributions of the D letters that follow the letter, then PASSES rounds of reassignment, each letter to the class under
# which TRAIN's next letters code least. Cells are (class, nearer letters, letter); Witten-Bell onto the (D-1)-back chain.
# Usage: python3 cap_e.py D [PASSES]        A ruler on host text, never machinery.
import numpy as np, time, sys, os
t0=time.time(); D=int(sys.argv[1]); PASSES=int(sys.argv[2]) if len(sys.argv)>2 else 3
exec(open('yard.py').read().split("xT,sT=load")[0])
xH,sH=load('HELD128.txt')
offs=lambda k: tuple(range(-k,0))
BN=B**(D-1)
CE='cap_e_cells_%d.npz'%D
if not os.path.exists(CE):
    z=np.load('train.npz'); xT=z['x'].astype(np.int64); sT=z['seg']
    uni=np.bincount(xT,minlength=B).astype(float)+0.5; uni/=uni.sum()
    Ms=[fit(ctx(xT,sT,offs(k)),xT) for k in range(1,D)]
    near=ctx(xT,sT,offs(D-1)) if D>1 else np.zeros(len(xT),np.int64); far=nb(xT,sT,-D)
    uk,N=np.unique((far*BN+near)*B+xT,return_counts=True); del near,far
    np.savez(CE,uk=uk,N=N,uni=uni,**{'M%d_%d'%(k,i):a for k,M in enumerate(Ms) for i,a in enumerate(M)})
z=np.load(CE); uk=z['uk']; N=z['N'].astype(float); uni=z['uni']; Ms=[tuple(z['M%d_%d'%(k,i)] for i in range(5)) for k in range(D-1)]
cx=uk%B; cn=(uk//B)%BN; cf=uk//(B*BN)
def chain(near,x):
    P=uni[x].copy()
    for k,M in enumerate(Ms):
        n,m,d=look(M,near%(B**(k+1)),x); lam=np.maximum(d,1).astype(float); P=np.where(n>0,(m+lam*P)/(n+lam),P)
    return P
Pp=chain(cn,cx)
un,ni=np.unique(cn,return_inverse=True); u3,c3=np.unique(cn*B+cx,return_inverse=True)
near3=np.searchsorted(un,u3//B); nn,n3=len(un),len(u3); wf=np.bincount(cf,weights=N,minlength=B)
nearH=ctx(xH,sH,offs(D-1)) if D>1 else np.zeros(len(xH),np.int64); farH=nb(xH,sH,-D); PpH=chain(nearH,xH)
base=-np.log(PpH).mean()
def read(cls):
    c=cls[cf]*BN+cn; up,inv=np.unique(c*B+cx,return_inverse=True); npair=np.bincount(inv,weights=N)
    uc,invc=np.unique(up//B,return_inverse=True); nc=np.bincount(invc,weights=npair); dc=np.bincount(invc)
    n,m,d=look((uc,nc,up,npair,dc),cls[farH]*BN+nearH,xH)
    lam=np.maximum(d,1).astype(float); P=np.where(n>0,(m+lam*PpH)/(n+lam),PpH); L=-np.log(P)
    return L.mean(),L[sH<32].mean(),len(up)
full,fullh,fullc=read(np.arange(B))
seen=int((wf>0).sum()); pf=wf[wf>0]/wf.sum()
print('D=%d  base (%d back) %.4f   whole letter %.4f   it adds %.4f   cells %d   letters seen at -D %d (entropy %.3f nats)   %.0fs'%(D,D-1,base,full,base-full,fullc,seen,-(pf*np.log(pf)).sum(),time.time()-t0)); sys.stdout.flush()
def show(tag,cls):
    a,b,c=read(cls); print('  D=%d %-30s K=%-3d HELD128 %.4f  holds %.3f  cells %7d  %.0fs'%(D,tag,len(np.unique(cls[wf>0])),a,(base-a)/(base-full),c,time.time()-t0)); sys.stdout.flush(); return (base-a)/(base-full)
F=np.zeros((B,D*B))
lets=[(cn//(B**j))%B for j in range(D-1)]+[cx]
for b,let in enumerate(lets): F[:,b*B:(b+1)*B]=np.bincount(cf*B+let,weights=N,minlength=B*B).reshape(B,B)
for b in range(D): F[:,b*B:(b+1)*B]/=np.maximum(F[:,b*B:(b+1)*B].sum(1,keepdims=True),1e-300)
F=np.sqrt(F); order=np.argsort(-wf)
out={}
for K in (2,4,8,16,32,64):
    if K>=seen: break
    h=show('hash',np.random.default_rng(7).integers(0,K,B))
    cen=F[order[:K]].copy(); cls=np.zeros(B,np.int64)
    for it in range(30):
        dist=(cen**2).sum(1)[None,:]-2*F@cen.T; new=dist.argmin(1)
        if it and (new==cls).all(): break
        cls=new; W=np.zeros((K,D*B)); np.add.at(W,cls,F*wf[:,None]); s=np.bincount(cls,weights=wf,minlength=K); ok=s>0; cen[ok]=W[ok]/s[ok,None]
    best=show('located (k-means)',cls)
    for p in range(PASSES):
        S=np.empty((B,K)); kc=cls[cf]
        for k in range(K):
            sel=kc==k
            if not sel.any(): S[:,k]=-np.inf; continue
            Ck=np.bincount(c3[sel],weights=N[sel],minlength=n3); Cn=np.bincount(ni[sel],weights=N[sel],minlength=nn)
            Dn=np.bincount(near3[np.unique(c3[sel])],minlength=nn); n=Cn[ni]; lam=np.maximum(Dn[ni],1).astype(float)
            P=np.where(n>0,(Ck[c3]+lam*Pp)/(n+lam),Pp); S[:,k]=np.bincount(cf,weights=N*np.log(P),minlength=B)
        new=S.argmax(1); new[wf==0]=cls[wf==0]
        if (new==cls).all(): break
        cls=new; best=max(best,show('located, reassigned %d'%(p+1),cls))
        if time.time()-t0>150: break
    out[K]=(h,best)
    if time.time()-t0>150: print('  stopped on time'); break
w=[K for K in sorted(out) if out[K][1]>=0.9]
print('D=%d  WIDTH (90%%): %s    held by K (hash, located): %s'%(D,w[0] if w else '>%d'%max(out),'  '.join('%d: %.2f, %.2f'%(K,out[K][0],out[K][1]) for K in sorted(out))))
