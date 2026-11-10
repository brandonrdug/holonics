# Two-grain count ruler, left only: the near pair (places -2,-1) kept letter for letter, the far pair (places -4,-3) read only
# as one of K classes. Classes are located on TRAIN: far pairs followed alike over the next three letters (weighted k-means on
# the square roots of the three following letters' distributions), then PASSES rounds of reassignment, each far pair to the
# class under which TRAIN's next letters code least. Cells are (class, near pair, letter); Witten-Bell onto the two-back chain.
# Usage: python3 cap_d.py K PASSES [hash]      A ruler on host text, never machinery.
import numpy as np, time, sys, os
t0=time.time(); K=int(sys.argv[1]); PASSES=int(sys.argv[2]); HASH=len(sys.argv)>3
exec(open('yard.py').read().split("xT,sT=load")[0])
xH,sH=load('HELD128.txt')
CE='cap_d_cells.npz'
if not os.path.exists(CE):
    z=np.load('train.npz'); xT=z['x'].astype(np.int64); sT=z['seg']
    uni=np.bincount(xT,minlength=B).astype(float)+0.5; uni/=uni.sum()
    M1=fit(ctx(xT,sT,(-1,)),xT); M2=fit(ctx(xT,sT,(-2,-1)),xT)
    near=ctx(xT,sT,(-2,-1)); far=ctx(xT,sT,(-4,-3))
    uk,N=np.unique((far*(B*B)+near)*B+xT,return_counts=True); del near,far
    np.savez(CE,uk=uk,N=N,uni=uni,**{'M1_%d'%i:a for i,a in enumerate(M1)},**{'M2_%d'%i:a for i,a in enumerate(M2)})
z=np.load(CE); uk=z['uk']; N=z['N'].astype(float); uni=z['uni']; M1=tuple(z['M1_%d'%i] for i in range(5)); M2=tuple(z['M2_%d'%i] for i in range(5))
cx=uk%B; cn=(uk//B)%(B*B); cf=uk//(B*B*B)
def two_back(near,x):
    P=uni[x].copy()
    for M,c in ((M1,near%B),(M2,near)):
        n,m,d=look(M,c,x); lam=np.maximum(d,1).astype(float); P=np.where(n>0,(m+lam*P)/(n+lam),P)
    return P
P2=two_back(cn,cx)
uf,fi=np.unique(cf,return_inverse=True); un,ni=np.unique(cn,return_inverse=True); u3,c3=np.unique(cn*B+cx,return_inverse=True)
near3=np.searchsorted(un,u3//B); nu,nn,n3=len(uf),len(un),len(u3); wf=np.bincount(fi,weights=N)
nearH=ctx(xH,sH,(-2,-1)); farH=ctx(xH,sH,(-4,-3)); P2h=two_back(nearH,xH)
def read(cls):
    c=cls[fi]*(B*B)+cn; up,inv=np.unique(c*B+cx,return_inverse=True); npair=np.bincount(inv,weights=N)
    uc,invc=np.unique(up//B,return_inverse=True); nc=np.bincount(invc,weights=npair); dc=np.bincount(invc)
    j=np.searchsorted(uf,farH); j[j>=nu]=0; seen=uf[j]==farH
    n,m,d=look((uc,nc,up,npair,dc),np.where(seen,cls[j]*(B*B)+nearH,-1),xH)
    lam=np.maximum(d,1).astype(float); P=np.where(n>0,(m+lam*P2h)/(n+lam),P2h); L=-np.log(P)
    return L.mean(),L[sH<32].mean(),len(up)
def show(tag,cls):
    a,b,c=read(cls); print('%-46s K=%-5d HELD128 %.4f   held 0-31 %.4f   cells %7d   %.0fs'%(tag,len(np.unique(cls)),a,b,c,time.time()-t0)); sys.stdout.flush()
if K==0:   # references in the same back-off: two back alone, far pair's near letter (-3) as the class, the far pair itself
    print('two back alone: HELD128 %.4f  held 0-31 %.4f  cells %d'%(-np.log(P2h).mean(),-np.log(P2h[sH<32]).mean(),len(M2[2])))
    show('class = the letter at -3',uf%B); show('class = the far pair itself',np.arange(nu)); sys.exit()
if HASH:
    cls=np.random.default_rng(7).integers(0,K,nu); show('classes by a hash of the far pair',cls); sys.exit()
F=np.zeros((nu,3*B))
for b,let in enumerate((cn//B,cn%B,cx)): F[:,b*B:(b+1)*B]=np.bincount(fi*B+let,weights=N,minlength=nu*B).reshape(nu,B)
for b in range(3): F[:,b*B:(b+1)*B]/=np.maximum(F[:,b*B:(b+1)*B].sum(1,keepdims=True),1e-300)
F=np.sqrt(F); order=np.argsort(-wf); cen=F[order[:K]].copy(); cls=np.zeros(nu,np.int64)
for it in range(20):
    dist=(cen**2).sum(1)[None,:]-2*F@cen.T; new=dist.argmin(1)
    if it and (new!=cls).mean()<1e-3: cls=new; break
    cls=new
    for b in range(0,3*B,B*3): pass
    W=np.zeros((K,3*B)); np.add.at(W,cls,F*wf[:,None]); s=np.bincount(cls,weights=wf,minlength=K)
    ok=s>0; cen[ok]=W[ok]/s[ok,None]
show('located: followed alike (k-means)',cls)
Nl=N
for p in range(PASSES):
    S=np.empty((nu,K)); kc=cls[fi]
    for k in range(K):
        sel=kc==k
        if not sel.any(): S[:,k]=-np.inf; continue
        Ck=np.bincount(c3[sel],weights=N[sel],minlength=n3); Cn=np.bincount(ni[sel],weights=N[sel],minlength=nn)
        Dn=np.bincount(near3[np.unique(c3[sel])],minlength=nn); n=Cn[ni]; lam=np.maximum(Dn[ni],1).astype(float)
        P=np.where(n>0,(Ck[c3]+lam*P2)/(n+lam),P2); S[:,k]=np.bincount(fi,weights=N*np.log(P),minlength=nu)
    new=S.argmax(1); moved=(new!=cls); mass=wf[moved].sum()/wf.sum(); cls=new
    show('located: reassigned, pass %d (moved %.3f of mass)'%(p+1,mass),cls)
    np.save('cap_d_cls_%d.npy'%K,cls)
    if time.time()-t0>140: break
