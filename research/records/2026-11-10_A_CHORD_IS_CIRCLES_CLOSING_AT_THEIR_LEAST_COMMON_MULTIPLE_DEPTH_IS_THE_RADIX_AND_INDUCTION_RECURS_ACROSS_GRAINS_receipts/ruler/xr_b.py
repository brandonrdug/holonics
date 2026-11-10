# Host ruler, step b: the count tables' distributions at each dumped place (usage: xr_b.py held 1).
import os, numpy as np, time, pickle, sys
t0=time.time()
exec(open('yard.py').read().split("xT,sT=load")[0])
V=root+'.local/wt/qgchgu-sampler/.local/run/2026-11-10-contacts/visit/lap26/'
dt=np.dtype([('problem','<u4'),('place','<u4'),('stop','u1'),('letter','<u2'),('face','<u2',(100,)),('chart','<i4',(32,))])
uni,both,Ms=pickle.load(open('tabs.pkl','rb'))
nm=sys.argv[1]; step=int(sys.argv[2])
x,seg=load('HELD128.txt' if nm=='held' else 'TRAIN.txt')
gi=np.load('gi_'+nm+'.npy')[::step]
r=np.memmap(V+nm+'.bin',dtype=dt,mode='r')
face=np.asarray(r['face'][::step]).astype(np.float32)/65536.0
let=np.asarray(r['letter'][::step]).astype(np.int64); stop=np.asarray(r['stop'][::step]).astype(bool)
N=len(gi); A=100
P=np.tile(uni[:A].astype(np.float64),(N,1))
out={}
for k,(offs,M) in enumerate(zip(both,Ms),1):
    c=ctx(x,seg,offs)[gi]
    Q=np.empty((N,A))
    for a in range(A):
        n,m,d=look(M,c,np.full(N,a,np.int64))
        lam=np.maximum(d,1).astype(float)
        Q[:,a]=np.where(n>0,(m+lam*P[:,a])/(n+lam),P[:,a])
    P=Q
    out['code%d'%k]=-np.log(P[np.arange(N),let])
    if k in (2,3): out['P%d'%k]=P.astype(np.float32)
    print(nm,'k',k,'table code',out['code%d'%k].mean(),'rowsum',P.sum(1).mean(),time.time()-t0,flush=True)
np.savez('xr_'+nm+'.npz',face=face,let=let,stop=stop,**out)
pf=np.maximum(face,2.0**-17); pf/=pf.sum(1,keepdims=True)
print(nm,'N',N,'field code',-np.log(pf[np.arange(N),let]).mean(),'letters only',-np.log(pf[np.arange(N),let])[~stop].mean(),'face sum',face.sum(1).mean())
