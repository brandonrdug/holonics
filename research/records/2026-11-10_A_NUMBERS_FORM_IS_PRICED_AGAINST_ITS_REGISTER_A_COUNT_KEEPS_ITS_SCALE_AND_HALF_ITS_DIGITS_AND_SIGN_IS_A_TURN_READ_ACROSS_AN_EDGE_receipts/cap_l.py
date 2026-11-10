# Host ruler (never machinery): G23. The laws of the leading and the trailing decimal digit of the counts.
import numpy as np, time
exec(open('yard.py').read().split("xT,sT=load")[0])
z=np.load('train.npz'); xT=z['x'].astype(np.int64); sT=z['seg']; t0=time.time()
uc,nc,up,npair,dc=fit(ctx(xT,sT,(-2,-1,1,2)),xT)
c=npair.astype(np.int64)
def H(v,k):
    p=np.bincount(v,minlength=k).astype(float); p=p/p.sum(); p=p[p>0]; return -(p*np.log2(p)).sum()
lead=lambda v: (v//10**np.floor(np.log10(v)+1e-12).astype(np.int64))
for lo,hi in ((10,10**9),(10,99),(100,999),(1000,10**9)):
    s=(c>=lo)&(c<=hi); v=c[s]; L=lead(v); p=np.bincount(L,minlength=10)[1:]/len(v)
    print('counts %d..%d: cells %d | leading digit shares %s | entropy %.3f bits (Benford 2.876, flat 3.170)'%(lo,hi,len(v),' '.join('%.3f'%q for q in p),H(L,10)))
for lo,hi in ((10,99),(100,10**9),(100,999),(1000,10**9)):
    s=(c>=lo)&(c<=hi); v=c[s]; d=v%10; p=np.bincount(d,minlength=10)/len(v)
    print('counts %d..%d: cells %d | last digit shares %s | entropy %.4f bits (flat 3.3219; plug-in bias %.4f)'%(lo,hi,len(v),' '.join('%.3f'%q for q in p),H(d,10),9/(2*len(v)*np.log(2))))
s=c>=1000; v=c[s]; d=(v//10)%10; print('counts 1000 and over: tens digit entropy %.4f bits; last two digits %.4f of %.4f'%(H(d,10),H(v%100,100),np.log2(100)))
# the context totals: the same two faces
n=nc.astype(np.int64); s=n>=100; print('context totals 100 and over: %d | leading digit entropy %.3f, share of 1 %.3f | last digit entropy %.4f'%(s.sum(),H(lead(n[s]),10),np.mean(lead(n[s])==1),H(n[s]%10,10)))
print('done %ds'%(time.time()-t0))
