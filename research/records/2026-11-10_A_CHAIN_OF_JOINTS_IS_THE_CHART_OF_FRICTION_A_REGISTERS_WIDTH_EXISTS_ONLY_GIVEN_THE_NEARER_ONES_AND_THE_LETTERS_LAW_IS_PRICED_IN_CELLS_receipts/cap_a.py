import numpy as np, time, pickle
t0=time.time()
exec(open('yard.py').read().split("xT,sT=load")[0])
z=np.load('train.npz'); xT=z['x'].astype(np.int64); sT=z['seg']
xH,sH=load('HELD128.txt')
o1,o2=(-1,1),(-2,-1,1,2)
cT1,cT2=ctx(xT,sT,o1),ctx(xT,sT,o2); cH1,cH2=ctx(xH,sH,o1),ctx(xH,sH,o2)
uni=np.bincount(xT,minlength=B).astype(float)+0.5; uni/=uni.sum()
M1=fit(cT1,xT); M2=fit(cT2,xT)
def wb(M,c,a,P):
    n,m,d=look(M,c,a); lam=np.maximum(d,1).astype(float)
    return np.where(n>0,(m+lam*P)/(n+lam),P), n
P1,_=wb(M1,cH1,xH,uni[xH]); P2,nH=wb(M2,cH2,xH,P1)
print('TRAIN places',len(xT),'HELD places',len(xH),'table1 %.4f table2 %.4f'%(-np.log(P1).mean(),-np.log(P2).mean()))
uc,nc=M2[0],M2[1]
print('distinct contexts',len(uc),'context-letter cells',len(M2[2]),'  %.1fs'%(time.time()-t0))
print('counts of counts (contexts seen r times): share of contexts | of TRAIN places | of HELD places | HELD code table1 | table2')
bands=[(0,0),(1,1),(2,2),(3,9),(10,99),(100,999),(1000,9999),(10000,10**9)]
for lo,hi in bands:
    selc=(nc>=lo)&(nc<=hi); selh=(nH>=lo)&(nH<=hi)
    print('  %6d..%-10d %7.4f  %7.4f  %7.4f   %6.3f  %6.3f'%(lo,hi,selc.mean() if lo>0 else 0,nc[selc].sum()/len(xT) if lo>0 else 0,selh.mean(),-np.log(P1[selh]).mean() if selh.any() else 0,-np.log(P2[selh]).mean() if selh.any() else 0))
order=np.argsort(-nc,kind='stable'); rank=np.empty(len(uc),np.int64); rank[order]=np.arange(len(uc))
i=np.searchsorted(uc,cH2); i[i>=len(uc)]=0; seen=uc[i]==cH2; rH=np.where(seen,rank[i],len(uc)+1)
# cells per context, cumulative in rank order
cells_ctx=M2[4]  # distinct letters per context, aligned with np.unique(up//B) == uc
cum=np.cumsum(cells_ctx[order]); cumpl=np.cumsum(nc[order])
print('table cut to its k most frequent contexts (others read by table1): k | cells kept | TRAIN places covered | HELD places covered | HELD code')
out=[]
for k in [0,100,300,1000,3000,10000,30000,100000,300000,len(uc)]:
    k=min(k,len(uc)); keep=rH<k
    P=np.where(keep,P2,P1); code=-np.log(P).mean()
    out.append((k,int(cum[k-1]) if k else 0,float(cumpl[k-1]/len(xT)) if k else 0.0,float(keep.mean()),float(code)))
    print('  %8d  %9d  %6.4f  %6.4f  %7.4f'%out[-1])
pickle.dump(out,open('cap_a.pkl','wb'))
print('done %.1fs'%(time.time()-t0))
