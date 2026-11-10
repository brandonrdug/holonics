import numpy as np, time, pickle, os
t0=time.time()
exec(open('yard.py').read().split("xT,sT=load")[0])
uni,both,Ms=pickle.load(open('tabs.pkl','rb'))
xH,sH=load('HELD128.txt'); gi=np.load('gi_held.npy'); pr=sH[gi]
z=np.load('xr_held.npz'); let=z['let']; N=len(let); A=100; I=np.arange(N)
P2=z['P2'].astype(np.float64)
c1=ctx(xH,sH,both[0])[gi]; c2=ctx(xH,sH,both[1])[gi]
P1=np.empty((N,A)); U=np.tile(uni[:A].astype(np.float64),(N,1))
for a in range(A):
    n,m,d=look(Ms[0],c1,np.full(N,a,np.int64)); lam=np.maximum(d,1).astype(float)
    P1[:,a]=np.where(n>0,(m+lam*U[:,a])/(n+lam),U[:,a])
uc,nc=Ms[1][0],Ms[1][1]
order=np.argsort(-nc,kind='stable'); rank=np.empty(len(uc),np.int64); rank[order]=np.arange(len(uc))
i=np.searchsorted(uc,c2); i[i>=len(uc)]=0; seen=uc[i]==c2
rH=np.where(seen,rank[i],len(uc)+1); nH=np.where(seen,nc[i],0)
print('tables fit outside the dumped sample: contexts',len(uc),'| table1 %.4f table2 %.4f'%(-np.log(P1[I,let]).mean(),-np.log(P2[I,let]).mean()),' %.1fs'%(time.time()-t0),flush=True)
np.savez('cap_a2_in.npz',P1=P1.astype(np.float32),rH=rH,nH=nH)
E=np.load('xr_e_out.npy'); names=['lap37','ctrl41','ct4']   # [state][0 field code, 1 product code] at each held record
ct=-np.log(P2[I,let])
print('by how often the context (two each side) occurs in the fitted TRAIN: share of HELD places | table1 | table2 | field (ct4) | product (ct4) | of the lack: lap37 ctrl41 ct4 | of what the field holds beyond (ct4)')
bands=[(0,0),(1,1),(2,2),(3,9),(10,99),(100,999),(1000,9999),(10000,10**9)]
tot=[(E[s][0]-E[s][1]).sum() for s in range(3)]
for lo,hi in bands:
    s=(nH>=lo)&(nH<=hi)
    print('  %6d..%-10d %6.4f | %6.3f | %6.3f | %6.3f | %6.3f | %6.3f %6.3f %6.3f | %6.3f'%(lo,hi,s.mean(),-np.log(P1[I,let][s]).mean(),ct[s].mean(),E[2][0][s].mean(),E[2][1][s].mean(),*[(E[k][0]-E[k][1])[s].sum()/tot[k] for k in range(3)],(ct-E[2][1])[s].sum()/(ct-E[2][1]).sum()))
print('lack in nats a place by band (ct4): '+' '.join('%.4f'%((E[2][0]-E[2][1])[(nH>=lo)&(nH<=hi)].sum()/N) for lo,hi in bands),'| total %.4f'%(tot[2]/N))
print('done %.1fs'%(time.time()-t0))
