# Host ruler, step a: fit the count tables on the TRAIN problems outside the dumped sample.
import os, numpy as np, time, pickle
t0=time.time()
exec(open('yard.py').read().split("xT,sT=load")[0])
V=root+'.local/wt/qgchgu-sampler/.local/run/2026-11-10-contacts/visit/lap26/'
dt=np.dtype([('problem','<u4'),('place','<u4'),('stop','u1'),('letter','<u2'),('face','<u2',(100,)),('chart','<i4',(32,))])
assert dt.itemsize==339
xT,sT=load('TRAIN.txt'); xH,sH=load('HELD128.txt')
def starts(seg):
    n=np.bincount(seg); return np.concatenate([[0],np.cumsum(n)]),n
stT,nT=starts(sT); stH,nH=starts(sH)
R={}
for nm in ('held','train_even','train_odd'):
    r=np.memmap(V+nm+'.bin',dtype=dt,mode='r')
    st=stH if nm=='held' else stT; x=xH if nm=='held' else xT; ln=nH if nm=='held' else nT
    pr=np.asarray(r['problem']).astype(np.int64); pl=np.asarray(r['place']).astype(np.int64)
    gi=st[pr]+pl
    ok=(pl<ln[pr])
    same=(x[gi[ok]]==np.asarray(r['letter'])[ok]).mean()
    up=np.unique(pr)
    print(nm,'records',len(r),'problems',len(up),'place in range',ok.mean(),'letters equal text',same,'stops',int(np.asarray(r['stop']).sum()),'first problems',up[:8],'mod6',np.unique(up%6),'(idx//6)%2',np.unique((up//6)%2) if nm!='held' else '')
    R[nm]=(pr,pl,gi)
    np.save('gi_'+nm+'.npy',gi)
# tables fit on TRAIN problems outside the dumped train sets
used=np.zeros(len(nT),bool); used[np.unique(R['train_even'][0])]=True; used[np.unique(R['train_odd'][0])]=True
keep=~used[sT]
xF,sF=xT[keep],sT[keep]
print('fit places',len(xF),'of',len(xT),'problems',int((~used).sum()),time.time()-t0)
uni=np.bincount(xF,minlength=B).astype(float)+0.5; uni/=uni.sum()
both=[(-1,1),(-2,-1,1,2),(-3,-2,-1,1,2,3),(-4,-3,-2,-1,1,2,3,4)]
Ms=[fit(ctx(xF,sF,o),xF) for o in both]
pickle.dump((uni,both,Ms),open('tabs.pkl','wb'),protocol=4)
print('tables fit',[len(M[2]) for M in Ms],time.time()-t0)
