# The additive yardstick: logits = sum over offsets d of a row W_d[letter at t+d] + bias. No joint cells at all.
# Fit on a spread TRAIN sample (even problems), read on held 0-31, held 128 and TRAIN odd. Host floats, analysis only.
import os, sys, numpy as np, time, pickle
exec(open('yard.py').read().split("def fit(")[0])
K=int(sys.argv[1]); tag=sys.argv[2]; EPOCHS=int(sys.argv[3])
offs=[d for k in range(1,K+1) for d in (-k,k)]
xT,sT=load('TRAIN.txt'); xH,sH=load('HELD128.txt')
rng=np.random.default_rng(0)
ev=np.flatnonzero(sT%2==0); od=np.flatnonzero(sT%2==1)
tr=np.sort(rng.choice(ev,1200000,replace=False)); te=np.sort(rng.choice(od,300000,replace=False))
def feats(x,seg,idx): return np.stack([nb(x,seg,d)[idx] for d in offs],1).astype(np.int16)
CT=feats(xT,sT,tr); YT=xT[tr].astype(np.int16); CO=feats(xT,sT,te); YO=xT[te].astype(np.int16)
CH=feats(xH,sH,np.arange(len(xH))); YH=xH.astype(np.int16)
nd=len(offs); W=np.zeros((nd,B,100),np.float32); b=np.log(np.bincount(YT,minlength=100)+0.5).astype(np.float32); b-=b.mean()
ck='add_%s.pkl'%tag
ep0=0
if os.path.exists(ck): W,b,m,v,mb,vb,step,ep0=pickle.load(open(ck,'rb'))
else: m=np.zeros_like(W); v=np.zeros_like(W); mb=np.zeros_like(b); vb=np.zeros_like(b); step=0
def logits(C):
    z=np.broadcast_to(b,(len(C),100)).copy()
    for j in range(nd): z+=W[j][C[:,j]]
    return z
def code(C,Y,sel=None):
    tot=0.0;n=0
    for s in range(0,len(C),100000):
        z=logits(C[s:s+100000]); z-=z.max(1,keepdims=True); lp=z[np.arange(len(z)),Y[s:s+100000]]-np.log(np.exp(z).sum(1))
        if sel is not None: lp=lp[sel[s:s+100000]]
        tot-=lp.sum(); n+=len(lp)
    return tot/n
lr=0.05; bs=50000; t0=time.time()
for ep in range(ep0,EPOCHS):
    perm=rng.permutation(len(CT))
    for s in range(0,len(CT),bs):
        idx=perm[s:s+bs]; C=CT[idx]; Y=YT[idx]
        z=logits(C); z-=z.max(1,keepdims=True); p=np.exp(z); p/=p.sum(1,keepdims=True); p[np.arange(len(p)),Y]-=1; p/=len(p)
        step+=1; a=lr*np.sqrt(1-0.999**step)/(1-0.9**step)
        gb=p.sum(0); mb=0.9*mb+0.1*gb; vb=0.999*vb+0.001*gb*gb; b-=a*mb/(np.sqrt(vb)+1e-8)
        for j in range(nd):
            oh=np.zeros((len(C),B),np.float32); oh[np.arange(len(C)),C[:,j]]=1; g=oh.T@p
            m[j]=0.9*m[j]+0.1*g; v[j]=0.999*v[j]+0.001*g*g; W[j]-=a*m[j]/(np.sqrt(v[j])+1e-8)
    if ep==EPOCHS//2: lr=0.01
    pickle.dump((W,b,m,v,mb,vb,step,ep+1),open(ck,'wb'))
    print('K=%d epoch %d  %.0fs  train-sample %.4f  TRAIN odd %.4f  held128 %.4f  held 0-31 %.4f'%(K,ep+1,time.time()-t0,code(CT[:200000],YT[:200000]),code(CO,YO),code(CH,YH),code(CH,YH,sel=(sH<32))),flush=True)
    if time.time()-t0>150: break
