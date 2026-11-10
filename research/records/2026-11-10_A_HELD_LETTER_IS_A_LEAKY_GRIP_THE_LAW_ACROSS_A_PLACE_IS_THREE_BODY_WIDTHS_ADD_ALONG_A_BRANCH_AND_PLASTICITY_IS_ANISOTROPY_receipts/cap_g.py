# Host ruler (never machinery; floats, analysis only): the best reader of a place built from pair contacts alone,
# Q(x|L,R) ~ a(L,x) b(x,R), fitted by conditional likelihood on TRAIN, read on HELD128. Against it the joint table's code
# measures the three-body part of the law across a place. Usage: cap_g.py K [seconds]  (K letters each side)
import numpy as np, time, sys, os, pickle
exec(open('yard.py').read().split("xT,sT=load")[0])
z=np.load('train.npz'); xT=z['x'].astype(np.int64); sT=z['seg']; xH,sH=load('HELD128.txt'); t0=time.time(); A=100
K=int(sys.argv[1]); BUD=float(sys.argv[2]) if len(sys.argv)>2 else 110
oL=tuple(range(-K,0)); oR=tuple(range(1,K+1))
uL,iL=np.unique(ctx(xT,sT,oL),return_inverse=True); uR,iR=np.unique(ctx(xT,sT,oR),return_inverse=True); nL,nR=len(uL),len(uR)
uk,ik=np.unique(iL.astype(np.int64)*nR+iR,return_inverse=True); nk=len(uk); Lc=uk//nR; Rc=uk%nR
uc,nc=np.unique(ik*A+xT,return_counts=True); cnt=np.zeros((nk,A),np.float32); cnt[uc//A,uc%A]=nc; n=cnt.sum(1); N=float(n.sum())
del iL,iR,ik,uc,nc
def agg(idx,m):
    o=np.argsort(idx,kind='stable'); st=np.searchsorted(idx[o],np.arange(m)); return lambda G: np.add.reduceat(G[o],st,axis=0)
aL=agg(Lc,nL); aR=agg(Rc,nR)
uni=np.bincount(xT,minlength=B).astype(np.float64)[:A]+0.5; uni/=uni.sum()
ck='cap_g_%d.pkl'%K
if os.path.exists(ck): a,b,ma,va,mb,vb,step,hist=pickle.load(open(ck,'rb'))
else:
    cl=aL(cnt); cr=aR(cnt)
    a=np.log((cl+0.5)/(cl.sum(1,keepdims=True)+50)).astype(np.float32); b=(np.log((cr+0.5)/(cr.sum(1,keepdims=True)+50))-np.log(uni)[None,:]).astype(np.float32)
    ma=np.zeros_like(a); va=np.zeros_like(a); mb=np.zeros_like(b); vb=np.zeros_like(b); step=0; hist=[]
# held: contexts seen in TRAIN read from the tables, the others from the Witten-Bell branch product
cLh=ctx(xH,sH,oL); cRh=ctx(xH,sH,oR); jL=np.searchsorted(uL,cLh); jL[jL>=nL]=0; jR=np.searchsorted(uR,cRh); jR[jR>=nR]=0
seen=(uL[jL]==cLh)&(uR[jR]==cRh); IH=np.arange(len(xH))
def held():
    Z=a[jL].astype(np.float64)+b[jR]; Z-=Z.max(1,keepdims=True); lp=Z[IH,xH]-np.log(np.exp(Z).sum(1))
    return -lp[seen].mean(), seen.mean()
print('K=%d left contexts %d right contexts %d joint contexts %d cells of the two pair tables %d  %.0fs'%(K,nL,nR,nk,int((aL(cnt)>0).sum()+(aR(cnt)>0).sum()),time.time()-t0),flush=True)
while time.time()-t0<BUD:
    Z=a[Lc]+b[Rc]; Z-=Z.max(1,keepdims=True); np.exp(Z,out=Z); s=Z.sum(1,keepdims=True); Z/=s
    loss=-float((cnt*np.log(np.maximum(Z,1e-30))).sum())/N
    Z*=n[:,None]; Z-=cnt; Z/=N; ga=aL(Z); gb=aR(Z); del Z
    step+=1; lr=0.1 if step<=40 else (0.03 if step<=120 else 0.01); al=lr*np.sqrt(1-0.999**step)/(1-0.9**step)
    ma=0.9*ma+0.1*ga; va=0.999*va+0.001*ga*ga; a-=(al*ma/(np.sqrt(va)+1e-12)).astype(np.float32)
    mb=0.9*mb+0.1*gb; vb=0.999*vb+0.001*gb*gb; b-=(al*mb/(np.sqrt(vb)+1e-12)).astype(np.float32)
    if step%5==0 or step==1:
        h,sh=held(); hist.append((step,loss,h)); print('  step %3d  TRAIN %.4f  HELD128 (seen contexts, share %.4f) %.4f   %.0fs'%(step,loss,sh,h,time.time()-t0),flush=True)
pickle.dump((a,b,ma,va,mb,vb,step,hist),open(ck,'wb'))
print('saved at step',step,' best HELD so far %.4f at step %d'%min((h,s) for s,l,h in hist) if hist else '')
