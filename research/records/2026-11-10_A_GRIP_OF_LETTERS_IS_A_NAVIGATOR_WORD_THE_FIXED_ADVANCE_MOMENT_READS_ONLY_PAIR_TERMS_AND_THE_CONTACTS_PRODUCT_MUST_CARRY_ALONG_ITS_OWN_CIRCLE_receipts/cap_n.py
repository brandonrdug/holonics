# Host ruler (never machinery; floats and fitted tables are the ruler's own): can a product of per-letter factors hold the joint law of
# several written letters?  cap_n.py G R SECONDS [STEP]: the target from G letters on its left.
#   R = 0: the pair-only reader: logit(x) = U[x] + sum_k P_k[u_k, x] (one table a letter, added).
#   R > 0: that plus R complex products, one factor a letter and offset: + Re sum_e gamma_e[x] prod_k alpha_(e,k)[u_k].
# Fitted on TRAIN's distinct contexts (full batch, Adam), read on HELD128 beside the count tables' own chain (Witten-Bell).
# State is saved, so a call continues the last (the VM ends a call at three minutes).
import numpy as np, time, sys, os
exec(open('yard.py').read().split("xT,sT=load")[0])
z=np.load('train.npz'); xT=z['x'].astype(np.int64); sT=z['seg']; xH,sH=load('HELD128.txt')
g=int(sys.argv[1]); r=int(sys.argv[2]); budget=float(sys.argv[3]); lr=float(sys.argv[4]) if len(sys.argv)>4 else 0.02
tag='cap_n_g%d_r%d'%(g,r); t0=time.time(); C=B
def places(x,s):
    t=np.arange(g,len(x)); return t[s[t]==s[t-g]]
def keys(x,t):
    k=np.zeros(len(t),np.int64)
    for j in range(1,g+1): k=k*C+x[t-j]
    return k
tT=places(xT,sT); tH=places(xH,sH)
uk,inv=np.unique(keys(xT,tT),return_inverse=True); nctx=len(uk)
L=np.stack([(uk//C**(g-j))%C for j in range(1,g+1)],1)            # L[:, j-1]: the letter j places back
cnt=np.zeros((nctx,C),np.float32); np.add.at(cnt,(inv,xT[tT]),1.0); n=cnt.sum(1); N=float(n.sum())
order=[np.argsort(L[:,j],kind='stable') for j in range(g)]
starts=[np.flatnonzero(np.r_[True,np.diff(L[o,j])!=0]) for j,o in enumerate(order)]
present=[L[o,j][s] for j,(o,s) in enumerate(zip(order,starts))]
# the held places: contexts as letters (a context unseen in TRAIN still has letters)
LH=np.stack([xH[tH-j] for j in range(1,g+1)],1); yH=xH[tH]
rng=np.random.default_rng(0)
if os.path.exists(tag+'.npz'):
    S=dict(np.load(tag+'.npz'))
else:
    S={'U':np.zeros(C,np.float32),'P':np.zeros((g,C,C),np.float32),'step':np.zeros(1)}
    if r:
        ph=rng.uniform(0,2*np.pi,(g,C,r)); S['ar']=np.cos(ph).astype(np.float32); S['ai']=np.sin(ph).astype(np.float32)
        S['gr']=(0.01*rng.standard_normal((C,r))).astype(np.float32); S['gi']=(0.01*rng.standard_normal((C,r))).astype(np.float32)
    for k in list(S):
        if k!='step': S['m_'+k]=np.zeros_like(S[k]); S['v_'+k]=np.zeros_like(S[k])
names=[k for k in S if k!='step' and not k.startswith(('m_','v_'))]
def forward(Lx):
    lg=S['U'][None,:]+sum(S['P'][j][Lx[:,j]] for j in range(g))
    Z=None
    if r:
        Z=(S['ar'][0][Lx[:,0]]+1j*S['ai'][0][Lx[:,0]]).astype(np.complex64)
        for j in range(1,g): Z=Z*(S['ar'][j][Lx[:,j]]+1j*S['ai'][j][Lx[:,j]])
        lg=lg+Z.real@S['gr'].T-Z.imag@S['gi'].T
    return lg,Z
def held():
    out=[]
    for a in range(0,len(tH),20000):
        lg,_=forward(LH[a:a+20000]); m=lg.max(1,keepdims=True); lse=m[:,0]+np.log(np.exp(lg-m).sum(1))
        out.append(lse-lg[np.arange(len(lg)),yH[a:a+20000]])
    return float(np.concatenate(out).mean())
b1,b2,eps=0.9,0.999,1e-8
batch=8192 if nctx>20000 else 0                 # many contexts: steps on contexts drawn in proportion to their places (an unbiased covector)
pn=n/N; rs=np.random.default_rng(1000+int(S['step'][0]))
def covector(Lx,cx,nx,scale):
    lg,Z=forward(Lx); m=lg.max(1,keepdims=True); e=np.exp(lg-m); se=e.sum(1,keepdims=True)
    loss=float(((np.log(se[:,0])+m[:,0])*nx-(cx*lg).sum(1)).sum()/scale)
    return loss,(e/se*nx[:,None]-cx)/scale,Z
while time.time()-t0<budget:
    step=int(S['step'][0])+1
    if batch:
        pick=rs.choice(nctx,batch,p=pn); Lx=L[pick]; loss,d,Z=covector(Lx,cnt[pick]/n[pick,None],np.ones(batch,np.float32),float(batch))
        G={'U':d.sum(0),'P':np.zeros_like(S['P'])}
        for j in range(g): np.add.at(G['P'][j],Lx[:,j],d)
    else:
        Lx=L; loss,d,Z=covector(L,cnt,n,N)
        G={'U':d.sum(0),'P':np.zeros_like(S['P'])}
        for j in range(g): G['P'][j][present[j]]=np.add.reduceat(d[order[j]],starts[j],axis=0)
    if r:
        G['gr']=d.T@Z.real; G['gi']=-(d.T@Z.imag)
        gz=(d@S['gr'])-1j*(d@S['gi'])                                # dLoss/dZr + i dLoss/dZi
        G['ar']=np.zeros_like(S['ar']); G['ai']=np.zeros_like(S['ai'])
        for j in range(g):
            rest=np.ones_like(Z)
            for i in range(g):
                if i!=j: rest=rest*(S['ar'][i][Lx[:,i]]+1j*S['ai'][i][Lx[:,i]])
            ga=gz*np.conj(rest)
            if batch:
                np.add.at(G['ar'][j],Lx[:,j],ga.real); np.add.at(G['ai'][j],Lx[:,j],ga.imag)
            else:
                s2=np.add.reduceat(ga[order[j]],starts[j],axis=0); G['ar'][j][present[j]]=s2.real; G['ai'][j][present[j]]=s2.imag
    rate=lr*min(1.0,step/20)/np.sqrt(max(1.0,step/300))
    for k in names:
        S['m_'+k]=b1*S['m_'+k]+(1-b1)*G[k]; S['v_'+k]=b2*S['v_'+k]+(1-b2)*G[k]**2
        S[k]=(S[k]-rate*(S['m_'+k]/(1-b1**step))/(np.sqrt(S['v_'+k]/(1-b2**step))+eps)).astype(np.float32)
    S['step'][0]=step
    if step%100==0 or step<=2: print('step %d %s %.4f %.0fs'%(step,'batch' if batch else 'train',loss,time.time()-t0),flush=True)
loss=0.0
for a in range(0,nctx,20000):
    lg,_=forward(L[a:a+20000]); m=lg.max(1,keepdims=True); loss+=float(((np.log(np.exp(lg-m).sum(1))+m[:,0])*n[a:a+20000]-(cnt[a:a+20000]*lg).sum(1)).sum())
loss/=N
np.savez(tag+'.npz',**S)
# the count tables' own chain on the same places
uni=np.bincount(xT,minlength=C).astype(float)+0.5; uni/=uni.sum(); Pw=uni[xH].copy(); chain=[]
for depth in range(1,g+1):
    offs=tuple(range(-depth,0)); M=fit(ctx(xT,sT,offs),xT); nn,mm,dd=look(M,ctx(xH,sH,offs),xH); lam=np.maximum(dd,1).astype(float)
    Pw=np.where(nn>0,(mm+lam*Pw)/(nn+lam),Pw); chain.append(float(-np.log(Pw[tH]).mean())); del M
print('READ g=%d r=%d step %d | contexts %d | train %.4f | held places %d | held %.4f | count tables on the same places, depth 1..g: %s | %.0fs'%(g,r,int(S['step'][0]),nctx,loss,len(tH),held(),' '.join('%.4f'%c for c in chain),time.time()-t0),flush=True)
