# Host ruler (never machinery; floats and fitted tables are the ruler's own): does a WORD OF SHARED STRIDES hold the joint law of a grip?
# cap_o.py G R SECONDS [STEP]: the target from G letters on its left.
#   logit(x) = U[x] + sum_k P_k[u_k, x] + Re sum_e gamma_e[x] m_e,
#   m_e = sum_k (prod_(j<k) alpha_e[u_j]) beta_e[u_k]   (k = 1 the nearest letter): the image of 0 under the moves z -> alpha_e[u] z + beta_e[u]
#   applied in passage order, far letter first.  ONE table alpha and ONE table beta for every offset: order comes from composition alone.
# Fitted on TRAIN's distinct contexts (Adam; many contexts: steps on contexts drawn in proportion to their places), read on HELD128.
# State is saved, so a call continues the last (the VM ends a call at three minutes).
import numpy as np, time, sys, os
exec(open('yard.py').read().split("xT,sT=load")[0])
z=np.load('train.npz'); xT=z['x'].astype(np.int64); sT=z['seg']; xH,sH=load('HELD128.txt')
g=int(sys.argv[1]); r=int(sys.argv[2]); budget=float(sys.argv[3]); lr=float(sys.argv[4]) if len(sys.argv)>4 else 0.02
tag='cap_o_g%d_r%d'%(g,r); t0=time.time(); C=B
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
LH=np.stack([xH[tH-j] for j in range(1,g+1)],1); yH=xH[tH]
rng=np.random.default_rng(0)
if os.path.exists(tag+'.npz'):
    S=dict(np.load(tag+'.npz'))
else:
    S={'U':np.zeros(C,np.float32),'P':np.zeros((g,C,C),np.float32),'step':np.zeros(1)}
    for nm in ('a','b'):
        ph=rng.uniform(0,2*np.pi,(C,r)); S[nm+'r']=np.cos(ph).astype(np.float32); S[nm+'i']=np.sin(ph).astype(np.float32)
    S['gr']=(0.01*rng.standard_normal((C,r))).astype(np.float32); S['gi']=(0.01*rng.standard_normal((C,r))).astype(np.float32)
    for k in list(S):
        if k!='step': S['m_'+k]=np.zeros_like(S[k]); S['v_'+k]=np.zeros_like(S[k])
names=[k for k in S if k!='step' and not k.startswith(('m_','v_'))]
def word(Lx):
    a=[(S['ar'][Lx[:,j]]+1j*S['ai'][Lx[:,j]]).astype(np.complex64) for j in range(g)]
    b=[(S['br'][Lx[:,j]]+1j*S['bi'][Lx[:,j]]).astype(np.complex64) for j in range(g)]
    pre=[np.ones_like(a[0])]
    for j in range(1,g): pre.append(pre[-1]*a[j-1])
    m=pre[0]*b[0]
    for k in range(1,g): m=m+pre[k]*b[k]
    return m,a,b,pre
def forward(Lx):
    lg=S['U'][None,:]+sum(S['P'][j][Lx[:,j]] for j in range(g))
    m,a,b,pre=word(Lx)
    return lg+m.real@S['gr'].T-m.imag@S['gi'].T,(m,a,b,pre)
def held():
    out=[]
    for s0 in range(0,len(tH),20000):
        lg,_=forward(LH[s0:s0+20000]); mx=lg.max(1,keepdims=True); lse=mx[:,0]+np.log(np.exp(lg-mx).sum(1))
        out.append(lse-lg[np.arange(len(lg)),yH[s0:s0+20000]])
    return float(np.concatenate(out).mean())
b1,b2,eps=0.9,0.999,1e-8
batch=8192 if nctx>20000 else 0
pn=n/N; rs=np.random.default_rng(1000+int(S['step'][0]))
while time.time()-t0<budget:
    step=int(S['step'][0])+1
    if batch:
        pick=rs.choice(nctx,batch,p=pn); Lx=L[pick]; cx=cnt[pick]/n[pick,None]; nx=np.ones(batch,np.float32); scale=float(batch)
    else:
        Lx=L; cx=cnt; nx=n; scale=N
    lg,(m,a,b,pre)=forward(Lx); mx=lg.max(1,keepdims=True); e=np.exp(lg-mx); se=e.sum(1,keepdims=True)
    loss=float(((np.log(se[:,0])+mx[:,0])*nx-(cx*lg).sum(1)).sum()/scale); d=((e/se*nx[:,None]-cx)/scale).astype(np.float32)
    G={'U':d.sum(0),'P':np.zeros_like(S['P'])}
    for j in range(g): np.add.at(G['P'][j],Lx[:,j],d)
    G['gr']=d.T@m.real; G['gi']=-(d.T@m.imag)
    gz=(d@S['gr'])-1j*(d@S['gi'])
    for nm in ('ar','ai','br','bi'): G[nm]=np.zeros_like(S[nm])
    suf=[None]*g; suf[g-1]=np.zeros_like(m)
    for j in range(g-2,-1,-1): suf[j]=b[j+1]+a[j+1]*suf[j+1]
    for j in range(g):
        gb=gz*np.conj(pre[j]); np.add.at(G['br'],Lx[:,j],gb.real); np.add.at(G['bi'],Lx[:,j],gb.imag)
        if j<g-1:
            ga=gz*np.conj(pre[j]*suf[j]); np.add.at(G['ar'],Lx[:,j],ga.real); np.add.at(G['ai'],Lx[:,j],ga.imag)
    rate=lr*min(1.0,step/20)/np.sqrt(max(1.0,step/300))
    for k in names:
        S['m_'+k]=b1*S['m_'+k]+(1-b1)*G[k]; S['v_'+k]=b2*S['v_'+k]+(1-b2)*G[k]**2
        S[k]=(S[k]-rate*(S['m_'+k]/(1-b1**step))/(np.sqrt(S['v_'+k]/(1-b2**step))+eps)).astype(np.float32)
    S['step'][0]=step
    if step%100==0 or step<=2: print('step %d %s %.4f %.0fs'%(step,'batch' if batch else 'train',loss,time.time()-t0),flush=True)
loss=0.0
for s0 in range(0,nctx,20000):
    lg,_=forward(L[s0:s0+20000]); mx=lg.max(1,keepdims=True); loss+=float(((np.log(np.exp(lg-mx).sum(1))+mx[:,0])*n[s0:s0+20000]-(cnt[s0:s0+20000]*lg).sum(1)).sum())
loss/=N
np.savez(tag+'.npz',**S)
print('READ word g=%d r=%d step %d | contexts %d | train %.4f | held places %d | held %.4f | mean |alpha| %.3f | %.0fs'%(g,r,int(S['step'][0]),nctx,loss,len(tH),held(),float(np.hypot(S['ar'],S['ai']).mean()),time.time()-t0),flush=True)
