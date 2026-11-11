# Host ruler for the lens of 2026-11-10 23:49Z (a longer word is a larger founded unit; coarse graining): never machinery.
# Question: past a unit's interior, what do contexts that end at unit boundaries read, level for level, beside contexts of fixed letter depth?
# A unit here is the ruler's own cut: a run of word letters (digits, letters, underscore), a run of one repeated space-class letter, or one other letter.
# Fitted on TRAIN, read on HELD128 at the places with four letters of their passage before them (42,960, as cap_p.py). Witten-Bell backoff down each chain.
import numpy as np, time, sys
exec(open('yard.py').read().split("xT,sT=load")[0])
t0=time.time(); part=sys.argv[1]
M1=np.uint64(0x9E3779B97F4A7C15); MI=np.uint64(pow(0x9E3779B97F4A7C15,-1,2**64)); C1=np.uint64(0xD6E8FEB86659FD93); C2=np.uint64(0xA24BAED4963EE407)
def kinds():
    k=np.zeros(B,np.int64)  # 0 space-class, 1 word, 2 other
    for i in range(B):
        if i>=VOID: k[i]=2; continue
        b=cl[i]
        if b in (10,32,9,13): k[i]=0
        elif (48<=b<=57) or (65<=b<=90) or (97<=b<=122) or b==95: k[i]=1
        else: k[i]=2
    return k
KIND=kinds()
def units(x,seg):
    n=len(x); k=KIND[x]; st=np.ones(n,bool)
    same=(seg[1:]==seg[:-1])&(k[1:]==k[:-1])&((k[1:]==1)|((k[1:]==0)&(x[1:]==x[:-1])))
    st[1:]=~same
    ar=np.arange(n); us=np.maximum.accumulate(np.where(st,ar,0)); uid=np.cumsum(st)-1
    with np.errstate(over='ignore'):
        pw=np.cumprod(np.full(n,M1,np.uint64)); pw=np.concatenate([[np.uint64(1)],pw[:-1]])
        ipw=np.cumprod(np.full(n,MI,np.uint64)); ipw=np.concatenate([[np.uint64(1)],ipw[:-1]])
        Hc=np.cumsum((x.astype(np.uint64)+np.uint64(1))*pw)
        Hm=np.concatenate([[np.uint64(0)],Hc])          # Hm[i] = sum over places < i
        pre=(Hm[ar]-Hm[us])*ipw[us]                      # letters of the unit before this place
        pre=(pre+C1)*C2+(ar-us).astype(np.uint64)
        s=np.flatnonzero(st); e=np.concatenate([s[1:],[n]])
        uh=(Hm[e]-Hm[s])*ipw[s]; uh=(uh+C2)*C1+(e-s).astype(np.uint64)
    useg=seg[s]; ulen=e-s
    return st,uid,pre,uh,useg,ulen,ar-us
def unit_keys(x,seg,K):
    # Every context is a function of the letters before the place alone: the cut is drawn on the prefix, never with the letter read.
    # (The first run drew it with the letter read, which told the context that letter's kind; cap_q_read_leak.out keeps that run.)
    st,uid,pre,uh,useg,ulen,pos=units(x,seg)
    n=len(x); ar=np.arange(n); us=np.maximum.accumulate(np.where(st,ar,0))
    has=np.zeros(n,bool); has[1:]=seg[1:]==seg[:-1]          # a letter of the same passage stands before the place
    p=np.where(has,ar-1,0); s0=us[p]; j=uid[p]
    with np.errstate(over='ignore'):
        pw=np.cumprod(np.full(n,M1,np.uint64)); pw=np.concatenate([[np.uint64(1)],pw[:-1]])
        ipw=np.cumprod(np.full(n,MI,np.uint64)); ipw=np.concatenate([[np.uint64(1)],ipw[:-1]])
        Hm=np.concatenate([[np.uint64(0)],np.cumsum((x.astype(np.uint64)+np.uint64(1))*pw)])
        tr=(Hm[ar]-Hm[s0])*ipw[s0]; tl=np.where(has,ar-s0,0)
        tr=np.where(has,(tr+C1)*C2+tl.astype(np.uint64),np.uint64(0x7654321))
    keys=[tr.copy()]; reach=[tl.astype(np.int64).copy()]
    PADH=np.uint64(0x1234567); k=tr.copy(); r=tl.astype(np.int64).copy()
    with np.errstate(over='ignore'):
        for q in range(1,K+1):
            i=j-q; ok=has&(i>=0); ii=np.where(ok,i,0); ok&=(useg[ii]==seg)
            u=np.where(ok,uh[ii],PADH); r=r+np.where(ok,ulen[ii],0)
            k=(k*C1+u+np.uint64(1))*C2
            keys.append(k.copy()); reach.append(r.copy())
    return [(q>>np.uint64(8)).astype(np.int64) for q in keys],reach,st,pos
def letter_keys(x,seg,N):
    keys=[]; g=np.zeros(len(x),np.uint64)
    with np.errstate(over='ignore'):
        for d in range(1,N+1):
            g=(g*C1+nb(x,seg,-d).astype(np.uint64)+np.uint64(1))*C2
            keys.append((g>>np.uint64(8)).astype(np.int64))
    return keys
z=np.load('train.npz'); xT=z['x'].astype(np.int64); sT=z['seg']; xH,sH=load('HELD128.txt')
sel=np.arange(4,len(xH)); sel=sel[sH[sel]==sH[sel-4]]
def levels(kT,kH,tag):
    out={}
    for i,(a,b) in enumerate(zip(kT,kH)):
        M=fit(a,xT); n,m,d=look(M,b,xH); out['n%d'%i]=n[sel]; out['m%d'%i]=m[sel]; out['d%d'%i]=d[sel]; out['c%d'%i]=np.array([len(M[0]),len(M[2])]); del M
        print('%s level %d: contexts %d cells %d  %.0fs'%(tag,i,out['c%d'%i][0],out['c%d'%i][1],time.time()-t0),flush=True)
    return out
if part=='L':
    N=int(sys.argv[2]); o=levels(letter_keys(xT,sT,N),letter_keys(xH,sH,N),'letters'); np.savez('cap_q_L.npz',**o)
if part=='U':
    K=int(sys.argv[2]); kT,rT,stT,posT=unit_keys(xT,sT,K); kH,rH,stH,posH=unit_keys(xH,sH,K)
    print('TRAIN units a place %.4f; word runs: mean length %.2f; HELD units a place %.4f'%(stT.mean(),(KIND[xT]==1).sum()/max(1,(stT&(KIND[xT]==1)).sum()),stH.mean()),flush=True)
    o=levels(kT,kH,'units'); o['start']=stH[sel]; o['pos']=posH[sel]; o['kind']=KIND[xH][sel]
    for j,r in enumerate(rH): o['r%d'%j]=r[sel]
    np.savez('cap_q_U.npz',**o)
if part=='read':
    L=np.load('cap_q_L.npz'); U=np.load('cap_q_U.npz'); x=xH[sel]
    uni=np.bincount(xT,minlength=B).astype(float)+0.5; uni/=uni.sum()
    def chain(steps):
        P=uni[x].copy(); out=[]
        for (S,i) in steps:
            n,m,d=S['n%d'%i],S['m%d'%i],S['d%d'%i]; lam=np.maximum(d,1).astype(float)
            P=np.where(n>0,(m+lam*P)/(n+lam),P); out.append(-np.log(P))
        return out
    nL=len([k for k in L.files if k.startswith('n')]); nU=len([k for k in U.files if k.startswith('n')])
    st=U['start']; print('HELD places read %d; unit starts %.4f of them'%(len(x),st.mean()))
    cl_=chain([(L,i) for i in range(nL)])
    print('letter chain (levels = letters): '+' '.join('%d:%.4f'%(i+1,c.mean()) for i,c in enumerate(cl_)))
    cu=chain([(U,i) for i in range(nU)])
    print('unit chain (level 1 = the last unit before the place, whole or begun; then one more whole unit a level): '+' '.join('%d:%.4f'%(i+1,c.mean()) for i,c in enumerate(cu)))
    print('   its mean reach in letters: '+' '.join('%d:%.2f'%(i+1,U['r%d'%i].mean()) for i in range(nU)))
    for base in (4,8):
        cm=chain([(L,i) for i in range(base)]+[(U,i) for i in range(1,nU)])
        print('letters to %d, then the unit chain from its second level: '%base+' '.join('+%d:%.4f'%(i,c.mean()) for i,c in enumerate(cm[base-1:])))
    for nm,c in (('letters to 4',cl_[3]),('letters to 8',cl_[7]),('unit chain, 4 levels',cu[3]),('unit chain, all levels',cu[-1])):
        print('   %-24s at unit starts %.4f (share of the code %.3f), inside units %.4f'%(nm,c[st].mean(),c[st].sum()/c.sum(),c[~st].mean()))
    k=U['kind']
    for nm,c in (('letters to 4',cl_[3]),('unit chain, all levels',cu[-1])):
        print('   %-24s by kind of the letter read: space-class %.4f, word %.4f, other %.4f'%(nm,c[k==0].mean(),c[k==1].mean(),c[k==2].mean()))
print('%.0fs'%(time.time()-t0))
