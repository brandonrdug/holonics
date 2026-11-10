# Count ruler on scattered written letters: a uniformly random order of each held answer's places; each place is coded
# from the letters already written among its eight neighbours (four each side). Every subset of the eight neighbours has
# its own count table fit on all of TRAIN; Witten-Bell from far to near (near order -1,+1,-2,+2,...). Resumable.
import numpy as np, time, sys, os
t0=time.time(); BUDGET=float(sys.argv[1]) if len(sys.argv)>1 else 150.0
exec(open('yard.py').read().split("xT,sT=load")[0])
z=np.load('train.npz'); xT=z['x'].astype(np.int64); sT=z['seg']
xH,sH=load('HELD128.txt'); nH=len(xH)
OFF=[-1,1,-2,2,-3,3,-4,4]; D=4; ST='cap_b_state.npz'
if os.path.exists(ST):
    s=np.load(ST); Wb=s['Wb']; share=s['share']; n=s['n']; m=s['m']; d=s['d']; done=set(s['done'].tolist())
else:
    rng=np.random.default_rng(20261110)
    starts=np.flatnonzero(np.r_[True,sH[1:]!=sH[:-1]]); ends=np.r_[starts[1:],nH]
    R=np.empty((D,nH),np.int64); share=np.empty((D,nH))
    for k in range(D):
        for a,b in zip(starts,ends):
            p=rng.permutation(b-a); R[k,a:b]=p; share[k,a:b]=p/(b-a)
    Wb=np.zeros((D,nH),np.int64)
    for j,off in enumerate(OFF):
        for k in range(D):
            r=R[k]; t=np.full(nH,-1,np.int64); q=abs(off)
            if off<0: ok=sH[q:]==sH[:-q]; t[q:][ok]=r[:-q][ok]
            else: ok=sH[:-q]==sH[q:]; t[:-q][ok]=r[q:][ok]
            Wb[k]|=(t<r).astype(np.int64)<<j          # outside the answer (PAD) counts as written
    Wb=Wb.ravel(); share=share.ravel(); N=D*nH
    n=np.zeros((8,N),np.int32); m=np.zeros((8,N),np.int32); d=np.zeros((8,N),np.int32); done=set()
idx=np.tile(np.arange(nH),D); xi=xH[idx]
NT=[nb(xT,sT,o).astype(np.uint8) for o in OFF]; NH=[nb(xH,sH,o)[idx] for o in OFF]
masks=[M for M in range(1,256)]
masks.sort(key=lambda M:(M.bit_length(),M))
for M in masks:
    if M in done: continue
    if time.time()-t0>BUDGET: break
    top=M.bit_length()-1; offs=[j for j in range(8) if M>>j&1]
    sel=np.flatnonzero((Wb&((1<<(top+1))-1))==M)
    if len(sel):
        c=np.zeros(len(xT),np.int64)
        for j in offs: c*=B; c+=NT[j]
        T=fit(c,xT); del c
        ch=np.zeros(len(sel),np.int64)
        for j in offs: ch=ch*B+NH[j][sel]
        a,b_,e=look(T,ch,xi[sel]); n[top,sel]=a; m[top,sel]=b_; d[top,sel]=e; del T
    done.add(M)
np.savez(ST,Wb=Wb,share=share,n=n,m=m,d=d,done=np.array(sorted(done),np.int64))
print('masks done %d of 255   %.0fs'%(len(done),time.time()-t0))
if len(done)==255:
    uni=np.bincount(xT,minlength=B).astype(float)+0.5; uni/=uni.sum()
    P=uni[xi].copy()
    for j in range(8):
        has=((Wb>>j)&1==1)&(n[j]>0); lam=np.maximum(d[j],1).astype(float)
        P=np.where(has,(m[j]+lam*P)/(n[j]+lam),P)
    L=-np.log(P); np.save('cap_b_out.npy',np.stack([L,share,Wb.astype(float),idx.astype(float)]))
    print('order-averaged code %.4f nats a place over %d draws of the order (HELD128, %d places)'%(L.mean(),D,nH))
    for k in range(D): print('   draw %d: %.4f'%(k,L[k*nH:(k+1)*nH].mean()))
    h32=sH[idx]<32; print('   held 0-31: %.4f'%L[h32].mean())
    print('by share of the answer already written: tenth | places | code | mean written neighbours of 8')
    cnt=np.array([bin(int(w)).count('1') for w in Wb])
    for b in range(10):
        s_=(share>=b/10)&(share<(b+1)/10); print('   %d0-%d0%%  %7d  %.3f  %.2f'%(b,b+1,s_.sum(),L[s_].mean(),cnt[s_].mean()))
    print('by written neighbours among the nearest two (-1,+1): none | left only | right only | both')
    for v,name in ((0,'none'),(1,'left only'),(2,'right only'),(3,'both')):
        s_=(Wb&3)==v; print('   %-10s %7d  %.3f'%(name,s_.sum(),L[s_].mean()))
