# Host rulers for the lens of 2026-11-10 22:15Z (rulers on text, never machinery; Witten-Bell chains fit on TRAIN):
#  mi   : the text's own information between two letters s places apart (TRAIN, both in one passage), shuffle floor subtracted
#  pin  : a written letter's worth to its neighbour by the letter's own surprise (HELD128)
#  auto : the place-by-place surprise of the reader of two letters each side, and of four on the left, against itself k places on
import numpy as np, time, sys
exec(open('yard.py').read().split("xT,sT=load")[0])
z=np.load('train.npz'); xT=z['x'].astype(np.int64); sT=z['seg']; xH,sH=load('HELD128.txt')
t0=time.time(); part=sys.argv[1]
uni=np.bincount(xT,minlength=B).astype(float)+0.5; uni/=uni.sum()
def probs(chain):
    P=uni[xH].copy()
    for offs in chain:
        M=fit(ctx(xT,sT,offs),xT); n,m,d=look(M,ctx(xH,sH,offs),xH); lam=np.maximum(d,1).astype(float)
        P=np.where(n>0,(m+lam*P)/(n+lam),P); del M
    return P
if part=='mi':
    rng=np.random.default_rng(0)
    def mi(a,b):
        N=len(a); J=np.bincount(a*B+b,minlength=B*B).reshape(B,B).astype(float); pa=J.sum(1); pb=J.sum(0)
        nz=J>0; E=(pa[:,None]*pb[None,:])[nz]; return float((J[nz]/N*np.log(J[nz]*N/E)).sum())
    f=np.bincount(xT,minlength=B)/len(xT); f=f[f>0]; print('TRAIN places %d  passages %d  entropy of one letter %.4f nats'%(len(xT),sT.max()+1,-(f*np.log(f)).sum()))
    S=list(range(1,41))+[44,48,52,56,60,64,72,80,96,112,128,160,192,256,320,384,512,768,1024]
    if len(sys.argv)>2: S=[s for s in S if int(sys.argv[2])<=s<=int(sys.argv[3])]
    print('  s | pairs | information | shuffle floor | net')
    for s in S:
        ok=sT[:-s]==sT[s:]; a=xT[:-s][ok]; b=xT[s:][ok]; I=mi(a,b); I0=mi(a,rng.permutation(b))
        print('%5d %9d %.5f %.5f %.5f'%(s,len(a),I,I0,I-I0),flush=True)
if part=='pin':
    p_skip=probs([(-2,)]); p_full=probs([(-2,),(-2,-1)]); p_pin=probs([(-1,)])
    t=np.arange(2,len(xH)); t=t[sH[t]==sH[t-2]]
    gain=np.log(p_full[t])-np.log(p_skip[t]); s=-np.log(p_pin[t-1])
    print('HELD places %d read %d | next letter given the letter two back %.4f, given both %.4f, mean gain %.4f | mean surprise of the pin %.4f'%(len(xH),len(t),-np.log(p_skip[t]).mean(),-np.log(p_full[t]).mean(),gain.mean(),s.mean()))
    for name,qs in (('quartile',4),('tenth',10)):
        e=np.quantile(s,np.linspace(0,1,qs+1)); b=np.minimum(np.searchsorted(e,s,side='right')-1,qs-1)
        print(' by %s of the pin\'s surprise: surprise of the pin | gain to the next letter | gain / surprise | share of the whole gain'%name)
        for k in range(qs):
            m=b==k; print('   %2d  %.3f  %.3f  %.3f  %.3f'%(k+1,s[m].mean(),gain[m].mean(),gain[m].mean()/s[m].mean(),gain[m].sum()/gain.sum()))
    print(' correlation of gain with the pin\'s surprise %.3f ; share of places where the gain exceeds the pin\'s surprise by 0.05: %.4f'%(np.corrcoef(gain,s)[0,1],(gain>s+0.05).mean()))
if part in('auto','auto4'):
    c=-np.log(probs([(-1,1),(-2,-1,1,2)] if part=='auto' else [(-1,),(-2,-1),(-3,-2,-1),(-4,-3,-2,-1)]))
    np.save('cap_m_%s.npy'%part,c)
    print('%s reader: HELD places %d mean code %.4f variance %.4f'%('two each side' if part=='auto' else 'four on the left',len(c),c.mean(),c.var()))
    print('   k | pairs | correlation | in standard errors')
    for k in (1,2,3,4,5,6,8,12,16,24,32,48,64,96,128,192,256):
        ok=sH[:-k]==sH[k:]; a=c[:-k][ok]; b=c[k:][ok]; r=np.corrcoef(a,b)[0,1]; print('%5d %7d %+.4f %+.1f'%(k,len(a),r,r*np.sqrt(len(a))))
print('%.0fs'%(time.time()-t0))
