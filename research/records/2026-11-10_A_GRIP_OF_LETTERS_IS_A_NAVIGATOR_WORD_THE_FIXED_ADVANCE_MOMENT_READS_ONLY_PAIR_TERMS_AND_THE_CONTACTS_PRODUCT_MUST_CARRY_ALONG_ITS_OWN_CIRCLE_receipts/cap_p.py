# Host ruler for the lens of 2026-11-10 23:49Z (a longer word is a larger founded unit): never machinery.
#  strides : the moduli of the strides the word ruler (cap_o) fitted, by letter: where do the strides stop?
#  units D : founded units by count. The contexts of 2..D left letters met c times or more on TRAIN are founded (a pruned context
#            tree, closed under suffixes); Witten-Bell down the founded suffixes; read on the HELD128 places with four letters on the left.
import numpy as np, time, sys
exec(open('yard.py').read().split("xT,sT=load")[0])
z=np.load('train.npz'); xT=z['x'].astype(np.int64); sT=z['seg']; xH,sH=load('HELD128.txt')
t0=time.time(); part=sys.argv[1]
freq=np.bincount(xT,minlength=B).astype(float); freq/=freq.sum()
def name(i):
    if i==VOID: return 'END'
    if i==PAD: return 'PAD'
    b=cl[i]
    return {10:'\\n',32:'SP',9:'TAB'}.get(b, chr(b) if 33<=b<127 else 'x%02x'%b)
def kind(i):
    if i>=VOID: return 'other'
    b=cl[i]
    if b in (10,32,9,13): return 'space'
    if (48<=b<=57) or (65<=b<=90) or (97<=b<=122) or b==95: return 'word'
    if 33<=b<127: return 'punct'
    return 'other'
if part=='strides':
    for g in (3,4):
        for r in (16,64):
            S=np.load('cap_o_g%d_r%d.npz'%(g,r)); mod=np.sqrt(S['ar']**2+S['ai']**2); a=mod.mean(1)
            top=np.argsort(-freq)[:20]
            print('g=%d r=%d step %d | frequency-weighted mean |alpha| %.3f | plain mean %.3f'%(g,r,int(S['step'][0]),(freq*a).sum(),a.mean()))
            for k in ('space','punct','word','other'):
                m=np.array([kind(i)==k for i in range(B)]); w=freq[m]
                print('   %-6s letters %3d share of places %.3f weighted |alpha| %.3f'%(k,m.sum(),w.sum(),(w*a[m]).sum()/max(w.sum(),1e-12)))
            m=np.array([kind(i) in('space','punct') for i in range(B)]); w=freq[m]; print('   separators (space and punct) %.3f'%((w*a[m]).sum()/w.sum()))
            order=top[np.argsort(a[top])]
            print('   the 20 most frequent letters by |alpha|: '+' '.join('%s:%.2f'%(name(i),a[i]) for i in order))
            # spread over circles: share of circles where the letter's stride is under one half
            print('   share of circles with |alpha| < 0.5: '+' '.join('%s:%.2f'%(name(i),(mod[i]<0.5).mean()) for i in order))
if part=='units':
    D=int(sys.argv[2]); uni=np.bincount(xT,minlength=B).astype(float)+0.5; uni/=uni.sum()
    sel=np.arange(4,len(xH)); sel=sel[sH[sel]==sH[sel-4]]
    N=[];Mm=[];Dd=[];NC=[];DC=[]
    for d in range(1,D+1):
        offs=tuple(range(-d,0)); M=fit(ctx(xT,sT,offs),xT); n,m,dd=look(M,ctx(xH,sH,offs),xH)
        N.append(n[sel]);Mm.append(m[sel]);Dd.append(dd[sel]);NC.append(M[1]);DC.append(M[4]); del M
        print('depth %d: contexts %d cells %d  %.0fs'%(d,len(NC[-1]),int(DC[-1].sum()),time.time()-t0),flush=True)
    x=xH[sel]
    print('HELD places read %d'%len(sel))
    print('     c | founded units of 2..%d letters (by length) | their cells | code, units to 4 letters | code, units to %d | mean letters matched'%(D,D))
    for c in (1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,65536):
        P=uni[x].copy(); codes={}; depth=np.zeros(len(x))
        for d in range(1,D+1):
            thr=1 if d==1 else c
            ok=N[d-1]>=thr; lam=np.maximum(Dd[d-1],1).astype(float)
            P=np.where(ok,(Mm[d-1]+lam*P)/(N[d-1]+lam),P); depth=np.where(ok,d,depth)
            codes[d]=-np.log(P).mean()
        u=[int((NC[d-1]>=c).sum()) for d in range(2,D+1)]; cells=sum(int(DC[d-1][NC[d-1]>=c].sum()) for d in range(2,D+1))
        u4=sum(u[:3]); c4=sum(int(DC[d-1][NC[d-1]>=c].sum()) for d in range(2,5))
        print('%6d | %8d (%s) | %9d | %.4f (units %d, cells %d) | %.4f | %.2f'%(c,sum(u),' '.join(map(str,u)),cells,codes[min(4,D)],u4,c4,codes[D],depth.mean()),flush=True)
    print('depth 1 alone %.4f'%codes[1])
print('%.0fs'%(time.time()-t0))
