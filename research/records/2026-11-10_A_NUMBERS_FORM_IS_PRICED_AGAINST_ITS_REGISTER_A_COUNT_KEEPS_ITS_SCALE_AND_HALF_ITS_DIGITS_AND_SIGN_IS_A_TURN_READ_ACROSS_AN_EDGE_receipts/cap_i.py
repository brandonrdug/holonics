# Host ruler for the lens of 2026-11-10 21:25Z (a ruler on the text's count tables, never machinery):
# what the cells of a count table cost in each number form, and what the held code loses when a count
# keeps only its leading digits at its own scale.
import numpy as np, time, sys, os
exec(open('yard.py').read().split("xT,sT=load")[0])
z=np.load('train.npz'); xT=z['x'].astype(np.int64); sT=z['seg']; xH,sH=load('HELD128.txt'); t0=time.time()
chain=[(-1,1),(-2,-1,1,2)]
Ms=[fit(ctx(xT,sT,o),xT) for o in chain]; cH=[ctx(xH,sH,o) for o in chain]
uni=np.bincount(xT,minlength=B).astype(float)+0.5; uni/=uni.sum()
def blen(c): return np.floor(np.log2(c)).astype(np.int64)+1
def gam(n): return 2*np.floor(np.log2(n)).astype(np.int64)+1
def code(Ms):
    P=uni[xH]
    for M,c in zip(Ms,cH):
        n,m,d=look(M,c,xH); lam=np.maximum(d,1).astype(float)
        P=np.where(n>0,(m+lam*P)/(n+lam),P)
    return -np.mean(np.log(P))
def rounded(M,f):
    uc,nc,up,npair,dc=M; m2=f(npair).astype(np.int64)
    st=np.r_[0,np.cumsum(dc)[:-1]]; n2=np.add.reduceat(m2,st)
    return (uc,n2,up,m2,dc)
def half(c): b=blen(c); s=(b+1)//2; sh=b-s; return np.rint(c/2.0**sh)*2.0**sh
def dig(k):
    def f(c): e=np.maximum(np.floor(np.log10(c)).astype(np.int64)-(k-1),0); return np.rint(c/10.0**e)*10.0**e
    return f
def pow2(c): return 2.0**np.rint(np.log2(c))
base=code(Ms); print('HELD128 code, counts whole: %.4f   %ds'%(base,time.time()-t0))
c=Ms[1][3]; V=len(c); b=blen(c)
print('cells %d   largest count %d   share with count 1: %.3f, 2-3: %.3f, 4-15: %.3f, 16-255: %.3f, 256 and over: %.3f'%(V,c.max(),np.mean(c==1),np.mean((c>=2)&(c<=3)),np.mean((c>=4)&(c<=15)),np.mean((c>=16)&(c<=255)),np.mean(c>=256)))
u,k=np.unique(c,return_counts=True); p=k/V; H=-(p*np.log2(p)).sum()
stair=np.select([b<=8,b<=16,b<=32],[8,16,32],64); stair_s=np.select([b+1<=8,b+1<=16,b+1<=32],[8,16,32],64)
delta=(b-1)+gam(b)
print('bits a cell: 64-bit register 64 | 32-bit register 32 | staircase signed %.2f, unsigned %.2f | least fixed width %d | Elias gamma %.2f | Elias delta %.2f | bare binary digits %.2f | entropy of the counts own law %.2f'%(stair_s.mean(),stair.mean(),int(blen(np.array([c.max()]))[0]),gam(c).mean(),delta.mean(),b.mean(),H))
# forms that keep leading digits at a scale: the scale by Elias gamma of the bit length (or of the decimal length), then the kept digits
s=(b+1)//2; L10=np.floor(np.log10(c)).astype(np.int64)+1
print('bits a cell, leading digits at a scale: half of the bits %.2f | two decimal digits %.2f | one decimal digit %.2f | scale alone (power of two) %.2f'%((gam(b)+s-1).mean(),(gam(L10)+np.where(L10>=2,np.log2(90),np.log2(9))).mean(),(gam(L10)+np.log2(9)).mean(),gam(b).mean()))
# radix economy on these counts: states of hardware, b a digit, whole digits
for bb in (2,3,4,10,16,256):
    d=np.floor(np.log(c)/np.log(bb)+1e-12).astype(np.int64)+1
    print('   base %3d: %.2f states a cell (%.2f digits)'%(bb,(bb*d).mean(),d.mean()),end='')
print('\n   floor e ln(c+1): %.2f states a cell;  2 log2(c+1): %.2f;  3 log3(c+1): %.2f'%((np.e*np.log(c+1.0)).mean(),(2*np.log2(c+1.0)).mean(),(3*np.log(c+1.0)/np.log(3)).mean()))
for nm,f in (('leading half of bits',half),('two decimal digits',dig(2)),('one decimal digit',dig(1)),('nearest power of two',pow2)):
    M2=[rounded(M,f) for M in Ms]; v=code(M2)
    ch=np.mean(M2[1][3]!=Ms[1][3])
    print('counts rounded to %-22s HELD128 %.4f  (%+.4f)   cells changed %.3f   %ds'%(nm+':',v,v-base,ch,time.time()-t0))
# where the held places land, by the size of the cell they hit
n,m,d=look(Ms[1],cH[1],xH)
for lo,hi in ((0,0),(1,1),(2,3),(4,15),(16,255),(256,4095),(4096,10**9)):
    print('   held places hitting a cell of count %d..%d: %.3f'%(lo,hi,np.mean((m>=lo)&(m<=hi))),end=';')
print('\ndone %ds'%(time.time()-t0))
