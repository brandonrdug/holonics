# Host ruler (never machinery): how much of a cell's scale its region (its context) already fixes.
import numpy as np, time
exec(open('yard.py').read().split("xT,sT=load")[0])
z=np.load('train.npz'); xT=z['x'].astype(np.int64); sT=z['seg']; t0=time.time()
uc,nc,up,npair,dc=fit(ctx(xT,sT,(-2,-1,1,2)),xT)
bl=lambda c: np.floor(np.log2(c)).astype(np.int64)+1
b=bl(npair); V=len(b); bn=np.repeat(bl(nc),dc); dd=np.repeat(dc,dc); nn=np.repeat(nc,dc)
def H(*ks):
    k=np.zeros(V,np.int64)
    for a in ks: k=k*4096+a
    u,c=np.unique(k,return_counts=True); p=c/V; return -(p*np.log2(p)).sum()
hb=H(b); h1=H(b,bn)-H(bn); h2=H(b,bn,np.minimum(dd,4095))-H(bn,np.minimum(dd,4095))
print('cells %d contexts %d'%(V,len(uc)))
print('entropy of a cell scale: alone %.3f bits | given its context total scale %.3f | given that and the count of distinct letters %.3f'%(hb,h1,h2))
print('share of cells whose context holds one cell: %.3f; in contexts of total 1: %.3f'%(np.mean(dd==1),np.mean(nn==1)))
# the cell read relative to its region: r = scale of context total - scale of cell
r=bn-b; print('entropy of the relative scale (context scale minus cell scale) alone: %.3f bits; given the context scale: %.3f'%(H(r),H(r,bn)-H(bn)))
# digits at the scale: mantissa bits beyond the leading one
print('bits a cell: unary scale %.3f + digits below the leading one %.3f = Elias gamma %.3f; a sign bit a value would add 1 (%.0f%%)'%(b.mean(),(b-1).mean(),(2*b-1).mean(),100/(2*b-1).mean()))
print('done %ds'%(time.time()-t0))
