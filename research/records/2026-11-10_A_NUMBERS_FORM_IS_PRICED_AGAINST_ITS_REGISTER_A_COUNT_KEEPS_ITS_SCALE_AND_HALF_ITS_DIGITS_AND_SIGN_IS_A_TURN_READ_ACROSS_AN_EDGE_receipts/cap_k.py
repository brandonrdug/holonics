# Host ruler (never machinery): G22. How much of a cell's scale its region fixes, on the cells that share a context,
# and the counts of counts by dyadic block against the law Elias gamma is the ideal code of.
import numpy as np, time
exec(open('yard.py').read().split("xT,sT=load")[0])
z=np.load('train.npz'); xT=z['x'].astype(np.int64); sT=z['seg']; t0=time.time()
uc,nc,up,npair,dc=fit(ctx(xT,sT,(-2,-1,1,2)),xT)
bl=lambda c: np.floor(np.log2(c)).astype(np.int64)+1
b=bl(npair); bn=np.repeat(bl(nc),dc); dd=np.repeat(dc,dc); nn=np.repeat(nc,dc)
def H(sel,*ks):
    V=int(sel.sum()); k=np.zeros(V,np.int64)
    for a in ks: k=k*4096+a[sel]
    u,c=np.unique(k,return_counts=True); p=c/V; return -(p*np.log2(p)).sum()
for name,sel in (('all cells',dd>0),('contexts of 2 cells or more',dd>1),('contexts of 8 cells or more',dd>=8)):
    d4=np.minimum(dd,4095)
    print('%-28s share %.3f | scale alone %.3f bits | given context total scale %.3f | given that and distinct count %.3f | given distinct count only %.3f'%(
        name,sel.mean(),H(sel,b),H(sel,b,bn)-H(sel,bn),H(sel,b,bn,d4)-H(sel,bn,d4),H(sel,b,d4)-H(sel,d4)))
print('contexts %d, cells a context %.3f; share of contexts with one cell %.3f'%(len(uc),len(b)/len(uc),np.mean(dc==1)))
# rank of the cell within its context (0 = largest), a region-relative coordinate
st=np.r_[0,np.cumsum(dc)[:-1]]; cid=np.repeat(np.arange(len(dc)),dc)
o=np.lexsort((-npair,cid)); rank=np.empty(len(b),np.int64); rank[o]=np.arange(len(b))-np.repeat(st,dc)
sel=dd>1; r=np.minimum(rank,4095)
print('contexts of 2 cells or more: scale given context total scale and the cell rank in its context %.3f bits'%(H(sel,b,bn,r)-H(sel,bn,r)))
# counts of counts by dyadic block against 2^-(j+1)
j=b-1; tot=len(b)
print('share of cells with floor(log2 count) = j, against 2^-(j+1):')
print('   '+'  '.join('j=%d %.4f|%.4f'%(q,np.mean(j==q),2.0**-(q+1)) for q in range(0,12)))
sh=np.array([np.mean(j==q) for q in range(0,18)]); qq=np.arange(18); ok=sh>0
sl=np.polyfit(qq[ok][:10],np.log2(sh[ok][:10]),1)[0]
print('slope of log2 share by block over j = 0..9: %.3f (the inverse-square law of gamma gives -1; share of count c then falls as c^(slope-1))'%sl)
print('done %ds'%(time.time()-t0))
