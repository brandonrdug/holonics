# Host ruler: reads design's locked visits (numbers only, no passage text) for G31 and G35. Never machinery.
import numpy as np, os, sys, time
exec(open('cap_q.py').read().split("z=np.load('train.npz')")[0].replace("part=sys.argv[1]","part='t'"))
xH,sH=load('HELD128.txt'); st,uid,pre,uh,useg,ulen,pos=units(xH,sH)
root=os.environ['HOLONICS_VISIT']+'/'   # the directory that holds design's locked visits, ct8/ and rt4/
dt=np.dtype([('problem','<u4'),('place','<u4'),('stop','u1'),('letter','<u2'),('face','<u2',(100,)),('chart','<i4',(64,))])
assert dt.itemsize==467
ruler=np.load('cap_m_auto.npy') if os.path.exists('cap_m_auto.npy') else None
for arm in sys.argv[1:]:
    r=np.fromfile(root+arm+'/held.bin',dtype=dt); o=np.lexsort((r['place'],r['problem'])); r=r[o]
    same=len(r)==len(xH) and bool(np.all(r['problem']==sH)) and bool(np.all(r['letter'].astype(np.int64)==xH))
    f=r['face'][np.arange(len(r)),np.minimum(r['letter'],99)].astype(float); c=-np.log(np.maximum(f,0.5)/65536.0)
    print('%s: records %d; the same places and letters as the ruler\'s HELD128: %s; mean locked code %.4f, variance %.4f; faces at zero on the letter %d'%(arm,len(r),same,c.mean(),c.var(),int((f==0).sum())))
    seg=r['problem'].astype(np.int64)
    print('   k | pairs | correlation | in standard errors')
    for k in (1,2,4,8,16,32,64,128,256):
        ok=seg[:-k]==seg[k:]; a=c[:-k][ok]; b=c[k:][ok]; q=np.corrcoef(a,b)[0,1]; print('%5d %7d %+.4f %+.1f'%(k,len(a),q,q*np.sqrt(len(a))))
    if same:
        print('   at unit starts (%.4f of places) mean %.4f, share of the code %.4f; inside units mean %.4f'%(st.mean(),c[st].mean(),c[st].sum()/c.sum(),c[~st].mean()))
        k=KIND[xH]; print('   by kind of the letter: space-class %.4f, word %.4f, other %.4f'%(c[k==0].mean(),c[k==1].mean(),c[k==2].mean()))
        if ruler is not None and len(ruler)==len(c): print('   correlation with the ruler of two letters each side (mean %.4f): %.4f'%(ruler.mean(),np.corrcoef(c,ruler)[0,1]))
