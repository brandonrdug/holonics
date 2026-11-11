# Host ruler for the lens of 2026-11-11 01:19Z (host and card as two surfaces; cost should follow news): never machinery.
#  grains : how many events each grain of the TRAIN passage has (places, separators, unit starts, newlines, passages).
#  news   : design's locked visits (numbers only): how the covector mass m_t = |p_t - q_t|^2 and the code lie over the held places.
import numpy as np, os, sys, time
exec(open('cap_q.py').read().split("z=np.load('train.npz')")[0].replace("part=sys.argv[1]","part='t'"))
part=sys.argv[1]
if part=='grains':
    z=np.load('train.npz'); xT=z['x'].astype(np.int64); sT=z['seg']
    k=KIND[xT]; n=len(xT); first=np.ones(n,bool); first[1:]=sT[1:]!=sT[:-1]
    word=k==1; prevword=np.zeros(n,bool); prevword[1:]=word[:-1]; prevword[first]=False
    start=word&~prevword
    nl=np.array([cl[i]==10 if i<VOID else False for i in range(B)])[xT]
    print('TRAIN places %d in %d passages (%.1f places a passage)'%(n,int(first.sum()),n/first.sum()))
    print('  space-class %.4f; word letters %.4f; other (punctuation and the rest) %.4f; separators (all but word letters) %.4f'%((k==0).mean(),word.mean(),(k==2).mean(),(~word).mean()))
    print('  unit starts (a word letter after a non-word letter) %.4f of places: %d units, %.2f word letters a unit'%(start.mean(),int(start.sum()),word.sum()/start.sum()))
    print('  newlines %.4f of places: %d lines, %.1f places a line'%(nl.mean(),int(nl.sum()),n/max(1,nl.sum())))
if part=='news':
    xH,sH=load('HELD128.txt'); st,uid,pre,uh,useg,ulen,pos=units(xH,sH)
    root=os.environ['HOLONICS_VISIT']
    dt=np.dtype([('problem','<u4'),('place','<u4'),('stop','u1'),('letter','<u2'),('face','<u2',(100,)),('chart','<i4',(64,))])
    for arm in sys.argv[2:]:
        r=np.fromfile(root+arm+'/held.bin',dtype=dt); o=np.lexsort((r['place'],r['problem'])); r=r[o]
        same=len(r)==len(xH) and bool(np.all(r['problem']==sH)) and bool(np.all(r['letter'].astype(np.int64)==xH))
        p=r['face'].astype(float)/65536.0; L=np.minimum(r['letter'],99).astype(np.int64); pt=p[np.arange(len(r)),L]
        m=(p*p).sum(1)-2*pt+1.0; c=-np.log(np.maximum(pt,0.5/65536.0))
        print('%s: records %d; same places and letters as HELD128: %s; face sums mean %.4f; mean code %.4f; mean covector mass %.4f'%(arm,len(r),same,p.sum(1).mean(),c.mean(),m.mean()))
        for nm,v in (('covector mass',m),('code',c)):
            s=np.sort(v)[::-1]; cs=np.cumsum(s)/s.sum()
            row=' '.join('%.0f%%:%.3f'%(100*q,(np.searchsorted(cs,q)+1)/len(s)) for q in (0.5,0.8,0.9,0.99))
            print('   %s: the share of places that holds a share of the total, largest first: %s'%(nm,row))
        for e in (4,6,8,10): print('   places with covector mass under 2^-%d: %.4f (they hold %.5f of the mass)'%(e,(m<2.0**-e).mean(),m[m<2.0**-e].sum()/m.sum()))
        for e in (0.95,0.99,0.999): print('   places with the face on the reference letter at %.3f or more: %.4f'%(e,(pt>=e).mean()))
        if same:
            print('   unit starts %.4f of places: mean mass %.4f, share of the mass %.4f; inside units mean mass %.4f; ratio %.3f'%(st.mean(),m[st].mean(),m[st].sum()/m.sum(),m[~st].mean(),m[st].mean()/m[~st].mean()))
            k=KIND[xH]; print('   mean mass by kind of the letter: space-class %.4f, word %.4f, other %.4f'%(m[k==0].mean(),m[k==1].mean(),m[k==2].mean()))
