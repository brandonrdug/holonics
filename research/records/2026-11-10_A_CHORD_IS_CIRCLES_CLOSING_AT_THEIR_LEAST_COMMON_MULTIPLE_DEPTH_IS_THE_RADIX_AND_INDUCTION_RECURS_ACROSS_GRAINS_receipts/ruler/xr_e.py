# "Lacks against the two-each-side count" for held locked visits with a 64-wide chart (467-byte records).
# usage: python3 xr_e.py lap37 ctrl41 ct4   (reads visit/<name>/held.bin; tables from xr_held.npz, fit outside the dumped sample)
import numpy as np, sys
import os
def dt(chart): return np.dtype([('problem','<u4'),('place','<u4'),('stop','u1'),('letter','<u2'),('face','<u2',(100,)),('chart','<i4',(chart,))])
exec(open('yard.py').read().split("xT,sT=load")[0]); xH,sH=load('HELD128.txt'); gi=np.load('gi_held.npy'); pr=sH[gi]
V=root+'.local/wt/qgchgu-sampler/.local/run/2026-11-10-contacts/visit/'
cl=list(map(int,open(C).read().split('\n')[1].split()))
z=np.load('xr_held.npz'); let=z['let']; N=len(let); i=np.arange(N)
l2=np.log(z['P2'].astype(np.float64)); l3=np.log(z['P3'].astype(np.float64))
name=lambda k: 'VOID' if k==99 else repr(chr(cl[k]))
def lface(nm,chart):
    d=np.fromfile(V+nm+'/held.bin',dtype=dt(chart)); assert len(d)==N,(len(d),N)
    assert (d['letter']==let).all(), 'letters differ from the lap-26 held dump'
    f=np.maximum(d['face'].astype(np.float64),0.5); f/=f.sum(1,keepdims=True); return np.log(f)
def code(lf,lt,a,b,sel=None):
    if sel is None: sel=slice(None)
    s=a*lf[sel]+b*lt[sel]; m=s.max(1,keepdims=True); lz=m[:,0]+np.log(np.exp(s-m).sum(1)); return lz-s[np.arange(len(lz)),let[sel]]
def fitw(lf,lt,sel):
    best=(9,1,0)
    for a in np.arange(0,1.51,0.25):
        for b in np.arange(0,1.51,0.25): best=min(best,(code(lf,lt,a,b,sel).mean(),a,b))
    c0,a0,b0=best
    for a in np.arange(max(a0-0.2,0),a0+0.21,0.05):
        for b in np.arange(max(b0-0.2,0),b0+0.21,0.05): best=min(best,(code(lf,lt,a,b,sel).mean(),a,b))
    return best
out={}
for nm in sys.argv[1:]:
    lf=lface(nm,32 if nm=='lap26' else 64); cf=-lf[i,let]; res=[nm,cf.mean()]
    for lt,k in ((l2,'2'),(l3,'3')):
        prod=np.zeros(N); w=[]
        for fold in (0,1):
            tr=(pr%2==fold); te=~tr; c,a,b=fitw(lf,lt,tr); prod[te]=code(lf,lt,a,b,te); w.append((round(float(a),2),round(float(b),2)))
        ct=-lt[i,let]; res+=[prod.mean(),ct.mean(),w]; 
        if k=='2': p2=prod
    out[nm]=(cf,p2)
    print('%-7s field %.4f | x table2: product %.4f (table %.4f, weights %s) LACKS %.4f, holds beyond %.4f | x table3: product %.4f LACKS %.4f, holds beyond %.4f'%(nm,res[1],res[2],res[3],res[4],res[1]-res[2],res[3]-res[2],res[5],res[1]-res[5],res[6]-res[5]),flush=True)
np.save('xr_e_out.npy',np.array([np.stack(out[k]) for k in out]))
names=list(out)
print('by reference letter: letter share | field code in each state | product2 in each state   (states: %s)'%' '.join(names))
cnt=np.bincount(let,minlength=100); c2=-l2[i,let]
for k in np.argsort(-cnt)[:24]:
    s=let==k; print('  %-6s %.3f | %s | %s | table2 %.3f'%(name(k),s.mean(),' '.join('%.3f'%out[n][0][s].mean() for n in names),' '.join('%.3f'%out[n][1][s].mean() for n in names),c2[s].mean()))
V_=[k for k in range(100) if k!=99 and chr(cl[k]) in 'eoiu']; S_=[k for k in range(100) if k!=99 and chr(cl[k]) in ' \n()[]{}']
for lab,ks in (('vowels e o i u',V_),('space newline brackets',S_)):
    s=np.isin(let,ks); print('%-24s share %.3f | field %s | nats a place contributed %s'%(lab,s.mean(),' '.join('%.4f'%out[n][0][s].mean() for n in names),' '.join('%.4f'%(out[n][0][s].sum()/N) for n in names)))
