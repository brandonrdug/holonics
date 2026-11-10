import numpy as np, time, os, sys
t0=time.time()
V=os.environ.get('HOLONICS_ROOT','./')+'.local/wt/qgchgu-sampler/.local/run/2026-11-10-contacts/visit/'  # the visit dumps, private
dt=np.dtype([('problem','<u4'),('place','<u4'),('stop','u1'),('letter','<u2'),('face','<u2',(100,)),('chart','<i4',(64,))])
z=np.load('xr_held.npz'); let=z['let']; N=len(let); I=np.arange(N); l2=np.log(z['P2'].astype(np.float64))
q=np.load('cap_a2_in.npz'); l1=np.log(q['P1'].astype(np.float64)); rH=q['rH']
exec(open('yard.py').read().split("xT,sT=load")[0]); xH,sH=load('HELD128.txt'); pr=sH[np.load('gi_held.npy')]
nm=sys.argv[1]
d=np.fromfile(V+nm+'/held.bin',dtype=dt); assert (d['letter']==let).all()
f=np.maximum(d['face'].astype(np.float64),0.5); f/=f.sum(1,keepdims=True); lf=np.log(f); cf=-lf[I,let]
def code(lt,a,b,sel):
    s=a*lf[sel]+b*lt[sel]; m=s.max(1,keepdims=True); lz=m[:,0]+np.log(np.exp(s-m).sum(1)); return lz-s[np.arange(len(lz)),let[sel]]
grid=[(a,b) for a in np.arange(0.4,1.01,0.1) for b in np.arange(0.0,0.91,0.1)]
print(nm,'field %.4f'%cf.mean(),'| k | table-k code | product | weights | LACKS against table-k | of which beyond table1 alone',flush=True)
base=None
for k in [0,300,1000,3000,10000,30000,100000,10**9]:
    lt=np.where((rH<k)[:,None],l2,l1); prod=np.zeros(N); w=[]
    for fold in (0,1):
        tr=(pr%2==fold); te=~tr
        c,a,b=min((code(lt,a,b,tr).mean(),a,b) for a,b in grid); prod[te]=code(lt,a,b,te); w.append((round(float(a),1),round(float(b),1)))
    lack=cf.mean()-prod.mean()
    if base is None: base=lack
    print('  %10d  %.4f  %.4f  %s  %.4f  %.4f   %.0fs'%(k,-lt[I,let].mean(),prod.mean(),w,lack,lack-base,time.time()-t0),flush=True)
