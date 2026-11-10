# Host rulers, held 0-31 rows for design's reads: uneven splits and strides (as cap_f.py), and the field against the fitted pair reader.
import numpy as np, time, sys, os, pickle
exec(open('yard.py').read().split("xT,sT=load")[0])
z=np.load('train.npz'); xT=z['x'].astype(np.int64); sT=z['seg']; xH,sH=load('HELD128.txt'); t0=time.time(); A=100
if sys.argv[1]=='rows':
    s=sH<32
    run('3 LEFT 1 RIGHT, held 0-31',[(-1,),(-1,1),(-2,-1,1),(-3,-2,-1,1)],xT,sT,xH,sH,sel=s)
    run('1 LEFT 3 RIGHT, held 0-31',[(1,),(-1,1),(-1,1,2),(-1,1,2,3)],xT,sT,xH,sH,sel=s)
    for st in (1,2,4,8): run('STRIDE %d, held 0-31'%st,[(-st,st),(-3*st,-st,st,3*st)],xT,sT,xH,sH,sel=s)
    run('RIGHT ONLY, held 0-31',[tuple(range(1,k+1)) for k in range(1,5)],xT,sT,xH,sH,sel=s)
if sys.argv[1]=='field':
    K=2; oL=(-2,-1); oR=(1,2); a,b=pickle.load(open('cap_g_2.pkl','rb'))[:2]
    uL=np.unique(ctx(xT,sT,oL)); uR=np.unique(ctx(xT,sT,oR)); nL,nR=len(uL),len(uR)
    cLh=ctx(xH,sH,oL); cRh=ctx(xH,sH,oR); jL=np.searchsorted(uL,cLh); jL[jL>=nL]=0; jR=np.searchsorted(uR,cRh); jR[jR>=nR]=0
    seen=(uL[jL]==cLh)&(uR[jR]==cRh); N=len(xH); I=np.arange(N); let=xH
    q=np.load('cap_f_field.npz'); lL,lR,lJ=q['lL'],q['lR'],q['lJ']
    uni=np.bincount(xT,minlength=B).astype(float)[:A]+0.5; uni/=uni.sum()
    def norm(s): m=s.max(1,keepdims=True); return s-m-np.log(np.exp(s-m).sum(1,keepdims=True))
    lB=norm(lL+lR-np.log(uni)[None,:]); lP=norm(a[jL].astype(np.float64)+b[jR]); lP[~seen]=lB[~seen]
    c=lambda l: -l[I,let].mean()
    V=os.environ.get('HOLONICS_ROOT','./')+'.local/wt/qgchgu-sampler/.local/run/2026-11-10-contacts/visit/'
    dt=np.dtype([('problem','<u4'),('place','<u4'),('stop','u1'),('letter','<u2'),('face','<u2',(100,)),('chart','<i4',(64,))])
    d=np.fromfile(V+'ct4/held.bin',dtype=dt); assert (d['letter']==let).all()
    f=np.maximum(d['face'].astype(np.float64),0.5); f/=f.sum(1,keepdims=True); lf=np.log(f); pr=sH
    grid=[(x,y) for x in np.arange(0.4,1.01,0.1) for y in np.arange(0.0,0.91,0.1)]
    def cs(l1,l2,x,y,sel):
        s=x*l1[sel]+y*l2[sel]; m=s.max(1,keepdims=True); lz=m[:,0]+np.log(np.exp(s-m).sum(1)); return lz-s[np.arange(len(lz)),let[sel]]
    def mult(l1,l2):
        out=np.zeros(N); w=[]
        for fold in (0,1):
            tr=(pr%2==fold); te=~tr
            _,x,y=min((cs(l1,l2,x,y,tr).mean(),x,y) for x,y in grid); out[te]=cs(l1,l2,x,y,te); w.append((round(float(x),1),round(float(y),1)))
        return out.mean(),w
    print('ct4 field %.4f | fitted pair reader %.4f (all held; unseen sides read by the branch product) | branch product %.4f | joint %.4f'%(c(lf),c(lP),c(lB),c(lJ)))
    for nm,lt in (('fitted pair reader',lP),('branch product',lB),('joint table',lJ)):
        p,w=mult(lf,lt); print('   field x %-20s %.4f weights %s  THE FIELD LACKS %.4f'%(nm,p,w,c(lf)-p),flush=True)
    p,w=mult(lP,lJ); print('   fitted pair reader x joint table %.4f weights %s: the pair reader lacks %.4f of the joint table'%(p,w,c(lP)-p))
    p,w=mult(lP,lf); print('   fitted pair reader x field %.4f weights %s: the pair reader lacks %.4f of the field'%(p,w,c(lP)-p))
print('done %.0fs'%(time.time()-t0))
