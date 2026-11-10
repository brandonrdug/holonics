# A ruler on the host, never machinery: Witten-Bell count tables of the letters around a place, fit on TRAIN.
import os, numpy as np, time
root=os.environ.get('HOLONICS_ROOT','./')  # the main checkout; the passages and dumps under .local/ are private
C=root+'.local/wt/qgchgu-sampler/.local/run/2026-11-05-code84/dev/CODEC'
cl=list(map(int,open(C).read().split('\n')[1].split()))
lut=np.full(256,-1,np.int16)
for i,b in enumerate(cl): lut[b]=i
VOID=99; PAD=100; B=101
def load(fn):
    b=open(root+'.local/data/python-codes-25k/passage/'+fn,'rb').read()
    xs=[];seg=[]
    k=0
    for r in b.split(b'\x1e'):
        if b'\x1f' not in r: continue
        a=np.frombuffer(r.split(b'\x1f',1)[1],dtype=np.uint8)
        c=np.concatenate([lut[a],[VOID]]).astype(np.int64)
        xs.append(c); seg.append(np.full(len(c),k,np.int32)); k+=1
    return np.concatenate(xs),np.concatenate(seg)
def nb(x,seg,d):
    n=len(x); out=np.full(n,PAD,np.int64)
    if d<0:
        k=-d; ok=seg[k:]==seg[:-k]; out[k:][ok]=x[:-k][ok]
    else:
        k=d; ok=seg[:-k]==seg[k:]; out[:-k][ok]=x[k:][ok]
    return out
def ctx(x,seg,offs):
    c=np.zeros(len(x),np.int64)
    for d in offs: c=c*B+nb(x,seg,d)
    return c
def fit(c,a):
    uc,nc=np.unique(c,return_counts=True)
    up,npair=np.unique(c*B+a,return_counts=True)
    # distinct letters per ctx
    ucp,dc=np.unique(up//B,return_counts=True)
    return uc,nc,up,npair,dc
def look(M,c,a):
    uc,nc,up,npair,dc=M
    i=np.searchsorted(uc,c); i[i>=len(uc)]=0; f=uc[i]==c
    n=np.where(f,nc[i],0); d=np.where(f,dc[i],0)
    p=c*B+a; j=np.searchsorted(up,p); j[j>=len(up)]=0; g=up[j]==p
    m=np.where(g,npair[j],0)
    return n,m,d
def run(name,chain,xtr,str_,xte,ste,sel=None):
    uni=np.bincount(xtr,minlength=B).astype(float)+0.5; uni/=uni.sum()
    P=uni[xte]; res=[('unigram',-np.mean(np.log(P if sel is None else P[sel])),B)]
    for offs in chain:
        t=time.time()
        M=fit(ctx(xtr,str_,offs),xtr)
        n,m,d=look(M,ctx(xte,ste,offs),xte)
        lam=np.maximum(d,1).astype(float)
        P=np.where(n>0,(m+lam*P)/(n+lam),P)
        res.append((str(offs),-np.mean(np.log(P if sel is None else P[sel])),len(M[2])))
        del M
    print(name); [print('   %-34s %.3f nats a place   (%d context-letter cells)'%r) for r in res]
xT,sT=load('TRAIN.txt'); xH,sH=load('HELD128.txt')
print('TRAIN places',len(xT),'HELD places',len(xH))
both=[(-1,1),(-2,-1,1,2),(-3,-2,-1,1,2,3),(-4,-3,-2,-1,1,2,3,4)]
left=[(-1,),(-2,-1),(-3,-2,-1),(-4,-3,-2,-1),(-5,-4,-3,-2,-1),(-6,-5,-4,-3,-2,-1),(-8,-7,-6,-5,-4,-3,-2,-1)]
ev=sT%2==0; od=~ev
run('BOTH SIDES, fit TRAIN, read HELD128 (all 128)',both,xT,sT,xH,sH)
run('BOTH SIDES, fit TRAIN, read HELD 0-31',both,xT,sT,xH,sH,sel=sH<32)
run('BOTH SIDES, fit TRAIN even, read TRAIN odd',both,xT[ev],sT[ev],xT[od],sT[od])
run('LEFT ONLY, fit TRAIN, read HELD128',left,xT,sT,xH,sH)
run('LEFT ONLY, fit TRAIN even, read TRAIN odd',left,xT[ev],sT[ev],xT[od],sT[od])
