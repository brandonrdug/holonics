import sys, math
sys.path.insert(0,'research/records/receipts/2026-11-18_audit')
from layout import layout
def read(path):
    L=open(path).read().split('\n')
    return L
def fams_all():
    f,at=layout(244,128,4,8,2,128,4,4,3771,4,0,32,10,1,0,1,0)
    f2,at2=layout(2,64,4,8,2,128,2,4,3771,2)
    out=list(f)
    for (nm,s,l,g) in f2: out.append(("L."+nm,at+s,l,g))
    base=at+at2; H=6; d0=128; d1=64
    a=0; ab=H*d1*d0; b=ab+d1; bb=b+H*d0*d1
    out+= [("G.a",base+a,ab-a,24),("G.ab",base+ab,d1,16),("G.b",base+b,bb-b,24),("G.bb",base+bb,H*d0,16)]
    return out, base+bb+H*d0
def isqrt(x): return math.isqrt(max(x,0))
path=sys.argv[1]; rate=12
L=read(path)
theta=[int(x) for x in L[2].split()]+[int(x) for x in L[5].split()]+[int(x) for x in L[6].split()]
m=[int(x) for x in L[7].split()]; v=[int(x) for x in L[8].split()]
fams,total=fams_all()
assert total==len(theta)==len(m), (total,len(theta),len(m))
import statistics as st
print("%-18s %7s %6s %6s %7s %7s %7s %6s %6s %9s"%("family","n","zeroMV","r_rms","r_med","zstep","stepmed","grain","maxstp","theta_rms"))
for nm,s,l,g in fams:
    if l==0: continue
    zmv=0; rs=[]; zs=0; steps=[]
    for i in range(s,s+l):
        if m[i]==0 and v[i]==0: zmv+=1
        root=isqrt(v[i])+1
        r=m[i]/root; rs.append(r)
        stp=int(((m[i]<<g)>>rate)/root) if True else 0
        # emulate trunc toward zero of i128 division
        num=(m[i]<<g)>>rate
        q=abs(num)//root; q= q if num>=0 else -q
        steps.append(q)
        if q==0: zs+=1
    rr=math.sqrt(sum(x*x for x in rs)/l)
    ab=sorted(abs(x) for x in rs)
    sa=sorted(abs(x) for x in steps)
    th=math.sqrt(sum(theta[i]**2 for i in range(s,s+l))/l)/(1<<g)
    print("%-18s %7d %6.3f %6.3f %7.3f %7.3f %7d %6d %6d %9.4f"%(nm,l,zmv/l,rr,ab[l//2],zs/l,sa[l//2],g,sa[-1],th))
