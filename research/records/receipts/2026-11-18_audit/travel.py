import sys, math
sys.path.insert(0,'research/records/receipts/2026-11-18_audit')
from moments import fams_all
def mat(path):
    L=open(path).read().split('\n')
    return [int(x) for x in L[2].split()]+[int(x) for x in L[5].split()]+[int(x) for x in L[6].split()]
paths=sys.argv[1:]
S=[mat(p) for p in paths]
fams,total=fams_all()
print("%-16s %6s"%("family","n"), " ".join("%9s"%("d%d_rms"%k) for k in range(len(S)-1)), " cos(d_k,d_k+1)...", " |end-start|/sum|d|")
for nm,s,l,g in fams:
    if l==0: continue
    sc=1<<g
    ds=[[S[k+1][i]-S[k][i] for i in range(s,s+l)] for k in range(len(S)-1)]
    rms=[math.sqrt(sum(x*x for x in d)/l)/sc for d in ds]
    cos=[]
    for k in range(len(ds)-1):
        a,b=ds[k],ds[k+1]
        dot=sum(x*y for x,y in zip(a,b)); na=math.sqrt(sum(x*x for x in a)); nb=math.sqrt(sum(x*x for x in b))
        cos.append(dot/(na*nb) if na*nb>0 else float('nan'))
    tot=[S[-1][i]-S[0][i] for i in range(s,s+l)]
    ntot=math.sqrt(sum(x*x for x in tot)); nsum=math.sqrt(sum(sum(x*x for x in d) for d in ds))
    print("%-16s %6d"%(nm,l), " ".join("%9.5f"%r for r in rms), " ".join("%6.3f"%c for c in cos), " %6.3f"%(ntot/nsum if nsum else float('nan')))
