import sys, math
sys.path.insert(0,'research/records/receipts/2026-11-18_audit')
from moments import fams_all
fams,_=fams_all()
L=open(sys.argv[1]).read().split('\n')
m=[int(x) for x in L[7].split()]; v=[int(x) for x in L[8].split()]
print("%-16s %8s %10s %10s %10s %8s %8s"%("family","n","root_p10","root_med","root_p90","r|low","r|high"))
for nm,s,l,g in fams:
    if l==0 or nm.startswith("L.") and nm in ("L.enc","L.before","L.after","L.read","L.read_bias","L.moment_before","L.moment_after","L.pace","L.moment_face","L.moment_face_bias","L.lift_bias"): continue
    rows=[]
    for i in range(s,s+l):
        root=math.isqrt(max(v[i],0))+1
        rows.append((root/2**32, abs(m[i])/root))
    rows.sort()
    rs=[r for _,r in rows]
    lo=rs[:l//10] or rs; hi=rs[-(l//10):] or rs
    print("%-16s %8d %10.3g %10.3g %10.3g %8.3f %8.3f"%(nm,l,rows[l//10][0],rows[l//2][0],rows[(9*l)//10][0],sum(lo)/len(lo),sum(hi)/len(hi)))
