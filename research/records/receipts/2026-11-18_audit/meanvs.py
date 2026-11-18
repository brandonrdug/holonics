import sys, math
sys.path.insert(0,'research/records/receipts/2026-11-18_audit')
from layout import layout
def mat(p):
    with open(p) as f:
        f.readline(); f.readline(); a=[int(x) for x in f.readline().split()]; f.readline(); f.readline(); b=[int(x) for x in f.readline().split()]; c=[int(x) for x in f.readline().split()]
    return a+b+c
fm,at=layout(244,128,4,8,2,128,4,4,3771,4,0,32,10,1,0,1,0)
M93=mat(sys.argv[1]); M94=mat(sys.argv[2]); S94=mat(sys.argv[3]); M90=mat(sys.argv[4])
print("%-14s %9s %9s %9s %7s"%("family","mean94-93","state-mean","mean94-90","ratio"))
for nm,s,l,g in fm:
    if l==0: continue
    sc=1<<g
    a=math.sqrt(sum((M94[i]-M93[i])**2 for i in range(s,s+l))/l)/sc
    b=math.sqrt(sum((S94[i]-M94[i])**2 for i in range(s,s+l))/l)/sc
    c=math.sqrt(sum((M94[i]-M90[i])**2 for i in range(s,s+l))/l)/sc
    print("%-14s %9.5f %9.5f %9.5f %7.2f"%(nm,a,b,c,c/a if a else 0))
