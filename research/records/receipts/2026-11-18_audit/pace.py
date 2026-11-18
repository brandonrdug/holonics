import sys
sys.path.insert(0,'research/records/receipts/2026-11-18_audit')
from moments import fams_all
fams,_=fams_all(); F={nm:(s,l,g) for nm,s,l,g in fams}
cod=open(sys.argv[2]).read().split('\n'); bytes_=[int(x) for x in cod[1].split()]
def lab(c):
    if c>=len(bytes_): return "<%d>"%c
    b=bytes_[c]; return repr(chr(b)) if 32<=b<127 else "0x%02x"%b
for p in sys.argv[1:2]+sys.argv[3:]:
    L=open(p).read().split('\n'); th=[int(x) for x in L[2].split()]
    s,l,g=F["pace"]
    for h in range(2):
        row=[(th[s+h*245+c]/(1<<g),c) for c in range(245)]
        row.sort(reverse=True)
        print(p, "head",h,"top", [(lab(c),round(v,2)) for v,c in row[:10]], "bottom",[(lab(c),round(v,2)) for v,c in row[-4:]])
print(len(bytes_))
