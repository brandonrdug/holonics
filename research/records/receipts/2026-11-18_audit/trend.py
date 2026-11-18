import sys, math
sys.path.insert(0,'research/records/receipts/2026-11-18_audit')
from layout import layout
names=["pace","temper","read_bias","mark","enc","opening","w_triad","w","read","out","q","probe","carry","a","b"]
for p in sys.argv[1:]:
    with open(p) as f:
        f.readline(); head=f.readline().split(); th=[int(x) for x in f.readline().split()]
    w=[int(x) for x in head[1:]]
    # parse head: name A D H n still f K frames reach lanes depth carry triads opening junction mark loud crossing
    A,D,H,n,still,fc,K,fr,reach,lanes=w[:10]
    depth=w[10] if len(w)>10 else 0; carry=w[11] if len(w)>11 else 0; triads=w[12] if len(w)>12 else 0
    opening=w[13] if len(w)>13 else 0; junction=w[14] if len(w)>14 else 0; mark=w[15] if len(w)>15 else 0; loud=w[16] if len(w)>16 and head[0]!="hnn-field-v14x" else 0
    if head[0]=="hnn-field-v14x": loud=w[16]
    fams,at=layout(A,D,H,n,still,fc,K,fr,reach,lanes,depth,carry,triads,opening,junction,mark,loud)
    if at!=len(th): print(p,"layout mismatch",at,len(th),head); continue
    F={nm:(s,l,g) for nm,s,l,g in fams}
    out=[]
    for nm in names:
        if nm not in F: out.append("%s=-"%nm); continue
        s,l,g=F[nm]
        out.append("%s=%.4f"%(nm, math.sqrt(sum((th[i]/(1<<g))**2 for i in range(s,s+l))/l)))
    s,l,g=F["pace"]; pv=[th[i]/(1<<g) for i in range(s,s+l)]
    s2,l2,g2=F["temper"]; tv=[round(th[i]/(1<<g2),2) for i in range(s2,s2+l2)]
    print(p.split('/')[-2], head[0], "pace max %.2f"%max(pv), "temper", tv, " ".join(out))
