import sys
def lines(p, ks):
    out={}
    with open(p) as f:
        for i,l in enumerate(f,1):
            if i in ks: out[i]=[int(v) for v in l.split()]
            if i>max(ks): break
    return out
a=lines(sys.argv[1],{3,6,7,8,9}); b=lines(sys.argv[2],{3,6,7,8,9})
for k,name in [(3,'fine'),(6,'level'),(7,'glue')]:
    x,y=a[k],b[k]
    same=[i for i in range(min(len(x),len(y))) if x[i]==y[i]]
    zeros=sum(1 for i in same if x[i]==0)
    print(name,len(y),'unchanged',len(same),'of which zero',zeros, 'first unchanged idx', same[:5], 'last', same[-3:] if same else None)
m1=b[8]; m2=b[9]
print('moments: first==0', sum(1 for v in m1 if v==0), 'second==0', sum(1 for v in m2 if v==0), 'of', len(m1))
for k,name in [(6,'level'),(3,'fine')]:
    x,y=a[k],b[k]
    same=[i for i in range(len(y)) if x[i]==y[i]]
    runs=[]; s=same[0]; p=same[0]
    for i in same[1:]:
        if i!=p+1: runs.append((s,p+1)); s=i
        p=i
    runs.append((s,p+1))
    big=[(r0,r1,r1-r0) for r0,r1 in runs if r1-r0>=32]
    print(name,'runs>=32:',big[:30], 'n_runs', len(runs))
