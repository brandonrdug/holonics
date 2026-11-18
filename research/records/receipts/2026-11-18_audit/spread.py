import sys, math
def lines(p, ks):
    out={}
    with open(p) as f:
        for i,l in enumerate(f,1):
            if i in ks: out[i]=l.split()
            if i>max(ks): break
    return out
a=lines(sys.argv[1],{3,6,7}); b=lines(sys.argv[2],{3,6,7})
for k,name in [(3,'fine'),(6,'level'),(7,'glue')]:
    x=[int(v) for v in a[k]]; y=[int(v) for v in b[k]]
    n=len(x)
    rms=math.sqrt(sum(v*v for v in x)/n)
    d=[p-q for p,q in zip(x,y)]
    drms=math.sqrt(sum(v*v for v in d)/n)
    print(name, 'entries',n,'rms',round(rms),'rms(state-other)',round(drms),'ratio',round(drms/rms,3), 'moved', sum(1 for v in d if v))
