M=(1<<64)-1
def mix(seed,c):
    z=(seed+c*0x9E3779B97F4A7C15)&M
    z=((z^(z>>30))*0xBF58476D1CE4E5B9)&M
    z=((z^(z>>27))*0x94D049BB133111EB)&M
    return z^(z>>31)
SY=[b"ba",b"de",b"ki",b"lo",b"mu",b"na",b"pe",b"ri",b"so",b"tu",b"va",b"we",b"xo",b"yi",b"za",b"ha",b"fe",b"gi",b"jo",b"cu"]
def prob(seed,p):
    d=[0]
    def draw(m):
        d[0]+=1; return mix(seed,(p<<16|d[0])&M)%m
    words=48+draw(32); count=2+draw(2); vals=[]
    for _ in range(count):
        low=10**draw(3); vals.append(low+draw(9*low))
    places=[]
    while len(places)<count:
        pl=draw(words)
        if pl not in places: places.append(pl)
    places.sort(); q=b""; nx=0; starts=[]
    for w in range(words):
        if w>0: q+=b" "
        if nx<count and places[nx]==w:
            starts.append(len(q)); q+=str(vals[nx]).encode(); nx+=1
        else:
            for _ in range(1+draw(3)): q+=SY[draw(20)]
    q+=b"?"
    return q,vals,starts
import statistics
ds=[];qs=[];ds2=[]
for p in range(2000):
    q,v,s=prob(20261101,p)
    qs.append(len(q))
    base=len(q)+1  # newline then answer
    # first calc "<<a+b=": a at base+2, b at base+2+len(a)+1
    a=str(v[0]); 
    ds.append(base+2-s[0]); ds.append(base+2+len(a)+1-s[1])
print("question bytes median",statistics.median(qs),"min",min(qs),"max",max(qs))
print("first calc operand distance median",statistics.median(ds),"q10",sorted(ds)[len(ds)//10],"q90",sorted(ds)[9*len(ds)//10], "frac>127", sum(x>127 for x in ds)/len(ds))
q,v,s=prob(20261101,0); print(q.decode()); print(v)
