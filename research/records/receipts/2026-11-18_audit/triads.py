import sys
def line(p,k):
    with open(p) as f:
        for i,l in enumerate(f,1):
            if i==k: return [int(v) for v in l.split()]
old=line(sys.argv[1],3); new=line(sys.argv[2],3)
# insertion runs: two-pointer
i=j=0; runs=[]
while j<len(new):
    if i<len(old) and old[i]==new[j]:
        i+=1; j+=1; continue
    # find run of inserted entries: advance j until new[j]==old[i] and next few match
    s=j
    while j<len(new) and not (i<len(old) and new[j:j+8]==old[i:i+8]):
        j+=1
    runs.append((s,j))
print('old',len(old),'new',len(new),'runs',[(a,b,b-a) for a,b in runs][:20])
for p in sys.argv[3:]:
    x=line(p,3)
    for a,b in runs:
        seg=x[a:b]; nz=sum(1 for v in seg if v)
        g=new[a:b]; ch=sum(1 for u,v in zip(g,seg) if u!=v)
        import math
        rms=math.sqrt(sum(v*v for v in seg)/len(seg)); rms0=math.sqrt(sum(v*v for v in g)/len(g))
        print(p.split('/')[-2]+'/'+p.split('/')[-1], 'run',a,b-a,'nonzero',nz,'changed_from_grown',ch,'rms',round(rms),'rms_at_growth',round(rms0))
