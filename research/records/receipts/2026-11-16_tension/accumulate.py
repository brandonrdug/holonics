# A ruler: what the open row's weights give if they are carried across the ticks as a store (log-weights summed with a leak g),
# from read-tension's shares.tsv. Head by head; the share on the aligned column at each tick, fresh (g = 0) and carried (g = 1/2, 1).
import sys, math, collections
sys.path.insert(0, 'tools')  # run from the repository's root
import tension_ruler as t
d=sys.argv[1]
rows=collections.defaultdict(dict)  # (label, place, head) -> tick -> {j: share}
for line in open(d+'/shares.tsv'):
    lab, place, k, h, i, *rest = line.rstrip('\n').split('\t')
    cells=[x.split(':') for x in (rest[0].split(' ') if rest and rest[0] else [])]
    rows[(lab,int(place),int(h),int(i))][int(k)]={int(c[0]): int(c[1])/1e6 for c in cells}
acc=collections.defaultdict(lambda:[0,0.0])
for (lab,place,h,i),ticks in rows.items():
    _,kind,op,a,b,v=lab.split(':')
    if op!='+': continue
    _,kv,_=t.site_role(lab,i)
    at_b=len(a)+3
    ak=len(a)-1-kv if kv<len(a) else None
    bk=at_b+len(b)-1-kv if kv<len(b) else None
    cols=[x for x in (ak,bk) if x is not None]
    if not cols: continue
    part='both' if len(cols)==2 else 'one'
    for g in (0.0,0.5,1.0):
        z={}
        for k in sorted(ticks):
            p=ticks[k]
            js=set(z)|set(p)
            z={j: g*z.get(j,-40.0)+math.log(max(p.get(j,0.0),1e-12)) if z else math.log(max(p.get(j,0.0),1e-12)) for j in js}
            m=max(z.values()); w={j: math.exp(x-m) for j,x in z.items()}; tot=sum(w.values())
            e=acc[(kind,part,h,g,k)]; e[0]+=1; e[1]+=sum(w.get(j,0.0) for j in cols)/tot
print('ACCUMULATED lengths columns head leak_g tick rows share_on_the_aligned_column')
for key in sorted(acc):
    if key[2] in (0,1):
        e=acc[key]; print('ACCUMULATED',*key,e[0],round(e[1]/e[0],4))
