import csv,sys
rows=list(csv.reader(open(sys.argv[1])))
hdr=None
for i,r in enumerate(rows):
    if r and r[0]=='Line No': hdr=r; start=i+1; break
idx={h:j for j,h in enumerate(hdr)}
S=idx['Warp Stall Sampling (All Samples)']; I=idx['Instructions Executed']; LOC=idx.get('L2 Theoretical Sectors Local')
stalls=[(j,h) for j,h in enumerate(hdr) if h.startswith('stall_')]
lines=[]
for r in rows[start:]:
    if len(r)<len(hdr) or r[2]!='-': continue
    try: s=int(r[S]); ins=int(r[I])
    except: continue
    loc=int(r[LOC]) if LOC is not None and r[LOC].isdigit() else 0
    st=sorted(((int(r[j]) if r[j].isdigit() else 0,h[6:]) for j,h in stalls),reverse=True)[:3]
    lines.append((s,int(r[0]),ins,loc,st,r[1][:70]))
tot=sum(l[0] for l in lines); toti=sum(l[2] for l in lines); totl=sum(l[3] for l in lines)
print(f"samples={tot} instructions={toti} local_sectors={totl}")
for s,ln,ins,loc,st,src in sorted(lines,reverse=True)[:int(sys.argv[2]) if len(sys.argv)>2 else 30]:
    print(f"{ln:5d} {s/tot*100:5.1f}% ins={ins/toti*100:5.1f}% loc={loc:7d} {' '.join(f'{n}:{v}' for v,n in st)} | {src}")
