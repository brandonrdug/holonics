#!/usr/bin/env -S python3 -I
"""forward_class_ruler.py ARM… (run inside a directory holding `cut_rows.tsv` and `cut_<ARM>/codes.tsv`): a ruler (the lead, November 28;
the formal thread's G-Z74 of 10:51 UTC). Her forward code (`read-reach … law`, the first setting) at the places past the reach ruler's
cut at 256 of each row, parted by the class of the place's octet (a word's first letter, a letter inside a word, a space, a line's end or
a tab, a digit, any other mark), the first arm's mean and each other arm's paired difference from it with its standard error, on one
partition for every arm. Outside the machine; floats at the exterior.
"""
import math, sys
from collections import defaultdict
rows=[]
for l in open('cut_rows.tsv', encoding='utf-8'):
    f=l.rstrip('\n').split('\t')
    rows.append(b''.join(bytes.fromhex(t[4:]) if t.startswith('hex:') else t.replace('\\n','\n').encode() for t in f[1:3]))
def letter(b): return 65<=b<=90 or 97<=b<=122
def klass(t,i):
    b=t[i]
    if letter(b): return 'first_letter' if i==0 or not letter(t[i-1]) else 'inside_letter'
    if b==32: return 'space'
    if b in (10,9): return 'line_tab'
    if 48<=b<=57: return 'digit'
    return 'mark'
arms=sys.argv[1:]
def load(n):
    d={}
    for l in open(f'cut_{n}/codes.tsv'):
        f=l.split('\t'); d[(int(f[0]),int(f[2]))]=int(f[3])*math.log(2)/(1<<20)
    return d
A={n:load(n) for n in arms}
base=arms[0]
by=defaultdict(lambda: defaultdict(list))
for (r,p),v in A[base].items():
    if p<257: continue
    t=rows[r]
    k=klass(t,p) if p<len(t) else 'end'
    for n in A: by[k][n].append(A[n][(r,p)])
    for n in A: by['all'][n].append(A[n][(r,p)])
for k in ('all','first_letter','inside_letter','space','mark','digit','line_tab','end'):
    if k not in by: continue
    p=by[k][base]; n=len(p)
    out=[f"FORWARD_CLASS {k} places={n} {base}={sum(p)/n:.4f}"]
    for a in arms[1:]:
        d=[x-y for x,y in zip(by[k][a],p)]; m=sum(d)/n; se=math.sqrt(sum((x-m)**2 for x in d)/(n-1)/n)
        out.append(f"{a}-{base}={m:+.4f}(±{se:.4f})")
    print(' '.join(out))
