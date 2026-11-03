# A reference reading only (§16.29), never a part of the field: a two-sided byte table of K neighbours a side, its counts
# from the training passage, Witten-Bell interpolated down to one class in the alphabet, coding each held answer's bytes
# (and its first void) from their neighbours. Usage: python3 -I two_sided_table.py GSM8K_DIR K
import sys, math
from collections import defaultdict, Counter
G=sys.argv[1].rstrip('/')+'/'
def problems(path):
    text=open(path,'rb').read()
    out=[]
    for block in text.split(b'\n\n'):
        block=block.strip(b'\n')
        if not block: continue
        q,_,a=block.partition(b'\n')
        out.append((q,a))
    return out
train=problems(G+'TRAIN.txt'); held=problems(G+'HELD128.txt')
# bidirectional context tables over answers (and questions) of the training passage
K=int(sys.argv[2]) if len(sys.argv)>2 else 2
tabs=[defaultdict(Counter) for _ in range(K+1)]
VOID=256
def seq(a): return list(a)+[VOID]
for q,a in train:
    s=list(q)+[10]+seq(a)
    for t in range(len(s)):
        for k in range(K+1):
            ctx=tuple(s[t-k:t]) if t>=k else None
            ctx2=tuple(s[t+1:t+1+k]) if t+1+k<=len(s) else None
            if ctx is None or ctx2 is None: continue
            tabs[k][(ctx,ctx2)][s[t]]+=1
alphabet=len(set(b for q,a in train for b in q+a))+2
def prob(s,t):
    # interpolated backoff (Witten-Bell), from the widest context down
    p=1.0/alphabet
    for k in range(0,K+1):
        if t<k or t+1+k>len(s): break
        c=tabs[k].get((tuple(s[t-k:t]),tuple(s[t+1:t+1+k])))
        if not c: break
        n=sum(c.values()); u=len(c)
        lam=n/(n+u)
        p=lam*c.get(s[t],0)/n+(1-lam)*p
    return p
bits=0.0; count=0
for q,a in held:
    s=list(q)+[10]+seq(a)
    start=len(q)+1
    for t in range(start,len(s)):
        bits+=-math.log2(prob(s,t)); count+=1
print(f"K={K} held answer sites={count} bits_a_byte={bits/count:.3f}")
entries=sum(len(c) for c in tabs[K].values())
print(f"K={K} contexts={len(tabs[K])} entries={entries} train_bytes={sum(len(q)+len(a)+2 for q,a in train)}")
