#!/usr/bin/env python3
"""The urn's base measure from the tree's own root (the contact loop record, section 30).

[measured-diagnostic; exterior] The count face's replica at depth 16 and prior mass 2^-J (environment
J, default 3), each node's prior masses split by a base pi: `even` (1/2, the law), `root` (the
digit tree's depth-0 node's face), `parent` (the parent's face, chained), `halfroot` (the root's
face mixed with the even split at 1/2), `halfroot-gG` (that, read at grain 2^-G), and `shared-g4`
(one base for every node of the digit tree, the root included: the root's even-base face mixed with
the even split at 1/2, read at grain 1/16). Environment MODES lists them. Arguments: the cut file,
its cells, the held-out start. Floating point is a search outside the machine; each total is the
exact dyadic of its float at 24 significant bits.
"""
import math, sys
sys.path.insert(0,'.')
from receiver_oracle import exact
import os
ALPHA=2.0**-int(os.environ.get("J","3")); DEPTH=16
def run(cells, mode):
    nodes={}; codes=[]
    for j,x in enumerate(cells):
        context=tuple(cells[max(0,j-DEPTH):j][::-1]); bits=0.0; prefix=1
        for i in range(7,-1,-1):
            b=(x>>i)&1; path=[]
            for d in range(len(context)+1):
                path.append(nodes.setdefault((prefix,context[:d]),[0,0,0.0]))
            # bases: 'even' 1/2; 'root' the depth-0 node's KT face; 'parent' each node's parent face (chained)
            bases=[]
            pi=[0.5,0.5]
            for d,node in enumerate(path):
                bases.append(pi)
                n0,n1,_=node
                kk=[(n0+2*ALPHA*pi[0])/(n0+n1+2*ALPHA),(n1+2*ALPHA*pi[1])/(n0+n1+2*ALPHA)]
                if mode=='parent': pi=kk
                elif mode=='root' and d==0: pi=kk
                elif mode=='halfroot' and d==0: pi=[(kk[0]+0.5)/2,(kk[1]+0.5)/2]
                elif mode.startswith('halfroot-g') and d==0:
                    g=int(mode[len('halfroot-g'):]); p0=round(((kk[0]+0.5)/2)*2**g)/2**g; pi=[p0,1-p0]
            if mode=='even': bases=[[0.5,0.5]]*len(path)
            if mode=='shared-g4':
                n0,n1,_=path[0]
                k0=(n0+ALPHA)/(n0+n1+2*ALPHA)
                p0=round(((k0+0.5)/2)*16)/16
                bases=[[p0,1-p0]]*len(path)
            rev=list(reversed(list(zip(path,bases)))); ks=[]; qs=[]
            for level,(node,pi) in enumerate(rev):
                n0,n1,lb=node
                k=[(n0+2*ALPHA*pi[0])/(n0+n1+2*ALPHA),(n1+2*ALPHA*pi[1])/(n0+n1+2*ALPHA)]; ks.append(k)
                if level==0: q=k[:]
                else:
                    lam=1/(1+math.exp(-lb)) if lb>-700 else 0.0
                    q=[lam*k[0]+(1-lam)*q[0], lam*k[1]+(1-lam)*q[1]]
                qs.append(q[:])
            bits-=math.log2(q[b])
            for level,(node,pi) in enumerate(rev):
                if level>0: node[2]+=math.log(ks[level][b]/qs[level-1][b])
                node[b]+=1
            prefix=2*prefix+b
        codes.append(bits)
    return codes
path,n,held=sys.argv[1],int(sys.argv[2]),int(sys.argv[3])
cells=list(open(path,'rb').read()[:n])
for mode in os.environ.get('MODES','even,root,parent').split(','):
    c=run(cells,mode); print(mode,'development',exact(sum(c[:held])),'held out',exact(sum(c[held:])),flush=True)
