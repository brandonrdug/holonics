#!/usr/bin/env -S python3 -I
"""A ruler (the lead, November 19, on Brandon's question of 03:17 UTC: how much of her writes is lossless recollection of the original
continuations): a `write-next` output (`forms.written`: label, prompt, written, reference) read against its reference continuations
(`ref`: the bytes shared before the write parts from the reference, the share of written bytes inside runs of 8+ and 16+ bytes the
reference holds, the longest shared run) or against its slice's training documents (`train K`: the share of written bytes inside K-byte
windows, taken every K/2 bytes, that occur anywhere in DOCS_<slice>.bin, and whether the held passage itself, its prompt's last 48
bytes with the reference's first 16, stands in the training documents). Outside the machine; bytes and counts only.
Usage: write_recall_ruler.py ref FORMS | write_recall_ruler.py train FORMS K"""
import sys, mmap, os
def rows(p):
    out=[]
    for line in open(p,'rb'):
        f=line.rstrip(b'\n').split(b'\t')
        if len(f)>=4:
            un=lambda b: b.replace(b'\\n',b'\n').replace(b'\\t',b'\t')
            out.append((f[0].decode(), un(f[1]), un(f[2]), un(f[3])))
    return out
def lcs(a,b):
    best=0; bi=0
    for i in range(len(a)):
        j=i+best+1
        while j<=len(a) and a[i:j] in b: best=j-i; bi=i; j+=1
    return best, a[bi:bi+best]
def cover(a, src, k):
    # bytes of a inside some run of length >= k that occurs in src
    n=len(a); cov=[0]*n; i=0
    while i+k<=n:
        if a[i:i+k] in src:
            j=i+k
            while j<n and a[i:j+1] in src: j+=1
            for t in range(i,j): cov[t]=1
            i=j
        else: i+=1
    return sum(cov)
mode=sys.argv[1]; path=sys.argv[2]
R=rows(path)
if mode=='ref':
    agg=dict(n=0,bytes=0,pre=0,pre_zero=0,cov8=0,cov16=0,lcs=[])
    for lab,p,w,r in R:
        pre=0
        while pre<min(len(w),len(r)) and w[pre]==r[pre]: pre+=1
        L,_=lcs(w,r)
        agg['n']+=1; agg['bytes']+=len(w); agg['pre']+=pre; agg['pre_zero']+= pre==0
        agg['cov8']+=cover(w,r,8); agg['cov16']+=cover(w,r,16); agg['lcs'].append(L)
    l=sorted(agg['lcs'])
    print(f"REF {os.path.basename(os.path.dirname(path))}: writes={agg['n']} bytes={agg['bytes']} mean_common_prefix={agg['pre']/agg['n']:.1f} bytes (none at the first byte: {agg['pre_zero']}) | bytes inside a run of 8+ shared with the reference: {agg['cov8']/agg['bytes']:.3f}, of 16+: {agg['cov16']/agg['bytes']:.3f} | longest shared run: median {l[len(l)//2]}, max {l[-1]}")
else:
    S='/home/b/Workspaces/holonics/.local/corpus/store-2026-11-12'
    k=int(sys.argv[3])
    maps={}
    tot=dict(bytes=0,cov=0,promptdup=0,refdup=0,n=0)
    for lab,p,w,r in R:
        sl=lab.split(':')[0]
        if sl not in maps:
            f=open(f'{S}/DOCS_{sl}.bin','rb'); maps[sl]=mmap.mmap(f.fileno(),0,access=mmap.ACCESS_READ)
        m=maps[sl]
        # greedy cover of the write by runs of k+ bytes found in the slice's training documents
        n=len(w); covered=[0]*n; runs=[]
        for i in range(0, n-k+1, k//2):
            if m.find(w[i:i+k])>=0:
                for t in range(i,i+k): covered[t]=1
                runs.append(w[i:i+k])
        cov=sum(covered)
        dup = m.find(p[-48:]+r[:16])>=0
        refin = m.find(r[:32])>=0
        tot['bytes']+=n; tot['cov']+=cov; tot['promptdup']+=dup; tot['refdup']+=refin; tot['n']+=1
        print(f"  {lab}: {cov}/{n} bytes in {k}-byte windows met in training; held passage (prompt tail + continuation) in training: {dup}; reference's first 32 bytes in training: {refin}; runs: {[x.decode('utf-8','replace') for x in runs][:4]}")
    print(f"TRAIN k={k}: {tot['cov']}/{tot['bytes']} bytes ({tot['cov']/tot['bytes']:.3f}) of her writes lie in {k}-byte windows (taken every {k//2} bytes) met in the training documents; held passages found in training: {tot['promptdup']} of {tot['n']}; references' openings found in training: {tot['refdup']} of {tot['n']}")
