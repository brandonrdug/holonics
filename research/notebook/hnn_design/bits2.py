# Exact bit growth under the revised step-4 law, against the review's measurements (bits.py).
from fractions import Fraction as F
import random, math
random.seed(1)
def bits(x): return x.numerator.bit_length()+x.denominator.bit_length()
def mbits(v): return max(bits(x) for x in v)
def solve(A,b):
    n=len(A); M=[row[:]+[b[i]] for i,row in enumerate(A)]
    for c in range(n):
        p=next(r for r in range(c,n) if M[r][c]!=0); M[c],M[p]=M[p],M[c]
        for r in range(n):
            if r!=c and M[r][c]!=0:
                f=M[r][c]/M[c][c]; M[r]=[a-f*bb for a,bb in zip(M[r],M[c])]
    return [M[i][n]/M[i][i] for i in range(n)]
def matvec(A,x): return [sum(a*b for a,b in zip(r,x)) for r in A]
n=4
def skew():
    A=[[F(0)]*n for _ in range(n)]
    for i in range(n):
        for j in range(i+1,n):
            v=F(random.randint(-3,3),random.randint(1,3)); A[i][j]=v; A[j][i]=-v
    return A
slices=[skew() for _ in range(n)]
Ws=[[F(-1 if i==j else 0) for j in range(n)] for i in range(n)]
y0=[F(random.randint(-3,3),random.randint(1,4)) for _ in range(n)]
def cayley_step(K,y):
    L=[[(1 if i==j else 0)-K[i][j]/2 for j in range(n)] for i in range(n)]
    R=[[(1 if i==j else 0)+K[i][j]/2 for j in range(n)] for i in range(n)]
    return solve(L,matvec(R,y))
# (1) review: K read from the evolving state every tick
y=y0[:]; out=[]
for t in range(7):
    K=[[Ws[i][j]+sum(y[r]*slices[r][i][j] for r in range(n)) for j in range(n)] for i in range(n)]
    y=cayley_step(K,y); out.append(mbits(y))
print("state-read reaction, ticks 1-7:", out)
# (2) revised: K read from the sheet class of the contrast (a finite set of operators)
def sheet(v): return [F(1) if x>=0 else F(-1) for x in v]
y=y0[:]; out=[]
for t in range(32):
    s=sheet(y)
    K=[[Ws[i][j]+sum(s[r]*slices[r][i][j] for r in range(n)) for j in range(n)] for i in range(n)]
    y=cayley_step(K,y); out.append(mbits(y))
print("class-read reaction, ticks 1,2,4,8,16,32:", [out[i-1] for i in (1,2,4,8,16,32)])
# (3) junction Swings + one-hop transit on a 6-ring cycle, ring width 2, rational admittances
G=6; d=2
Y={}
for g in range(G):
    Y[(g,(g+1)%G)]=F(random.randint(1,5),random.randint(1,5)); Y[((g+1)%G,g)]=Y[(g,(g+1)%G)]
Yself=[F(random.randint(1,5),random.randint(1,5)) for _ in range(G)]
# waves: incoming at ring g from neighbour h: a[(g,h)] in Q^d ; self port wave s[g]
a={ (g,h):[F(0)]*d for (g,h) in Y }
sw=[[F(0)]*d for _ in range(G)]
a[(1,0)]=[F(1),F(0)]   # one change injected at ring 1 from ring 0
support=[]
out=[]
for t in range(1,65):
    b={}
    for g in range(G):
        ports=[(g,h) for (gg,h) in Y if gg==g]
        tot=Yself[g]+sum(Y[p] for p in ports)
        v=[(Yself[g]*sw[g][k]+sum(Y[p]*a[p][k] for p in ports))/tot for k in range(d)]
        for p in ports: b[p]=[2*v[k]-a[p][k] for k in range(d)]
        sw[g]=[2*v[k]-sw[g][k] for k in range(d)]
    a={ (h,g):b[(g,h)] for (g,h) in b }   # transit: one hop
    reached=sorted({g for (g,h),w in a.items() if any(x!=0 for x in w)})
    if t<=3: support.append(reached)
    out.append(max(mbits(w) for w in a.values()))
print("local Swing tick: rings reached after ticks 1-3:", support)
print("local Swing tick, bits at ticks 1,2,4,8,16,32,64:", [out[i-1] for i in (1,2,4,8,16,32,64)])
# (4) source moment: Cayley ring (review) vs closing period-5 ring with selective stepping
c,s_=F(3,5),F(4,5); Uinv=[[c,s_],[-s_,c]]
m=[F(0),F(0)]; P=[[F(1),F(0)],[F(0),F(1)]]
codes={0:[F(1),F(0)],1:[F(0),F(1)]}
rot={}
src=[random.randint(0,1) for _ in range(4096)]
for k in range(1,129):
    v=matvec(P,codes[src[k-1]]); m=[a_+b_ for a_,b_ in zip(m,v)]
    P=[[sum(P[i][l]*Uinv[l][j] for l in range(2)) for j in range(2)] for i in range(2)]
    if k in (2,8,32,128): rot[k]=mbits(m)
print("Cayley-ring moment bits at n=2,8,32,128:", rot)
dper=5; notch={1}
M=[[0,0] for _ in range(dper)]; tau=0; per={}
for k in range(1,4097):
    x=src[k-1]; tau=(tau+(1 if x in notch else 0))%dper
    M[tau][x]+=1
    if k in (2,8,32,128,1024,4096): per[k]=max(v.bit_length() for row in M for v in row)
print("closing period-5 ring, selective stepping, moment bits at n=2,8,32,128,1024,4096:", per)
# (5) standing carried across epochs: critical (period-5 permutation) + stable (dissipative contact), injected each epoch
# T = [[P,0],[C,S]]  S has rational entries with spectral radius < 1
Pm=[[1 if (j==(i+1)%5) else 0 for j in range(5)] for i in range(5)]
S=[[F(1,3),F(1,4)],[F(-1,4),F(1,3)]]
C=[[F(1,2),0,0,0,0],[0,0,F(1,2),0,0]]
def stepT(x):
    crit=[sum(Pm[i][j]*x[j] for j in range(5)) for i in range(5)]
    st=[sum(C[i][j]*x[j] for j in range(5))+sum(S[i][j]*x[5+j] for j in range(2)) for i in range(2)]
    return crit+st
def run(epochs, aeon):
    x=[F(0)]*7; rec=[]
    for e in range(1,epochs+1):
        x=stepT(x); x[random.randint(0,4)]+=1; x[5]+=F(1)
        if aeon and e%aeon==0:
            x=x[:5]+[F(0),F(0)]    # collapse: stable part released at the aeon boundary
        rec.append(mbits(x))
    return rec
random.seed(7); wo=run(256,None)
random.seed(7); wq=run(256,8)
print("standing without quotient, bits at epochs 8,32,128,256:", [wo[i-1] for i in (8,32,128,256)])
print("WITHDRAWN (R2 C2a: it zeroed the wrong coordinates, so these are not the collapse's bits):")
print("   the first design's truncation every 8 epochs, bits at 8,32,128,256 (at the boundary):", [wq[i-1] for i in (8,32,128,256)])
print("   max within an aeon, with that truncation:", max(wq))
