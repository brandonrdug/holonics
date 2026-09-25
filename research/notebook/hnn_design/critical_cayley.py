# The ring element Cay_r with skew slices (W_s = 0, the reaction_stage_isometry case) is lossless and
# non-closing. If the storage wave persists across words, repeated injections accumulate in it exactly
# like the banned rotation-ring moment. The collapse keeps critical (unit-modulus) modes, so nothing bounds it.
from fractions import Fraction as F
import random
random.seed(5)
def bits(x): return x.numerator.bit_length()+x.denominator.bit_length()
n=4
def solve(A,b):
    m=len(A); M=[row[:]+[b[i]] for i,row in enumerate(A)]
    for c in range(m):
        p=next(r for r in range(c,m) if M[r][c]!=0); M[c],M[p]=M[p],M[c]
        for r in range(m):
            if r!=c and M[r][c]!=0:
                f=M[r][c]/M[c][c]; M[r]=[a-f*bb for a,bb in zip(M[r],M[c])]
    return [M[i][m]/M[i][i] for i in range(m)]
K=[[F(0)]*n for _ in range(n)]
for i in range(n):
    for j in range(i+1,n):
        v=F(random.randint(-3,3),random.randint(1,3)); K[i][j]=v; K[j][i]=-v
L=[[(1 if i==j else 0)-K[i][j]/2 for j in range(n)] for i in range(n)]
R=[[(1 if i==j else 0)+K[i][j]/2 for j in range(n)] for i in range(n)]
s=[F(0)]*n; out={}
for t in range(1,257):
    s=solve(L,[sum(R[i][j]*s[j] for j in range(n)) for i in range(n)])
    s[0]+=random.choice([F(0),F(1)])       # one 1-bit injection per word into the persisting storage wave
    if t in (8,32,128,256): out[t]=max(bits(v) for v in s)
print("persisting lossless Cay storage wave, max bits after 8,32,128,256 words:", out)
print("norm preserved (lossless):", sum(x*x for x in solve(L,[sum(R[i][j]*[F(1),0,0,0][j] for j in range(n)) for i in range(n)]))==1)
