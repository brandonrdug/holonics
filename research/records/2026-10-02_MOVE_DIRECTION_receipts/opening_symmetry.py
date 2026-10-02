"""The opening E0 against the comparison's lattice symmetries (the move-direction record, section 2).

E0 is the declared sign sequence times 1/2 (`hnn::constitution::declared_sign`, locus 0, ring 0),
120 rows by 5 columns; node t is the complex entry (row 2t, row 2t+1). For each ring shift m of 60
and each of the 8 signed permutations of a node's two coordinates (quarter turns and conjugation),
it tests whether the element fixes E0, and prints the largest number of the 300 complex entries
any one nontrivial element leaves unchanged. Exact integer arithmetic (the factor 1/2 is dropped).
"""
M=(1<<64)-1
def sm(s):
    z=(s+0x9E3779B97F4A7C15)&M
    z=((z^(z>>30))*0xBF58476D1CE4E5B9)&M
    z=((z^(z>>27))*0x94D049BB133111EB)&M
    return z^(z>>31)
def sign(locus,i,j):
    z=sm(0)
    for x in (locus,i,j): z=sm(z^x)
    return 1 if z&1 else -1
N,A=60,5
E=[[sign(0,i,j) for j in range(A)] for i in range(2*N)]  # times 1/2
# node t, column j, as the integer pair (Re, Im)
Z=[[(E[2*t][j],E[2*t+1][j]) for j in range(A)] for t in range(N)]
# the quarter turns i^r and their composites with conjugation, on integer pairs
def turn(z,r):
    for _ in range(r): z=(-z[1],z[0])
    return z
d4=[(lambda z,r=r:turn(z,r)) for r in range(4)]+[(lambda z,r=r:turn((z[0],-z[1]),r)) for r in range(4)]
fixed=[]
for m in range(N):
    for k,d in enumerate(d4):
        if (m,k)==(0,0): continue
        if all(Z[(t+m)%N][j]==d(Z[t][j]) for t in range(N) for j in range(A)): fixed.append((m,k))
print("nontrivial fixing elements:",fixed)
# largest agreement fraction over nontrivial elements
best=max(((sum(Z[(t+m)%N][j]==d(Z[t][j]) for t in range(N) for j in range(A)),m,k) for m in range(N) for k,d in enumerate(d4) if (m,k)!=(0,0)))
print("most entries agreeing under one element:",best, "of", N*A)
