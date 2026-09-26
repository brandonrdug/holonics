# Re-run bits2.py case (5) under (a) the Bezout/spectral projector the design states and
# (b) the certified release the design states (release only when certified inside tolerance).
from fractions import Fraction as F
from field import exact
import random
def bits(x): return x.numerator.bit_length()+x.denominator.bit_length()
def mbits(v): return max(bits(x) for x in v)
Pm=[[1 if (j==(i+1)%5) else 0 for j in range(5)] for i in range(5)]
S=[[F(1,3),F(1,4)],[F(-1,4),F(1,3)]]
C=[[F(1,2),0,0,0,0],[0,0,F(1,2),0,0]]
def stepT(x):
    crit=[sum(Pm[i][j]*x[j] for j in range(5)) for i in range(5)]
    st=[sum(C[i][j]*x[j] for j in range(5))+sum(S[i][j]*x[5+j] for j in range(2)) for i in range(2)]
    return crit+st
# Solve X P - S X = C for X (2x5): vectorize
import itertools
def solve(A,b):
    n=len(A); M=[row[:]+[b[i]] for i,row in enumerate(A)]
    for c in range(n):
        p=next(r for r in range(c,n) if M[r][c]!=0); M[c],M[p]=M[p],M[c]
        for r in range(n):
            if r!=c and M[r][c]!=0:
                f=M[r][c]/M[c][c]; M[r]=[a-f*bb for a,bb in zip(M[r],M[c])]
    return [M[i][n]/M[i][i] for i in range(n)]
idx=lambda i,j: i*5+j
A=[[F(0)]*10 for _ in range(10)]; b=[F(0)]*10
for i in range(2):
    for j in range(5):
        r=idx(i,j)
        # (X P)[i][j] = sum_k X[i][k] P[k][j]
        for k in range(5):
            if Pm[k][j]: A[r][idx(i,k)]+=Pm[k][j]
        # -(S X)[i][j] = -sum_l S[i][l] X[l][j]
        for l in range(2): A[r][idx(l,j)]-=S[i][l]
        b[r]=F(C[i][j])
Xv=solve(A,b); X=[[Xv[idx(i,j)] for j in range(5)] for i in range(2)]
print("Sylvester X (critical invariant subspace is the graph of X): max bits", max(bits(v) for r in X for v in r))
# check invariance: T(c, Xc) = (Pc, X P c)
c=[F(1),F(2),F(0),F(3),F(1)]
y=stepT(c+[sum(X[i][j]*c[j] for j in range(5)) for i in range(2)])
Pc=y[:5]; assert y[5:]==[sum(X[i][j]*Pc[j] for j in range(5)) for i in range(2)]
def run(epochs, aeon, mode, tol=F(1,16)):
    random.seed(7)
    x=[F(0)]*7; rec=[]; released=0; refused=0
    for e in range(1,epochs+1):
        x=stepT(x); x[random.randint(0,4)]+=1; x[5]+=F(1)
        if aeon and e%aeon==0:
            crit=x[:5]; Xc=[sum(X[i][j]*crit[j] for j in range(5)) for i in range(2)]
            stab=[x[5]-Xc[0], x[6]-Xc[1]]
            if mode=='script':  x=crit+[F(0),F(0)]
            elif mode=='bezout': x=crit+Xc
            elif mode=='certified':
                # receiver reads the stable coordinates with gain 1 (sup norm); release only inside tol
                if max(abs(v) for v in stab) <= tol: x=crit+Xc; released+=1
                else: refused+=1
        rec.append(mbits(x))
    return rec, released, refused
for mode in ('script','bezout','certified'):
    r,rel,ref=run(256,8,mode)
    label = {'script': 'withdrawn truncation (R2 C2a: zeroes the wrong coordinates)'}.get(mode, mode)
    print(label, "bits at epochs 8,32,128,256:", [r[i-1] for i in (8,32,128,256)], "max:", max(r), "released:",rel,"refused:",ref)
# does the script's truncation change what a receiver reading the stable coordinates sees?
random.seed(7)
x=[F(0)]*7
for e in range(8): x=stepT(x); x[random.randint(0,4)]+=1; x[5]+=F(1)
crit=x[:5]; Xc=[sum(X[i][j]*crit[j] for j in range(5)) for i in range(2)]
print("stable-coordinate reading before collapse:", "; ".join(exact(v) for v in x[5:]), " after script truncation: [0,0]  after Bezout:", "; ".join(exact(v) for v in Xc))
