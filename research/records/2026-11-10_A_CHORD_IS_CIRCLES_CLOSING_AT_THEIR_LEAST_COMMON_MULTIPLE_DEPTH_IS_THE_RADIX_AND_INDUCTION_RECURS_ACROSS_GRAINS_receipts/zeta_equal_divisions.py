# |zeta(1/2 + it)| at t = 2*pi*N/ln 2, by Borwein's eta series with integer coefficients (floats only in this reading).
import math, cmath
from math import factorial
n=760
d=[]; acc=0
for i in range(n+1):
    acc+=factorial(n+i-1)*4**i//(factorial(n-i)*factorial(2*i)) if i>0 or True else 0
    d.append(n*acc)
dn=d[n]; w=[((-1)**k)*float((d[k]-dn)/dn) if False else ((-1)**k)*((d[k]-dn)/dn) for k in range(n)]
logs=[math.log(k+1) for k in range(n)]
def zeta_half(t):
    s=complex(0.5,t)
    eta=-sum(w[k]*cmath.exp(-s*logs[k]) for k in range(n))
    return eta/(1-2**(1-s))
L=math.log(2)
# sanity: first zero near t=14.134725, and |zeta(1/2+0i)| = 1.4603545
print("check |zeta(1/2)| = %.6f (1.460355), |zeta(1/2+14.134725i)| = %.2e"%(abs(zeta_half(0.0)),abs(zeta_half(14.134725))))
vals=[(k/20, abs(zeta_half(2*math.pi*(k/20)/L))) for k in range(40,60*20+1)]
peaks=sorted(((v,N) for i,(N,v) in enumerate(vals) if 0<i<len(vals)-1 and v>vals[i-1][1] and v>vals[i+1][1]),reverse=True)
print("largest local maxima, N in [2,60] at step 0.05 (N, |zeta|):")
print(sorted((round(N,2),round(v,2)) for v,N in peaks[:16]))
import statistics
print("median |zeta| over the grid: %.2f; mean %.2f"%(statistics.median(v for _,v in vals),sum(v for _,v in vals)/len(vals)))
print("at integers:", [(int(N),round(v,2)) for N,v in vals if abs(N-round(N))<1e-9 and int(round(N)) in (5,7,10,12,19,22,24,27,31,34,41,46,53)])
