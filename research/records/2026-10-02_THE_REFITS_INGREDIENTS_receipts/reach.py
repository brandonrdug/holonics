from fractions import Fraction as F
import math, sys
W='.local/wt/window-chain/.local'
def E(path):
    L=open(path).read().split('\n')
    r,c=map(int,L[0].split()[1:])
    return [F(x) for row in L[1:1+r] for x in row.split()]
def lat(xs):
    return max(int(math.log2(x.denominator)) for x in xs)
def sub(a,b): return [x-y for x,y in zip(a,b)]
def dot(a,b): return sum(x*y for x,y in zip(a,b))
def cell(q,g=4096): # floor enclosure at grain g
    k=math.floor(q*g); return f"[{k}/{g}, {k+1}/{g})"
c0=E('research/records/2026-10-01_THE_GUARDED_WITNESS_receipts/c0.state')
m6=E(W+'/states/m6.state'); w16=E(W+'/states/w16end.state'); r13=E(W+'/states/r13held.state')
Lc=max(lat(c0),lat(m6),lat(w16)); u=F(1,2**Lc)
fit_raw=E(W+'/states/refit8_port.txt')
fit=[F(math.floor(x/u+F(1,2)))*u for x in fit_raw]   # nearest on the lattice
fit256=E('research/records/2026-09-30_THE_MODULUS_FOUNDED_OFF_ONE_receipts/refit_on_lattice.txt')
print(f"source port lattice exponent L = {Lc} (unit 2^-{Lc}); entries n = {len(c0)}")
step=F(1,2)  # the largest entry change one move makes at the kinetic entry scale: eta0*u <= 1/2
for name,start in (('opening',c0),('m6',m6),('w16',w16)):
    for fname,f in (('8-request fit',fit),('256-request refit',fit256)):
        d=sub(f,start)
        mx=max(abs(x) for x in d); l1=sum(abs(x) for x in d); l2sq=dot(d,d)
        print(f"{name} -> {fname}: largest entry change {mx} = {mx/u} units; l1 {l1/u} units; l2^2 {l2sq/u/u} units^2; least moves at 1/2 an entry per move: {math.ceil(mx/step)}")
def cos2(a,b):
    s=dot(a,b); q=F(s*s, dot(a,a)*dot(b,b)) if dot(a,a) and dot(b,b) else F(0)
    return ('+' if s>=0 else '-')+cell(q)
for name,start,end in (('w16 - m6',m6,w16),('r13 - opening (rho 168127/262144)',c0,r13)):
    disp=sub(end,start); to=sub(fit,start)
    frac=dot(disp,to)/dot(to,to)
    print(f"{name}: signed cos^2 with (fit - start) {cos2(disp,to)}; fraction of the distance covered along it {cell(frac)}; |disp|^2/|to|^2 {cell(dot(disp,disp)/dot(to,to))}")
prev=m6
for k in range(1,17):
    cur=E(f"{W}/wk/w{k}/w{k}-kinetic.state")
    print(f"move {k}: signed cos^2 of (E_k - E_(k-1)) with (fit - E_(k-1)) {cos2(sub(cur,prev),sub(fit,prev))}")
    prev=cur
