# Is the design's tick power-neutral? Junction Swing with weights kappa_ri*Y_i, then lossless one-hop transit.
from fractions import Fraction as F
import random
random.seed(3)
G=6; d=2
nbr={g:[(g-1)%G,(g+1)%G] for g in range(G)}
Y={}
for g in range(G):
    h=(g+1)%G; y=F(random.randint(1,5),random.randint(1,5)); Y[(g,h)]=y; Y[(h,g)]=y
Yself=[F(random.randint(1,5),random.randint(1,5)) for _ in range(G)]
def run(kappa, ticks=6):
    a={(g,h):[F(random.randint(-3,3),random.randint(1,3)) for _ in range(d)] for g in range(G) for h in nbr[g]}
    s=[[F(random.randint(-3,3),random.randint(1,3)) for _ in range(d)] for g in range(G)]
    def power(a,s):
        return sum(Yself[g]*sum(x*x for x in s[g]) for g in range(G)) + sum(kappa[(g,h)]*Y[(g,h)]*sum(x*x for x in a[(g,h)]) for (g,h) in a)
    out=[power(a,s)]
    for t in range(ticks):
        b={}; s2=[]
        for g in range(G):
            w={h:kappa[(g,h)]*Y[(g,h)] for h in nbr[g]}
            tot=Yself[g]+sum(w.values())
            v=[(Yself[g]*s[g][k]+sum(w[h]*a[(g,h)][k] for h in nbr[g]))/tot for k in range(d)]
            for h in nbr[g]: b[(g,h)]=[2*v[k]-a[(g,h)][k] for k in range(d)]
            s2.append([2*v[k]-s[g][k] for k in range(d)])   # element = identity (a lossless Cay would keep |s|)
        # junction-local power check
        a={(h,g):b[(g,h)] for (g,h) in b}; s=s2          # transit: wave leaving g toward h arrives at h from g
        out.append(power(a,s))
    return out
beta=[F(random.randint(1,4)) for _ in range(G)]
Q={}
for g in range(G):
    h=(g+1)%G; q=F(random.randint(1,4)); Q[(g,h)]=q; Q[(h,g)]=q
asym={(g,h):F(2)**(-(beta[g]*Q[(g,h)]//2)) for g in range(G) for h in nbr[g]}   # per-ring beta (the design's s_ri = -beta_r Q_ri/2), L=1
sym={(g,h):F(2)**(-(min(beta[g],beta[h])*Q[(g,h)]//2)) for g in range(G) for h in nbr[g]}  # one exponent per contact
pa=run(asym); ps=run(sym)
print("per-ring beta: kappa_gh == kappa_hg on every contact?", all(asym[(g,h)]==asym[(h,g)] for (g,h) in asym))
print("per-ring beta, global weighted power over ticks:", [float(p) for p in pa])
print("per-contact kappa, global weighted power over ticks:", [float(p) for p in ps])
