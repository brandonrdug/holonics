# Probe (floats, a reading): how a grown chart's frictions change at the count's first read, under two charts of the mass.
#   alpha: m(t) = dh(t)^2/(1+dh(t))                       (the site's own rest friction)
#   gamma: m(t) = mu2(d_c) * 2^x(t), dh(t) = d_c 2^x(t)   (level through mu2, rows linear) == m = dh/5 with converted bias
import math, random
def mu2(d): return d*d/(1+d)
def rest(m): return (1+math.sqrt(1+4/m))/2
def run(dh, masses, r0):
    r=r0; out=[]
    for m in masses:
        d=m*r; out.append((d,r)); r=1+r/(1+d)
    return out
def stats(name, dh, masses, r0, x, kinds=None):
    out=run(dh,masses,r0)
    n=len(dh); burn=200
    dl=[math.log2(out[t][0]/dh[t]) for t in range(burn,n)]
    xs=x[burn:]
    mx=sum(xs)/len(xs); md=sum(dl)/len(dl)
    cov=sum((a-mx)*(b-md) for a,b in zip(xs,dl))/len(xs); var=sum((a-mx)**2 for a in xs)/len(xs)
    sd=math.sqrt(sum((b-md)**2 for b in dl)/len(dl))
    # weights concentration: sum w^2 of the charge's weights over a window ~ steady: E[w/(2-w)]-ish; report mean w
    wn=[out[t][0]/(1+out[t][0]) for t in range(burn,n)]; wb=[dh[t]/(1+dh[t]) for t in range(burn,n)]
    line=f"  {name:6s} mean shift of l {md:+.3f}; slope of the shift on the site's own x {cov/var if var>0 else 0:+.3f} (log-contrast x{1+(cov/var if var>0 else 0):.2f}); sd of shift {sd:.3f}; mean take w {sum(wn)/len(wn):.3f} (built {sum(wb)/len(wb):.3f})"
    if kinds:
        for k in sorted(set(kinds)):
            sel=[dl[i] for i in range(len(dl)) if kinds[burn+i]==k]
            line+=f"; {k}: {sum(sel)/len(sel):+.3f}"
    print(line)
rng=random.Random(1)
n=40000
for d_c in (0.11,0.25,0.43):
    for sigma in (0.5,1.0):
        x=[rng.gauss(0,sigma) for _ in range(n)]
        dh=[d_c*2**v for v in x]
        print(f"level d_c={d_c}, iid site spread sigma={sigma} units of l")
        stats("alpha", dh, [mu2(d) for d in dh], rest(mu2(d_c)), x)
        stats("gamma", dh, [mu2(d_c)*2**v for v in x], rest(mu2(d_c)), x)
# kinds in runs: open sites offset delta_o, given offset delta_g, plus iid spread; quarter-4-like (7/8 open, geometric runs) and quarter-1-like
def strand(p_open, d_o, d_g, sigma, n):
    kinds=[]; x=[]
    for _ in range(n):
        k='open' if rng.random()<p_open else 'given'
        kinds.append(k); x.append((d_o if k=='open' else d_g)+rng.gauss(0,sigma))
    return kinds,x
for label,(d_o,d_g) in (("holder (open -0.4, given +0.4)",(-0.4,0.4)),("relay (open +0.3, given -0.3)",(0.3,-0.3)),("clean holder (open -3, given 0)",(-3.0,0.0))):
    for q,p in (("quarter 4 like, 7/8 open",0.875),("quarter 1 like, 1/8 open",0.125)):
        kinds,x=strand(p,d_o,d_g,0.5,n)
        d_c=0.25
        dh=[d_c*2**v for v in x]
        print(f"{label}; {q}; sigma 0.5")
        stats("alpha", dh, [mu2(d) for d in dh], rest(mu2(d_c)), x, kinds)
        stats("gamma", dh, [mu2(d_c)*2**v for v in x], rest(mu2(d_c)), x, kinds)
