#!/usr/bin/env python3
"""The held-under three-part split (theory, November 9 08:13, 08:15): the swing G'(S) - G'(B) per place as smooth
G'(theta_S; C_B, h_B) - G'(theta_B) + halvings G'(theta_S; C_B, h_S) - G'(theta_S; C_B, h_B) + support G'(theta_S) - G'(theta_S; C_B, h_S),
each part's sum of squares over the swing's, and the cross terms; in the order given (B's maps held). G' is G less beta at each theta.
Args: PLAIN_B(enum:lap) PLAIN_S(enum:lap) UNDER_CBHB UNDER_CB STATE_B STATE_S. A reading only."""
import csv, math, sys
names="enc before after q q_bias v v_bias out out_bias a a_bias b b_bias w w_bias read read_bias moment_before moment_after temper probe probe_bias pace moment_face moment_face_bias lift_bias pair_c face_temper".split()
lens=[3232,3232,3232,2048,64,2048,64,2048,32,1024,32,1024,32,1024,32,1024,100,3232,3232,8,2048,64,202,2048,32,32,32,1]
off={}; at=0
for n,l in zip(names,lens): off[n]=at; at+=l
def theta(p):
    for l in open(p):
        t=l.split()
        if len(t)==31223 and t[0].lstrip('-').isdigit(): return list(map(int,t))
def betas(th):
    b=th[off['lift_bias']:off['lift_bias']+32]
    return [-(sum(x*y for x,y in zip(th[off['enc']+c*32:off['enc']+(c+1)*32],b)) + th[off['read_bias']+c]*2**16) for c in range(100)]
def codes(spec, B):
    path,lap=(spec.split(':')+['-1'])[:2]; lap=int(lap); o={}
    for r in csv.DictReader(open(path),delimiter='\t'):
        if int(r['lap'])!=lap: continue
        T=2.0**(int(r['log2_t'])/2**24); g=[(int(v)-b)/2**32 for v,b in zip(r['energies'].split(','),B)]; lo=min(g)
        w=[2.0**(-(x-lo)/T) for x in g]; o[(r['problem'],r['place'])]=-math.log(w[int(r['truth'])]/sum(w))
    return o
pb,ps,ubh,ub,sb,ss=sys.argv[1:7]
Bb,Bs=betas(theta(sb)),betas(theta(ss))
GB=codes(pb,Bb); GS=codes(ps,Bs); Gbh=codes(ubh,Bs); Gb=codes(ub,Bs)
ks=list(GB)
sm={k:Gbh[k]-GB[k] for k in ks}; hv={k:Gb[k]-Gbh[k] for k in ks}; sp={k:GS[k]-Gb[k] for k in ks}
tot=sum((GS[k]-GB[k])**2 for k in ks)
sq=lambda d: sum(v*v for v in d.values())/tot
cr=lambda a,b: 2*sum(a[k]*b[k] for k in ks)/tot
mean=lambda d: sum(d.values())/len(ks)
print(f"  sum dG'^2 {tot:.1f} ({tot/len(ks):.3f} a place); smooth {sq(sm):.2f}, halvings {sq(hv):.2f}, support {sq(sp):.2f}; cross sm*hv {cr(sm,hv):+.2f}, sm*sp {cr(sm,sp):+.2f}, hv*sp {cr(hv,sp):+.2f}; means: smooth {mean(sm):+.4f}, halvings {mean(hv):+.4f}, support {mean(sp):+.4f}")
