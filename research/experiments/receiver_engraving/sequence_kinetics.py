"""Exact sequence-dependent ligand binding/catalysis extension of the FCC fold chart."""
from collections import defaultdict
from pathlib import Path
import json
from fractions import Fraction as Q
from sequence_folding import build_model, SEQUENCES, state_key, contacts

def open_dirs(state, dirs):
    occupied=set(state); p=state[5]
    return tuple(d for d in dirs if tuple(p[k]+d[k] for k in range(3)) not in occupied)

def advance(seq, states, index, fold_rows, denominator, initial, dirs, open_cache, steps=24):
    Dj=2*denominator
    # keyed by ('f', state-index) or ('b', state-index, direction)
    mass={('f',initial):1}; product={}; drawn={}; snapshots={}
    # initial index is supplied by caller through the straight-chain index convention
    def add(dst, m, prod=0, draw=0):
        mass[dst]=mass.get(dst,0)+m
        if prod: product[dst]=product.get(dst,0)+prod
        if draw: drawn[dst]=drawn.get(dst,0)+draw
    def snapshot(t):
        total=sum(mass.values()); pm=sum(product.values()); dm=sum(drawn.values())
        bound=sum(v for k,v in mass.items() if k[0]=='b')
        access_free=sum(v*len(open_cache[k[1]]) for k,v in mass.items() if k[0]=='f')
        access_all=sum(v*len(open_cache[k[1]]) for k,v in mass.items())
        den=Dj**t
        return {"denominator":str(den),"mass_numerator":str(total),"free_numerator":str(total-bound),
                "bound_numerator":str(bound),"product_numerator":str(pm),"net_drawn_numerator":str(dm),
                "open_free_direction_numerator":str(access_free),"open_all_direction_numerator":str(access_all),
                "bound_plus_product_equals_drawn":bound+pm==dm,
                "probability_mass_equals_one":total==den}
    snapshots[0]=snapshot(0)
    for t in range(1,steps+1):
        nm={}; np={}; nd={}
        old_mass,old_product,old_drawn=mass,product,drawn; mass={}; product={}; drawn={}
        def transfer(src,dst,w,dp=0,dd=0):
            m=old_mass.get(src,0); p=old_product.get(src,0); d=old_drawn.get(src,0)
            if not (m or p or d): return
            mass[dst]=mass.get(dst,0)+m*w
            product[dst]=product.get(dst,0)+p*w+m*w*dp
            drawn[dst]=drawn.get(dst,0)+d*w+m*w*dd
        for src,m in old_mass.items():
            if src[0]=='f':
                i=src[1]; open_now=open_cache[i]; fold_sum=0
                for j,w in fold_rows[i]:
                    fold_sum+=w; transfer(src,('f',j),w)
                # Half chemistry: each open direction binds with global probability 1/48.
                for d in open_now: transfer(src,('b',i,d),Dj//48,dd=1)
                transfer(src,src,Dj//2-sum(Dj//48 for _ in open_now))
            else:
                i,d=src[1],src[2]; fold_sum=0
                for j,w in fold_rows[i]:
                    if d in open_cache[j]: transfer(src,('b',j,d),w)
                    else: transfer(src,src,w)
                transfer(src,('f',i),Dj//8,dd=-1)
                transfer(src,src,Dj//4)
                transfer(src,('f',i),Dj//8,dp=1)
        assert sum(mass.values())==Dj**t and all(v>=0 for v in mass.values())
        assert sum(product.values())>=0 and sum(drawn.values())>=0
        if not all(drawn.get(k,0)==product.get(k,0)+(mass.get(k,0) if k[0]=='b' else 0) for k in set(mass)|set(product)|set(drawn)):
            bad=next(k for k in set(mass)|set(product)|set(drawn) if drawn.get(k,0)!=product.get(k,0)+(mass.get(k,0) if k[0]=='b' else 0))
            raise AssertionError((t,bad,mass.get(bad,0),product.get(bad,0),drawn.get(bad,0)))
        if t in (6,12,24): snapshots[t]=snapshot(t)
    return snapshots

def main():
    states,index,neighbors,counts,max_drop,denominator=build_model()
    from sequence_folding import STEPS
    open_cache=[open_dirs(s,STEPS) for s in states]
    straight=tuple((i,i,0) for i in range(6)); initial=index[state_key(straight)]
    receipts={}
    for seq in SEQUENCES:
        # rows are reconstructed through the public model interface.
        from sequence_folding import transition_rows
        rows,_=transition_rows(states,seq,neighbors,index,max_drop,denominator)
        snaps=advance(seq,states,index,rows,denominator,initial,STEPS,open_cache)
        receipts[seq]={"snapshots":{str(k):v for k,v in snaps.items()},
                       "terminal_open_direction_counts":{"free":len(open_cache[initial])},
                       "scope":"exact finite binding/catalysis chart; rates are declared dimensionless and not calibrated"}
    # The enzyme-state projection can be stationary while labeled product current persists.
    stationary={}
    for seq in SEQUENCES:
        weights=[2**c for c in counts[seq]]
        bound_weight=sum(w*len(ds) for w,ds in zip(weights,open_cache))
        normalizer=12*sum(weights)+bound_weight
        flux=Q(bound_weight,8*normalizer)
        stationary[seq]={"normalizer":str(normalizer),"free_weight":str(12*sum(weights)),
                         "bound_weight":str(bound_weight),"product_current":[str(flux.numerator),str(flux.denominator)],
                         "free_state_weight":"12*2^contacts", "bound_direction_weight":"2^contacts",
                         "scope":"stationary enzyme-state projection; product emissions remain marked"}
        assert flux>0
    # The joint state is not closed by mean free accessibility: report the exact final defect.
    defect={}
    for seq in SEQUENCES:
        s=receipts[seq]["snapshots"]["24"]; den=int(s["denominator"])
        actual=Q(int(s["bound_numerator"]),den)
        free=Q(int(s["free_numerator"]),den)
        mean_access=Q(int(s["open_all_direction_numerator"]),12*den)
        actual_current=Q(int(s["open_free_direction_numerator"]),48*den)
        closure=actual_current-free*mean_access/Q(4)
        defect[seq]={"actual_bound_probability":[str(actual.numerator),str(actual.denominator)],
                     "actual_binding_current":[str(actual_current.numerator),str(actual_current.denominator)],
                     "free_times_marginal_mean_access_current":[str((free*mean_access/Q(4)).numerator),str((free*mean_access/Q(4)).denominator)],
                     "closure_defect":[str(closure.numerator),str(closure.denominator)]}
    product_difference={}
    for t in ("0","6","12","24"):
        a=receipts[SEQUENCES[0]]["snapshots"][t]; b=receipts[SEQUENCES[1]]["snapshots"][t]
        pa=Q(int(a["product_numerator"]),int(a["denominator"])); pb=Q(int(b["product_numerator"]),int(b["denominator"]))
        d=pa-pb; product_difference[t]=[str(d.numerator),str(d.denominator)]
    out={"schema":"holonics.receiver-engraving.sequence-kinetics.v1","fold_state_count":len(states),
         "joint_transition_denominator":str(2*denominator),"proposal_clock":48,
         "chemistry":{"free_bind_per_open_direction":"1/48","bound_unbind":"1/8","bound_catalyze":"1/8","bound_stay":"1/4"},
         "receipts":receipts,"stationary_enzyme_projection":stationary,"marginal_mean_access_closure_defect":defect,
         "expected_product_difference_HHPHPH_minus_HPHHPH":product_difference,
         "selection":"no sequence or conformation is selected by target matching; geometry determines open directions"}
    Path(__file__).with_name('sequence_kinetics_receipt.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
    print('returned exact sequence kinetics for',len(SEQUENCES),'sequences')
if __name__=='__main__': main()
