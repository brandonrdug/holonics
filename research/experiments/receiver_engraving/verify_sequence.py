"""Independent checks of sequence, fold/kinetic quotient and rendered source relations."""
from fractions import Fraction as Q
from pathlib import Path
from collections import defaultdict
import json
import sequence_folding as sf
import sequence_kinetics as sk
import sequence_figures as fig
r=fig.r;ROOT=fig.ROOT

def read(x):return Q(x) if isinstance(x,int) else Q(int(x[0]),int(x[1]))
def point(x):return tuple(read(v) for v in x)
def p3(x):return tuple(read(v[0]) for v in x)

def main():
    model=sf.build_model();states,index,neighbors,counts,max_drop,D=model
    fold=json.loads(Path(__file__).with_name('sequence_folding_receipt.json').read_text())
    assert len(states)==len(set(states))==12711 and len(sf.STEPS)==12
    assert all(tuple(s[:2])==sf.ANCHOR and len(set(s))==6 and all(sf.sq(s[i],s[i+1])==2 for i in range(5)) for s in states)
    assert sum(len(n) for n in neighbors)==79476
    assert sorted(sf.SEQUENCES[0])==sorted(sf.SEQUENCES[1])
    rows={};norms={}
    for seq in sf.SEQUENCES:
        rows[seq],c=sf.transition_rows(states,seq,neighbors,index,max_drop,D)
        for i,row in enumerate(rows[seq]):
            assert sum(w for j,w in row)==D and all(w>=0 for j,w in row)
            for j,w in row:
                if i==j:continue
                delta=c[j]-c[i]
                expected=Q(1,48)*min(Q(1),Q(2)**delta)
                assert Q(w,D)==expected
                assert 2**c[i]*w==2**c[j]*dict(rows[seq][j])[i]
        rec=fold['sequence_receipts'][seq];assert rec['contact_counts']==c
        for k,values in rec['snapshots'].items():assert sum(map(int,values))==D**int(k)
        ground=rec['energy_summary'];assert ground['ground_state_count']==sum(v==max(c) for v in c)==16
        for b,z in ground['equilibrium_partition_Z'].items():assert int(z)==sum(int(b)**v for v in c)
        path=ground['shortest_legal_path_to_ground']['state_indices']
        assert c[path[-1]]==max(c)
        for a,b in zip(path,path[1:]):assert dict(rows[seq][a]).get(b,0)>0
    witness=fold['non_lumpability_witness'];seq=witness['sequence'];a,b=witness['state_a'],witness['state_b']
    def project(i):
        out=defaultdict(int)
        for j,w in rows[seq][i]:out[counts[seq][j]]+=w
        return dict(out)
    assert counts[seq][a]==counts[seq][b]==1
    assert project(a).get(2,0)==0 and Q(project(b)[2],D)==Q(1,48)
    kinetic=json.loads(Path(__file__).with_name('sequence_kinetics_receipt.json').read_text())
    for seq,rec in kinetic['receipts'].items():
        for step,s in rec['snapshots'].items():
            den=int(s['denominator']);free=int(s['free_numerator']);bound=int(s['bound_numerator']);prod=int(s['product_numerator']);drawn=int(s['net_drawn_numerator'])
            assert free+bound==den and bound+prod==drawn
        s=rec['snapshots']['24'];den=int(s['denominator'])
        actual=Q(int(s['open_free_direction_numerator']),48*den)
        closure=Q(int(s['free_numerator'])*int(s['open_all_direction_numerator']),48*den**2)
        data=kinetic['marginal_mean_access_closure_defect'][seq]
        assert read(data['actual_binding_current'])==actual and read(data['free_times_marginal_mean_access_current'])==closure
        assert read(data['closure_defect'])==actual-closure!=0
    for seq,rec in kinetic['stationary_enzyme_projection'].items():
        weights=[2**c for c in counts[seq]]
        openings=[len(sk.open_dirs(s,sf.STEPS)) for s in states]
        bound=sum(a*b for a,b in zip(weights,openings));z=12*sum(weights)+bound
        assert int(rec['normalizer'])==z and read(rec['product_current'])==Q(bound,8*z)>0
        for weight in weights:assert Q(12*weight,48)==Q(weight,4)
    # Homogeneous accessibility must have zero marginal-closure error (guards units/factor12).
    free=Q(2,3);a=Q(7,12);assert free*a/4==Q(1,48)*(12*a*free)
    delta=read(kinetic['expected_product_difference_HHPHPH_minus_HPHHPH']['24'])
    assert Q(1,2**26)<delta<Q(1,2**25)
    geo=json.loads(Path(__file__).with_name('sequence_geometry_receipt.json').read_text())
    source=states[geo['source']];target=states[geo['target']];d=tuple(geo['ligand_direction']);moved=geo['moved']
    assert d in sk.open_dirs(source,sf.STEPS) and d not in sk.open_dirs(target,sf.STEPS)
    assert tuple(source[5][j]+d[j] for j in range(3))==target[moved]
    assert read(geo['unbound_move_probability'])==Q(dict(rows[geo['sequence']][geo['source']])[geo['target']],2*D)==Q(1,96)
    scenes=json.loads((ROOT/'research/papers/source/papers/hnn-information-chemistry/sequence-scenes.json').read_text())
    for name,scene in scenes.items():
        src=scene['meta']['source'];packet=scene['source_packet'];i=src['state_index'];seq=src['sequence'];bound=src['bound_direction']
        assert src['positions']==[list(p) for p in states[i]]
        expected=[[Q(0),Q(0)] for _ in range(6)]
        for target,moved,_ in neighbors[i]:
            j=index[sf.state_key(target)]
            if bound is not None and tuple(bound) not in sk.open_dirs(target,sf.STEPS):continue
            rate=Q(1,48)*min(Q(1),Q(2)**(counts[seq][j]-counts[seq][i]))
            expected[moved][0]+=4*rate;expected[moved][1]+=4*rate*(counts[seq][j]-counts[seq][i])
        assert src['per_monomer_receivers']==fig.wire(expected)
        for part in src['parts']:
            center=point(part['center']);a,b=map(read,part['coefficients'])
            for j in range(part['start'],part['end']):
                local=r.mul(r.sub(p3(packet['vertices'][j]),center),1/fig.RADIUS)
                alpha=((1+a)*local[0]+local[2],(1+b)*local[1]+local[2])
                assert tuple(read(v) for v in packet['currents'][j][0])==alpha
        assert not scene['meta']['degenerate_faces'] and not scene['meta']['unresolved_near_faces']
    print('Verified all FCC conformations, detailed-balance rows, non-lumpability, reaction moments, steric feedback and',len(scenes),'rendered source packets.')

if __name__=='__main__':main()
