"""Exact six monomer FCC sequence/conformation and Metropolis kinetic witness.

This is a finite coarse physical chart: it does not classify sequences or claim calibrated
protein chemistry.  All conformations, legal moves, energies, and populations are derived from
the declared FCC geometry and the stated contact law.
"""
from itertools import permutations
from collections import defaultdict, deque
from pathlib import Path
import json

P=tuple
STEPS=sorted(set(list(permutations((1,1,0)))+list(permutations((1,-1,0)))+
                 list(permutations((-1,1,0)))+list(permutations((-1,-1,0)))))
ANCHOR=(P((0,0,0)),P((1,1,0)))
SEQUENCES=("HHPHPH","HPHHPH")

def sq(a,b): return sum((a[i]-b[i])**2 for i in range(3))
def contacts(state,sequence):
    return sum(sequence[i]=="H" and sequence[j]=="H" and sq(state[i],state[j])==2
               for i in range(6) for j in range(i+2,6))
def state_key(state): return tuple(tuple(x) for x in state)
def wire_int(n): return str(n)

def enumerate_states():
    states=list(ANCHOR)
    layers=[ANCHOR]
    for _ in range(4):
        nxt=[]
        for state in layers:
            for d in STEPS:
                q=tuple(state[-1][i]+d[i] for i in range(3))
                if q in state: continue
                nxt.append(state+(q,))
        layers=nxt
    # The anchor makes every generated tuple unique; retain a deterministic lexical order.
    return sorted(set(layers))

def legal_neighbors(state):
    """Relocate one of monomers 2..5 by one FCC hop, preserving all bonds and exclusion."""
    out=[]
    occupied=set(state)
    for i in range(2,6):
        for d in STEPS:
            q=tuple(state[i][k]+d[k] for k in range(3))
            if q in occupied and q!=state[i]: continue
            candidate=list(state); candidate[i]=q
            if any(sq(candidate[j],candidate[j+1])!=2 for j in range(5)): continue
            if len(set(candidate))!=6: continue
            out.append((tuple(candidate),i,d))
    return out

def connected_components(states,index,neighbors):
    unseen=set(range(len(states))); result=[]
    while unseen:
        root=min(unseen); unseen.remove(root); comp=[root]; queue=[root]
        while queue:
            i=queue.pop()
            for target,_,_ in neighbors[i]:
                j=index[state_key(target)]
                if j in unseen: unseen.remove(j); queue.append(j); comp.append(j)
        result.append(sorted(comp))
    return result

def transition_rows(states,sequence,neighbors,index,max_drop,denominator):
    counts=[contacts(s,sequence) for s in states]; rows=[]
    for i,edges in enumerate(neighbors):
        row=defaultdict(int)
        for target,_,_ in edges:
            j=index[state_key(target)]
            delta=counts[j]-counts[i]
            # D = 48*2^M; accepted numerator is 2^M for uphill/equal and 2^(M+delta) downhill.
            row[j]+=2**(max_drop+min(0,delta))
        row[i]+=denominator-sum(row.values())
        if row[i]<0: raise AssertionError((i,row[i]))
        rows.append(sorted(row.items()))
        assert sum(w for _,w in row.items())==denominator and all(w>=0 for w in row.values())
    return rows,counts

def propagate(initial,rows,denominator,steps):
    values=[0]*len(rows); values[initial]=1; snapshots={0:values[:]}
    for t in range(1,steps+1):
        nxt=[0]*len(rows)
        for i,value in enumerate(values):
            if value:
                for j,w in rows[i]: nxt[j]+=value*w
        values=nxt
        if t in (6,12,24): snapshots[t]=values[:]
    return snapshots

def encode_population(values): return [str(x) for x in values]

def build_model():
    states=enumerate_states(); index={state_key(s):i for i,s in enumerate(states)}
    neighbors=[legal_neighbors(s) for s in states]
    reverse={(i,index[state_key(t)]) for i,row in enumerate(neighbors) for t,_,_ in row}
    assert all((j,i) in reverse for i,j in reverse)
    counts={seq:[contacts(s,seq) for s in states] for seq in SEQUENCES}
    max_drop=max(max(c)-min(c) for c in counts.values()); denominator=48*2**max_drop
    return states,index,neighbors,counts,max_drop,denominator

def main():
    states,states_index,neighbors,counts_by_sequence,MAX_DROP,denominator=build_model()
    components=connected_components(states,states_index,neighbors)
    sequence_receipts={}
    row_by_sequence={}
    initial=states_index[state_key(tuple((i,i,0) for i in range(6)))]
    for seq in SEQUENCES:
        rows,counts=transition_rows(states,seq,neighbors,states_index,MAX_DROP,denominator)
        row_by_sequence[seq]=rows
        snapshots=propagate(initial,rows,denominator,24)
        summaries={}
        for t,values in snapshots.items():
            bins=defaultdict(int)
            for i,value in enumerate(values): bins[str(counts[i])]+=value
            summaries[str(t)]={"common_denominator_power":t,"denominator":str(denominator**t),
                               "nonzero_state_count":sum(value!=0 for value in values),
                               "contact_bin_numerators":{k:str(v) for k,v in sorted(bins.items())}}
        energies={"minimum_energy_contact":max(counts),"maximum_energy_contact":min(counts),
                  "ground_state_count":sum(c==max(counts) for c in counts),
                  "maximum_contact_state_count":sum(c==max(counts) for c in counts)}
        energies["equilibrium_partition_Z"]={str(b):str(sum(b**c for c in counts)) for b in (1,2,4,16)}
        energies["ground_mass_at_b"]={str(b):str(sum(b**c for c in counts if c==max(counts)))+"/"+str(sum(b**c for c in counts)) for b in (1,2,4,16)}
        target=set(i for i,c in enumerate(counts) if c==max(counts)); prev={initial:None}; queue=deque([initial])
        while queue and not (set(prev)&target):
            i=queue.popleft()
            for target_state,_,_ in neighbors[i]:
                j=states_index[state_key(target_state)]
                if j not in prev: prev[j]=i; queue.append(j)
        end=next(i for i in prev if i in target); path=[]
        while end is not None: path.append(end); end=prev[end]
        path=list(reversed(path)); energies["shortest_legal_path_to_ground"]={"state_indices":path,"steps":len(path)-1}
        # Detailed balance is exact on every directed legal edge.
        detailed=[]
        for i,row in enumerate(rows):
            for j,w in row:
                if i!=j:
                    reverse_weight=dict(rows[j])[i]
                    detailed.append((2**counts[i]*w)==(2**counts[j]*reverse_weight))
        assert all(detailed)
        sequence_receipts[seq]={"contact_counts":counts,"energy_convention":"E/epsilon = -contact_count",
            "transition_denominator":str(denominator),"snapshots":{str(t):encode_population(v) for t,v in snapshots.items()},
            "snapshot_summaries":summaries,
            "detailed_balance_edge_count":len(detailed),"detailed_balance_verified":all(detailed),"energy_summary":energies,
            "minimum_energy_indices":[i for i,c in enumerate(counts) if c==max(counts)],
            "ground_state_indices":[i for i,c in enumerate(counts) if c==max(counts)],
            "max_contact_indices":[i for i,c in enumerate(counts) if c==max(counts)]}
    # Exact energy-bin non-lumpability: same contact count, different next-contact response.
    witness=None
    seq=SEQUENCES[0]; counts=counts_by_sequence[seq]
    signatures={}
    rows=row_by_sequence[seq]
    for i,row in enumerate(rows):
        bins=defaultdict(int)
        for j,w in row: bins[counts[j]]+=w
        sig=tuple(sorted(bins.items()))
        c=counts[i]
        if c in signatures and signatures[c][1]!=sig:
            witness={"sequence":seq,"contact_count":c,"state_a":signatures[c][0],"state_b":i,
                     "next_contact_bin_response_a":list(signatures[c][1]),"next_contact_bin_response_b":list(sig)};break
        signatures[c]=(i,sig)
    if witness is None: raise AssertionError("non-lumpability witness absent")
    # Representatives are derived from the actual population: minimum energy, and initial state.
    rep={seq:{"initial_state_index":initial,"initial_state":[list(p) for p in states[initial]],
              "minimum_energy_state_index":sequence_receipts[seq]["minimum_energy_indices"][0],
              "minimum_energy_state":[list(p) for p in states[sequence_receipts[seq]["minimum_energy_indices"][0]]],
              "selection_rule":"population-derived; maximum contact is minimum declared energy"}
         for seq in SEQUENCES}
    receipt={"schema":"holonics.receiver-engraving.sequence-folding.v1",
      "scope":"finite FCC coarse physical chart; not calibrated protein chemistry and not an HNN semantic classifier",
      "source_rules":{"monomers":6,"anchors":[list(ANCHOR[0]),list(ANCHOR[1])],"fcc_steps":[list(x) for x in STEPS],
                       "self_avoidance":"all six positions distinct","contact":"nonbonded squared distance 2; HH only",
                       "sequences":list(SEQUENCES),"proposal_clock":48,"beta_epsilon":"log(2)",
                       "move":"one of monomers 2..5 relocates by one FCC hop; all bonds and exclusion retained",
                       "initial":"straight chain p_i=(i,i,0)","selection":"population-derived only"},
      "state_count":len(states),"states":[[list(p) for p in s] for s in states],
      "legal_move_count":sum(len(x) for x in neighbors),"connected_component_count":len(components),
      "component_sizes":[len(c) for c in components],"kinetic_graph_connected":len(components)==1,
      "common_denominator":str(denominator),"sequence_receipts":sequence_receipts,
      "non_lumpability_witness":witness,"representatives":rep}
    out=Path(__file__).with_name("sequence_folding_receipt.json");out.write_text(json.dumps(receipt,separators=(",",":"))+"\n")
    print("returned FCC states",len(states),"legal moves",receipt["legal_move_count"],"components",len(components),"denominator",denominator)

if __name__=="__main__": main()
