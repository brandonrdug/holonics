"""Mount a documented geometric contact chart and its recorded physical observation.

This prepares operands, not a learner. The Rust example owns the reference operator
composition; NormalizedKernel owns its differential and material update.
"""
from pathlib import Path
from fractions import Fraction as Q
import json, sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'research/experiments/receiver_engraving'))
import woven_ecology as w

def unpair(v): return Q(int(v[0]), int(v[1]))
def strings(a): return [[str(x) for x in row] for row in a]

grid, basis, tets, contacts = w.scene_lattice()
n = len(w.RINGS)
record = json.loads((ROOT / 'research/experiments/receiver_engraving/woven_ecology_receipt.json').read_text())
initial = [[unpair(z) for z in row] for row in record['states'][0][0]]
observed = [[unpair(z) for z in row] for row in record['states'][1][0]]
# Both heads see the same actual overlap incidence, through different supplied
# positive material charts. s=log K is exact; these are not exp(dot Q,K).
a = [[Q(2 if i == j else 0) for j in range(n)] for i in range(n)]
b = [[Q(1 if i == j else 0) for j in range(n)] for i in range(n)]
for (i, j), (strength, _) in contacts.items():
    sample = Q(round(16 * strength), 16)
    a[i][j] = a[j][i] = 1 + sample
    b[i][j] = b[j][i] = 1 + sample * sample
edge = max(contacts, key=lambda ij: (contacts[ij][0], ij))
i,j = edge
site = grid[contacts[edge][1]]
pi,pj = w.phase(w.RINGS[i],site),w.phase(w.RINGS[j],site)
phase = w.r.cm(pi,(pj[0],-pj[1]))
data = dict(scope='exterior exact rational reference; supplied geometric kernel charts and recorded field observation',
            observation_source='research/experiments/receiver_engraving/woven_ecology_receipt.json: states[0], states[1]',
            input=strings(initial), observed=strings(observed), head_a=strings(a), head_b=strings(b),
            contact_edge=edge, contact_phase=list(map(str,phase)),
            contacts=[dict(edge=list(ij),strength=str(s),site=list(map(str,grid[vi]))) for ij,(s,vi) in sorted(contacts.items())],
            rings=w.RINGS, overlap_receiver='nearest multiple of 1/16; absolute error at most 1/32; original strengths retained in contacts', gate_odds='1/3', material_rate='1/64', iteration_factor='1/2')
Path(__file__).with_name('input.json').write_text(json.dumps(data,indent=2)+'\n')
print(f'{n} complex channels, {len(contacts)} witnessed contacts; friction edge {edge}; phase {phase}')
