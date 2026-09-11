"""Exact sequence/fold/ligand source views; colors read kinetic current, not H/P labels."""
from pathlib import Path
from fractions import Fraction as Q
import json,runpy
import sequence_folding as sf
import sequence_kinetics as sk
base=runpy.run_path(str(Path(__file__).with_name('build.py')));r=base['r'];ROOT=base['ROOT']
ZERO=(Q(0),Q(0));RADIUS=Q(1,4)


def wire(x):
    if isinstance(x,Q):return r.ratio(x)
    if isinstance(x,dict):return {k:wire(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [wire(v) for v in x]
    return x


def positive_faces(vertices,faces):
    volume=sum(r.dot(vertices[a],r.cross(vertices[b],vertices[c])) for a,b,c in faces)/6
    assert volume!=0
    return [tuple(reversed(f)) for f in faces] if volume<0 else faces


def bar(p,q,radius):
    d=r.sub(q,p);seed=(Q(1),Q(0),Q(0));n=r.cross(d,seed)
    if r.dot(n,n)==0:n=r.cross(d,(Q(0),Q(1),Q(0)))
    n=r.mul(n,1/max(map(abs,n)));b=r.cross(d,n);b=r.mul(b,1/max(map(abs,b)))
    ring=[n,b,r.mul(n,-1),r.mul(b,-1)];v=[r.add(x,r.mul(a,radius)) for x in (p,q) for a in ring]
    f=[]
    for j in range(4):k=(j+1)%4;f.extend(((j,k,4+k),(j,4+k,4+j)))
    f.extend(((0,2,1),(0,3,2),(4,5,6),(4,6,7)))
    return v,positive_faces(v,f)


def kinetic_receivers(i,seq,model,rows,bound=None):
    states,index,neighbors,counts,_,den=model;c=counts[seq];props=[[Q(0),Q(0)] for _ in range(6)]
    weights=dict(rows[i])
    for target,moved,_ in neighbors[i]:
        j=index[sf.state_key(target)]
        if bound is not None and bound not in sk.open_dirs(target,sf.STEPS):continue
        rate=Q(weights[j],den);props[moved][0]+=4*rate;props[moved][1]+=4*rate*(c[j]-c[i])
    return props


def render(name,i,seq,model,rows,origin,bounds,bound=None):
    state=model[0][i];props=kinetic_receivers(i,seq,model,rows,bound)
    vertices=[];faces=[];currents=[];parts=[]
    def append(v,f,center,coeff,kind,ids):
        start=len(vertices)
        for p in v:
            local=r.mul(r.sub(p,center),1/RADIUS)
            # A fixed local C3 probe, modulated by actual move acceptance and energy release.
            amp=((1+coeff[0])*local[0]+local[2],(1+coeff[1])*local[1]+local[2])
            currents.append((amp,ZERO,ZERO));vertices.append(p)
        faces.extend(tuple(start+j for j in t) for t in f)
        parts.append(dict(start=start,end=len(vertices),center=center,coefficients=coeff,kind=kind,source_indices=ids))
    sv,sf_faces=base['sphere'](n=2,m=2)
    for j,point in enumerate(state):
        center=tuple(map(Q,point));v=[r.add(center,r.mul(p,RADIUS/2)) for p in sv]
        append(v,positive_faces(v,sf_faces),center,props[j],'monomer',(j,))
    bonds=[(j,j+1,'backbone') for j in range(5)]
    bonds += [(j,k,'contact') for j in range(6) for k in range(j+2,6) if seq[j]==seq[k]=='H' and sf.sq(state[j],state[k])==2]
    for j,k,kind in bonds:
        p,q=tuple(map(Q,state[j])),tuple(map(Q,state[k]));v,f=bar(p,q,RADIUS/(3 if kind=='backbone' else 6))
        center=r.mul(r.add(p,q),Q(1,2));coeff=tuple((props[j][a]+props[k][a])/2 for a in range(2))
        append(v,f,center,coeff,kind,(j,k))
    if bound is not None:
        ligand=r.add(state[5],bound);assert bound in sk.open_dirs(state,sf.STEPS)
        # Same geometric probe and reaction-rate receivers; ligand identity is not a palette.
        v=[r.add(ligand,r.mul(p,RADIUS/2)) for p in sv]
        append(v,positive_faces(v,sf_faces),ligand,(Q(1,4),Q(0)),'ligand',(5,))
        v,f=bar(tuple(map(Q,state[5])),ligand,RADIUS/3);append(v,f,r.mul(r.add(state[5],ligand),Q(1,2)),(Q(1,4),Q(0)),'binding',(5,))
    source=wire(dict(kind='sequence-kinetic-view',sequence=seq,state_index=i,positions=state,bound_direction=bound,
                     contacts=model[3][seq][i],per_monomer_receivers=props,parts=parts,
                     probe_radius=RADIUS,probe='((1+activity)x+z)+i((1+contact-release)y+z)',
                     receiver_rates='activity=4 sum move_probability; release=4 sum move_probability*delta_contacts',
                     visual_convention='thick edges backbone, fine edges actual HH contact; H/P never selects color'))
    return r.compile_scene(vertices,faces,currents=currents,receiver=r.Receiver(origin=origin,distance=Q(40),aperture=Q(1,16)),source=source,step=Q(1,8),bounds=bounds,closed_outward=True)


def main():
    model=sf.build_model();states,index,neighbors,counts,max_drop,den=model
    fold=json.loads(Path(__file__).with_name('sequence_folding_receipt.json').read_text())
    rows={seq:sf.transition_rows(states,seq,neighbors,index,max_drop,den)[0] for seq in sf.SEQUENCES}
    origin=(Q(1,2),Q(1,2),Q(0));scenes={}
    for letter,seq in zip('ab',sf.SEQUENCES):
        rec=fold['representatives'][seq];initial=rec['initial_state_index'];ground=fold['sequence_receipts'][seq]['energy_summary']['shortest_legal_path_to_ground']['state_indices'][-1]
        for suffix,i,bounds in (('initial',initial,(-5,-3,5,6)),('ground',ground,(-3,-3,3,3))):
            key=f'seq_{letter}_{suffix}';scenes[key]=render(key,i,seq,model,rows[seq],origin,bounds)
            print(key,len(scenes[key]['marks']),'marks',flush=True)
    path_states=fold['sequence_receipts'][sf.SEQUENCES[0]]['energy_summary']['shortest_legal_path_to_ground']['state_indices']
    for k in (0,len(path_states)//2,len(path_states)-1):
        key=f'fold_path_{k}';scenes[key]=render(key,path_states[k],sf.SEQUENCES[0],model,rows[sf.SEQUENCES[0]],origin,(-5,-3,5,6))
    witness=fold['non_lumpability_witness'];a,b=witness['state_a'],witness['state_b'];seq=witness['sequence']
    paired=tuple(sum(Q(p[j]) for state in (states[a],states[b]) for p in state)/12 for j in range(3))
    for key,i in (('fold_equal_a',a),('fold_equal_b',b)):
        scenes[key]=render(key,i,seq,model,rows[seq],paired,(-4,-3,4,3))
    # An actual ligand occupation blocks an otherwise admitted nonterminal move.
    found=None
    for i in fold['sequence_receipts'][seq]['ground_state_indices']:
        for target,moved,hop in neighbors[i]:
            if moved==5:continue
            d=r.sub(target[moved],states[i][5])
            if d in sk.open_dirs(states[i],sf.STEPS) and d not in sk.open_dirs(target,sf.STEPS):
                found=dict(sequence=seq,source=i,target=index[sf.state_key(target)],moved=moved,hop=hop,ligand_direction=d,
                           unbound_move_probability=Q(dict(rows[seq][i])[index[sf.state_key(target)]],2*den),bound_move_probability=Q(0));break
        if found:break
    assert found
    i=found['source'];paired=tuple(sum(Q(p[j]) for p in states[i])/6 for j in range(3))
    for key,d in (('ligand_free',None),('ligand_bound',found['ligand_direction'])):
        scenes[key]=render(key,i,seq,model,rows[seq],paired,(-3,-3,3,3),bound=d)
    out=ROOT/'research/papers/source/papers/hnn-information-chemistry/sequence-scenes.json'
    out.write_text(json.dumps(scenes,separators=(',',':'))+'\n')
    Path(__file__).with_name('sequence_geometry_receipt.json').write_text(json.dumps(wire(found),indent=2)+'\n')
    export=runpy.run_path(str(ROOT/'research/papers/source/packages/holonic-receiver/export_svg.py'))['scene_svg']
    for key,scene in scenes.items():
        assert not scene['meta']['unresolved_near_faces'] and not scene['meta']['degenerate_faces']
        (ROOT/'research/papers/rendered/receiver-engraving'/f'{key}.svg').write_text(export(scene,width_mm=Q(100),line_width_pt=Q(1,2)))
    # The hop locator is annotation, distinct from the kinetic color field.
    import html
    for key in ('ligand_free','ligand_bound'):
        scene=scenes[key];cam=scene['meta']['receiver']
        read=lambda q:Q(int(q[0]),int(q[1]))
        center=tuple(read(x) for x in cam['origin']);right=tuple(read(x) for x in cam['right']);up=tuple(read(x) for x in cam['up'])
        point=tuple(map(Q,states[found['source']][found['moved']]));target=r.add(point,found['hop'])
        def project(p):v=r.sub(p,center);return r.dot(right,v),-r.dot(up,v)
        x,y=project(point);xx,yy=project(target)
        label=html.escape(json.dumps(wire(dict(kind='annotation',source=point,target=target,partner_direction=found['ligand_direction']))))
        extra=f'<metadata id="kinetic-hop">{label}</metadata><defs><marker id="hop-tip" viewBox="0 0 10 10" refX="10" refY="5" markerWidth="0.18" markerHeight="0.18" markerUnits="userSpaceOnUse" orient="auto"><path d="M 0 0 L 10 5 L 0 10 z" fill="white"/></marker></defs>'
        extra+=f'<path d="M {float(x)} {float(y)} L {float(xx)} {float(yy)}" fill="none" stroke="white" stroke-width="0.018" stroke-dasharray="0.07 0.05" marker-end="url(#hop-tip)"/><text x="{float(x+Q(1,8))}" y="{float(y+Q(1,4))}" fill="white" font-family="serif" font-size="0.28">5</text><text x="{float(xx+Q(1,8))}" y="{float(yy-Q(1,8))}" fill="white" font-family="serif" font-size="0.28">S</text>'
        drawing=export(scene,width_mm=Q(100),line_width_pt=Q(1,2))
        (ROOT/'research/papers/rendered/receiver-engraving'/f'{key}_annotated.svg').write_text(drawing.replace('</svg>',extra+'</svg>'))
    print('ligand witness',wire(found),flush=True)

if __name__=='__main__':main()
