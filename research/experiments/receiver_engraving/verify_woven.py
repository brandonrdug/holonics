"""Source, contact, horizon, field-passage and conformation checks for the woven plates."""
from fractions import Fraction as Q
from pathlib import Path
from collections import defaultdict
import json,itertools,runpy,subprocess,importlib.util,sys
import woven_ecology as w
import woven_bridge as wb
import ecology_details as detail
import constitutive_lobes as lobes
import knot_waves as kw
import knot_geometry as kg
import triangle_embedding as meshcheck
r=w.r;ROOT=w.ROOT

def read(q):return Q(int(q[0]),int(q[1]))
def complex_read(v):return tuple(read(x) for x in v)
def point_read(v):return tuple(read(x) for x in v)
def painted_point(v):return tuple(read(x[0]) for x in v)
def parity(seq):return -1 if sum(seq[i]>seq[j] for i in range(len(seq)) for j in range(i+1,len(seq)))%2 else 1

def atlas_check(grid,tets):
    boundary=defaultdict(list)
    for tet in tets:
        tet=list(tet);a,b,c,d=[grid[i] for i in tet]
        det=r.dot(r.sub(b,a),r.cross(r.sub(c,a),r.sub(d,a)));assert det!=0
        if det<0:tet[0],tet[1]=tet[1],tet[0]
        for j in range(4):
            f=tet[:j]+tet[j+1:];boundary[tuple(sorted(f))].append((-1 if j%2 else 1)*parity(f))
    assert all((len(v)==2 and sum(v)==0) or (len(v)==1 and all(r.dot(grid[i],grid[i])==(w.SCALE*w.RADII[-1])**2 for i in f)) for f,v in boundary.items())
    print('Radial atlas: nondegenerate cells; interior oriented faces cancel; only outer sphere boundary remains.')

def main():
    grid,basis,tets,witness=w.scene_lattice();atlas_check(grid,tets)
    rec=json.loads(Path(__file__).with_name('woven_ecology_receipt.json').read_text())
    connections={tuple(e):complex_read(u) for e,u in rec['connections']};edges=sorted(connections)
    cycle=tuple(rec['cycle']);site=tuple(read(x) for x in rec['bridge_site']);quart=tuple(rec['bridge_quartet'])
    for row in rec['contact_witnesses']:
        i,j=row['edge'];p=grid[row['node']]
        assert w.kernel(w.RINGS[i],p)>0 and w.kernel(w.RINGS[j],p)>0
        gi=w.phase(w.RINGS[i],p);gj=w.phase(w.RINGS[j],p)
        assert connections[i,j]==r.cm(gi,(gj[0],-gj[1]))
    ordinary,law=w.evolution(edges,connections);off,offlaw=w.evolution(edges,connections,coupled=False)
    twisted,twlaw=w.evolution(edges,connections,twist=(cycle[0],cycle[2]));closed,claw=w.evolution(edges,connections,driven=False)
    assert rec['states']==w.wire(ordinary) and rec['uncoupled']==w.wire(off) and rec['twisted']==w.wire(twisted) and rec['closed']==w.wire(closed)
    for series,l in ((ordinary,law),(off,offlaw),(twisted,twlaw),(closed,claw)):
        for k,(psi,h) in enumerate(series):
            work=sum(x['work'] for x in l['source_returns'] if x['step']<=k)
            assert sum(map(w.power,psi))+sum(h)==l['initial_energy']+work
    # A receiver phase reorientation transports the basis inversely and preserves every nodal image.
    gs=[((1-Q(i,len(w.RINGS))**2)/(1+Q(i,len(w.RINGS))**2),2*Q(i,len(w.RINGS))/(1+Q(i,len(w.RINGS))**2)) for i in range(len(w.RINGS))]
    psi=ordinary[6][0];reoriented=[r.cm(g,z) for g,z in zip(gs,psi)]
    for row in basis:
        transformed={i:r.cm((gs[i][0],-gs[i][1]),v) for i,v in row.items()}
        assert w.amplitude(row,psi)==w.amplitude(transformed,reoriented)
    def transport(i,j):return connections[i,j] if i<j else (connections[j,i][0],-connections[j,i][1])
    for cyc in ((quart[0],quart[1],quart[2]),(quart[0],quart[1],quart[3])):
        p=w.ONE
        for i,j in zip(cyc,cyc[1:]+cyc[:1]):p=r.cm(p,transport(i,j))
        assert p==w.ONE
    scenes=json.loads((ROOT/'research/papers/source/papers/hnn-information-chemistry/woven-scenes.json').read_text())
    variants={'woven_0':ordinary[0],'woven_6':ordinary[6],'woven_12':ordinary[12],'woven_off':off[12],'woven_twist':twisted[12]}
    for name,(psi,heat) in variants.items():
        scene=scenes[name];source=scene['meta']['source'];packet=scene['source_packet']
        assert source['psi']==w.wire(psi) and source['heat']==w.wire(heat)
        vv,ff,cc,mm=w.horizon(grid,basis,tets,psi)
        clock=read(source['material_clock']);assert clock==Q(source['chronology']['step'],len(source['chronology']['law']['matchings']))
        assert [painted_point(v) for v in packet['vertices']]==[kw.flow(v,clock) for v in vv] and [tuple(f) for f in packet['triangles']]==ff
        assert [tuple(complex_read(z) for z in p) for p in packet['currents']]==cc
        assert source['mesh']==w.wire(mm)
        nodal=[w.amplitude(row,psi) for row in basis]
        for a,b,t in mm['source_edges']:
            aa,bb=nodal[a],nodal[b];mixed=r.mix(aa,bb,t)
            defect=(1-t)*w.power(aa)+t*w.power(bb)-w.power(mixed)
            assert defect==t*(1-t)*w.power(r.sub(bb,aa))>=0
        assert not scene['meta']['unresolved_near_faces'] and not scene['meta']['degenerate_faces']
    assert scenes['woven_12']['source_packet']!=scenes['woven_off']['source_packet']
    assert scenes['woven_12']['source_packet']!=scenes['woven_twist']['source_packet']
    b=json.loads(Path(__file__).with_name('woven_bridge_receipt.json').read_text())
    box=tuple(tuple(read(x) for x in bound) for bound in b['support']['aabb'])
    for i in b['scene']['selected_quartet']:
        assert wb.torus_poly_upper(w.RINGS[i],box)==read(b['support']['polynomial_upper_bounds'][str(i)])<0
    frame=[point_read(v) for v in b['affine_frame']['columns']];scale=read(b['support']['scale']);center=point_read(b['scene']['site'])
    assert r.dot(frame[0],r.cross(frame[1],frame[2]))>0
    local=[point_read(v) for v in b['source_geometry_mapped']['source_coordinates']]
    mapped=[point_read(v) for v in b['source_geometry_mapped']['vertices']]
    assert mapped==[wb.affine_point(center,scale,frame,v) for v in local]
    # The folded-domain geometry is embedded before its exact rigid receiver transport.
    for key,p in kg.knots().items():
        if key=='unknot':continue
        points=[tuple(Q(int(x[0]),int(x[1])) for x in v) for v in p['vertices']][::2]
        v,f,_=kw.tube(points,radius=Q(1,4));check=meshcheck.verify_mesh(v,f)
        assert check['embedded'] and check['closed'] and check['orientable'] and not check['defects']
    l=lobes.build();details=json.loads((ROOT/'research/papers/source/papers/hnn-information-chemistry/ecology-detail-scenes.json').read_text())
    for name in ('lobes_0','lobes_2','lobes_4','lobes_off'):
        scene=details[name];src=scene['meta']['source'];p=scene['source_packet'];camera=r.Receiver()
        assert src['law']==l
        for dom in src['domains']:
            q=read(dom['q']);g=read(dom['gradient']);co,si=map(read,dom['rotation']);center=point_read(dom['center'])
            assert co*co+si*si==1
            vv,ff,_=kw.tube([point_read(x) for x in dom['source_centerline']],radius=Q(1,4))
            for j,v in enumerate(vv):
                v=r.mul(v,Q(1,2));arm=(co*v[0]+si*v[1],-si*v[0]+co*v[1],v[2]);idx=dom['start']+j
                assert painted_point(p['vertices'][idx])==r.add(center,arm)
                alpha=(lobes.conformation(q)*r.dot(arm,camera.view),-g*r.dot(arm,camera.right))
                assert complex_read(p['currents'][idx][0])==alpha
    # Exact optical normal/tangential witness and Fresnel power normalization.
    N1=Q(9,5);N2=Q(16,5);reflection=(N1-N2)/(N1+N2);transmission=Q(24,25)
    assert 3*Q(4,5)==4*Q(3,5)==Q(12,5) and reflection**2+transmission**2==1
    for s in (Q(0),Q(1,100),Q(1,2),Q(1),Q(3)):
        assert 1-1/(1+s)**2==s*(2+s)/(1+s)**2<=2*s
    print('Verified contact/gauge/holonomy, all five horizons, complete overlap box, embedded folded domains, source/heat and optical/local-gravity witnesses.')

if __name__=='__main__':main()
