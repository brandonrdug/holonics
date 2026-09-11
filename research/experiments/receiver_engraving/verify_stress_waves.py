"""Checks that connect rendered packets to the actual fluid/wave source."""
import json
from fractions import Fraction as Q
from pathlib import Path
import knot_waves as w
r=w.r


def main():
    w.check_flow()
    # The optional entropy enclosure changes a receiver measurement only.
    for p in (Q(1,3),Q(1,2**90+1),Q(2**93+1,2**94+3)):
        center,error=r.log_interval(p);dyadic=Q(center*2**20//1,2**20)
        assert abs(center-dyadic)<=Q(1,2**20)
        assert error+abs(center-dyadic)<=error+Q(1,2**20)
    tri=[(0,0,0),(1,0,0),(0,1,0)]
    current=[((Q(i+1,7),Q(i+2,11)),(0,0),(0,0)) for i in range(3)]
    exact=r.compile_scene(tri,[(0,1,2)],currents=current,potential='entropy')
    bounded=r.compile_scene(tri,[(0,1,2)],currents=current,potential='entropy',log_display_bits=20)
    assert exact['source_packet']==bounded['source_packet']
    assert r.read_ratio(bounded['meta']['log_station_radius'])<=Q(1,3)*(Q(1,2**18)+Q(1,2**20))
    scenes=json.loads((w.ROOT/'research/papers/source/papers/hnn-information-chemistry/knot-scenes.json').read_text())
    cached={};count=0
    for name,scene in scenes.items():
        src=scene['meta']['source'];packet=scene['source_packet'];t=r.read_ratio(src['clock']);k=src['step']
        vertices=[tuple(r.read_ratio(v) for v in p) for p in src['carrier_vertices']]
        points=[tuple(tuple(r.read_ratio(v) for v in z) for z in p) for p in packet['vertices']]
        assert points==[tuple(r.pair(x) for x in w.flow(p,t)) for p in vertices]
        assert packet['triangles']==src['carrier_faces']
        lengths=src['topology'].get('component_lengths',[src['topology']['length']] if 'length' in src['topology'] else [])
        key=tuple(lengths)
        if key not in cached:
            parts=[w.states(n,active=(i==0)) for i,n in enumerate(lengths)]
            cached[key]=[tuple(sum((list(part[j][field]) for part in parts),[]) for field in range(3)) for j in range(25)]
        plus,minus,heat=cached[key][k]
        assert src['plus']==w.wire(plus) and src['minus']==w.wire(minus) and src['heat']==w.wire(heat)
        assert sum(map(w.power,plus))+sum(map(w.power,minus))+sum(heat)==2
        tangents=[tuple(r.read_ratio(v) for v in p) for p in src['tangents']]
        for i,(point,current) in enumerate(zip(points,packet['currents'])):
            p=tuple(v[0] for v in point);u=w.velocity(p,t);tangent=w.flow(tangents[i//6],t)
            psi=r.ca(plus[i//6],minus[i//6]);omega=(-t*t/8,Q(1,2),t/2)
            expected=tuple(r.ca((a,b),r.cs(psi,c)) for a,b,c in zip(u,omega,tangent))
            mode=src.get('receiver_kind','joint')
            if mode=='impulse': expected=tuple(r.cs(psi,c) for c in tangent)
            if mode=='heat':
                station=i//6; n=len(heat);norm=Q(n,2)
                expected=((norm*heat[station],norm*(heat[station]-heat[(station+1)%n])/4),(Q(0),Q(0)),(Q(0),Q(0)))
            actual=tuple(tuple(r.read_ratio(v) for v in z) for z in current)
            assert actual==expected
        assert src['mesh']['embedded'] and src['mesh']['closed'] and src['mesh']['orientable'] and not src['mesh']['defects']
        assert not scene['meta']['unresolved_near_faces'] and not scene['meta']['degenerate_faces']
        count+=1
    print('Verified',count,'packets against fluid flow, transported current, directional wave states, heat, mesh receipts and bounded entropy stations.')

if __name__=='__main__':main()
