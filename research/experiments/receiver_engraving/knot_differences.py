"""Separate the impulse and heat receiver from the joint bulk-flow image."""
from pathlib import Path
from fractions import Fraction as Q
import json,runpy,copy
import knot_waves as w
r=w.r


def main():
    path=w.ROOT/'research/papers/source/papers/hnn-information-chemistry/knot-scenes.json'
    scenes=json.loads(path.read_text());names=[]
    for mode,steps in (('impulse',(0,12,24)),('heat',(6,12,24))):
        for k in steps:
            parent=scenes[f'trefoil_3_1_{k}'];src=copy.deepcopy(parent['meta']['source'])
            vertices=[tuple(r.read_ratio(z[0]) for z in p) for p in parent['source_packet']['vertices']]
            n=len(src['plus']);currents=[];t=Q(k,24)
            plus=[tuple(r.read_ratio(x) for x in z) for z in src['plus']]
            minus=[tuple(r.read_ratio(x) for x in z) for z in src['minus']]
            heat=[r.read_ratio(x) for x in src['heat']]
            tangents=[tuple(r.read_ratio(x) for x in p) for p in src['tangents']]
            for j,p in enumerate(vertices):
                i=j//6
                if mode=='impulse':
                    # Exact source difference: joint current minus its unexcited bulk reading.
                    psi=r.ca(plus[i],minus[i]);tan=w.flow(tangents[i],t)
                    currents.append(tuple(r.cs(psi,c) for c in tan))
                else:
                    # Heat and directed edge heat flow, in units of initial energy per node.
                    norm=Q(n,2);amp=(norm*heat[i],norm*(heat[i]-heat[(i+1)%n])/4)
                    currents.append((amp,(Q(0),Q(0)),(Q(0),Q(0))))
            src['receiver_kind']=mode
            src['receiver_units']='source-relative wave current' if mode=='impulse' else 'heat and outgoing edge heat flow / (initial energy 2 / station count)'
            camera=r.Receiver(right=(Q(1),Q(0),Q(0)),up=(Q(0),Q(4,5),Q(3,5)),view=(Q(0),-Q(3,5),Q(4,5)),distance=Q(32),aperture=Q(1,16))
            key=f'trefoil_{mode}_{k}'
            scenes[key]=r.compile_scene(vertices,parent['source_packet']['triangles'],currents=currents,receiver=camera,tau=t,step=Q(1,32),bounds=(-6,-6,6,6),source=src)
            names.append(key);print(key,len(scenes[key]['marks']),'marks',flush=True)
    path.write_text(json.dumps(scenes,separators=(',',':'))+'\n')
    export=runpy.run_path(str(w.ROOT/'research/papers/source/packages/holonic-receiver/export_svg.py'))['scene_svg']
    for name in names:
        (w.ROOT/'research/papers/rendered/receiver-engraving'/f'{name}.svg').write_text(export(scenes[name],width_mm=Q(100),line_width_pt=Q(1,2)))

if __name__=='__main__':main()
