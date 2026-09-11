"""Receiver views of the woven channels, overlap bridge, and coupled folded domains."""
from fractions import Fraction as Q
from pathlib import Path
import json,runpy
import woven_ecology as w
import knot_waves as kw
import knot_geometry as kg
import constitutive_lobes as lobes
r=w.r;ROOT=w.ROOT

def ratio(q):return Q(int(q[0]),int(q[1]))

def carrier(psi):
    lon=w.base['circle'](5);mer=w.base['circle'](1);width=len(lon)
    vertices=[];currents=[];faces=[]
    # Thin displayed cores; full toroidal field supports keep their separate width 3/4.
    radius=Q(w.MINOR,w.SCALE*5)
    for ring,z in zip(w.RINGS,psi):
        start=len(vertices);axis=ring['axis'];b=(axis+1)%3;c=(axis+2)%3
        for u,v in mer:
            for x,y in lon:
                p=[Q(0)]*3;p[axis]=Q(ring['center'],w.SCALE)+radius*v
                p[b]=(Q(ring['radius'],w.SCALE)+radius*u)*x;p[c]=(Q(ring['radius'],w.SCALE)+radius*u)*y
                vertices.append(tuple(p));amp=r.cm(z,w.phase(ring,r.mul(p,w.SCALE)))
                currents.append((amp,w.ZERO,w.ZERO))
        for j in range(len(mer)):
            for i in range(width):
                a=start+j*width+i;b1=start+j*width+(i+1)%width
                c1=start+((j+1)%len(mer))*width+(i+1)%width;d=start+((j+1)%len(mer))*width+i
                faces.extend(((a,b1,c1),(a,c1,d)))
    source=w.wire(dict(kind='toroidal-channel-cores',rings=w.RINGS,psi=psi,physical_core_radius=radius,physical_field_minor=Q(w.MINOR,w.SCALE),current='psi_i * rational local phase plate',field_interactions='witnessed support nodes; drawn core crossings do not create new contacts'))
    return r.compile_scene(vertices,faces,currents=currents,source=source,step=Q(1,16),receiver=r.Receiver(distance=Q(32),aperture=Q(1,16)),bounds=(-5,-5,5,5),closed_outward=True)


def bridge():
    data=json.loads(Path(__file__).with_name('woven_bridge_receipt.json').read_text())
    vertices=[tuple(ratio(x)/w.SCALE for x in p) for p in data['source_geometry_mapped']['vertices']]
    faces=data['source_geometry_mapped']['faces'];site=tuple(ratio(x)/w.SCALE for x in data['scene']['site'])
    scale=ratio(data['support']['scale'])/w.SCALE
    # The receiver uses the physical site and a declared magnification, retaining its origin.
    current=[]
    for coords in data['source_geometry_mapped']['source_coordinates']:
        local=tuple(ratio(x) for x in coords)
        # A retained phase field on the source chart; independent of drawing color labels.
        amp=(local[0]+local[2],local[1]+local[2])
        current.append((amp,w.ZERO,w.ZERO))
    frame=[tuple(ratio(v) for v in col) for col in data['affine_frame']['columns']]
    det=r.dot(frame[0],r.cross(frame[1],frame[2]))
    dual=[r.mul(r.cross(frame[(i+1)%3],frame[(i+2)%3]),1/det) for i in range(3)]
    def pull(cov):return tuple(sum(cov[i]*dual[i][j] for i in range(3)) for j in range(3))
    receiver=r.Receiver(origin=site,right=r.mul(pull(r.Receiver().right),1/scale),up=r.mul(pull(r.Receiver().up),1/scale),view=pull(r.Receiver().view),distance=Q(12),aperture=Q(1,16))
    return r.compile_scene(vertices,faces,currents=current,receiver=receiver,step=Q(1,8),bounds=(-3,-3,3,3),source=dict(kind='overlap-shorts',receipt=data,receiver_current='sum of the retained C3 polynomial current A*z on the magnified local chart; both sides',magnification=r.ratio(1/scale)))


def lobe_scene(step,off=False):
    law=lobes.build();state=law['contact_off_ablation'][step] if off else law['states'][step]
    qs=[ratio(state['q1']),Q(0)] if off else [ratio(x) for x in state['q']]
    gradients=[lobes.domain_response(qs[0])-1,Q(0)] if off else [ratio(x) for x in state['gradient']]
    vertices=[];faces=[];currents=[];domains=[];camera=r.Receiver(distance=Q(40),aperture=Q(1,16))
    source_knots=kg.knots()
    for index,key in enumerate(('trefoil_3_1','figure_eight_4_1')):
        packet=source_knots[key];points=[tuple(Q(int(x[0]),int(x[1])) for x in p) for p in packet['vertices']][::2]
        # Coarser angular source retains the same explicit crossing population.
        assert len(kg._projected_crossings(points))==packet['projected_crossing_count']
        for i in range(len(points)):
            for j in range(i+2,len(points)):
                if i==0 and j==len(points)-1:continue
                assert kg._seg_intersection_3(points[i],points[(i+1)%len(points)],points[j],points[(j+1)%len(points)]) is None
        vv,ff,_=kw.tube(points,radius=Q(1,4))
        volume=sum(r.dot(vv[a],r.cross(vv[b],vv[c])) for a,b,c in ff)/6
        if volume<0:ff=[tuple(reversed(f)) for f in ff]
        assert sum(r.dot(vv[a],r.cross(vv[b],vv[c])) for a,b,c in ff)>0
        q=qs[index];co=(1-q*q)/(1+q*q);si=2*q/(1+q*q)
        center=(Q(-3 if index==0 else 3),Q(0),Q(0));start=len(vertices)
        for p in vv:
            p=r.mul(p,Q(1,2));arm=(co*p[0]+si*p[1],-si*p[0]+co*p[1],p[2]);world=r.add(center,arm)
            vertices.append(world)
            amp=(lobes.conformation(q)*r.dot(arm,camera.view),-gradients[index]*r.dot(arm,camera.right))
            currents.append((amp,w.ZERO,w.ZERO))
        faces.extend(tuple(start+i for i in f) for f in ff)
        domains.append(dict(kind=key,center=center,q=q,gradient=gradients[index],rotation=(co,si),source_centerline=points,start=start,end=len(vertices)))
    src=w.wire(dict(kind='coupled-conformation-domains',step=step,contact_off=off,law=law,domains=domains,current='conformation * arm.view + i * (-generalized gradient) * arm.right',geometric_chart='R(q), theta=-2 arctan(q); q is not a literal angle'))
    return r.compile_scene(vertices,faces,currents=currents,receiver=camera,source=src,step=Q(1,8),bounds=(-7,-4,7,4),closed_outward=True)


def main():
    receipt=json.loads(Path(__file__).with_name('woven_ecology_receipt.json').read_text())
    psi=[tuple(ratio(x) for x in z) for z in receipt['states'][0][0]]
    path=ROOT/'research/papers/source/papers/hnn-information-chemistry/ecology-detail-scenes.json';scenes=json.loads(path.read_text()) if path.exists() else {}
    import sys
    selected=sys.argv[1:]
    for name,build in [('woven_cores',lambda:carrier(psi)),('woven_bridge',bridge),('lobes_0',lambda:lobe_scene(0)),('lobes_2',lambda:lobe_scene(2)),('lobes_4',lambda:lobe_scene(4)),('lobes_off',lambda:lobe_scene(4,True))]:
        if selected and name not in selected:continue
        scenes[name]=build();assert not scenes[name]['meta']['unresolved_near_faces'] and not scenes[name]['meta']['degenerate_faces']
        path.write_text(json.dumps(scenes,separators=(',',':'))+'\n');print(name,len(scenes[name]['marks']),'marks',flush=True)
    export=runpy.run_path(str(ROOT/'research/papers/source/packages/holonic-receiver/export_svg.py'))['scene_svg']
    for name,scene in scenes.items():(ROOT/'research/papers/rendered/receiver-engraving'/f'{name}.svg').write_text(export(scene,width_mm=Q(100),line_width_pt=Q(1,2)))
    # Source locator is annotation, separate from phase ink and opaque visibility.
    body=json.loads((ROOT/'research/papers/source/papers/hnn-information-chemistry/woven-scenes.json').read_text())['woven_0']
    site=tuple(ratio(x)/w.SCALE for x in scenes['woven_bridge']['meta']['source']['receipt']['scene']['site'])
    camera=body['meta']['receiver']
    origin=tuple(ratio(x) for x in camera['origin']);right=tuple(ratio(x) for x in camera['right']);up=tuple(ratio(x) for x in camera['up'])
    point=r.sub(site,origin);x=r.dot(right,point);y=-r.dot(up,point)
    drawing=export(body,width_mm=Q(100),line_width_pt=Q(1,3))
    annotation='<metadata id="source-locator">'+json.dumps(w.wire(dict(kind='annotation',world_site=site,projected=(x,-y),scope='buried source contact; not a visible optical return')))+'<'+ '/metadata>'
    annotation+=f'<circle cx="{float(x)}" cy="{float(y)}" r="0.1" fill="none" stroke="white" stroke-width="0.02"/><text x="{float(x+Q(1,5))}" y="{float(y-Q(1,10))}" fill="white" font-family="serif" font-size="0.35">w</text>'
    (ROOT/'research/papers/rendered/receiver-engraving/woven_contact_locator.svg').write_text(drawing.replace('</svg>',annotation+'</svg>'))


if __name__=='__main__':main()
