"""Exact finite transmission waves on material knot carriers in a forced C³ flow.

Rational scattering is a declared constitutive lattice, not a sampled NS solver.
Every step retains directional complex amplitudes, heat and causal incidence.
"""
from pathlib import Path
from fractions import Fraction as Q
import runpy,json,sys,time
base=runpy.run_path(str(Path(__file__).with_name('build.py')))
r=base['r']; ROOT=base['ROOT']
ZERO=(Q(0),Q(0))
REFLECTION=Q(3,5); TRANSMISSION=Q(4,5); ATTENUATION=Q(15,16)


def power(z): return z[0]**2+z[1]**2

def advance(plus,minus,heat):
    """Local impedance scattering, one-edge travel, heat on the same cycle."""
    n=len(plus)
    pa=[r.ca(r.cs(a,REFLECTION),r.cs(b,-TRANSMISSION)) for a,b in zip(plus,minus)]
    ma=[r.ca(r.cs(a,TRANSMISSION),r.cs(b,REFLECTION)) for a,b in zip(plus,minus)]
    assert sum(map(power,pa))+sum(map(power,ma))==sum(map(power,plus))+sum(map(power,minus))
    source=[(1-ATTENUATION**2)*(power(a)+power(b)) for a,b in zip(pa,ma)]
    pp=[r.cs(pa[(i-1)%n],ATTENUATION) for i in range(n)]
    mm=[r.cs(ma[(i+1)%n],ATTENUATION) for i in range(n)]
    # A positivity-preserving finite heat passage: self 1/2; each neighbor 1/4.
    hh=[heat[i]/2+(heat[(i-1)%n]+heat[(i+1)%n])/4+source[i] for i in range(n)]
    assert sum(map(power,pp))+sum(map(power,mm))+sum(hh)==sum(map(power,plus))+sum(map(power,minus))+sum(heat)
    assert all(v>=0 for v in hh)
    return pp,mm,hh


def states(n,last=24,active=True):
    plus=[ZERO]*n;minus=[ZERO]*n;heat=[Q(0)]*n
    if active: plus[0]=(Q(1),Q(0));minus[0]=(Q(0),Q(1))
    out=[(plus,minus,heat)]
    for k in range(last):
        plus,minus,heat=advance(plus,minus,heat)
        # Exact finite-speed cone; diffusion here is a finite passage too.
        for i in range(n):
            if min(i,n-i)>k+1: assert plus[i]==minus[i]==ZERO and heat[i]==0
        out.append((plus,minus,heat))
    return out


def flow(p,t):
    x,y,z=p
    return (x+t*z/2,y+t*t*x/4+t**3*z/8,z)


def velocity(p,t):
    x,y,z=p
    return (z/2,t*x/2+t*t*z/8,Q(0))


def check_flow():
    import sympy as s
    x,y,z,t,nu=s.symbols('x y z t nu');p=s.Matrix([x,y,z])
    f=s.Matrix(flow(p,t));u=s.Matrix(velocity(p,t))
    jac=f.jacobian(p)
    assert s.expand(jac.det())==1
    assert s.simplify(s.diff(f,t)-u.subs(dict(zip(p,f)),simultaneous=True))==s.zeros(3,1)
    force=s.Matrix([0,x/2+t*z/2,0])
    lap=s.Matrix([sum(s.diff(v,q,2) for q in p) for v in u])
    assert s.simplify(s.diff(u,t)+u.jacobian(p)*u-nu*lap-force)==s.zeros(3,1)
    assert s.trace(u.jacobian(p))==0
    return dict(flow='F_t=(x+t*z/2,y+t²*x/4+t³*z/8,z)',velocity='U=(z/2,t*x/2+t²*z/8,0)',force='f=(0,x/2+t*z/2,0)',pressure='0',complex_domain='C^3; complex-bilinear advection; pictured real invariant slice',determinant='1',viscosity='any declared nu; Lap U=0',inverse='z=Z,x=X-t*Z/2,y=Y-t²*X/4')


def wire(v):
    if isinstance(v,Q): return r.ratio(v)
    if isinstance(v,dict): return {k:wire(x) for k,x in v.items()}
    if isinstance(v,(list,tuple)): return [wire(x) for x in v]
    return v


def wave_receipt(n):
    series=states(n)
    return dict(stations=n,reflection=REFLECTION,transmission=TRANSMISSION,impedance_ratio=4,
                attenuation=ATTENUATION,clock_step=Q(1,24),heat_passage=(Q(1,4),Q(1,2),Q(1,4)),
                snapshots=[dict(step=k,plus=a,minus=b,heat=h,wave_energy=sum(map(power,a))+sum(map(power,b))) for k,(a,b,h) in enumerate(series)])



def tube(points,radius=Q(1,4),origin=(Q(0),Q(0),Q(0))):
    """Rational hexagonal transverse sections; supplied finite triangulated body."""
    ring=((Q(1),Q(0)),(Q(3,5),Q(4,5)),(-Q(3,5),Q(4,5)),(-Q(1),Q(0)),(-Q(3,5),-Q(4,5)),(Q(3,5),-Q(4,5)))
    vertices=[];faces=[];tangents=[]
    for i,p in enumerate(points):
        tangent=r.sub(points[(i+1)%len(points)],points[(i-1)%len(points)])
        tangent=r.mul(tangent,1/max(map(abs,tangent)))
        # Radial seed; projection removes its tangential part without square roots.
        seed=(p[0]-origin[0],p[1]-origin[1],p[2]-origin[2])
        normal=r.sub(seed,r.mul(tangent,r.dot(seed,tangent)/r.dot(tangent,tangent)))
        if r.dot(normal,normal)==0:
            seed=(Q(0),Q(0),Q(1));normal=r.sub(seed,r.mul(tangent,r.dot(seed,tangent)/r.dot(tangent,tangent)))
        normal=r.mul(normal,1/max(map(abs,normal)))
        binormal=r.cross(tangent,normal);binormal=r.mul(binormal,1/max(map(abs,binormal)))
        tangents.append(tangent)
        for c,s in ring: vertices.append(r.add(p,r.mul(r.add(r.mul(normal,c),r.mul(binormal,s)),radius)))
    w=len(ring)
    for i in range(len(points)):
        for j in range(w):
            a=i*w+j;b=((i+1)%len(points))*w+j;c=((i+1)%len(points))*w+(j+1)%w;d=i*w+(j+1)%w
            faces.extend(((a,b,c),(a,c,d)))
    return vertices,faces,tangents


def render_knot(name,packet,steps=(0,6,12,18,24)):
    points=[tuple(Q(*x) for x in p) for p in packet['vertices']]
    lengths=packet.get('component_lengths',[len(points)])
    vertices=[];faces=[];tangents=[];series=[];start=0
    for ci,length in enumerate(lengths):
        local=points[start:start+length]
        origin=tuple(sum(p[j] for p in local)/length for j in range(3))
        vv,ff,tt=tube(local,origin=origin)
        offset=len(vertices);vertices.extend(vv);faces.extend(tuple(i+offset for i in f) for f in ff);tangents.extend(tt)
        series.append(states(length,active=(ci==0)));start+=length
    wave=[tuple(sum((list(part[k][field]) for part in series),[]) for field in range(3)) for k in range(25)]
    # The mesh check rejects intersections, including at adjacent joints.
    import triangle_embedding as embedding
    check=embedding.verify_mesh(vertices,faces)
    print(name,'mesh',check,flush=True)
    assert check['embedded']
    scenes={};receipts=[]
    camera=r.Receiver(right=(Q(1),Q(0),Q(0)),up=(Q(0),Q(4,5),Q(3,5)),view=(Q(0),-Q(3,5),Q(4,5)),distance=Q(32),aperture=Q(1,16))
    for k in steps:
        t=Q(k,24);plus,minus,heat=wave[k]
        moved=[flow(p,t) for p in vertices];currents=[]
        for j,p in enumerate(moved):
            station=j//6; psi=r.ca(plus[station],minus[station])
            # Push-forward the actual directional material carrier, not a screen normal.
            tangent=flow(tangents[station],t)
            u=velocity(p,t)
            currents.append(tuple(r.ca((a,omega),r.cs(psi,b)) for a,omega,b in zip(u,(-t*t/8,Q(1,2),t/2),tangent)))
        src=wire(dict(kind='knot-transmission-in-forced-flow',topology=packet,step=k,clock=t,
                      carrier_vertices=vertices,carrier_faces=faces,tangents=tangents,
                      plus=plus,minus=minus,heat=heat,flow=check_flow(),mesh=check,
                      receiver_current='U + i*ell*curl(U) + (psi_plus+psi_minus)*DF_t(tangent); ell=1 declared lane-length chart',
                      wave_energy=sum(map(power,plus))+sum(map(power,minus)),heat_energy=sum(heat)))
        potential='current'
        key=f'{name}_{k}'
        scenes[key]=r.compile_scene(moved,faces,currents=currents,receiver=camera,tau=t,step=Q(1,16),bounds=(-6,-6,6,6),source=src,potential=potential)
        assert not scenes[key]['meta']['unresolved_near_faces'] and not scenes[key]['meta']['degenerate_faces']
        print(key,len(scenes[key]['marks']),'marks',flush=True)
        if k in (0,24):
            style='mono' if k==0 else 'phase';pot='current' if k==0 else 'entropy'
            alt=key+('_mono' if k==0 else '_entropy')
            scenes[alt]=r.compile_scene(moved,faces,currents=currents,receiver=camera,tau=t,step=Q(1,32) if pot=='entropy' else Q(1,16),bounds=(-6,-6,6,6),source=src,potential=pot,style=style,log_display_bits=20)
    return scenes,wire(dict(topology=packet,mesh=check,components=lengths,wave=[wave_receipt(n) if i==0 else dict(stations=n,source='zero',propagates='independently; no cross-component contact') for i,n in enumerate(lengths)]))


def build_knots():
    import knot_geometry
    output=ROOT/'research/papers/source/papers/hnn-information-chemistry/knot-scenes.json'
    allscenes=json.loads(output.read_text()) if output.exists() else {}
    record={};selected=sys.argv[1:]
    for name,packet in dict(knot_geometry.knots(),chain=chain_packet()).items():
        if selected and name not in selected: continue
        scenes,receipt=render_knot(name,packet)
        allscenes.update(scenes);record[name]=receipt
        output.write_text(json.dumps(allscenes,separators=(',',':'))+'\n')
        (Path(__file__).with_name('knot_wave_'+name+'_receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n')
    # Same packet in SVG; supports standalone viewing without the entire paper.
    import importlib.util
    spec=importlib.util.spec_from_file_location('wave_svg',ROOT/'research/papers/source/packages/holonic-receiver/export_svg.py')
    exporter=importlib.util.module_from_spec(spec);spec.loader.exec_module(exporter)
    out=ROOT/'research/papers/rendered/receiver-engraving';out.mkdir(exist_ok=True)
    for name,scene in allscenes.items():
        (out/(name+'.svg')).write_text(exporter.scene_svg(scene,width_mm=Q(100),line_width_pt=Q(1,2),mode='mono' if name.endswith('mono') else 'phase'))

def chain_packet():
    circle=base['circle'](6);points=[]
    for center,plane in ((-3,'xy'),(0,'xz'),(3,'xy')):
        points.extend((2*x+center,2*y,Q(0)) if plane=='xy' else (2*x+center,Q(0),2*y) for x,y in circle)
    return dict(kind='three_component_chain',vertices=[[[v.numerator,v.denominator] for v in p] for p in points],
                component_lengths=[len(circle)]*3,linking='adjacent pairs have one oriented spanning-disk intersection; end pair is separated by x',
                certificate='three planar unknotted cores; adjacent Hopf links',source_port='first component only; separated surfaces do not exchange wave amplitude')

if __name__=='__main__': build_knots()
