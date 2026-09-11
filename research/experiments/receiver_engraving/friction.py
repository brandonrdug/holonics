"""Two linked guided bodies: contact grip, viscous slip, heat and complex propagation.

This is an exact bounded constitutive model, not an unconstrained elastic-knot solver.
The coordinates a=e^-2t give rational snapshots of the continuous contact solution.
"""
from pathlib import Path
from fractions import Fraction as Q
from collections import defaultdict
import runpy,json,time
base=runpy.run_path(str(Path(__file__).with_name('build.py')))
r=base['r']; ROOT=base['ROOT']
RADIUS=Q(1,4); CORNER=Q(1,2)


def rounded_boundary(bounds,radius,n=4):
    xmin,xmax,ymin,ymax=map(Q,bounds)
    centers=((xmax-CORNER,ymax-CORNER),(xmin+CORNER,ymax-CORNER),
             (xmin+CORNER,ymin+CORNER),(xmax-CORNER,ymin+CORNER))
    points=[]
    for k,(cx,cy) in enumerate(centers):
        for x,y in base['quarter'](n)+[(Q(0),Q(1))]:
            x,y=((x,y),(-y,x),(-x,-y),(y,-x))[k]
            points.append((cx+radius*x,cy+radius*y))
    # Keep four contact-strip stations in the straight sides, shared by offsets.
    out=[]
    for p,q in zip(points,points[1:]+points[:1]):
        out.append(p)
        if p[0]==q[0] and abs(p[1]-q[1])>2*RADIUS:
            for y in sorted((-RADIUS,RADIUS),reverse=q[1]<p[1]):
                if min(p[1],q[1])<y<max(p[1],q[1]): out.append((p[0],y))
    return out


def body(bounds,plane):
    outer=rounded_boundary(bounds,CORNER+RADIUS)
    inner=rounded_boundary(bounds,CORNER-RADIUS)
    assert len(outer)==len(inner)
    vertices=[]
    for normal in (-RADIUS,RADIUS):
        for ring in (outer,inner):
            vertices.extend((x,y,normal) if plane=='xy' else (x,normal,y) for x,y in ring)
    n=len(outer);faces=[]
    def quad(a,b,c,d): faces.extend(((a,b,c),(a,c,d)))
    for i in range(n):
        j=(i+1)%n
        quad(i,j,j+n,i+n);quad(i+2*n,i+3*n,j+3*n,j+2*n)
        quad(i,i+2*n,j+2*n,j);quad(i+n,j+n,j+3*n,i+3*n)
    if plane=='xy': faces=[tuple(reversed(f)) for f in faces]
    edges=defaultdict(list)
    for f in faces:
        for a,b in zip(f,f[1:]+f[:1]):
            e=tuple(sorted((a,b)));edges[e].append(1 if (a,b)==e else -1)
    assert all(len(x)==2 and sum(x)==0 for x in edges.values())
    assert len(vertices)-len(edges)+len(faces)==0
    return vertices,faces


def states(a):
    a=Q(a)
    assert 0<a<=1
    d=(1-a)/2
    # C4 is the actual boundary-node incidence of the contact square.
    # Adjacent nodes are ell=2r apart; unit diffusivity gives rate 1/ell²=4.
    rate=1/(4*RADIUS*RADIUS)
    mean=(1-a*a)/2
    one=(a*a-a**4)
    two=(a*a-a**8)/6
    theta=tuple(mean+one*x+two*y for x,y in zip((1,0,-1,0),(1,-1,1,-1)))
    # Diffusing received tangential impulse: psi'=-4L psi+2(1+i)a delta0.
    impulse0=(1-a)/4
    impulse1=(a-a**4)/6
    impulse2=(a-a**8)/28
    impulse=tuple(impulse0+impulse1*x+impulse2*y for x,y in zip((1,0,-1,0),(1,-1,1,-1)))
    assert sum(theta)==2*(1-a*a) and all(x>=0 for x in theta)
    assert sum(impulse)==1-a and all(x>=0 for x in impulse)
    lap=lambda x:tuple(2*x[i]-x[(i-1)%4]-x[(i+1)%4] for i in range(4))
    dmean=2*a*a;done=(-4*a*a+8*a**4);dtwo=(-4*a*a+16*a**8)/6
    dtheta=tuple(dmean+done*x+dtwo*y for x,y in zip((1,0,-1,0),(1,-1,1,-1)))
    assert dtheta==tuple(-rate*v+(8*a*a if i==0 else 0) for i,v in enumerate(lap(theta)))
    ip0=a/2;ip1=(-2*a+8*a**4)/6;ip2=(-2*a+16*a**8)/28
    dimpulse=tuple(ip0+ip1*x+ip2*y for x,y in zip((1,0,-1,0),(1,-1,1,-1)))
    assert dimpulse==tuple(-rate*v+(2*a if i==0 else 0) for i,v in enumerate(lap(impulse)))
    assert 2*a*a+sum(theta)==2
    return dict(a=a,d=d,rate=rate,theta=theta,impulse=impulse,impulse_rate=dimpulse,heat_rate=dtheta,heat=2*(1-a*a),kinetic=2*a*a,power=8*a*a)


def contact(a):
    state=states(a);d=state['d']
    # Common plane of A's outer-right wall and B's inner-right wall.
    c=(Q(9,4),-d,d)
    vertices=[c]+[(c[0],c[1]+y,c[2]+z) for y,z in ((-RADIUS,-RADIUS),(RADIUS,-RADIUS),(RADIUS,RADIUS),(-RADIUS,RADIUS))]
    faces=[(0,i+1,(i+1)%4+1) for i in range(4)]
    cell_area=RADIUS*RADIUS
    assert cell_area==Q(1,16) and 4*cell_area==Q(1,4)
    # Both closed bodies retain an exact finite flat patch throughout 0<=a<=1.
    assert 2*d+RADIUS<=Q(3,2)
    # B's descending left core pierces the rounded spanning disk of A; its
    # ascending right core is outside. Both crossings stay on straight portions.
    assert -Q(3,2)<-2*d<Q(3,2) and -2<Q(-1,2)<2 and Q(5,2)>2
    return vertices,faces,state


def wire_complex(z): return [r.ratio(z[0]),r.ratio(z[1])]


def links_scene(a):
    _,_,state=contact(a);d=state['d'];center=(Q(9,4),-d,d)
    receiver=r.Receiver(distance=Q(32))
    all_vertices=[];all_faces=[];currents=[];regions=[]
    for sign,bounds,plane in ((1,(-2,2,-2,2),'xy'),(-1,(Q(-1,2),Q(5,2),-2,2),'xz')):
        vertices,faces=body(bounds,plane)
        shift=(Q(0),sign*d,sign*d)
        vertices=[r.add(p,shift) for p in vertices]
        force=(-Q(sign),-2*sign*a,-2*sign*a)
        torque_row=r.cross(force,receiver.view)
        row=tuple((f/2,t/2) for f,t in zip(force,torque_row))
        offset=tuple(-sum(row[j][k]*center[j] for j in range(3)) for k in range(2))
        start=len(all_vertices)
        for p in vertices:
            amp=tuple(sum(row[j][k]*p[j] for j in range(3))+offset[k] for k in range(2))
            currents.append((amp,(Q(0),Q(0)),(Q(0),Q(0))))
        all_vertices.extend(vertices);all_faces.extend(tuple(start+i for i in face) for face in faces)
        regions.append(dict(start=start,end=len(all_vertices),row=[wire_complex(x) for x in row],offset=wire_complex(offset)))
    source=dict(kind='affine-by-region',a=r.ratio(a),clock='t=-log(a)/2',regions=regions,
                contact_center=[r.ratio(v) for v in center],kinetic=r.ratio(state['kinetic']),heat=r.ratio(state['heat']))
    return r.compile_scene(all_vertices,all_faces,currents=currents,receiver=receiver,tau=a,
                           step=Q(1,8),bounds=(-5,-4,5,4),source=source)


def patch_scene(a):
    vertices,faces,state=contact(a)
    # Four dynamical boundary nodes; the central mean is a receiver reconstruction,
    # not a fifth thermal state. The two source components are impulse and heat.
    theta=(sum(state['theta'])/4,)+state['theta']
    impulse_rate=(sum(state['impulse_rate'])/4,)+state['impulse_rate']
    values=tuple((j/2,j/2+h/2) for j,h in zip(impulse_rate,theta))
    currents=[(value,(Q(0),Q(0)),(Q(0),Q(0))) for value in values]
    d=state['d']
    local_vertices=vertices
    receiver=r.Receiver(origin=(Q(9,4),-d,d),right=(Q(0),Q(1),Q(0)),up=(Q(0),Q(0),Q(1)),view=(Q(1),Q(0),Q(0)),aperture=RADIUS*RADIUS)
    source=dict(kind='vertex-values',a=r.ratio(a),clock='t=-log(a)/2',values=[wire_complex(x) for x in values],
                carrier_vertices=[[[str(x.numerator),str(x.denominator)] for x in p] for p in vertices],carrier_faces=faces,
                boundary_adjacency=((1,3),(0,2),(1,3),(0,2)),theta=[r.ratio(x) for x in state['theta']],
                impulse=[r.ratio(x) for x in state['impulse']],impulse_rate=[r.ratio(x) for x in state['impulse_rate']],rate=r.ratio(state['rate']),
                patch_area=r.ratio(4*RADIUS*RADIUS),node_aperture=r.ratio(RADIUS*RADIUS))
    return r.compile_scene(local_vertices,faces,currents=currents,receiver=receiver,tau=a,
                           step=Q(1,256),bounds=(Q(-3,10),Q(-3,10),Q(3,10),Q(3,10)),source=source)


def main():
    scenes={};receipts=[]
    for a in (Q(1),Q(1,2),Q(1,8)):
        start=time.monotonic();name=f'friction_{a.numerator}_{a.denominator}'
        scenes[name]=links_scene(a)
        receipts.append({k:r.ratio(v) if isinstance(v,Q) else [r.ratio(x) for x in v] for k,v in states(a).items()})
        print(name,len(scenes[name]['marks']),'marks',round(time.monotonic()-start,2),'seconds',flush=True)
    for a in (Q(255,256),Q(15,16),Q(1,2)):
        name=f'contact_{a.numerator}_{a.denominator}';scenes[name]=patch_scene(a)
        print(name,len(scenes[name]['marks']),'marks',flush=True)
    path=ROOT/'research/papers/source/papers/hnn-information-chemistry/receiver-scenes.json'
    existing=json.loads(path.read_text());existing.update(scenes);path.write_text(json.dumps(existing,separators=(',',':'))+'\n')
    (ROOT/'research/experiments/receiver_engraving/friction-receipt.json').write_text(json.dumps(receipts,indent=2)+'\n')
    print('Returned: linked core disk intersection -1; actual contact plane, equal/opposite grip and slip forces, closed kinetic/heat budget, local C4 heat and complex impulse propagation.',flush=True)

if __name__=='__main__':main()
