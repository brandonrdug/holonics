"""Build exact source/receiver packets consumed by the Typst engraving packages."""
from pathlib import Path
from fractions import Fraction as Q
import importlib.util,sys,json,time
from collections import defaultdict
ROOT=Path(__file__).resolve().parents[3]
PACKAGE=ROOT/'research/papers/source/packages/holonic-receiver/compile.py'
spec=importlib.util.spec_from_file_location('receiver_compile',PACKAGE)
r=importlib.util.module_from_spec(spec);sys.modules[spec.name]=r;spec.loader.exec_module(r)


def field_matrix(swirl=Q(0)):
    return ((0,0,(Q(1),swirl)),(0,0,(-swirl,Q(1))),((Q(1),-swirl),(swirl,Q(1)),0))

def flow_with(matrix,p,t):
    z=tuple(r.pair(x) for x in p)
    az=r.complex_matrix(matrix,z);aaz=r.complex_matrix(matrix,az)
    return tuple(r.ca(r.ca(x,r.cs(y,t)),r.cs(w,t*t/2)) for x,y,w in zip(z,az,aaz))

def quarter(n):
    return [(Q(n*n-j*j,n*n+j*j),Q(2*j*n,n*n+j*j)) for j in range(n)]

def circle(n=6):
    points=[]
    for k in range(4):
        for x,y in quarter(n):
            points.append(((x,y),(-y,x),(-x,-y),(y,-x))[k])
    assert all(x*x+y*y==1 for x,y in points)
    return points


def torus(n=6,m=4):
    longitude=circle(n); meridian=circle(m)
    vertices=[((3+b)*x,(3+b)*y,a) for b,a in meridian for x,y in longitude]
    faces=[];w=len(longitude);h=len(meridian)
    for j in range(h):
        for i in range(w):
            a=j*w+i;b=j*w+(i+1)%w;c=((j+1)%h)*w+(i+1)%w;d=((j+1)%h)*w+i
            faces.extend(((a,b,c),(a,c,d)))
    return vertices,faces


def sphere(n=6,m=4):
    longitude=circle(n); lat=circle(m)[:2*m+1]
    vertices=[(Q(0),Q(0),Q(2))]
    for c,s in lat[1:]:
        if s==0: continue
        vertices.extend((2*s*x,2*s*y,2*c) for x,y in longitude)
    vertices.append((Q(0),Q(0),Q(-2)))
    w=len(longitude);rows=(len(vertices)-2)//w;faces=[]
    for i in range(w): faces.append((0,1+i,1+(i+1)%w))
    for j in range(rows-1):
        for i in range(w):
            a=1+j*w+i;b=1+j*w+(i+1)%w;c=b+w;d=a+w
            faces.extend(((a,d,c),(a,c,b)))
    for i in range(w): faces.append((len(vertices)-1,1+(rows-1)*w+(i+1)%w,1+(rows-1)*w+i))
    return vertices,faces


def shorts(kind='shorts',n=8,width=4):
    coords=list(map(Q,(-1,Q(-2,3),Q(-1,3),Q(-1,6),0,Q(1,6),Q(1,3),Q(2,3),1)))
    vertices=[(x,y,Q(0)) for y in coords for x in coords];faces=[]
    def quad(a,b,c,d): faces.extend(((a,b,c),(a,c,d)))
    for j in range(8):
        for i in range(8): quad(j*9+i,j*9+i+1,(j+1)*9+i+1,(j+1)*9+i)
    half=circle(n)[:2*n]+[(Q(-1),Q(0))]
    for band in ('a','b') if kind=='shorts' else ('a',):
        rows=[]
        for i,(c,s) in enumerate(half):
            row=[]
            for j in range(width+1):
                v=Q(j-2,6)
                if i in (0,len(half)-1):
                    if band=='a':
                        y=2+j if i==0 or kind=='annulus' else 6-j
                        vertex=9*y+(0 if i==0 else 8)
                    else: vertex=2+j+(0 if i==0 else 72)
                else:
                    if band=='a':
                        center=(-c,Q(0),2*s)
                        # Exact rational transverse frame: norm²=1-3 sin⁴(t)/4.
                        frame=(Q(0),Q(1),Q(0)) if kind=='annulus' else (-s*c,c,s*s/2)
                    else: center=(Q(0),-c,-2*s);frame=(Q(1),Q(0),Q(0))
                    vertex=len(vertices);vertices.append(r.add(center,r.mul(frame,v)))
                row.append(vertex)
            rows.append(row)
        for i in range(len(rows)-1):
            for j in range(width): quad(rows[i][j],rows[i+1][j],rows[i+1][j+1],rows[i][j+1])
    return vertices,faces


def verify():
    # Exact nilpotent complex flow, closed contour, receiver and color controls.
    probes=[tuple(map(Q,p)) for p in ((1,2,3),(-1,0,2),(0,1,0))]
    for p in probes:
        z=tuple(r.pair(x) for x in p)
        a=r.complex_matrix(r.A,z);aa=r.complex_matrix(r.A,a);aaa=r.complex_matrix(r.A,aa)
        assert aaa==((0,0),(0,0),(0,0))
        for t in (Q(0),Q(1,2),Q(1),Q(2)):
            f=r.complex_flow(p,t)
            af=r.complex_matrix(r.A,f);aaf=r.complex_matrix(r.A,af)
            back=tuple(r.ca(r.ca(x,r.cs(y,-t)),r.cs(w,t*t/2)) for x,y,w in zip(f,af,aaf))
            assert back==z
            assert sum(r.primaries(r.Receiver().amplitude(f)))<1
    triangle=[r.vec(x) for x in ((1,0,0),(0,1,0),(0,0,1))]
    for swirl in (Q(0),Q(1,2),Q(1)):
        matrix=field_matrix(swirl)
        circulation=(Q(0),Q(0))
        for p,q in zip(triangle,triangle[1:]+triangle[:1]):
            u=r.complex_matrix(matrix,tuple(r.pair(v) for v in r.mul(r.add(p,q),Q(1,2))))
            circulation=r.ca(circulation,tuple(sum(r.cs(v,d)[j] for v,d in zip(u,r.sub(q,p))) for j in range(2)))
        assert circulation==(swirl,swirl)
        for p in probes:
            z=tuple(r.pair(v) for v in p)
            a=r.complex_matrix(matrix,z);aa=r.complex_matrix(matrix,a)
            assert r.complex_matrix(matrix,aa)==((0,0),(0,0),(0,0))
    # Matrix words retain their noncommuting cross term in the four-generator algebra.
    qmatrix=((1,r.I,0),(r.I,-1,0),(0,0,0))
    for lam,mu in ((Q(0),Q(1,2)),(Q(1,2),Q(1))):
        left,right=field_matrix(lam),field_matrix(mu)
        for point in ((1,0,0),(0,1,0),(0,0,1)):
            z=tuple(r.pair(v) for v in point)
            lr=r.complex_matrix(left,r.complex_matrix(right,z))
            rl=r.complex_matrix(right,r.complex_matrix(left,z))
            difference=tuple((a-c,b-d) for (a,b),(c,d) in zip(lr,rl))
            expected=tuple(r.cm((Q(0),2*(lam-mu)),v) for v in r.complex_matrix(qmatrix,z))
            assert difference==expected
    amplitude=(Q(1),Q(2));opposite=tuple(-x for x in amplitude);reference=(Q(1),Q(0))
    assert r.primaries(amplitude)==r.primaries(opposite)
    assert r.primaries(r.ca(amplitude,reference))!=r.primaries(r.ca(opposite,reference))
    # A foreground triangle removes the middle subinterval, including correct depth.
    triangle=tuple(map(r.vec,((-1,-1,1),(1,-1,1),(0,1,1))))
    vis=r.Visibility([triangle])
    assert vis.intervals(r.vec((-2,0,0)),r.vec((2,0,0)),set())==[(Q(0),Q(3,8)),(Q(5,8),Q(1))]
    assert vis.intervals(r.vec((-2,0,2)),r.vec((2,0,2)),set())==[(0,1)]
    # Finite-depth receiver is not allowed to manufacture a point at its pole.
    assert r.Receiver(distance=Q(0)).project((0,0,0)) is None
    for factory in (torus,sphere):
        vertices,faces=factory();edges=defaultdict(int)
        for f in faces:
            for a,b in zip(f,f[1:]+f[:1]): edges[tuple(sorted((a,b)))]+=1
        assert all(v==2 for v in edges.values())
        assert len(vertices)-len(edges)+len(faces)==(0 if factory==torus else 2)
    orientation_file=ROOT/'research/papers/source/papers/hnn-information-chemistry/orientation-example.py'
    orient_spec=importlib.util.spec_from_file_location('orientation_witness',orientation_file)
    orient=importlib.util.module_from_spec(orient_spec);orient_spec.loader.exec_module(orient)
    for kind,chi,boundary,orientable in (('annulus',0,2,True),('mobius',0,1,False),('shorts',-1,1,False)):
        vertices,faces=shorts(kind)
        result,_=orient.inspect(faces)
        assert (result['chi'],result['boundary_count'],result['orientable'])==(chi,boundary,orientable)
    detector=r.Receiver()
    for a,b,target in ((detector.right,detector.right,1),(detector.up,detector.up,1),(detector.view,detector.view,1),(detector.right,detector.up,0)):
        assert r.dot(a,b)==target
    for x in (Q(1,3),Q(1),Q(2),Q(7,5)):
        center,radius=r.log_interval(x)
        assert radius<=Q(1,2**18)
    print('Exact receiver, visibility, nilpotent C^3 flow, closed-mesh and log-enclosure controls returned.',flush=True)


def main():
    verify();scenes={}
    jobs=[
      ('sphere_stipple',sphere,dict(style='stipple',step=Q(1,12),bounds=(-3,-3,3,3))),
      ('sphere_mono',sphere,dict(style='mono',step=Q(1,10),bounds=(-3,-3,3,3))),
      ('sphere_phase',sphere,dict(step=Q(1,8),bounds=(-3,-3,3,3))),
      ('torus_phase',torus,dict(step=Q(1,8),bounds=(-5,-4,5,4))),
      ('torus_mono',torus,dict(style='mono',step=Q(1,8),bounds=(-5,-4,5,4))),
      ('shorts_phase',shorts,dict(step=Q(1,12),bounds=(-2,-3,2,3))),
      ('shorts_mono',shorts,dict(style='mono',step=Q(1,12),bounds=(-2,-3,2,3))),
      ('mobius_phase',lambda:shorts('mobius'),dict(step=Q(1,12),bounds=(-2,-2,2,3))),
      ('annulus_mono',lambda:shorts('annulus'),dict(style='mono',step=Q(1,12),bounds=(-2,-2,2,3))),
      ('torus_entropy',torus,dict(potential='entropy',step=Q(1,32),bounds=(-5,-4,5,4))),
      ('torus_pinhole',torus,dict(receiver=r.Receiver(perspective=True,distance=Q(8),focal=Q(8)),step=Q(1,8),bounds=(-6,-5,6,5))),
    ]
    base=r.Receiver();turned_up=tuple(-x for x in base.right)
    camera=r.Receiver(right=base.up,up=turned_up)
    for t in (Q(0),Q(1,2),Q(1)):
        jobs.append((f'flow_{t.numerator}_{t.denominator}',torus,dict(tau=t,receiver=camera,step=Q(1,6),bounds=(-10,-6,10,6))))
    for phase,name in (((Q(1),Q(0)),'real'),((Q(3,5),Q(4,5)),'turned')):
        jobs.append(('receiver_'+name,torus,dict(tau=Q(1),receiver=r.Receiver(right=base.up,up=turned_up,phase=phase),step=Q(1,6),bounds=(-10,-6,10,6))))
    jobs.append(('near_fold',torus,dict(tau=Q(7,5),receiver=camera,step=Q(1,4),bounds=(-10,-6,10,6))))
    jobs.append(('reopened',torus,dict(tau=Q(7,5),receiver=r.Receiver(right=base.up,up=turned_up,phase=(Q(3,5),Q(4,5))),step=Q(1,4),bounds=(-10,-6,10,6))))
    for swirl in (Q(1,2),Q(1)):
        jobs.append((f'curl_{swirl.numerator}_{swirl.denominator}',torus,dict(tau=Q(7,5),swirl=swirl,receiver=r.Receiver(right=base.up,up=turned_up,distance=Q(32)),step=Q(1,4),bounds=(-12,-10,12,10))))
    wanted=set(sys.argv[1:])
    for name,factory,options in jobs:
        if wanted and name not in wanted: continue
        start=time.monotonic();vertices,faces=factory()
        swirl=options.pop('swirl',Q(0));matrix=field_matrix(swirl)
        positions=[flow_with(matrix,p,options.get('tau',Q(0))) for p in vertices]
        currents=[r.complex_matrix(matrix,z) for z in positions]
        matrix_wire=[[[str(a.numerator),str(a.denominator),str(b.numerator),str(b.denominator)] for a,b in map(r.pair,row)] for row in matrix]
        source=dict(name=name,generator=matrix_wire,swirl=[str(swirl.numerator),str(swirl.denominator)])
        scenes[name]=r.compile_scene(positions,faces,currents=currents,source=source,**options)
        print(name,len(scenes[name]['marks']),'marks',round(time.monotonic()-start,2),'seconds',flush=True)
    output=ROOT/'research/papers/source/papers/hnn-information-chemistry/receiver-scenes.json'
    if wanted and output.exists(): old=json.loads(output.read_text());old.update(scenes);scenes=old
    output.write_text(json.dumps(scenes,separators=(',',':'))+'\n')
    receipt=ROOT/'research/experiments/receiver_engraving/receipt.json'
    receipt.write_text(json.dumps({k:v['meta'] for k,v in scenes.items()},indent=2)+'\n')

if __name__=='__main__':main()
