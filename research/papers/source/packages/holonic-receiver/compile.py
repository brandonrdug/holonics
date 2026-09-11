"""Exact exterior receiver/engraving compiler for repository-local Typst packets.

Geometry, line-level intersection, depth clipping, and primary responses use Fraction.
Only the final drawing coordinates become decimal display values. This is an exterior
renderer, not native HNN conduct, a physical radiative-transfer solver, or a mesh learner.
Original implementation; methodology sources are recorded in README.md.
"""
from fractions import Fraction as Q
from collections import defaultdict
from dataclasses import dataclass


def exact(x):
    if not isinstance(x,(int,Q)): raise TypeError('source arithmetic requires integers or Fraction values')
    return Q(x)
def vec(v): return tuple(map(exact,v))
def add(a,b): return tuple(x+y for x,y in zip(a,b))
def sub(a,b): return tuple(x-y for x,y in zip(a,b))
def mul(a,s): return tuple(x*s for x in a)
def dot(a,b): return sum(x*y for x,y in zip(a,b))
def cross(a,b): return (a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
def mix(a,b,t): return add(a,mul(sub(b,a),t))
def wedge(a,b): return a[0]*b[1]-a[1]*b[0]
def pair(z): return (Q(z),Q(0)) if isinstance(z,(int,Q)) else tuple(map(exact,z))
def ratio(x): return [str(x.numerator),str(x.denominator)]
def read_ratio(x): return Q(int(x[0]),int(x[1]))
def ca(a,b): return (a[0]+b[0],a[1]+b[1])
def cm(a,b): return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def cs(a,s): return (a[0]*s,a[1]*s)
def complex_matrix(a,z): return tuple(tuple(sum(cm(pair(v),w)[k] for v,w in zip(row,z)) for k in range(2)) for row in a)

I=(Q(0),Q(1))
A=((0,0,1),(0,0,I),(1,I,0))

def complex_flow(p,t):
    z=tuple(pair(x) for x in p)
    az=complex_matrix(A,z); aaz=complex_matrix(A,az)
    return tuple(ca(ca(x,cs(y,t)),cs(w,t*t/2)) for x,y,w in zip(z,az,aaz))


def primaries(amplitude,aperture=Q(1)):
    """The existing coherent receiver law; no post-hoc hue/brightness normalization."""
    assert aperture>0
    a,b=amplitude
    p=(a*a,b*b,(a+b)*(a+b))
    d=aperture+sum(p)
    out=tuple(v/d for v in p)
    assert sum(out)+aperture/d==1
    return out


def log_interval(x,bits=18):
    assert x>0
    k=0
    while x<1: x*=2; k-=1
    while x>2: x/=2; k+=1
    def series(y,tolerance):
        t=(y-1)/(y+1); power=t; total=Q(0); n=0
        while True:
            total+=2*power/(2*n+1); n+=1; power*=t*t
            tail=2*abs(power)/((2*n+1)*(1-t*t))
            if tail<=tolerance: return total,tail
    eps=Q(1,2**bits*(1+abs(k)))
    value,error=series(x,eps)
    if k:
        l2,e2=series(Q(2),eps); value+=k*l2; error+=abs(k)*e2
    return value,error


@dataclass(frozen=True)
class Receiver:
    origin: tuple=(Q(0),Q(0),Q(0))
    right: tuple=(Q(3,5),Q(-4,5),Q(0))
    up: tuple=(Q(12,25),Q(9,25),Q(4,5))
    view: tuple=(Q(-16,25),Q(-12,25),Q(3,5))
    phase: tuple=(Q(1),Q(0))
    distance: Q=Q(12)
    focal: Q=Q(8)
    perspective: bool=False
    near: Q=Q(1,16)
    aperture: Q=Q(1)
    reference: tuple=(Q(1,3),Q(1,3),Q(1,3))
    analyzer: tuple=((Q(1),Q(0)),(Q(1),Q(0)),(Q(1),Q(0)))

    def __post_init__(self):
        for axis in (self.origin,self.right,self.up,self.view):
            if len(axis)!=3: raise ValueError('receiver covector must have three components')
            tuple(map(exact,axis))
        if dot(cross(self.right,self.up),self.view)==0: raise ValueError('receiver frame is singular')
        for x in (*self.phase,self.distance,self.focal,self.near,self.aperture,*self.reference): exact(x)
        if self.near<=0 or self.aperture<=0 or self.focal<=0: raise ValueError('declare positive receiver scales')
        if dot(self.phase,self.phase)!=1: raise ValueError('phase is a unit pair; put detector gain in the analyzer')

    def real_face(self,z):
        a,b=self.phase
        return tuple(a*x+b*y for x,y in z)

    def project(self,p):
        p=sub(p,self.origin)
        depth=self.distance-dot(self.view,p)
        if depth<=self.near: return None
        x,y=dot(self.right,p),dot(self.up,p)
        # Larger third coordinate is nearer. Reciprocal depth is affine in
        # projected barycentric coordinates for perspective-correct visibility.
        return (x*self.focal/depth,y*self.focal/depth,1/depth) if self.perspective else (x,y,-depth)

    def amplitude(self,z):
        if len(z)!=len(self.analyzer): raise ValueError("current and analyzer covector dimensions differ")
        weighted=[cm(pair(a),v) for a,v in zip(self.analyzer,z)]
        amplitude=tuple(sum(v[k] for v in weighted) for k in range(2))
        a,b=self.phase
        return (a*amplitude[0]+b*amplitude[1],a*amplitude[1]-b*amplitude[0])


def halfplane_interval(lo,hi,a,b):
    """Intersect [lo,hi] with a+b*t >= 0, exactly."""
    if b==0: return (lo,hi) if a>=0 else None
    root=-a/b
    if b>0: lo=max(lo,root)
    else: hi=min(hi,root)
    return (lo,hi) if lo<=hi else None


def cover_interval(p,q,triangle):
    area=wedge(sub(triangle[1],triangle[0]),sub(triangle[2],triangle[0]))
    if area==0: return None
    hand=1 if area>0 else -1
    lo,hi=Q(0),Q(1)
    for a,b in zip(triangle,triangle[1:]+triangle[:1]):
        edge=sub(b,a)
        at=hand*wedge(edge,sub(p,a)); change=hand*wedge(edge,sub(q,p))
        clipped=halfplane_interval(lo,hi,at,change)
        if clipped is None: return None
        lo,hi=clipped
    return lo,hi


def plane_depth(p,triangle):
    a,b,c=triangle
    den=wedge(sub(b,a),sub(c,a))
    u=wedge(sub(p,a),sub(c,a))/den
    v=wedge(sub(b,a),sub(p,a))/den
    return a[2]+u*(b[2]-a[2])+v*(c[2]-a[2])


def remove_intervals(intervals):
    merged=[]
    for lo,hi in sorted(intervals):
        if lo>=hi: continue
        if merged and lo<=merged[-1][1]: merged[-1]=(merged[-1][0],max(hi,merged[-1][1]))
        else: merged.append((lo,hi))
    result=[]; at=Q(0)
    for lo,hi in merged:
        if lo>at: result.append((at,lo))
        at=max(at,hi)
    if at<1: result.append((at,Q(1)))
    return result


class Visibility:
    def __init__(self,triangles,cell=Q(1,2)):
        self.triangles=triangles; self.cell=cell; self.buckets=defaultdict(set)
        for i,t in enumerate(triangles):
            if wedge(sub(t[1],t[0]),sub(t[2],t[0]))==0: continue
            for address in self.addresses(t): self.buckets[address].add(i)
    def addresses(self,points):
        xs=[p[0] for p in points]; ys=[p[1] for p in points]
        for i in range(min(xs)//self.cell,max(xs)//self.cell+1):
            for j in range(min(ys)//self.cell,max(ys)//self.cell+1): yield i,j
    def intervals(self,p,q,own):
        candidates=set().union(*(self.buckets[k] for k in self.addresses((p,q))))
        hidden=[]
        for f in candidates-own:
            t=self.triangles[f]
            span=cover_interval(p,q,t)
            if span is None: continue
            # A coplanar receiver tie does not arbitrarily select one source.
            a=plane_depth(p,t)-p[2]; b=plane_depth(q,t)-q[2]-a
            if a==b==0: continue
            clipped=halfplane_interval(*span,a,b)
            if clipped: hidden.append(clipped)
        return remove_intervals(hidden)


def level_segment(points,values,level):
    hits=[]
    for a,b,va,vb in zip(points,points[1:]+points[:1],values,values[1:]+values[:1]):
        if va==level: hits.append(a)
        if (va<level<vb) or (vb<level<va): hits.append(mix(a,b,(level-va)/(vb-va)))
    unique=list(dict.fromkeys(hits))
    if len(unique)==2: return tuple(unique)
    return None


def compile_scene(vertices,faces,receiver=Receiver(),tau=Q(0),step=Q(1,8),
                  style='phase',potential='current',source=None,contours=True,bounds=None,currents=None):
    if style not in ('phase','mono','stipple'): raise ValueError('unsupported engraving style')
    if potential not in ('current','entropy'): raise ValueError('supply a declared receiver potential')
    if currents is None: raise ValueError('supply the actual complex current at every source vertex')
    if len(currents)!=len(vertices): raise ValueError('source/current incidence disagreement')
    if any(len(p)!=3 for p in vertices): raise ValueError('supply the declared C^3 geometric projection')
    if any(len(f)!=3 or len(set(f))!=3 or any(v<0 or v>=len(vertices) for v in f) for f in faces): raise ValueError('invalid triangle incidence')
    z=[tuple(pair(v) for v in p) for p in vertices]
    currents=[tuple(pair(v) for v in p) for p in currents]
    assert len(receiver.reference)==3 and sum(receiver.reference)==1 and all(x>0 for x in receiver.reference)
    real=[receiver.real_face(p) for p in z]
    projected=[receiver.project(p) for p in real]
    # Near-plane intersections need a source clip rather than a invented point.
    # The present mesh API retains any unsupported straddling triangle explicitly.
    rejected=[i for i,f in enumerate(faces) if any(projected[v] is None for v in f)]
    active=[(i,f) for i,f in enumerate(faces) if i not in set(rejected)]
    triangles=[tuple(projected[v] for v in f) for _,f in active]
    visible=Visibility(triangles)
    amps=[receiver.amplitude(tuple(pair(v) for v in p)) for p in currents]
    potentials=[]; errors=[]
    for amp in amps:
        if potential=='entropy':
            a,b=amp; p=(a*a,b*b,(a+b)*(a+b)); den=receiver.aperture+sum(p)
            probabilities=tuple((receiver.aperture/3+x)/den for x in p)
            # Reference p=(1/3,1/3,1/3). Each family is a distributed
            # cross-entropy contribution -p_i log q_i at packet stations.
            logs=[log_interval(q) for q in probabilities]
            potentials.append(tuple(-x*receiver.reference[i] for i,(x,_) in enumerate(logs[:2])))
            errors.extend(e*receiver.reference[i] for i,(_,e) in enumerate(logs))
        else: potentials.append(amp)
    marks=[]; exact_marks=[]; lost=0; degenerate=[]
    def emit(p,q,amp_a,amp_b,width,kind,owners,feature=None):
        nonlocal lost
        intervals=visible.intervals(p,q,set(owners))
        if intervals!=[(Q(0),Q(1))]: lost+=1
        for lo,hi in intervals:
            if bounds is not None:
                change=sub(q,p)
                for axis,sign,edge in ((0,1,bounds[0]),(1,1,bounds[1]),(0,-1,bounds[2]),(1,-1,bounds[3])):
                    result=halfplane_interval(lo,hi,sign*(p[axis]-edge),sign*change[axis])
                    if result is None: lo=hi=Q(0);break
                    lo,hi=result
            if lo==hi: continue
            first,last=mix(p,q,lo),mix(p,q,hi)
            station=(lo+hi)/2
            if receiver.perspective:
                station=station*q[2]/((1-station)*p[2]+station*q[2])
            color=primaries(mix(amp_a,amp_b,station),receiver.aperture)
            exact_marks.append((first,last,color,Q(width),kind,tuple(owners),lo,hi,feature,station))
    edges=defaultdict(list)
    for i,(_,face) in enumerate(active):
        world=tuple(real[v] for v in face); screen=triangles[i]
        n=cross(sub(world[1],world[0]),sub(world[2],world[0]))
        nn=dot(n,n)
        if nn==0:
            degenerate.append(active[i][0]);continue
        grazing=1-dot(n,receiver.view)**2/(nn*dot(receiver.view,receiver.view))
        width=Q(1,3)+grazing if style in ('mono','stipple') else Q(1)
        for family in range(2):
            values=tuple(potentials[v][family] for v in face)
            # Monochrome second family is an exact foreshortening receiver.
            if style=='stipple' and family==1: continue
            if style=='mono' and family==1 and grazing<Q(1,2): continue
            for k in range(min(values)//step,max(values)//step+1):
                attributed=tuple(real[v]+amps[v]+potentials[v] for v in face)
                segment=level_segment(attributed,values,k*step)
                if segment is None: continue
                p,q=(receiver.project(v[:3]) for v in segment)
                feature=dict(family=family,level=ratio(k*step))
                if style=='stipple':
                    va,vb=segment[0][6],segment[1][6]
                    if va==vb: continue
                    for m in range(min(va,vb)//step,max(va,vb)//step+1):
                        amount=(m*step-va)/(vb-va)
                        if not 0<=amount<=1: continue
                        station=mix(segment[0],segment[1],amount)
                        projected_station=receiver.project(station[:3])
                        emit(projected_station,projected_station,station[3:5],station[3:5],width,'stipple',(i,),dict(feature,secondary_level=ratio(m*step)))
                else:
                    emit(p,q,segment[0][3:5],segment[1][3:5],width,'hatch',(i,),feature)
        for a,b in zip(face,face[1:]+face[:1]):
            edge=tuple(sorted((a,b))); sign=1 if (a,b)==edge else -1
            edges[edge].append((i,sign,n))
    if contours:
        for (a,b),incident in edges.items():
            show=len(incident)==1
            if len(incident)==2:
                (_,sf,nf),(_,sg,ng)=incident
                t=-sf*sg
                silhouette=dot(nf,receiver.view)*dot(ng,receiver.view)*t<=0
                crease=dot(nf,ng)**2*4<3*dot(nf,nf)*dot(ng,ng)
                show=silhouette or crease
            if show:
                emit(projected[a],projected[b],amps[a],amps[b],Q(5,4),'contour',tuple(x[0] for x in incident),dict(edge=(a,b)))
    # Deterministic final decimal view; compare its exact binary values with the
    # rational source. No display float participates in visibility or color laws.
    view_error=Q(0)
    def number(x):
        nonlocal view_error
        v=float(x); view_error=max(view_error,abs(Q(v)-x)); return v
    for p,q,rgb,width,kind,owners,lo,hi,feature,station in exact_marks:
        points=[[number(x) for x in p[:2]]] if kind=='stipple' else [[number(x) for x in p[:2]],[number(x) for x in q[:2]]]
        marks.append(dict(points=points,
                          rgb=[number(x) for x in rgb],width=number(width),kind=kind,
                          faces=[active[i][0] for i in owners],feature=feature,
                          visible_span=[ratio(lo),ratio(hi)],
                          source_station_parameter=ratio(station)))
    ps=[p for p in projected if p is not None]
    xs=[p[0] for p in ps]; ys=[p[1] for p in ps]
    margin=Q(1,4)
    bounds=tuple(map(Q,bounds)) if bounds is not None else (min(xs)-margin,min(ys)-margin,max(xs)+margin,max(ys)+margin)
    wire=ratio
    return dict(schema='org.holonics.receiver-engraving.v1',bounds=[number(x) for x in bounds],marks=marks,
                source_packet=dict(vertices=[[[wire(a),wire(b)] for a,b in p] for p in z],
                                   currents=[[[wire(a),wire(b)] for a,b in p] for p in currents],triangles=faces),
                meta=dict(source=source,style=style,vertices=len(vertices),faces=len(faces),marks=len(marks),
                          projection='pinhole' if receiver.perspective else 'orthographic',
                          phase=[wire(x) for x in receiver.phase],tau=wire(tau),
                          receiver=dict(origin=[wire(Q(x)) for x in receiver.origin],right=[wire(Q(x)) for x in receiver.right],up=[wire(Q(x)) for x in receiver.up],
                                        view=[wire(Q(x)) for x in receiver.view],distance=wire(receiver.distance),
                                        focal=wire(receiver.focal),near=wire(receiver.near),
                                        analyzer=[[wire(a),wire(b)] for a,b in map(pair,receiver.analyzer)]),
                          aperture=wire(receiver.aperture),hatch_step=wire(step),potential=potential,
                          entropy_reference=[wire(x) for x in receiver.reference],
                          clipped_marks=lost,unresolved_near_faces=rejected,degenerate_faces=degenerate,
                          near_face_details=[dict(face=i,depth_interval=[wire(min(receiver.distance-dot(receiver.view,sub(real[v],receiver.origin)) for v in faces[i])),wire(max(receiver.distance-dot(receiver.view,sub(real[v],receiver.origin)) for v in faces[i]))],reason='outside-near' if all(receiver.distance-dot(receiver.view,sub(real[v],receiver.origin))<=receiver.near for v in faces[i]) else 'straddles-near') for i in rejected],
                          rank_deficient_projection_faces=[active[i][0] for i,t in enumerate(triangles) if wedge(sub(t[1],t[0]),sub(t[2],t[0]))==0],
                          log_station_radius=wire(max(errors,default=Q(0))),
                          decimal_coordinate_error=wire(view_error),
                          visibility='exact rational affine/reciprocal-depth clipping',
                          color='premultiplied primaries P/(aperture+sum P); opaque marks on black'))
