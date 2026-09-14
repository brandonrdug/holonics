"""Exact collision-face subcomplexes on the two toroidal support boundaries.
All membership/orientation/containment decisions use rational arithmetic.
The output retains oriented area vectors; no float area/normal controls admission.
"""
from fractions import Fraction as Q
from pathlib import Path
import json
HERE=Path(__file__).parent
CENTERS={2:(Q(0),Q(0),Q(0)),5:(Q(0),Q(3),Q(0))};AXES={2:2,5:0}
R=Q(2);r=Q(1)
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def cross(a,b):return (a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
def circle(n):
    result=[]
    for quadrant in range(4):
        for j in range(n):
            x=Q(n*n-j*j,n*n+j*j);y=Q(2*n*j,n*n+j*j)
            result.append([(x,y),(-y,x),(-x,-y),(y,-x)][quadrant])
    assert all(x*x+y*y==1 for x,y in result)
    return result

def polynomial(p,i,minor=r):
    q=sub(p,CENTERS[i]);s=dot(q,q)
    return (s+R*R-minor*minor)**2-4*R*R*(s-q[AXES[i]]**2)

def gradient(p,i):
    q=sub(p,CENTERS[i]);s=dot(q,q)
    return tuple(4*q[k]*(s+R*R-r*r)-(0 if k==AXES[i] else 8*R*R*q[k]) for k in range(3))

def mesh(i):
    lon,mer=circle(12),circle(6);n=len(lon);m=len(mer);vertices=[]
    for cp,sp in mer:
        for ct,st in lon:
            v=list(CENTERS[i]);axis=AXES[i];v[axis]+=r*sp
            v[(axis+1)%3]+=(R+r*cp)*ct;v[(axis+2)%3]+=(R+r*cp)*st
            vertices.append(tuple(v))
    assert all(polynomial(p,i)==0 for p in vertices)
    faces=[]
    for j in range(m):
        for k in range(n):
            a=j*n+k;b=j*n+(k+1)%n;c=((j+1)%m)*n+(k+1)%n;d=((j+1)%m)*n+k
            faces.extend([(a,b,c),(a,c,d)])
    return vertices,faces

def main():
    out=[]
    for i,j in [(2,5),(5,2)]:
        vertices,faces=mesh(i);chosen=[]
        for index,face in enumerate(faces):
            pts=[vertices[k] for k in face];center=tuple(sum(p[k] for p in pts)/3 for k in range(3))
            radius=max(sum(abs(x-y) for x,y in zip(p,center)) for p in pts)
            available=r-radius
            if available<=0 or polynomial(center,j,available)>=0:continue
            area=tuple(x/2 for x in cross(sub(pts[1],pts[0]),sub(pts[2],pts[0])))
            assert dot(area,area)>0 and dot(area,gradient(center,i))>0
            chosen.append(dict(face=index,indices=face,center=center,area_vector=area,containment_radius=radius))
        out.append(dict(owner=i,interacting_with=j,vertices=vertices,faces=faces,collision_faces=chosen))
        print('surface',i,'inside field',j,':',len(chosen),'certified facet charts')
    assert all(x['collision_faces'] for x in out)
    def wire(v):
        if isinstance(v,Q):return str(v)
        if isinstance(v,dict):return {k:wire(x) for k,x in v.items()}
        if isinstance(v,(tuple,list)):return [wire(x) for x in v]
        return v
    receipt=dict(schema='holonics.exact-torus-collision-faces.v1',units=dict(position='L0',area_vector='L0^2',worldtube_face='c dt times oriented area'),surfaces=out,
        containment='distance to core circle is 1-Lipschitz; every point in each triangle is within the recorded L1 radius of its center; center belongs to the other torus at minor radius 1-radius',
        scope='conservative finite facet charts; full curved torus source retained by rational conic parametrization; under common material advection carry the entire facet and its area bivector')
    (HERE/'surface_faces.json').write_text(json.dumps(wire(receipt),separators=(',',':'))+'\n')
if __name__=='__main__':main()
