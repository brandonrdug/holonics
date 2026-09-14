"""Exact source geometry -> display-only architecture projections.
The source is the existing six-domain field, deformed by one invertible polynomial map.
A diagram is an operator-placement schematic, not a simulated/trained HNN result.
"""
from pathlib import Path
from fractions import Fraction as Q
import json
import argparse
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).parent
parser=argparse.ArgumentParser()
parser.add_argument('output',type=Path,help='Task-owned path for the inline diagram fragment')
OUTPUT=parser.parse_args().output
CENTERS=[(-6,0,0),(-3,0,0),(0,0,0),(3,0,0),(6,0,0),(0,3,0)]
AXES=[2,1,2,1,2,0]
def circle(n):
    pts=[]
    for quadrant in range(4):
        for j in range(n):
            x=Q(n*n-j*j,n*n+j*j); y=Q(2*n*j,n*n+j*j)
            pts.append([(x,y),(-y,x),(-x,-y),(y,-x)][quadrant])
    return pts

def mul(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def power(a,n):
    p=(Q(1),Q(0))
    for _ in range(n):p=mul(p,a)
    return p

def point(i,theta,phi,radius):
    p=list(map(Q,CENTERS[i]));axis=AXES[i]
    p[axis]+=radius*phi[1]
    p[(axis+1)%3]+=(2+radius*phi[0])*theta[0]
    p[(axis+2)%3]+=(2+radius*phi[0])*theta[1]
    return p

def bend(p):
    x,y,z=p
    return (x,y+x*x/12,z+x*y/12)

def camera(p):
    x,y,z=p
    # Rational viewing chart; every number below is a display coordinate.
    return (Q(4,5)*x+Q(3,10)*y-Q(1,5)*z,
            -Q(1,10)*x-Q(1,2)*y+Q(4,5)*z,
            Q(1,5)*x-Q(4,5)*y-Q(1,2)*z)

def project(p):
    return camera(bend(p))

def world_ink(p):
    return [round(c*10000) for c in camera(p)]

def ink(p):
    # Integer ink stations: denominators remain in source; no float affects incidence.
    return [round(c*10000) for c in project(p)]

regions=[]
for i in range(6):
    mesh=[]
    for phi in circle(2):
        mesh.append([ink(point(i,t,phi,Q(1))) for t in circle(12)+circle(12)[:1]])
    for theta in circle(4):
        mesh.append([ink(point(i,theta,p,Q(1))) for p in circle(6)+circle(6)[:1]])
    strands=[]
    for phase in [(1,0),(0,1),(-1,0),(0,-1)]:
        strands.append([ink(point(i,power(t,2),mul(power(t,3),phase),Q(1,3))) for t in circle(20)+circle(20)[:1]])
    regions.append(dict(mesh=mesh,strands=strands,center=ink(list(map(Q,CENTERS[i])))))
source=json.loads((ROOT/'research/experiments/contact_receiver_faces/surface_faces.json').read_text())
patches=[]
for surf in source['surfaces']:
    v=[[Q(x) for x in p] for p in surf['vertices']]
    for face in surf['collision_faces'][::3]:
        patches.append(dict(owner=surf['owner'],points=[ink(v[j]) for j in face['indices']]))
pts=[p for r in regions for line in r['mesh'] for p in line]
data=dict(schema='holonics.hnn-architecture-display.v1',regions=regions,patches=patches,
          bounds=[[min(p[k] for p in pts),max(p[k] for p in pts)] for k in range(3)],
          source='Existing six-domain field and certified 2/5 collision facets. One invertible det=1 polynomial material map preserves their incidence. Integer ink stations only.',
          source_map='F(x,y,z)=(x,y+x²/12,z+xy/12); F inverse (X,Y,Z)=(X,Y-X²/12,Z-X(Y-X²/12)/12)',
          role='Operator-placement schematic. Six drawn regions do not prescribe HNN extent, rank or topology; paths illustrate admitted circulation, not a measured trajectory.')
# The receiver and the beams are already in the deformed world chart. They are not bent again.
receiver=json.loads((HERE/'receiver-motion.json').read_text())
gamma=Q(receiver['gamma']);z=Q(receiver['z']);radius=Q(receiver['radius'])
base=world_ink((Q(0),Q(0),z))
def receptor(theta,phi,minor=Q(1,6)):
    r=radius+minor*phi[0]
    return world_ink((gamma*r*theta[0],r*theta[1],z+minor*phi[1]))
receiver['rim']=[[receptor(t,p) for t in circle(12)+circle(12)[:1]] for p in circle(2)]
receiver['aperture']=[world_ink((gamma*radius*t[0],radius*t[1],z)) for t in circle(20)+circle(20)[:1]]
receiver['interior']=[[world_ink((gamma*Q(k,5)*t[0],Q(k,5)*t[1],z)) for t in circle(12)+circle(12)[:1]] for k in [2,4,6]]
receiver['axes']=[base,world_ink((gamma,Q(0),z)),world_ink((Q(0),Q(1),z)),world_ink((Q(0),Q(0),z-1))]
receiver['base_center']=base
for beam in receiver['beams']:
    beam['source_display']=world_ink(tuple(Q(x) for x in beam['source']))
    beam['hit_display']=world_ink(tuple(Q(x) for x in beam['hit']))
for f in receiver['frames']:
    center=world_ink((Q(f['center_x']),Q(0),z))
    f['display_shift']=[center[k]-base[k] for k in range(3)]
allpoints=pts[:]
for f in receiver['frames']:
    for line in receiver['rim']:
        allpoints.extend([[p[k]+f['display_shift'][k] for k in range(3)] for p in line])
data['bounds']=[[min(p[k] for p in allpoints),max(p[k] for p in allpoints)] for k in range(3)]
data['receiver']=receiver
(HERE/'geometry.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
fragment=(HERE/'explorer.template.html').read_text().replace('@@GEOMETRY@@',json.dumps(data,separators=(',',':')))
OUTPUT.parent.mkdir(parents=True,exist_ok=True)
OUTPUT.write_text(fragment)
print(OUTPUT)
print('bytes',len(fragment.encode()))
