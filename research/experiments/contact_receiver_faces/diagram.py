"""Exact rational geodesic and face diagrams; decimal SVG text is a pixel codec only."""
from fractions import Fraction as Q
from pathlib import Path
import json,html
from math import isqrt
HERE=Path(__file__).parent
ROOT=HERE.parents[2]
OUT=ROOT/'research/papers/source/papers/elementary-holon-generation/figures'
data=json.loads((HERE/'receipt.json').read_text())

def dec(x,places=5):
    x=Q(x);scale=10**places;v=(abs(x.numerator)*scale*2//x.denominator+1)//2
    sign='-' if x<0 else ''
    return sign+str(v//scale)+'.'+str(v%scale).rjust(places,'0')
def screen(p):return (Q(95)+600*p[0],Q(405)-600*p[1])
def point(p):return ','.join(dec(v) for v in screen(p))
def geodesic(p,q,steps=80):
    cross=p[0]*q[1]-p[1]*q[0]
    if cross==0:return [[(1-Q(i,steps))*p[k]+Q(i,steps)*q[k] for k in range(2)] for i in range(steps+1)]
    b1=(1+sum(x*x for x in p))/2;b2=(1+sum(x*x for x in q))/2
    center=((b1*q[1]-b2*p[1])/cross,(p[0]*b2-q[0]*b1)/cross)
    t0=-(p[0]-center[0])/(p[1]-center[1]);t1=(q[1]-p[1])/(q[0]-p[0])
    result=[]
    for i in range(steps+1):
        t=t0+Q(i,steps)*(t1-t0);d=(Q(1),t)
        lam=-2*sum((p[k]-center[k])*d[k] for k in range(2))/sum(x*x for x in d)
        z=tuple(p[k]+lam*d[k] for k in range(2))
        assert sum(x*x for x in z)<1
        assert sum((z[k]-center[k])**2 for k in range(2))==sum(c*c for c in center)-1
        result.append(z)
    assert result[0]==tuple(p) and result[-1]==tuple(q)
    return result

def main():
    pts=[tuple(map(Q,p)) for p in data['gyroparallelogram']['poincare_vertices']]
    out=['<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1000 480"><rect width="1000" height="480" fill="white"/>']
    def text(x,y,s,size=20):out.append(f'<text x="{x}" y="{y}" font-family="serif" font-size="{size}">{html.escape(s)}</text>')
    text(25,30,'Gyroparallelogram in the contact velocity chart',21)
    for axis in range(2):
        p0=screen((Q(0),Q(0)));p1=screen((Q(3,5),Q(0)) if axis==0 else (Q(0),Q(3,5)))
        out.append(f'<path d="M{dec(p0[0])},{dec(p0[1])} L{dec(p1[0])},{dec(p1[1])}" stroke="#888" fill="none"/>')
        for tick in [Q(1,4),Q(1,2)]:
            p=screen((tick,0) if axis==0 else (0,tick));text(dec(p[0]+(0 if axis==0 else -35)),dec(p[1]+(25 if axis==0 else 0)),str(tick),15)
    paths=[]
    for a,b in [(0,1),(1,3),(3,2),(2,0),(0,3),(1,2)]:
        path=geodesic(pts[a],pts[b]);paths.append(dict(endpoints=[a,b],samples=[[str(x) for x in p] for p in path]))
        color='#888' if (a,b) in [(0,3),(1,2)] else '#202020'
        out.append('<polyline points="'+' '.join(point(p) for p in path)+f'" stroke="{color}" stroke-width="2" fill="none"'+(' stroke-dasharray="5 4"' if color=='#888' else '')+'/>')
    for p,label in zip(pts,['A = 0','B = u','C = v','D = u ⊞ v']):
        x,y=screen(p);out.append(f'<circle cx="{dec(x)}" cy="{dec(y)}" r="4" fill="#222"/>');text(dec(x+8),dec(y-9),label,18)
    # Positive algebraic root retained; rational interval used only for the ink marker.
    rootlo=Q(isqrt(222*10**12),10**6);roothi=rootlo+Q(1,10**6)
    assert rootlo*rootlo<=222<roothi*roothi
    m=(Q(9)/(35+2*rootlo),Q(16)/(35+2*rootlo));x,y=screen(m)
    out.append(f'<circle cx="{dec(x)}" cy="{dec(y)}" r="4" fill="#ad6b16"/>');text(dec(x+7),dec(y-8),'M',18)
    text(540,75,'Exact local data · velocities in units of c',21)
    rows=[('u = (3/5, 0)','γu = 5/4'),('v = (0, 4/5)','γv = 5/3'),('u ⊕ v = (3/5, 16/25)','v ⊕ u = (9/25, 4/5)'),('D = (315/781, 560/781)','M = (9/35, 16/35) in Einstein coordinates'),('gyr[u,v] = (1/37) [[35, 12], [−12, 35]]','The complete tensor and receiver transform together.')]
    for k,(a,b) in enumerate(rows):text(540,118+k*62,a,18);text(540,143+k*62,b,16)
    text(25,468,'Drawn through C(v)=γv/(1+γ); every arc retains its exact conic equation and rational stations.',16)
    out.append('</svg>');(OUT/'exact-gyroparallelogram.svg').write_text(''.join(out))
    (HERE/'geodesics.json').write_text(json.dumps(dict(chart='Einstein velocity ball -> Poincare: C(v)=gamma v/(1+gamma)',vertices=[[str(x) for x in p] for p in pts],arcs=paths,midpoint='(9,16)/(35+2 sqrt(222)); positive root',pixel_codec='rational coordinate to integer decimal pixel window; not a state transition'),separators=(',',':'))+'\n')
if __name__=='__main__':main()
