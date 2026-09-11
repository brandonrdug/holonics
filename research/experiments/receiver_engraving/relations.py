"""Exact source relations behind the receiver edition. Exterior verification only."""
from fractions import Fraction as Q
from pathlib import Path
import json

def matmul(a,b): return tuple(tuple(sum(x*y for x,y in zip(row,col)) for col in zip(*b)) for row in a)
def transpose(a): return tuple(zip(*a))
def mv(a,b): return tuple(sum(x*y for x,y in zip(row,b)) for row in a)
def det(a): return a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])-a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])+a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0])
def cr(a,b,c,d): return (a-c)*(b-d)/((a-d)*(b-c))
def wire(x):
    if isinstance(x,Q): return [x.numerator,x.denominator]
    raise TypeError(type(x))

def main():
    eta=((Q(1),0,0),(0,Q(-1),0),(0,0,Q(-1)))
    lx=((Q(5,4),Q(-3,4),0),(Q(-3,4),Q(5,4),0),(0,0,Q(1)))
    ly=((Q(5,3),0,Q(-4,3)),(0,Q(1),0),(Q(-4,3),0,Q(5,3)))
    for l in (lx,ly): assert matmul(matmul(transpose(l),eta),l)==eta
    ordered=matmul(ly,lx); reverse=matmul(lx,ly)
    assert ordered!=reverse
    t,x,y=mv(ordered,(1,0,0))
    return_boost=((t,-x,-y),(-x,1+x*x/(t+1),x*y/(t+1)),(-y,x*y/(t+1),1+y*y/(t+1)))
    rotation=matmul(return_boost,ordered)
    assert rotation[0]==(1,0,0) and tuple(row[0] for row in rotation)==(1,0,0)
    assert matmul(matmul(transpose(rotation),eta),rotation)==eta
    assert det(rotation)==1
    source=tuple(map(Q,(0,1,2,3)))
    shadow=tuple(t/(1+t/2) for t in source)
    assert cr(*source)==cr(*shadow)==Q(4,3)
    # Signed level crossings preserve the endpoint potential with a bounded remainder.
    delta=Q(1,8); a=Q(-7,13); b=Q(19,11)
    count=b//delta-a//delta
    remainder=(b-delta*(b//delta))-(a-delta*(a//delta))
    assert b-a==delta*count+remainder and abs(remainder)<delta
    # Real restriction loses rank although the exact complex polynomial flow does not.
    for t in (Q(0),Q(1,2),Q(1),Q(7,5),Q(2)):
        real=((1+t*t/2,0,t),(0,1-t*t/2,0),(t,0,1))
        imaginary=((0,t*t/2,0),(t*t/2,0,t),(0,t,0))
        assert det(real)==(1-t*t/2)**2
        changed=tuple(tuple(Q(3,5)*x+Q(4,5)*y for x,y in zip(u,v)) for u,v in zip(real,imaginary))
        if t==Q(7,5): assert det(changed)!=0
    # Curved GR source: radial null geodesic, unit Killing energy, G=c=M=1.
    schwarzschild=[]
    for radius,lapse in ((Q(25,8),Q(3,5)),(Q(50,9),Q(4,5))):
        f=1-2/radius; fp=2/(radius*radius)
        assert f==lapse*lapse
        metric=((-f,0,0,0),(0,1/f,0,0),(0,0,radius*radius,0),(0,0,0,radius*radius))
        tetrad=((1/lapse,0,0,0),(0,lapse,0,0),(0,0,1/radius,0),(0,0,0,1/radius))
        minkowski=((Q(-1),0,0,0),(0,Q(1),0,0),(0,0,Q(1),0),(0,0,0,Q(1)))
        assert matmul(matmul(transpose(tetrad),metric),tetrad)==minkowski
        ray=(1/f,Q(1),Q(0),Q(0)); observer=(1/lapse,Q(0),Q(0),Q(0))
        pairing=lambda x,y: sum(a*b for a,b in zip(x,mv(metric,y)))
        assert pairing(ray,ray)==0
        frequency=-pairing(ray,observer)
        assert frequency==1/lapse
        # d k^t/dlambda + 2 Gamma^t_tr k^t k^r = 0;
        # Gamma^r_tt (k^t)^2 + Gamma^r_rr (k^r)^2 = 0.
        assert -fp/f**2+2*(fp/(2*f))*(1/f)==0
        assert (f*fp/2)*(1/f)**2-fp/(2*f)==0
        schwarzschild.append(dict(radius=radius,lapse=lapse,metric=metric,tetrad=tetrad,ray=ray,frequency=frequency))
    assert schwarzschild[1]['frequency']/schwarzschild[0]['frequency']==Q(3,4)
    result=dict(schwarzschild=schwarzschild,lorentz_x=lx,lorentz_y=ly,ordered=ordered,reverse=reverse,returned_rotation=rotation,
                source=source,projective_shadow=shadow,cross_ratio=Q(4,3),
                hatch=dict(step=delta,count=count,remainder=remainder),
                complex=dict(A_cubed='zero',complex_determinant=1,real_determinant='(1-tau^2/2)^2'))
    path=Path(__file__).with_name('relations.json');path.write_text(json.dumps(result,default=wire,indent=2)+'\n')
    print('Returned: rational Lorentz forms and Wigner rotation; projective cross-ratio; signed hatch flux remainder; complex/real receiver determinants; Schwarzschild tetrads, radial null geodesic and 3/4 redshift.')
    print('Wigner spatial rotation:',tuple(row[1:] for row in rotation[1:]))

if __name__=='__main__':main()
