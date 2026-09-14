"""Coupled exact material source; numerical volume rendering is an exterior receiver only.

The state is (complex mode currents, thermal modes, a word of nonlinear incompressible maps).
No random texture or independently animated geometry is used. The mode contact/heat law is
PhaseContactPassage; the kernels and unit phase plates reuse the woven-field construction.
"""
from fractions import Fraction as Q
from pathlib import Path
import json, math, argparse
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).parent
CENTERS=[(-6,0,0),(-3,0,0),(0,0,0),(3,0,0),(6,0,0),(0,3,0)]
AXES=[2,1,2,1,2,0]
OPTICAL={'display_gain':'8','display_gamma':'11/5','opacity_scale':'3/25','thermal_activity':'3/25','red_heat':'1/10','green_heat':'1/25','blue_heat':'3/50','band_aperture':'9/50','distance':'24','view_x':['-11','11'],'view_y':['-33/4','33/4'],'depth':['-11','11']}
EDGES=[(0,1),(1,2),(1,5),(2,3),(2,5),(3,4),(3,5)]
SITES=[(-Q(9,2),0,0),(-Q(3,2),0,0),(-Q(1,2),Q(1,2),0),(Q(3,2),0,0),(0,Q(3,2),0),(Q(9,2),0,0),(Q(1,2),Q(1,2),0)]
def cm(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def add(a,b):return (a[0]+b[0],a[1]+b[1])
def sub(a,b):return (a[0]-b[0],a[1]-b[1])
def scale(a,s):return (s*a[0],s*a[1])
def conj(a):return (a[0],-a[1])
def power(a):return a[0]**2+a[1]**2

def phase(i,p):
    a=Q(p[(AXES[i]+1)%3])-CENTERS[i][(AXES[i]+1)%3]
    return ((4-a*a)/(4+a*a),4*a/(4+a*a))
def poly(i,p):
    v=[Q(p[k])-CENTERS[i][k] for k in range(3)];s=sum(x*x for x in v)
    return (s+3)**2-16*(s-v[AXES[i]]**2)
def twist(p,axis,s):
    v=list(p);a=(axis+1)%3;b=(axis+2)%3;q=s*v[axis]
    c=(1-q*q)/(1+q*q);sn=2*q/(1+q*q)
    v[a],v[b]=c*v[a]-sn*v[b],sn*v[a]+c*v[b]
    return tuple(v)

def source(last=48):
    connections=[]
    for (i,j),p in zip(EDGES,SITES):
        assert poly(i,p)<0 and poly(j,p)<0
        u=cm(phase(i,p),conj(phase(j,p)));assert power(u)==1;connections.append(u)
    groups=[]
    for k,e in enumerate(EDGES):
        for g in groups:
            if not set(e)&{v for h in g for v in EDGES[h]}:g.append(k);break
        else:groups.append([k])
    psi=[(Q(2),Q(0)),(Q(0),Q(1)),(Q(1),Q(0)),(Q(0),-Q(1)),(Q(1),Q(0)),(Q(1),Q(1))]
    heat=[Q(0)]*6;initial=sum(map(power,psi));alpha=Q(1,8);turn=(Q(255,257),Q(32,257))
    assert power(turn)==1
    states=[];word=[]
    for n in range(last+1):
        states.append(dict(index=n,clock=str(Q(n,16)),psi=[[str(a),str(b)] for a,b in psi],heat=list(map(str,heat)),
            wave_energy=str(sum(map(power,psi))),heat_energy=str(sum(heat)),word=[dict(axis=a,parameter=str(s)) for a,s in word]))
        if n==last:break
        psi=[cm(turn,z) for z in psi]
        for e in groups[n%len(groups)]:
            i,j=EDGES[e];u=connections[e];x,y=psi[i],psi[j];d=sub(y,cm(u,x))
            xx=add(x,scale(cm(conj(u),d),alpha));yy=sub(y,scale(d,alpha));h=2*alpha*(1-alpha)*power(d)
            assert power(xx)+power(yy)+h==power(x)+power(y)
            psi[i],psi[j]=xx,yy;heat[i]+=h/2;heat[j]+=h/2
            # Thermal transport acts on the same admitted pair, in its material chart.
            transfer=Q(1,16)*(heat[j]-heat[i]);heat[i]+=transfer;heat[j]-=transfer
        assert sum(map(power,psi))+sum(heat)==initial and all(h>=0 for h in heat)
        i=n%6;j=(n+1)%6;signed=psi[i][1]-psi[j][0]
        s=Q(1,36)*(1+signed/(1+signed*signed))*(1 if n%3!=1 else -1)
        word.append((n%3,s))
        p=(Q(1,2),Q(3,4),-Q(2,3))
        assert twist(twist(p,n%3,s),n%3,-s)==p
    # A concrete exact separator: ordered nonlinear twists are not a rigid reorientation.
    a=(Q(2),Q(1),Q(0));b=(Q(2),Q(2),Q(1));s=Q(1,8)
    aa=twist(twist(a,0,s),2,-s);bb=twist(twist(b,0,s),2,-s)
    assert sum((aa[i]-bb[i])**2 for i in range(3))!=sum((a[i]-b[i])**2 for i in range(3))
    return dict(schema='holonics.continuing-coupled-field.v1',centers=CENTERS,axes=AXES,major_radius='2',minor_radius='1',
        contact_edges=EDGES,contact_sites=[[str(x) for x in p] for p in SITES],connections=[[str(x) for x in u] for u in connections],matchings=groups,
        contact_alpha=str(alpha),phase_turn=list(map(str,turn)),thermal_exchange='1/16',initial_energy=str(initial),states=states,optical_receiver=OPTICAL,
        source_law='PhaseContactPassage on witnessed contacts; exact heat return and conservative thermal exchange; current-dependent noncommuting Cayley twists transport the entire common material chart.',
        twist='q=s*x_axis; C=(1-q^2)/(1+q^2), S=2q/(1+q^2); transverse pair rotates by [[C,-S],[S,C]]',
        rate='s_n=(sign_n/36)*(1+d_n/(1+d_n^2)); d_n=Im(psi_i)-Re(psi_j), after contact; axes cycle x,y,z',
        reconstruction='A_n(X)=sum psi_i(n) K_i(Phi_n^-1 X) g_i(Phi_n^-1 X); thermal field=sum H_i(n) K_i(Phi_n^-1 X)',
        geometry='Every torus/support/phase plate is transported by the same word Phi_n. det DPhi_n=1; inverse reverses word and negates parameters. The exact word is retained, not expanded into giant rational coordinates.',
        receiver='Fixed perspective frame R; emission-absorption integration through the reconstructed volume. Pixel quadrature is numerical display, never semantic/native state.',
        scope='Supplied coupled phase/thermal/material model; finite-resolution filamentation, not a theorem of fractal dimension or a solution of unforced Navier-Stokes.')

def numeric_twist(p,axis,s):
    a=(axis+1)%3;b=(axis+2)%3;q=s*p[...,axis];den=1+q*q;c=(1-q*q)/den;sn=2*q/den
    x=p[...,a].copy();y=p[...,b].copy();p[...,a]=c*x-sn*y;p[...,b]=sn*x+c*y
    return p

def reconstruct(points,state):
    import numpy as np
    p=points.copy()
    for item in reversed(state['word']):numeric_twist(p,item['axis'],-float(Q(item['parameter'])))
    amp=np.zeros(p.shape[:-1],complex);thermal=np.zeros(p.shape[:-1]);support=np.zeros(p.shape[:-1])
    for i,(center,axis) in enumerate(zip(CENTERS,AXES)):
        v=p-center;s=np.sum(v*v,axis=-1);f=(s+3)**2-16*(s-v[...,axis]**2);k=np.maximum(0,-f)/16
        a=v[...,(axis+1)%3];phase=(4-a*a+4j*a)/(4+a*a)
        psi=complex(*[float(Q(x)) for x in state['psi'][i]])
        amp+=psi*k*phase;thermal+=float(Q(state['heat'][i]))*k;support+=k
    return amp,thermal,support

def render(job):
    import numpy as np
    from PIL import Image
    state,out,size,rays=job;w=size;h=round(size*3/4)
    u=np.linspace(-11,11,w);v=np.linspace(-8.25,8.25,h)[::-1]
    xx,yy=np.meshgrid(u,v);zs=np.linspace(11,-11,rays)
    # Fixed rational orientation of the receiver, not an animated camera.
    cy,sy=15/17,8/17;cx,sx=4/5,3/5
    rot=np.array([[cy,sy*sx,sy*cx],[0,cx,-sx],[-sy,cy*sx,cy*cx]])
    samples=np.stack([xx[...,None]*(24-zs)/24,yy[...,None]*(24-zs)/24,np.broadcast_to(zs,(h,w,len(zs)))],axis=-1)
    samples=samples@rot
    amp,thermal,support=reconstruct(samples,state)
    intensity=amp.real**2+amp.imag**2
    density=intensity+float(Q(OPTICAL['thermal_activity']))*thermal
    # The same fixed receiver law/exposure is used for every frame.
    optical_depth=float(Q(OPTICAL['opacity_scale']))*density*(22/(len(zs)-1))*np.sqrt(1+(xx[...,None]/24)**2+(yy[...,None]/24)**2)
    alpha=1-np.exp(-optical_depth)
    cumulative=np.cumsum(optical_depth,axis=-1)-optical_depth
    transmission=np.exp(-cumulative)
    a,b=amp.real,amp.imag
    bands=np.stack([a*a+float(Q(OPTICAL['red_heat']))*thermal,b*b+float(Q(OPTICAL['green_heat']))*thermal,(a+b)**2+float(Q(OPTICAL['blue_heat']))*thermal],axis=-1)
    bands/=float(Q(OPTICAL['band_aperture']))+bands.sum(axis=-1,keepdims=True)
    # Scalar display transfer brightens the declared phase/thermal bands, never the state.
    colors=np.sqrt(np.maximum(0,bands))
    rgb=np.sum(transmission[...,None]*alpha[...,None]*colors,axis=-2)
    opacity=1-np.exp(-optical_depth.sum(axis=-1))
    straight=rgb/np.maximum(opacity[...,None],1e-12)
    rgba=np.concatenate([np.clip(straight,0,1),np.clip(opacity[...,None],0,1)],axis=-1)
    image=Image.fromarray(np.uint8(np.round(rgba*255)),'RGBA')
    path=Path(out)/f'field-{state["index"]:03d}.png';image.save(path,optimize=True)
    # Actual deformed circulation carriers, in the SAME receiver projection.
    curves=[]
    for i,(center,axis) in enumerate(zip(CENTERS,AXES)):
        t=np.linspace(0,2*np.pi,161);theta=2*t;phi=3*t
        p=np.tile(np.array(center,float),(len(t),1));p[:,axis]+=np.sin(phi)/3
        p[:,(axis+1)%3]+=(2+np.cos(phi)/3)*np.cos(theta);p[:,(axis+2)%3]+=(2+np.cos(phi)/3)*np.sin(theta)
        for item in state['word']:numeric_twist(p,item['axis'],float(Q(item['parameter'])))
        p=p@rot.T;px=24*p[:,0]/(24-p[:,2]);py=24*p[:,1]/(24-p[:,2]);curves.append(np.round(np.stack([px,py],axis=1)*1000).astype(int).tolist())
    print('rendered field',state['index'],flush=True)
    return dict(index=state['index'],image=path.name,curves=curves,opacity_sum=float(opacity.sum()),
        pixel_sum=[float(x) for x in rgb.sum(axis=(0,1))])

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);p.add_argument('--size',type=int,default=256);p.add_argument('--steps',type=int,default=48);p.add_argument('--stride',type=int,default=1);p.add_argument('--rays',type=int,default=160);p.add_argument('--workers',type=int,default=2);args=p.parse_args()
    args.output.mkdir(parents=True,exist_ok=True);model=source(args.steps)
    (HERE/'continuing-field.json').write_text(json.dumps(model,indent=2)+'\n')
    from concurrent.futures import ProcessPoolExecutor
    jobs=[(s,str(args.output),args.size,args.rays) for s in model['states'][::args.stride]]
    with ProcessPoolExecutor(max_workers=args.workers) as pool:frames=list(pool.map(render,jobs))
    (args.output/'frames.json').write_text(json.dumps(dict(frames=frames,size=args.size,scope=model['scope']),separators=(',',':'))+'\n')
    print('complete',len(frames),'received volume frames')
