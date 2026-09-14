"""New figures from connected_holonic_field/result.json.

The source calculation is exact Rust algebra. Matplotlib is an exterior plotter;
geometry uses a declared dyadic receiver followed by the existing exact decoder.
No previously rendered Information Chemistry figure is imported.
"""
from pathlib import Path
from fractions import Fraction as Q
import json,sys,math,runpy

ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).parent
OUT=ROOT/'research/papers/source/papers/elementary-holon-generation/figures'
data=json.loads((HERE/'result.json').read_text())
OUT.mkdir(exist_ok=True)

def field(name):
    v=data[name]
    if len(v[0])==1: return [(Q(v[2*i][0]),Q(v[2*i+1][0])) for i in range(len(v)//2)]
    return [tuple(map(Q,row)) for row in v]

def geometry():
    sys.path.insert(0,str(ROOT/'research/experiments/receiver_engraving'))
    import woven_ecology as w
    grid,basis,tets,contacts=w.scene_lattice()
    export=runpy.run_path(str(ROOT/'research/papers/source/packages/holonic-receiver/export_svg.py'))['scene_svg']
    receipts={}
    initial=[tuple(map(Q,row)) for row in data['input']['input']]
    for name,psi in [('input',initial),('layer_two',field('layer_two_field')),('integrated',field('solution'))]:
        denominator=2**24
        projected=[tuple(Q(round(x*denominator),denominator) for x in z) for z in psi]
        error=max(abs(a-b) for z,y in zip(psi,projected) for a,b in zip(z,y))
        assert error<=Q(1,2*denominator)
        v,f,c,mesh=w.horizon(grid,basis,tets,projected)
        source=w.wire(dict(kind='connected-normalized-field-intensity-horizon',name=name,
            exact_psi=psi,receiver_psi=projected,coordinate_error_bound=Q(1,2*denominator),
            mesh=mesh,threshold=w.LEVEL,rings=w.RINGS,
            law='result.json: L=C[(1-g)I+g(A+B)/2 tensor I2], x*= (I-lambda L^2)^-1 (1-lambda)h',
            decoder='nodal coherent sum in the existing toroidal basis; affine nodal intensity; level 1/3',
            status='exact polyhedral level set of the declared dyadic receiver chart; no isotopy claim for the unprojected field'))
        print(name,len(v),len(f),'compiling receiver',flush=True)
        scene=w.r.compile_scene(v,f,currents=c,receiver=w.r.Receiver(distance=Q(32),aperture=Q(1,16)),
            source=source,step=Q(1,6),bounds=(-5,-5,5,5),closed_outward=True)
        assert not scene['meta']['unresolved_near_faces'] and not scene['meta']['degenerate_faces']
        (OUT/f'{name}-geometry.svg').write_text(export(scene,width_mm=Q(100),line_width_pt=Q(1,3)))
        # Keep the exact computational source in result.json; the figure metadata binds
        # the decoder and finite receiver. Full source-edge population remains in receipt.
        receipts[name]=dict(source=source,marks=len(scene['marks']))
        (HERE/'geometry.json').write_text(json.dumps(receipts,separators=(',',':'))+'\n')
        print(name,len(scene['marks']),'marks done',flush=True)

def plots():
    import numpy as np
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.patches import FancyArrowPatch, Circle
    from matplotlib.colors import LinearSegmentedColormap
    plt.rcParams.update({'font.family':'DejaVu Serif','font.size':10,'svg.fonttype':'path',
        'axes.spines.top':False,'axes.spines.right':False,'axes.labelsize':10,
        'xtick.labelsize':8,'ytick.labelsize':8,'savefig.facecolor':'white'})
    def arr(name):return np.array([[float(Q(x)) for x in r] for r in data[name]])
    def save(fig,name):
        fig.savefig(OUT/f'{name}.svg',bbox_inches='tight',pad_inches=.06)
        plt.close(fig)
    a0,a,b=map(arr,['head_a_before','head_a_after','head_b'])
    grad=arr('log_potential_gradient')
    fig,axes=plt.subplots(1,3,figsize=(11.3,3.25),layout='constrained')
    for ax,m,title in zip(axes,[a,b,grad],['Head A · after material update','Head B · overlap-squared chart','Observed error pulled to log K']):
        signed=title.startswith('Observed')
        bound=np.max(abs(m))
        im=ax.imshow(m,cmap='RdBu_r' if signed else 'Greys',vmin=-bound if signed else 0,vmax=bound)
        ax.set(title=title,xlabel='emitting channel j',ylabel='receiving channel i',xticks=[0,5,10,14],yticks=[0,5,10,14])
        fig.colorbar(im,ax=ax,shrink=.7)
    save(fig,'heads-and-gradient')

    # Actual contact-row score perturbation, with its other admitted masses fixed.
    i,j=data['input']['contact_edge']
    t=np.linspace(-5,5,250);odds=1/3
    sigmoid=1/(1+np.exp(-t));prob=a[i,j]*np.exp(t)/(1-a[i,j]+a[i,j]*np.exp(t))
    fig,axes=plt.subplots(1,2,figsize=(9,2.8),layout='constrained')
    axes[0].plot(t,sigmoid,color='black',label='sigmoid(s)')
    axes[0].plot(t,sigmoid*(1-sigmoid),color='#666666',linestyle='--',label='derivative p(1−p)')
    axes[0].scatter([math.log(odds)],[.25],c='black',s=25)
    axes[0].set(xlabel='binary potential s',ylabel='participation / sensitivity',title='Gate used in the layer: σ(log 1/3)=1/4')
    axes[0].legend(frameon=False,fontsize=8)
    axes[1].plot(t,prob,color='black',label=f'contact {j} → {i}')
    for k in np.flatnonzero(a[i]):
        if k!=j: axes[1].plot(t,a[i,k]/(1-a[i,j]+a[i,j]*np.exp(t)),color='#8a8a8a',lw=.7)
    axes[1].set(xlabel=f'log-potential change δs[{i},{j}]',ylabel='normalized row weights',title='One changed comparison redistributes its whole row')
    axes[1].legend(frameon=False,fontsize=8)
    save(fig,'sigmoid-and-participation')

    # The same receiver row, restricted to two varying log-potentials. Background
    # contours are its squared current error, arrows its analytic negative gradient.
    v=np.array([[float(Q(x)) for x in r] for r in data['input']['input']])
    target=np.array([[float(Q(x)) for x in r] for r in data['input']['observed']])
    other=next(k for k in np.flatnonzero(a[i]) if k!=j and not np.allclose(v[k],v[j]))
    X,Y=np.meshgrid(np.linspace(-3,3,61),np.linspace(-3,3,61));loss=np.zeros_like(X);gx=loss.copy();gy=loss.copy()
    for row in range(len(X)):
        for col in range(len(X)):
            p=a0[i].copy();p[j]*=math.exp(X[row,col]);p[other]*=math.exp(Y[row,col]);p/=p.sum()
            y=p@v;d=y-target[i];loss[row,col]=.5*np.dot(d,d)
            gx[row,col]=p[j]*np.dot(d,v[j]-y);gy[row,col]=p[other]*np.dot(d,v[other]-y)
    fig,ax=plt.subplots(figsize=(5.1,3.3),layout='constrained')
    cs=ax.contour(X,Y,loss,levels=10,colors='#8a8a8a',linewidths=.6);ax.clabel(cs,fontsize=6)
    ax.streamplot(X,Y,-gx,-gy,color='black',density=.7,linewidth=.65,arrowsize=.65)
    ax.scatter([0],[0],c='black',s=20)
    ax.set(xlabel=f'δ log K[{i},{j}]',ylabel=f'δ log K[{i},{other}]',title='Material variation curves the transported complex current')
    save(fig,'gradient-flow')

    # Actual matrix coefficients connecting all 15 current channels across 2 layers.
    layer=arr('layer');psi0=v
    states=[psi0,np.array(field('layer_one_field'),dtype=float),np.array(field('layer_two_field'),dtype=float)]
    fig,ax=plt.subplots(figsize=(10.8,4.1),layout='constrained')
    phase_colors=LinearSegmentedColormap.from_list('phase',['#00a9b5','#a04de0','#ee8e22','#00a9b5'])
    for step in range(2):
        for r in range(15):
            for c in range(15):
                block=layer[2*r:2*r+2,2*c:2*c+2];weight=np.linalg.norm(block)/math.sqrt(2)
                if weight>0:
                    rad=0 if r==c else (.035 if r>c else -.035)
                    ax.add_patch(FancyArrowPatch((step,c),(step+1,r),connectionstyle=f'arc3,rad={rad}',
                        arrowstyle='-',lw=.25+2*weight,color='#555555',alpha=.1+.55*min(1,weight)))
    for k,psi in enumerate(states):
        z=psi[:,0]+1j*psi[:,1]
        ax.scatter([k]*15,range(15),s=15+14*abs(z),c=np.angle(z),cmap=phase_colors,vmin=-np.pi,vmax=np.pi,zorder=4,edgecolors='black',linewidths=.35)
    ax.set(xticks=[0,1,2],xticklabels=['|H₀⟩ · input','|H₁⟩ · one layer','|H₂⟩ · composed layers'],yticks=[0,5,10,14],ylabel='complex channel',xlim=(-.12,2.12),ylim=(-1,15))
    ax.spines[['bottom','left']].set_visible(False)
    save(fig,'interaction-chain')

    snaps=data['snapshots'];steps=[s['step'] for s in snaps]
    residual=[float(Q(s['residual_squared']))**.5 for s in snaps]
    error=[float(Q(s['error_squared']))**.5 for s in snaps]
    fig,axes=plt.subplots(1,2,figsize=(10,3),layout='constrained')
    axes[0].semilogy(steps,residual,'o-',color='black',label='‖(I−λL²)xₖ−(1−λ)h‖₂')
    axes[0].semilogy(steps,error,'s--',color='#777777',label='‖xₖ−x*‖₂')
    axes[0].set(xlabel='whole-field refinement step k',ylabel='receiver norm',title='Integration converges to the same exact implicit solution')
    axes[0].legend(frameon=False,fontsize=7)
    changed=arr('material_effect').reshape(15,2)
    sensitivity=arr('sensitivity').reshape(15,2)
    axes[1].plot(range(15),changed[:,0],'-',c='black',label='Δ Re x* from measured material update')
    axes[1].plot(range(15),changed[:,1],'--',c='#777777',label='Δ Im x* from measured material update')
    axes[1].set(xlabel='channel',ylabel='signed output difference',title='The learned head changes the integrated generated field')
    axes[1].legend(frameon=False,fontsize=7)
    save(fig,'convergence-and-learning')

    # The exact phase-sensitive contact is part of each layer, not a decorative knot.
    ci=np.array(field('contact_input'),dtype=float);co=np.array(field('contact_output'),dtype=float)
    fig,ax=plt.subplots(figsize=(5.3,3.2),layout='constrained')
    phase=complex(*map(lambda s:float(Q(s)),data['input']['contact_phase']))
    contact_points=[complex(0)]
    for k,color in [(i,'black'),(j,'#888888')]:
        z=complex(*ci[k]);zz=complex(*co[k])
        if k==i:z*=phase;zz*=phase
        contact_points.extend([z,zz])
        ax.annotate('',(z.real,z.imag),(0,0),arrowprops=dict(arrowstyle='->',color=color,lw=1.2))
        ax.annotate('',(zz.real,zz.imag),(z.real,z.imag),arrowprops=dict(arrowstyle='->',color=color,lw=1.8))
        ax.text(z.real,z.imag,f'  {k} before',fontsize=8)
        ax.text(zz.real,zz.imag,f'  {k} after',fontsize=8)
    ax.set(xlabel='real current in the shared contact frame',ylabel='imaginary current',title='Relative phase slip contracts; the energy difference is deposited')
    xmin,xmax=min(z.real for z in contact_points),max(z.real for z in contact_points)
    ymin,ymax=min(z.imag for z in contact_points),max(z.imag for z in contact_points)
    dx=max(.1,xmax-xmin);dy=max(.1,ymax-ymin)
    ax.set(xlim=(xmin-.18*dx,xmax+.45*dx),ylim=(ymin-.25*dy,ymax+.25*dy))
    ax.axhline(0,lw=.4,c='#888888');ax.axvline(0,lw=.4,c='#888888')
    save(fig,'friction-current')
    print('computed coefficient, gradient, chain, friction and convergence plots complete',flush=True)

if __name__=='__main__':
    if 'geometry' in sys.argv:geometry()
    else:plots()
