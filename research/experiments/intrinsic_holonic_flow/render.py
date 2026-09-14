"""Geometric, phase-current and arrival receivers of the same analytic object."""
from pathlib import Path
from itertools import permutations,combinations,product
from collections import Counter
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.colors import Normalize
from matplotlib.patches import Rectangle
from matplotlib.transforms import Bbox
from mpl_toolkits.mplot3d import proj3d
from mpl_toolkits.mplot3d.art3d import Poly3DCollection,Line3DCollection
import flow as f

ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).parent
OUT=ROOT/'research/papers/source/papers/elementary-holon-generation/figures'
d=json.loads((HERE/'receipt.json').read_text())
plt.rcParams.update({'font.family':'DejaVu Serif','font.size':10,'svg.fonttype':'path','axes.spines.top':False,'axes.spines.right':False,'savefig.facecolor':'white'})

def save(fig,name):
    fig.savefig(OUT/f'{name}.svg',bbox_inches='tight',pad_inches=.08);plt.close(fig)

def surface(i,radius=f.CORE_RADIUS,rows=18,cols=64):
    u,v=np.meshgrid(np.linspace(0,1,cols,endpoint=False),np.linspace(0,1,rows,endpoint=False))
    points=f.advect(f.torus_point(i,u,v,radius).reshape(-1,3))
    faces=[]
    for j in range(rows):
        for k in range(cols):
            a=j*cols+k;b=j*cols+(k+1)%cols;c=((j+1)%rows)*cols+(k+1)%cols;dd=((j+1)%rows)*cols+k
            faces.extend([(a,b,c),(a,c,dd)])
    edges=Counter()
    for face in faces:
        for a,b in zip(face,face[1:]+face[:1]):edges[tuple(sorted((a,b)))]+=1
    assert all(n==2 for n in edges.values())
    assert len(points)-len(edges)+len(faces)==0
    return points,np.array(faces)

def setup(ax,local=False):
    ax.set_proj_type('persp',focal_length=1.3)
    ax.view_init(elev=27,azim=-61 if not local else -45)
    if not local:
        ax.set(xlim=(-8.5,8.5),ylim=(-3,6),zlim=(-3,3));ax.set_box_aspect((17,9,6),zoom=1.05)
    ax.set_axis_off()

def draw_body(ax,indices=range(f.N),alpha=.10,substeps=14,paths=True):
    cmap=plt.get_cmap('twilight_shifted')
    for i in indices:
        pts,faces=surface(i)
        ax.add_collection3d(Poly3DCollection(pts[faces],facecolors='#bad0d7',edgecolors='#6b838b',linewidths=.08,alpha=alpha,zorder=1))
        # Two fundamental phase cycles of the same torus, not extra copied nodes.
        tt=np.linspace(0,1,240)
        for q,p in [(tt,np.zeros_like(tt)),(np.zeros_like(tt),tt)]:
            curve=f.advect(f.torus_point(i,q,p,f.CORE_RADIUS*1.05));ax.plot(*curve.T,color='#334f58',lw=.7,alpha=.7,zorder=2)
        pos=f.CENTERS[i].copy();pos[f.AXES[i]]+=.7
        ax.text(*f.advect(pos),f'{i}',fontsize=10,color='black')
    if paths:
        for pa,color in zip(d['paths'],['#c3473b','#1552a0']):
            q,p=np.array(pa['q']),np.array(pa['p'])
            upto=min(len(q),1+substeps*22)
            for i in indices:
                curve=f.advect(f.torus_point(i,q[:upto,i],p[:upto,i],f.CORE_RADIUS*1.075),t=np.linspace(0,1,upto))
                ax.plot(*curve.T,color=color,lw=1.1,alpha=.92,zorder=10)
                ax.scatter(*curve[0],color=color,s=14,zorder=11)
    for w in f.WITNESSES:
        if all(i in indices for i in w['edge']):
            ax.scatter(*f.advect(w['point']),s=20,marker='D',c='#bf943d',depthshade=False)

def volume_complex():
    # Common quarter-unit cubes. The entire cube lies in each recorded owner:
    # signed distance to a circle is 1-Lipschitz, and ||corner-center|| <= 3h.
    spacing=.25;half=spacing/2;inner=f.FIELD_RADIUS-3*half
    axes=[np.arange(-8.5,8.5,spacing)+half,np.arange(-2.75,5.75,spacing)+half,np.arange(-2.75,2.75,spacing)+half]
    centers=np.stack(np.meshgrid(*axes,indexing='ij'),axis=-1).reshape(-1,3)
    owned=np.stack([f.torus_polynomial(centers,i,inner)<0 for i in range(f.N)],axis=1)
    selected=np.flatnonzero(owned.any(axis=1));centers=centers[selected];owned=owned[selected]
    # Dyadic coordinates below are exactly representable in the numerical receiver.
    cubeids=np.rint((centers-half)*4).astype(int)
    vertexids={};vertices=[];tets=[];ownership=[]
    for cube,owners in zip(cubeids,owned):
        for perm in permutations(range(3)):
            offsets=[np.zeros(3,dtype=int)]
            for axis in perm:
                nxt=offsets[-1].copy();nxt[axis]+=1;offsets.append(nxt)
            vs=[]
            for off in offsets:
                key=tuple(cube+off)
                if key not in vertexids:vertexids[key]=len(vertices);vertices.append(np.array(key)/4)
                vs.append(vertexids[key])
            p=np.array([vertices[v] for v in vs])
            if np.linalg.det(p[1:]-p[0])<0:vs[2],vs[3]=vs[3],vs[2]
            tets.append(vs);ownership.append(np.flatnonzero(owners).tolist())
    # Boundary-of-boundary on the generator simplex, with its oriented incidence.
    boundary=Counter()
    for omit in range(4):
        face=[j for j in range(4) if j!=omit]
        for omit2 in range(3):
            edge=tuple(face[j] for j in range(3) if j!=omit2)
            boundary[edge]+=(-1)**(omit+omit2)
    assert not any(boundary.values())
    vertices=np.array(vertices);tets=np.array(tets)
    joint=sum(len(o)>1 for o in ownership)
    return vertices,tets,ownership,dict(vertices=len(vertices),tetrahedra=len(tets),joint_tetrahedra=joint,spacing=spacing,
        containment='cube center is in radius 1-3/8 torus; 1-Lipschitz circle-distance proves each radius-1 owner contains its complete cube',boundary_squared_zero=True)

def geometry():
    fig=plt.figure(figsize=(12.2,4.35));ax=fig.add_subplot(111,projection='3d',computed_zorder=False)
    draw_body(ax);setup(ax)
    fig.subplots_adjust(left=0,right=1,bottom=0,top=.92)
    for artist in ax.get_children(): artist.set_clip_on(False)
    fig.canvas.draw()
    all_points=[surface(i)[0] for i in range(f.N)]
    for pa in d['paths']:
        q,p=np.array(pa['q']),np.array(pa['p'])
        for i in range(f.N):all_points.append(f.advect(f.torus_point(i,q[:,i],p[:,i],f.CORE_RADIUS*1.075),t=np.linspace(0,1,len(q))))
    pts=np.concatenate(all_points)
    x,y,z=proj3d.proj_transform(*pts.T,ax.get_proj())
    pixels=ax.transData.transform(np.c_[x,y]);lo=pixels.min(axis=0)/fig.dpi-.20;hi=pixels.max(axis=0)/fig.dpi+.20
    fig.savefig(OUT/'intrinsic-torus-chain.svg',bbox_inches=Bbox.from_extents(*lo,*hi))
    plt.close(fig)
    vertices,tets,owners,stats=volume_complex()
    edge=next(w for w in f.WITNESSES if w['edge']==[2,5]);site=np.array(edge['point'])
    fig=plt.figure(figsize=(11.6,4.1));ax=fig.add_subplot(121,projection='3d',computed_zorder=False)
    draw_body(ax,indices=[1,2,3,5],alpha=.13,substeps=14);setup(ax)
    ax.set(xlim=(-5.5,5.5),ylim=(-3,6),zlim=(-3,3));ax.set_box_aspect((11,9,6),zoom=1.25);ax.set_title('Overlapping field domains around a real join',fontsize=12)
    # Thick field boundaries restricted to a cutaway; complete definitions retained.
    for i in [2,5]:
        pts,faces=surface(i,radius=f.FIELD_RADIUS,rows=14,cols=40)
        triangles=pts[faces];keep=np.mean(triangles,axis=1)[:,2]<f.advect(site)[2]
        ax.add_collection3d(Poly3DCollection(triangles[keep],facecolors='#bababa',edgecolors='#888888',linewidths=.17,alpha=.09))
    ax2=fig.add_subplot(122,projection='3d',computed_zorder=False);centroids=vertices[tets].mean(axis=1)
    keep=np.max(abs(centroids-site),axis=1)<.85
    edges={};jointfaces=[]
    for tet,own in zip(tets[keep],np.array(owners,dtype=object)[keep]):
        for a,b in combinations(tet,2):edges[tuple(sorted((int(a),int(b))))]=len(own)>1 or edges.get(tuple(sorted((int(a),int(b)))),False)
        if 2 in own and 5 in own:
            for a,b,c in combinations(tet,3):jointfaces.append(f.advect(vertices[[a,b,c]]))
    edge_curves=[f.advect(np.linspace(*vertices[list(e)],14)) for e in edges]
    ax2.add_collection3d(Line3DCollection(edge_curves,colors=['#ad6b16' if joint else '#9bb1b9' for joint in edges.values()],linewidths=[.6 if joint else .23 for joint in edges.values()],alpha=.72))
    if jointfaces:ax2.add_collection3d(Poly3DCollection(jointfaces,facecolors='#d8a33c',edgecolors='none',alpha=.075))
    site=f.advect(site)
    ax2.set(xlim=(site[0]-.9,site[0]+.9),ylim=(site[1]-.9,site[1]+.9),zlim=(site[2]-.9,site[2]+.9));ax2.set_box_aspect((1,1,1));setup(ax2,True)
    ax2.set_title('Magnified shared volume · conforming tetrahedra',fontsize=12)
    fig.subplots_adjust(left=0,right=1,bottom=0,top=.91,wspace=.03)
    save(fig,'intrinsic-contact-complex')
    sample=vertices[::max(1,len(vertices)//23)]
    dt=1e-6;current=f.advect(sample)
    velocity=np.stack([np.zeros(len(sample)),-current[:,0]*current[:,2]/8,current[:,0]*current[:,1]/8],axis=1)
    derivative=(f.advect(sample,1+dt)-f.advect(sample,1-dt))/(2*dt)
    inverse_error=float(np.max(abs(f.advect(current,t=-1)-sample)))
    ode_error=float(np.max(abs(derivative-velocity)))
    assert inverse_error<1e-12 and ode_error<1e-7
    link_receipts=[]
    for i,j in [(0,1),(1,2),(2,3),(3,4),(2,5)]:
        ai,aj=f.AXES[i],f.AXES[j];assert ai!=aj
        shared=next(k for k in range(3) if k not in (ai,aj))
        assert f.CENTERS[i,ai]==f.CENTERS[j,ai]
        crossings=[]
        for sign in [-1,1]:
            point=f.CENTERS[j].copy();point[shared]+=sign*f.R
            radial=float(np.sum((point-f.CENTERS[i])**2))
            assert radial!=f.R**2
            crossings.append(dict(point=point.tolist(),disk_radius_squared=radial,inside=radial<f.R**2))
        assert sum(c['inside'] for c in crossings)==1
        link_receipts.append(dict(pair=[i,j],absolute_linking_number=1,crossings=crossings))
    (HERE/'mesh.json').write_text(json.dumps(dict(stats=stats,contact=edge,advection_time=1,advection_rate=1/8,advection_inverse_error=inverse_error,advection_ode_error=ode_error,advection_map='(x, y cos(xt/8)-z sin(xt/8), y sin(xt/8)+z cos(xt/8)); determinant one',local_display_tetrahedra=int(keep.sum()),torus_boundary_euler_characteristic=0,analytic_link_pairs=link_receipts,
        link_witness='each neighboring perpendicular radius-2 core crosses the other spanning disk once; the other plane crossing is outside the disk'),indent=2)+'\n')
    np.savez_compressed(HERE/'mesh.npz',vertices=vertices,advected_vertices=f.advect(vertices),tetrahedra=tets,owners=np.array([[int(i in own) for i in range(f.N)] for own in owners],dtype=np.uint8))

def basins():
    fields=np.load(HERE/'arrival.npz');names=['coarse','zoom','fine']
    cmap=plt.get_cmap('viridis').copy();cmap.set_bad('#dddddd')
    fig,axes=plt.subplots(1,3,figsize=(12,3.45),layout='constrained')
    for i,(ax,name,bounds) in enumerate(zip(axes,names,d['bounds'])):
        image=np.ma.masked_greater(fields[name],f.CAP)
        im=ax.imshow(image,origin='lower',extent=bounds,cmap=cmap,vmin=0,vmax=f.CAP,interpolation='nearest',aspect='equal')
        if i<2:
            b=d['bounds'][i+1];ax.add_patch(Rectangle((b[0],b[2]),b[1]-b[0],b[3]-b[2],fill=False,edgecolor='white',lw=1))
        ax.set(xlabel='initial longitude q₀',ylabel='initial meridian p₀',title=['Full initial-condition section','Freshly evolved 6.25× zoom','Freshly evolved 31.25× zoom'][i])
        ax.tick_params(labelsize=8)
    cb=fig.colorbar(im,ax=axes,shrink=.75,pad=.02);cb.set_label('first receiver arrival · iteration')
    save(fig,'intrinsic-arrival-basins')
    fig=plt.figure(figsize=(11.5,3.8));ax=fig.add_subplot(121,projection='3d',computed_zorder=False)
    times=fields['zoom'];xx=np.linspace(d['bounds'][1][0],d['bounds'][1][1],192);yy=np.linspace(d['bounds'][1][2],d['bounds'][1][3],192)
    x,y=np.meshgrid(xx,yy);z=np.where(times<=f.CAP,times,np.nan).astype(float)
    ax.plot_surface(x[::3,::3],y[::3,::3],z[::3,::3],cmap=cmap,linewidth=0,antialiased=True,rasterized=True)
    ax.view_init(elev=31,azim=-61);ax.set(xlabel='q₀',ylabel='p₀',zlabel='arrival time',title='A receiver-height surface of the same section')
    ax2=fig.add_subplot(122)
    qa,pa=[np.array(d['paths'][0][s]) for s in ['q','p']];qb,pb=[np.array(d['paths'][1][s]) for s in ['q','p']]
    # Phase distance retains all twelve axes, not only their 3D display positions.
    dist=np.sqrt(np.sum(((np.c_[qa,pa]-np.c_[qb,pb]+.5)%1-.5)**2,axis=1))
    ax2.semilogy(np.arange(len(dist))/22,dist,color='black')
    ax2.set(xlabel='split-flow iteration',ylabel='distance in the 12-phase chart',title=f"Neighboring starts · arrival {d['arrival_pair'][0]} versus {d['arrival_pair'][1]}")
    fig.subplots_adjust(left=.02,right=.98,bottom=.18,top=.9,wspace=.3)
    save(fig,'intrinsic-route-separation')

def heads():
    qs=np.array(d['paths'][0]['q']);idx=[0,min(22*4,len(qs)-1)]
    fig,axes=plt.subplots(2,2,figsize=(7.1,5.1),layout='constrained')
    for row,step in enumerate(idx):
        for col,beta in enumerate(f.BETAS):
            a,_=f.head(qs[step],beta);ax=axes[row,col]
            im=ax.imshow(a,cmap='Greys',vmin=0,vmax=1);ax.set(title=f'head β={beta:g} · flow step {step/22:g}',xlabel='current chart j',ylabel='receiving chart i',xticks=range(f.N),yticks=range(f.N));ax.tick_params(labelsize=8)
    fig.colorbar(im,ax=axes,shrink=.7,pad=.02,label='normalized phase participation')
    save(fig,'intrinsic-heads')

def response():
    q,_=f.initialize(*map(np.asarray,d['selected_neighbor_pair'][0]))
    t=np.linspace(0,1,280);family=np.repeat(q[None,:],len(t),axis=0);family[:,0]=t
    gate=1/(1+np.exp(np.cos(2*np.pi*t)))
    fig,axes=plt.subplots(1,2,figsize=(10.7,2.95),layout='constrained')
    axes[0].plot(t,gate,color='black',label='g₀ = sigmoid(−cos 2πq₀)')
    axes[0].plot(t,gate*(1-gate),color='#777777',ls='--',label='dg/ds = g(1−g)')
    axes[0].set(xlabel='longitude phase q₀',ylabel='local reaction gate / derivative',title='Sigmoid on the same phase field')
    axes[0].legend(frameon=False,fontsize=8)
    neighbor=next(j for j in range(f.N) if j!=0 and f.MASK[0,j])
    for beta,style in zip(f.BETAS,['-','--']):
        a,_=f.head(family,beta);axes[1].plot(t,a[:,0,neighbor],style,color='black',label=f'β={beta:g} · chart {neighbor} → 0')
    axes[1].set(xlabel='same longitude phase q₀',ylabel='normalized phase participation',title='Two heads respond within one moving state')
    axes[1].legend(frameon=False,fontsize=8)
    save(fig,'intrinsic-response')

def friction():
    q,_=f.initialize(*map(np.asarray,d['selected_neighbor_pair'][0]));i,j=2,5
    x=np.exp(2j*np.pi*q[i]);y=np.exp(2j*np.pi*q[j]);u=np.exp(-2j*np.pi*f.PHASE[i,j]);alpha=.25
    delta=y-u*x;xx=x+alpha*np.conj(u)*delta;yy=y-alpha*delta
    heat=2*alpha*(1-alpha)*abs(delta)**2
    assert abs(abs(x)**2+abs(y)**2-abs(xx)**2-abs(yy)**2-heat)<1e-12
    fig,axes=plt.subplots(1,2,figsize=(10.8,3.25),layout='constrained')
    ax=axes[0]
    for start,end,label,color in [(u*x,u*xx,'2','#c3473b'),(y,yy,'5','#1552a0')]:
        ax.annotate('',(start.real,start.imag),(0,0),arrowprops=dict(arrowstyle='->',color=color,lw=1))
        ax.annotate('',(end.real,end.imag),(start.real,start.imag),arrowprops=dict(arrowstyle='->',color=color,lw=2))
        ax.text(start.real,start.imag,'  '+label+' incident',fontsize=8)
        ax.text(end.real,end.imag,'  '+label+' after contact',fontsize=8)
    ax.set(xlim=(-1.45,1.45),ylim=(-1.3,1.3),xlabel='real current in shared frame',ylabel='imaginary current',title='Phase slip at the actual 2↔5 contact');ax.axhline(0,c='#aaa',lw=.5);ax.axvline(0,c='#aaa',lw=.5)
    avalues=np.linspace(0,1,180);diss=2*avalues*(1-avalues)*abs(delta)**2
    axes[1].plot(avalues,diss,color='black');axes[1].scatter([alpha],[heat],c='black')
    axes[1].set(xlabel='declared contact coefficient α',ylabel='deposited quadratic energy',title='The same relative current determines dissipation')
    save(fig,'intrinsic-friction')
    (HERE/'contact.json').write_text(json.dumps(dict(edge=[i,j],alpha=alpha,phase=[u.real,u.imag],input=[[x.real,x.imag],[y.real,y.imag]],output=[[xx.real,xx.imag],[yy.real,yy.imag]],heat=heat,scope='local constitutive contact evaluated on phase currents; radial amplitude and heat augment the conservative phase chart'),indent=2)+'\n')

def main():geometry();basins();heads();response();friction()
if __name__=='__main__':main()
