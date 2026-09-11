"""Fifteen toroidal field channels, witnessed contacts and coherent receiver horizons.

The lattice/threshold is a declared exterior receiver chart. Its piecewise affine
intensity is the source of the triangulated horizon, not an approximate hidden
material boundary. Arithmetic before paint is integer/Fraction throughout.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import combinations
from collections import defaultdict
import runpy,json,sys,time
base=runpy.run_path(str(Path(__file__).with_name('build.py')));r=base['r'];ROOT=base['ROOT']
ZERO=(Q(0),Q(0));ONE=(Q(1),Q(0))
SCALE=20; MINOR=15; LEVEL=Q(1,3)
RINGS=[dict(axis=a,center=h,radius=rad) for a in range(3) for h,rad in ((0,60),(-36,48),(36,48),(-48,36),(48,36))]


def poly(ring,p):
    v=list(p);v[ring['axis']]-=ring['center'];s=sum(x*x for x in v)
    R=ring['radius'];plane=s-v[ring['axis']]**2
    return (s+R*R-MINOR*MINOR)**2-4*R*R*plane


def kernel(ring,p):
    f=poly(ring,p)
    return Q(max(0,-f),4*ring['radius']**2*MINOR**2)


def phase(ring,p):
    # Rational unit phase plate in the local torus chart; its full covector is retained.
    axis=(ring['axis']+1)%3;a=p[axis];R=ring['radius'];den=R*R+a*a
    return (Q(R*R-a*a,den),Q(2*R*a,den))


RADII=(Q(1),Q(2),Q(5,2),Q(3),Q(7,2),Q(4),Q(5))
DIRECTIONS_N=6;DIRECTIONS_M=4


def scene_lattice():
    # Rational spherical direction atlas and homothetic radial triangular frusta.
    # A frustum is divided into three tetrahedra with globally consistent vertex order.
    sphere,triangles=base['sphere'](n=DIRECTIONS_N,m=DIRECTIONS_M)
    directions=[r.mul(p,Q(1,2)) for p in sphere];n=len(directions)
    assert all(r.dot(v,v)==1 for v in directions)
    grid=[(Q(0),Q(0),Q(0))]+[r.mul(d,SCALE*radius) for radius in RADII for d in directions]
    basis=[];witness={}
    for vi,p in enumerate(grid):
        row={i:kernel(t,p) for i,t in enumerate(RINGS)};row={i:k for i,k in row.items() if k}
        basis.append({i:r.cs(phase(RINGS[i],p),k) for i,k in row.items()})
        for i,j in combinations(row,2):
            strength=min(row[i],row[j])
            if (i,j) not in witness or strength>witness[i,j][0]:witness[i,j]=(strength,vi)
    tets=[(0,1+a,1+b,1+c) for a,b,c in triangles]
    for layer in range(len(RADII)-1):
        lo=1+layer*n;hi=lo+n
        for triangle in triangles:
            a,b,c=sorted(triangle)
            tets.extend(((lo+a,lo+b,lo+c,hi+c),(lo+a,lo+b,hi+b,hi+c),(lo+a,hi+a,hi+b,hi+c)))
    assert all(r.dot(r.sub(grid[t[1]],grid[t[0]]),r.cross(r.sub(grid[t[2]],grid[t[0]]),r.sub(grid[t[3]],grid[t[0]])))!=0 for t in tets)
    return grid,basis,tets,witness


def matchings(edges):
    rounds=[]
    for e in edges:
        for group in rounds:
            used={v for pair in group for v in pair}
            if not set(e)&used: group.append(e);break
        else: rounds.append([e])
    assert sorted(e for g in rounds for e in g)==sorted(edges)
    assert all(len({v for e in g for v in e})==2*len(g) for g in rounds)
    return rounds


def power(z):return z[0]**2+z[1]**2


def evolution(edges,connections,last=12,twist=None,coupled=True,driven=True):
    groups=matchings(edges);psi=[ONE]*len(RINGS);psi[0]=(Q(0),Q(3));heat=[Q(0)]*len(RINGS)
    initial=sum(map(power,psi));out=[(psi[:],heat[:])];returns=[];source_returns=[];work=Q(0);clock=ONE
    alpha=Q(1,4);turn=(Q(3,5),Q(4,5))
    for k in range(last):
        psi=[r.cm(turn,z) for z in psi];clock=r.cm(turn,clock)
        for i,j in groups[k%len(groups)] if coupled else []:
            u=r.cs(connections[i,j],-1 if (i,j)==twist else 1);uc=(u[0],-u[1])
            x,y=psi[i],psi[j];delta=r.sub(y,r.cm(u,x))
            xx=r.add(x,r.cs(r.cm(uc,delta),alpha));yy=r.sub(y,r.cs(delta,alpha))
            h=2*alpha*(1-alpha)*power(delta)
            assert power(xx)+power(yy)+h==power(x)+power(y)
            assert r.add(xx,r.cm(uc,yy))==r.add(x,r.cm(uc,y))
            psi[i],psi[j]=xx,yy;heat[i]+=h/2;heat[j]+=h/2
            returns.append(dict(step=k+1,edge=(i,j),phase=u,difference=delta,heat=h))
        if driven:
            source=r.cm(clock,(Q(0),Q(1)))
            for i in (0,5,10):
                old=psi[i];new=r.add(old,source);supply=power(new)-power(old);psi[i]=new;work+=supply
                source_returns.append(dict(step=k+1,port=i,amplitude=source,work=supply))
        assert sum(map(power,psi))+sum(heat)==initial+work and all(h>=0 for h in heat)
        out.append((psi[:],heat[:]))
    return out,dict(initial_energy=initial,alpha=alpha,turn=turn,matchings=groups,events=returns,source_returns=source_returns,driven=driven,twist=twist)


def amplitude(row,psi):
    return tuple(sum(r.cm(k,psi[i])[c] for i,k in row.items()) for c in range(2))


def horizon(grid,basis,tets,psi):
    amps=[amplitude(row,psi) for row in basis];levels=[power(a)-LEVEL for a in amps]
    assert all(v!=0 for v in levels),'threshold hits a lattice vertex: retain that degenerate receiver explicitly'
    vertices=[];currents=[];faces=[];edgeids={};source_edges=[]
    def crossing(a,b):
        key=tuple(sorted((a,b)))
        if key not in edgeids:
            a,b=key;t=-levels[a]/(levels[b]-levels[a]);assert 0<t<1
            p=tuple(Q(v,SCALE) for v in grid[a]);q=tuple(Q(v,SCALE) for v in grid[b])
            edgeids[key]=len(vertices);vertices.append(r.mix(p,q,t));currents.append((r.mix(amps[a],amps[b],t),ZERO,ZERO))
            source_edges.append((a,b,t))
        return edgeids[key]
    for tet in tets:
        pos=[i for i in tet if levels[i]>0];neg=[i for i in tet if levels[i]<0]
        if not pos or not neg:continue
        if len(pos)==1: polygons=[[crossing(pos[0],i) for i in neg]]
        elif len(neg)==1:polygons=[[crossing(neg[0],i) for i in pos]]
        else:
            a,b=pos;c,d=neg;polyline=[crossing(a,c),crossing(a,d),crossing(b,d),crossing(b,c)]
            polygons=[polyline[:3],[polyline[0],polyline[2],polyline[3]]]
        inside=tuple(Q(v,SCALE) for v in grid[pos[0]])
        for f in polygons:
            a,b,c=[vertices[i] for i in f];normal=r.cross(r.sub(b,a),r.sub(c,a))
            assert r.dot(normal,normal)>0
            if r.dot(normal,r.sub(inside,a))>0:f.reverse()
            faces.append(tuple(f))
    edges=defaultdict(list)
    for f in faces:
        for a,b in zip(f,f[1:]+f[:1]):edges[tuple(sorted((a,b)))].append(1 if a<b else -1)
    assert all(len(v)==2 and sum(v)==0 for v in edges.values())
    # Ambient box boundary is outside this receiver; no square perimeter caps are inserted.
    assert all(levels[i]<0 for i,p in enumerate(grid) if r.dot(p,p)==(SCALE*RADII[-1])**2)
    return vertices,faces,currents,dict(V=len(vertices),E=len(edges),F=len(faces),chi=len(vertices)-len(edges)+len(faces),source_edges=source_edges)


def wire(v):
    if isinstance(v,Q):return r.ratio(v)
    if isinstance(v,dict):return {str(k):wire(x) for k,x in v.items()}
    if isinstance(v,(list,tuple)):return [wire(x) for x in v]
    return v


def compile_horizon(name,data,psi,heat,event):
    grid,basis,tets,witness=data
    v,f,c,mesh=horizon(grid,basis,tets,psi)
    from knot_waves import flow
    material_clock=Q(event['step'],len(event['law']['matchings']))
    v=[flow(p,material_clock) for p in v]
    print(name,'horizon',mesh['V'],mesh['F'],'triangles',flush=True)
    src=wire(dict(kind='coherent-torus-horizon',rings=RINGS,scale=SCALE,minor=MINOR,radial_layers=RADII,direction_chart=(DIRECTIONS_N,DIRECTIONS_M),threshold=LEVEL,
                  psi=psi,heat=heat,chronology=event,mesh=mesh,material_clock=material_clock,
                  material_flow='F_tau from plate14; advected scalar optical amplitude; positive determinant1; coupling points/atlas move together',
                  intensity_chart='I_h: nodal |sum psi_i K_i*g_i|², affine on each radial-atlas tetrahedron',
                  amplitude_chart='A_h: separately affine nodal complex amplitude; retained as color/current receiver'))
    camera=r.Receiver(distance=Q(32),aperture=Q(1,16))
    scene=r.compile_scene(v,f,currents=c,receiver=camera,source=src,step=Q(1,8),bounds=(-5,-5,5,5),closed_outward=True)
    assert not scene['meta']['unresolved_near_faces'] and not scene['meta']['degenerate_faces']
    return scene


def main():
    data=scene_lattice();grid,basis,tets,witness=data
    from woven_bridge import choose_site
    site,quartet=choose_site(data);a,b,c,d=quartet;vi=grid.index(site)
    spine=[tuple(sorted(e)) for e in ((a,b),(b,c),(c,a),(b,d),(d,a))]
    for e in spine:witness[e]=(min(kernel(RINGS[i],site) for i in e),vi)
    edges=sorted(witness)
    connections={}
    for edge,(_,vi) in witness.items():
        i,j=edge;pi=phase(RINGS[i],grid[vi]);pj=phase(RINGS[j],grid[vi]);connections[edge]=r.cm(pi,(pj[0],-pj[1]));assert power(connections[edge])==1
    states,receipt=evolution(edges,connections);uncoupled,off=evolution(edges,connections,coupled=False);closed,closed_law=evolution(edges,connections,driven=False)
    # Choose a witnessed triangle, with exactly one reversing seam; preserve the actual cycle.
    cycle=(a,b,c)
    twisted,tw=evolution(edges,connections,twist=(cycle[0],cycle[2]))
    path=ROOT/'research/papers/source/papers/hnn-information-chemistry/woven-scenes.json'
    scenes=json.loads(path.read_text()) if path.exists() else {};selected=sys.argv[1:]
    # The initial optical face is unchanged; retain its newly admitted future-contact law.
    if 'woven_0' in scenes:
        scenes['woven_0']['meta']['source']['chronology']=wire(dict(step=0,law=receipt))
        scenes['woven_0']['meta']['source']['material_clock']=wire(Q(0))
        scenes['woven_0']['meta']['source']['material_flow']='F_tau from plate14; advected scalar optical amplitude; positive determinant1; coupling points/atlas move together'
    for name,k,series,law in [('woven_0',0,states,receipt),('woven_6',6,states,receipt),('woven_12',12,states,receipt),('woven_off',12,uncoupled,off),('woven_twist',12,twisted,tw)]:
        if selected and name not in selected:continue
        scenes[name]=compile_horizon(name,data,*series[k],dict(step=k,law=law));path.write_text(json.dumps(scenes,separators=(',',':'))+'\n')
        print(name,len(scenes[name]['marks']),'marks',flush=True)
    rec=wire(dict(rings=RINGS,grid=grid,contact_witnesses=[dict(edge=e,node=v[1],strength=v[0]) for e,v in witness.items()],
                  cycle=cycle,bridge_site=site,bridge_quartet=quartet,connections=[(e,u) for e,u in connections.items()],law=receipt,states=states,uncoupled=uncoupled,twisted=twisted,closed=closed,closed_law=closed_law))
    Path(__file__).with_name('woven_ecology_receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
    export=runpy.run_path(str(ROOT/'research/papers/source/packages/holonic-receiver/export_svg.py'))['scene_svg']
    for name,scene in scenes.items():(ROOT/'research/papers/rendered/receiver-engraving'/f'{name}.svg').write_text(export(scene,width_mm=Q(100),line_width_pt=Q(1,3)))
    print('contacts',len(edges),'matchings',len(receipt['matchings']),'orientation cycle',cycle,flush=True)

if __name__=='__main__':main()
