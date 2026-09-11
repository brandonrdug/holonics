"""Exact rational polygonal knot sources.

The braid word is the topology receipt; the returned PL centreline is an exact annular
realisation suitable for renderers.  All coordinates are ``Fraction`` values.  This module
deliberately does not infer knot type from a sampled curve: it retains the closed braid word,
permutation, and every received projected crossing.
"""
from fractions import Fraction as Q
import json
from pathlib import Path

V = tuple

def _add(a,b): return tuple(x+y for x,y in zip(a,b))
def _sub(a,b): return tuple(x-y for x,y in zip(a,b))
def _mul(a,s): return tuple(x*s for x in a)
def _dot(a,b): return sum(x*y for x,y in zip(a,b))
def _cross(a,b): return (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0])

def _solve2(a,b,c,d,e,f):
    det=a*e-b*d
    if not det: return None
    return ((c*e-b*f)/det, (a*f-c*d)/det)

def _seg_intersection_3(a,b,c,d):
    """Exact proper/endpoint intersection witness for 3D segments, or None."""
    u,v=_sub(b,a),_sub(d,c); w=_sub(c,a)
    # Parallel collinear segments need an interval-overlap witness; solving two coordinates
    # alone would silently miss these (and a zero-length segment is a genuine defect).
    if u == (0,0,0) or v == (0,0,0):
        return (Q(0),Q(0),a) if a == c else None
    if _cross(u,v) == (0,0,0) and _cross(w,u) == (0,0,0):
        axis=max(range(3),key=lambda i: abs(u[i]))
        s0=(c[axis]-a[axis])/u[axis]; s1=(d[axis]-a[axis])/u[axis]
        lo=max(Q(0),min(s0,s1)); hi=min(Q(1),max(s0,s1))
        if lo <= hi: return (lo,lo,_add(a,_mul(u,lo)))
        return None
    # Solve two coordinates, then verify the third.
    for i,j in ((0,1),(0,2),(1,2)):
        sol=_solve2(u[i],-v[i],w[i],u[j],-v[j],w[j])
        if sol is None: continue
        s,t=sol
        if 0 <= s <= 1 and 0 <= t <= 1 and _add(a,_mul(u,s)) == _add(c,_mul(v,t)):
            return (s,t,_add(a,_mul(u,s)))
    return None

def _orient(a,b,c):
    return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])

def _projected_crossings(points):
    out=[]; n=len(points)
    for i in range(n):
        a,b=points[i],points[(i+1)%n]
        for j in range(i+1,n):
            if j in (i-1,i+1) or (i==0 and j==n-1): continue
            c,d=points[j],points[(j+1)%n]
            den=_solve2(b[0]-a[0],-(d[0]-c[0]),c[0]-a[0],b[1]-a[1],-(d[1]-c[1]),c[1]-a[1])
            if den is None: continue
            s,t=den
            if not (0 < s < 1 and 0 < t < 1): continue
            pa=_add(a,_mul(_sub(b,a),s)); pb=_add(c,_mul(_sub(d,c),t))
            # Generic projection requires a strict depth ordering.
            if pa[2] == pb[2]: raise AssertionError(("depth_tie",i,j,pa))
            out.append({"edges":[i,j],"parameters":[[s.numerator,s.denominator],[t.numerator,t.denominator]],
                        "xy":[[pa[0].numerator,pa[0].denominator],[pa[1].numerator,pa[1].denominator]],
                        "over_edge":i if pa[2]>pb[2] else j,
                        "over_depth":[max(pa[2],pb[2]).numerator,max(pa[2],pb[2]).denominator],
                        "depth_difference":[(pa[2]-pb[2]).numerator,(pa[2]-pb[2]).denominator]})
    return out

def _circle_point(q,n):
    """Rational quarter stereographic polygon, with 4*n angular samples."""
    N=4*n; q%=N; quadrant,j=divmod(q,n); t=Q(j,n)
    x=(1-t*t)/(1+t*t); y=2*t/(1+t*t)
    return ((x,y),( -y,x),( -x,-y),(y,-x))[quadrant]

def _annular_component(word,lanes,R=4,spacing=1):
    H=len(word); n=3*H; samples=12*H
    offsets=[Q(2*i-(lanes-1),2)*spacing for i in range(lanes)]
    lane_of=list(range(lanes)); paths=[[] for _ in range(lanes)]; receipts=[]
    for cell,(i,sign) in enumerate(word):
        left,right=lane_of[i],lane_of[i+1]
        for sub in range(12):
            s=Q(sub,11); theta_q=cell*12+sub
            (cx,cy)=_circle_point(theta_q,n)
            for strand in range(lanes):
                radius=Q(R)+offsets[lane_of.index(strand)]
                z=Q(0)
                if strand==left: radius=Q(R)+offsets[i]*(1-s)+offsets[i+1]*s; z=Q(sign)*4*s*(1-s)
                elif strand==right: radius=Q(R)+offsets[i+1]*(1-s)+offsets[i]*s; z=-Q(sign)*4*s*(1-s)
                paths[strand].append((radius*cx,radius*cy,z))
        lane_of[i],lane_of[i+1]=right,left
        receipts.append({"generator":i+1,"sign":sign,"cell":cell,"samples":12})
    # Add the final angular endpoint (same rational point as angle zero).
    cx,cy=_circle_point(samples,n)
    for strand in range(lanes):
        radius=Q(R)+offsets[lane_of.index(strand)]
        paths[strand].append((radius*cx,radius*cy,Q(0)))
    top_lane={strand:lane for lane,strand in enumerate(lane_of)}
    cycle=[]; start=0; seen=set()
    while start not in seen:
        seen.add(start); cycle.append(start); start=top_lane[start]
    if len(cycle)!=lanes: raise ValueError("annular closure is a link")
    points=[]
    for strand in cycle:
        points.extend(paths[strand] if not points else paths[strand][1:])
    if points[-1]==points[0]: points.pop()
    return points,receipts,[],top_lane

def _source(kind, word, alexander, lanes=3):
    if kind=="unknot":
        points=[(Q(4)*_circle_point(q,3)[0],Q(4)*_circle_point(q,3)[1],Q(0)) for q in range(12)]
        braid=[]; closure=[]; permutation=[0]
    else:
        points, braid, closure, top_lane=_annular_component(word,lanes=lanes)
        permutation=[top_lane[i] for i in range(lanes)]
    n=len(points); intersections=[]
    for i in range(n):
        for j in range(i+1,n):
            if j in (i-1,i+1) or (i==0 and j==n-1): continue
            hit=_seg_intersection_3(points[i],points[(i+1)%n],points[j],points[(j+1)%n])
            if hit is not None: intersections.append([i,j])
    if intersections: raise AssertionError((kind,"3d_intersections",intersections[:8]))
    projected=_projected_crossings(points)
    # In the annular construction the angular cell is the braid station; the xy coordinate is no
    # longer a monotone time coordinate.  The detector is exhaustive and every event belongs to
    # exactly one angular braid cell.
    braid_projected=projected if word else []
    if kind != "unknot" and len(projected) != len(braid):
        raise AssertionError((kind,"annular crossing receipt mismatch",len(braid),len(projected)))
    # Read the angular segment and actual crossing sign back from the polygon.
    # Positive generators carry the inner incoming lane over the outer lane.
    observed_cells=[]
    for crossing in braid_projected:
        i,j=crossing['edges']; period=12*len(word)
        assert i%period==j%period
        cell=(i%period)//12
        ri=points[i][0]**2+points[i][1]**2
        rj=points[j][0]**2+points[j][1]**2
        depth=Q(*crossing['depth_difference'])
        assert ri!=rj and depth!=0
        sign=1 if (rj-ri)*depth>0 else -1
        assert sign==word[cell][1]
        crossing['angular_cell']=cell
        crossing['observed_generator_sign']=sign
        observed_cells.append(cell)
    assert sorted(observed_cells)==list(range(len(word)))
    annular={"major_radius":[4,1],"angular_samples":12*len(word) if word else 12,
             "quarter_stereographic_n":3*len(word) if word else 3,
             "radial_lane_spacing":[1,1],"crossing_substeps":12,
             "angular_sector_bound":"< pi/2"}
    return {"kind":kind,"vertices":[[[x.numerator,x.denominator] for x in p] for p in points],
            "edges":[[i,(i+1)%n] for i in range(n)],"length":n,
            "braid_word":[[i+1,s] for i,s in word],"closure":closure,
            "closure_permutation":permutation,"intended_crossings":braid,
            "braid_projected_crossings":braid_projected,
            "projected_crossings":projected,"projected_crossing_count":len(projected),
            "annular":annular,
            "alexander_polynomial":alexander,
            "alexander_status":"external standard invariant of the certified closed braid; not computed by this generator",
            "certificate":"planar_spanning_disk" if kind=="unknot" else "closed_braid_word_and_Alexander_polynomial",
            "clearance_scope":"all nonincident polygon edges have no exact 3D intersection; tube radius requires local-joint frame check"}

def knots():
    return {
        "unknot":_source("unknot",[],"1"),
        "trefoil_3_1":_source("trefoil_3_1",[(0,1),(0,1),(0,1)],"t^-1 - 1 + t",lanes=2),
        "figure_eight_4_1":_source("figure_eight_4_1",[(0,1),(1,-1),(0,1),(1,-1)],"-t^-1 + 3 - t"),
    }

def main():
    data=knots(); out=Path(__file__).with_name("knot_geometry_receipt.json")
    out.write_text(json.dumps(data,indent=2)+"\n")
    print("returned exact rational knot sources:", ", ".join(data),
          "projected crossings:", {k:v["projected_crossing_count"] for k,v in data.items()})

if __name__=="__main__": main()
