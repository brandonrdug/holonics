// Receiver maps for exterior scientific drawing. Original implementation.
// Exact source/visibility calculations live in the optional Fraction compiler;
// these pure Typst operations are the declared final numeric presentation chart.
#let dot(a,b)=array.zip(a,b).map(((x,y))=>x*y).sum()
#let sub(a,b)=array.zip(a,b).map(((x,y))=>x - y)
#let receiver(right:(1,0,0),up:(0,1,0),view:(0,0,1),origin:(0,0,0),distance:12,focal:8,near:1/16,pinhole:false,phase:(1,0),aperture:1)={
 assert(aperture>0,message:"receiver aperture must be positive")
 assert(near>0,message:"pinhole boundary must be explicit")
 (right:right,up:up,view:view,origin:origin,distance:distance,focal:focal,near:near,pinhole:pinhole,phase:phase,aperture:aperture)
}
#let project(r,point)={
 let p=sub(point,r.origin)
 let d=r.distance-dot(r.view,p)
 if d<=r.near {(admitted:false,depth:d,point:none)} else {
  let s=if r.pinhole {r.focal/d} else {1}
  (admitted:true,depth:d,point:(s*dot(r.right,p),s*dot(r.up,p)))
 }
}
#let complex-face(r,z)={
 let (a,b)=r.phase
 (a*z.at(0)+b*z.at(1),a*z.at(1)-b*z.at(0))
}
#let primary-response(r,amplitude)={
 let (a,b)=complex-face(r,amplitude)
 let p=(a*a,b*b,(a+b)*(a+b))
 let d=r.aperture+p.sum()
 (primaries:p.map(x=>x/d),alpha:p.sum()/d,transmittance:r.aperture/d)
}
#let causal-interval(source,target,c:1)={
 let dt=target.at(0)-source.at(0)
 let dx=sub(target.slice(1),source.slice(1))
 let q=c*c*dt*dt-dot(dx,dx)
 (future:dt>=0,quadratic:q,admitted:dt>=0 and q>=0)
}
#let softmax-cross-entropy-differential(probabilities,reference,score-differentials)={
 assert(probabilities.len()==reference.len())
 assert(probabilities.len()==score-differentials.len())
 let d=score-differentials.first().len()
 range(d).map(k=>range(probabilities.len()).map(i=>(probabilities.at(i)-reference.at(i))*score-differentials.at(i).at(k)).sum())
}

// A supplied Lorentz metric/tetrad at the receiving event. The caller owns the
// geodesic and source event; this map reads the arriving contravariant null ray.
#let metric-pair(g,a,b)=range(a.len()).map(i=>range(b.len()).map(j=>a.at(i)*g.at(i).at(j)*b.at(j)).sum()).sum()
#let tetrad-reading(g,tetrad,ray)={
 let observer=tetrad.map(row=>row.at(0))
 let frequency=-metric-pair(g,ray,observer)
 let q=metric-pair(g,ray,ray)
 if frequency<=0 {(admitted:false,frequency:frequency,quadratic:q,direction:none)} else {
  (admitted:true,frequency:frequency,quadratic:q,
   direction:range(1,tetrad.len()).map(i=>metric-pair(g,ray,tetrad.map(row=>row.at(i)))/frequency))
 }
}
