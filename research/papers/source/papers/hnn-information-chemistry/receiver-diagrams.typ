#import "@preview/cetz:0.3.4"
#let event-cone()=cetz.canvas(length:13mm,padding:1/4,{
 import cetz.draw: *
 let ink=black
 for k in range(1,9) {
  let t=k/3
  line((t - 3,t),(3-t,t),stroke:(1pt/5)+gray)
 }
 line((-3,0),(0,3),(3,0),stroke:(3pt/5)+ink)
 line((-1,0),(-1,3),stroke:(paint:ink,thickness:1pt/3,dash:"dashed"))
 line((1,0),(1,3),stroke:(paint:ink,thickness:1pt/3,dash:"dashed"))
 for p in ((-1,2),(1,2)) {
  circle(p,radius:1/20,fill:black,stroke:none)
  line(p,(0,3),stroke:(3pt/4)+black,mark:(end:">"))
 }
 line((-2,0),(-1,1),(0,3),stroke:(1pt/2)+black,mark:(end:">"))
 circle((0,3),radius:1/16,fill:black,stroke:none)
 circle((2,2),radius:1/14,fill:white,stroke:(1pt/2)+black)
 content((0,10/3),[$R$])
 content((5/2,7/3),text(size:9pt)[outside this cone])
 content((-2,4/3),text(size:9pt)[$g(k,k)=0$])
 content((0,-1/3),text(size:9pt)[received clock cuts])
})
#let pinhole()=cetz.canvas(length:19mm,padding:1/4,{
 import cetz.draw: *
 let source=range(4).map(t=>(t,1+t/2))
 line(..source,stroke:(4pt/5)+black)
 line((-7/4,-1),(1/2,-1),stroke:(4pt/5)+black)
 for t in range(4) {
  let p=source.at(t);let q=(-t/(1+t/2),-1)
  line(p,q,stroke:(1pt/3)+black,mark:(end:">"))
  circle(p,radius:1/35,fill:black,stroke:none)
  circle(q,radius:1/35,fill:black,stroke:none)
 }
 line((-1/2,0),(-1/12,0),stroke:2pt+black)
 line((1/12,0),(1,0),stroke:2pt+black)
 content((-3/4,0),text(size:9pt)[pinhole])
 content((2,3),text(size:9pt)[source line])
 content((-2,-1),text(size:9pt)[receiver])
})
#let receiver-slice()=cetz.canvas(length:11mm,padding:1/4,{
 import cetz.draw: *
 for i in range(7) {
  let t=i/6
  let p=(t*3,t*t)
  line(p,(p.at(0)+1/2,p.at(1)+2),stroke:(1pt/3)+black)
 }
 line((0,0),(3,1),stroke:(3pt/4)+black)
 line((1/2,2),(7/2,3),stroke:(3pt/4)+black)
 content((3/2,-1/3),text(size:9pt)[one receiver cut])
 content((2,10/3),text(size:9pt)[transported cut])
})
