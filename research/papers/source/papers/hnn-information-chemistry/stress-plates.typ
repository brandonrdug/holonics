#import "@preview/fletcher:0.5.8": diagram,node,edge
#import "@preview/cetz:0.3.4": canvas,draw

#let stress-plates(title,eq,note)=[
#pagebreak()
#title("16","Stress and current cross the same material boundary","Fluid traction, electromagnetic work and capacitive storage meet through their actual ports.")
#align(center,diagram(
 spacing:(24mm,13mm),node-stroke:black,node-fill:white,
 node((0,0),[$T_("fluid")$\ momentum, pressure, shear],name:<fluid>,width:67mm,height:20mm),
 node((1,0),[$Sigma$\ oriented contact / charge surface],name:<surface>,width:67mm,height:20mm),
 node((2,0),[$F_(mu nu),j^mu$\ electric and magnetic current],name:<em>,width:67mm,height:20mm),
 node((1,1),[$E_("stored")+Q$\ returned energy and heat],name:<energy>,width:67mm,height:20mm),
 edge(<fluid>,<surface>,[$T n, quad t dot u$],"<->"),
 edge(<surface>,<em>,[$Delta V, I$],"<->"),
 edge(<surface>,<energy>,[$P_("port")$],"->"),
))
#v(4mm)
#grid(columns:(1fr,1fr),gutter:15mm,
 [*The fluid return retains rotational momentum.*
 #eq[$rho D_t u=-nabla p+nabla dot tau+j times B+f, quad tau=2mu D, quad D=frac(nabla u+(nabla u)^T,2)$]
 #eq[$partial_t u=nu Delta u+u times op("curl")u-nabla(p/rho+frac(abs(u)^2,2))+f/rho$]
 #note([*Conditional physical chart.* Incompressible constant-density Newtonian fluid; the second line uses force-inclusive $f$. Viscous heat is $2mu D:D$. Maxwell stress adds both traction and energy flow; a surface normal alone supplies neither.])],
 [*The same boundary can store an electrical difference.*
 #eq[$Q_S=integral_S D_("EM") dot n, quad I_S=integral_S j dot n, quad Delta Q=C Delta V$]
 #eq[$j=sigma(E+u times B), quad P_("Ohm")=integral_V frac(abs(j)^2,sigma)$]
 #note([*Conditional circuit reduction.* The closed boundary reads enclosed free charge; the charge/voltage comparison also needs the medium and boundary law. Here $sigma>0$ is scalar. A changing magnetic flux requires the full path emf. Lightning adds ionization, conductivity evolution and moving leader incidence. The existing leader construction supplies that incidence question.])],
)
#v(4mm)
#eq[$E=frac(1,2)(C v^2+L^(-1)phi^2), quad e=nabla E, quad dot(x)=s-G e, quad dot(E)=e dot s-e dot G e, quad dot(Q)=e dot G e, quad frac(d,d t)(E+Q)=e dot s$]
#note([*Proved-derived · Lean.* `PortEnergyHeat` derives the last balance from coordinate derivatives and the storage law. $x=(v,phi)$ has conjugate $e=(C v,L^(-1)phi)$; the supplied source and conductance coefficients carry the corresponding units. Contact drag uses the same work/return pattern with its own constitutive law.])

#pagebreak()
#title("17","A receiver reads energy, momentum and tension together","Einstein's source retains energy and stress; the observer changes their measured faces.")
#eq[$G^(mu nu)+Lambda g^(mu nu)=frac(8pi G,c^4)T^(mu nu)_"total", quad nabla_mu T^(mu nu)_"total"=0$]
#align(center,diagram(spacing:(9mm,13mm),node-stroke:black,
 node((0,0),[$T_"fluid"+T_"EM"+T_"other"$\ retained constitutive sectors],name:<tensor>,width:77mm,height:19mm),
 node((1,0),[$g, nabla, "curvature"$\ field equation + boundary data],name:<metric>,width:77mm,height:19mm),
 node((2,0),[$u_R, n_R, Sigma_R$\ local energy / flux receiver],name:<receiver>,width:77mm,height:19mm),
 edge(<tensor>,<metric>,"<->"),edge(<metric>,<receiver>,"->"),
))
#v(3mm)
#eq[$T^(mu nu)_"fluid"=(e+p)u^mu u^nu+p g^(mu nu)+pi^(mu nu), quad g(u,u)=-1 quad (c=1, pi="shear stress")$]
#eq[$J^(lambda mu nu)=x^mu T^(lambda nu)-x^nu T^(lambda mu), quad partial_lambda J^(lambda mu nu)=T^(mu nu)-T^(nu mu)+x^mu f^nu-x^nu f^mu$]
#note([*Proved-derived · Lean.* The angular-current identity assumes $partial_lambda T^(lambda nu)=f^nu$ and retains antisymmetric stress. Symmetric stress and zero divergence cancel them in the inertial derivative chart. Spin may contribute an additional current; curved spacetime needs the corresponding connection and symmetry/Killing field for a conserved global charge.])
#v(4mm)
#grid(columns:(1fr,1fr),gutter:12mm,
 [*A concrete observer change separates dark-sector proposals.*
 #eq[$T=op("diag")(e,p_1,p_2,p_3), quad u_R=(5/3,4/3,0,0), quad n_R=(4/3,5/3,0,0)$]
 #eq[$T(u_R,u_R)=frac(25e+16p_1,9), quad T(u_R,n_R)=frac(20(e+p_1),9)$]
 #table(columns:(auto,1fr,1fr),inset:4pt,stroke:1pt/4,
 [*Source chart*],[*Energy*],[*Mixed reading*],
 [Dust: $p_j=0$],[$frac(25e,9)$],[$frac(20e,9)$],
 [Vacuum: $p_j=-e$],[$e$],[$0$],
 )],
 [*Tension is a testable stress choice.*
 #eq[$e+sum_(j) p_j=cases(e & "dust", -2e & "vacuum", 0 & "axial: "p_1=-e, p_2=p_3=0)$]
 #note([*Interpretation.* Investigate dark contributions through density, anisotropic stress, exchange and receiver fibres. Vacuum negative pressure and clustering matter have different transported readings. The physical identifications owe lensing, expansion and structure-formation returns; one scalar “tension” cannot identify all three.])
 #v(2mm)#eq[$E^2=c^2 abs(p)^2+(m_0c^2)^2, quad p=0, E>=0 arrow.r E=m_0c^2$]
 #note([*Proved-derived · Lean.* The positive rest branch follows from the existing mass-shell owner with $m_0>=0,c>0$.])],
)
#v(3mm)
#note([Sources: #link("https://www.damtp.cam.ac.uk/user/tong/gr/gr.pdf")[Tong, General Relativity]; #link("https://pdg.lbl.gov/2025/reviews/rpp2025-rev-dark-matter.pdf")[PDG dark matter]; #link("https://pdg.lbl.gov/2025/reviews/rpp2025-rev-dark-energy.pdf")[PDG dark energy]. The existing Einstein–fluid interface derives conservation from the field equation, Bianchi identity and metric compatibility.])

#pagebreak()
#title("18","Quantum paths retain amplitudes and interaction rules","A knotted material carrier, a circuit graph and a Feynman graph have different edges; their compositional maps can be explicit.")
#grid(columns:(1fr,1fr),gutter:16mm,
 [*A local complex wave has a reversible completion.*
 #eq[$R=mat(3/5,-4/5;4/5,3/5), quad R^dagger R=I$]
 #eq[$V=mat(15/16,-sqrt(31)/16;sqrt(31)/16,15/16), quad V^dagger V=I$]
 #align(center,diagram(spacing:(12mm,10mm),node-stroke:black,
  node((0,0),[$Psi$\ carried channel],name:<in>,width:30mm),
  node((1,0),[$V$\ system + environment],name:<joint>,width:40mm,height:17mm),
  node((2,0),[$frac(15Psi,16)$\ retained channel],name:<out>,width:33mm),
  node((1,1),[$frac(sqrt(31)Psi,16)$\ environment return],name:<env>,width:47mm),
  edge(<in>,<joint>,"->"),edge(<joint>,<out>,"->"),edge(<joint>,<env>,"->"),
 ))
 #v(3mm)#note([*Proved-derived.* The same finite scattering map preserves classical complex wave power and quantum amplitude norm. Reading the discarded port as physical heat additionally requires a reservoir and its energy law. $sqrt(31)$ is derived from $16^2-15^2$, not a fitted rendering constant.])],
 [*A propagator and a vertex make the graph executable.*
 #v(4mm)
 #align(center,canvas({
   import draw: *
   set-style(stroke:7pt/10)
   line((0,0),(2,1));line((0,2),(2,1));line((4,1),(6,0));line((4,1),(6,2))
   for i in range(16) {let x=2+i/8;let y=1+if calc.rem(i,2)==0 {1/8} else {-1/8};if i==0 {line((2,1),(x,y))} else {line((x - 1/8,1+if calc.rem(i,2)==0 {-1/8} else {1/8}),(x,y))}}
   line((31/8,7/8),(4,1))
   circle((2,1),radius:3/50,fill:black);circle((4,1),radius:3/50,fill:black)
   content((1,12/5),[$psi,overline(psi)$]);content((5,12/5),[$psi,overline(psi)$]);content((3,7/20),[$D_(mu nu)$]);content((2,33/20),[$-upright(i)e gamma^mu$]);content((4,33/20),[$-upright(i)e gamma^nu$])
 }))
 #eq[$G=G_0+G_0 Sigma G, quad G=(G_0^(-1)-Sigma)^(-1)$]
 #note([*Conditional.* The drawn QED exchange has fermion lines, two coupling vertices and a photon propagator. It is a term in an amplitude expansion, not an electron trajectory or a literal knot crossing. The displayed Dyson relation is an exact inverse identity where the inverses exist; its iterated series also needs convergence or a declared formal-series chart.])],
)
#v(2mm)
#table(columns:(1fr,1fr,2fr),inset:3pt,stroke:1pt/4,
 [*Sector*],[*Connection / fibre*],[*What the common carrier preserves*],
 [Electromagnetic],[$U(1)$],[Oriented paths, joins and returned face holonomy],
 [Weak / electroweak],[$S U(2)_L times U(1)_Y$],[Sector representation and Higgs coupling remain attached],
 [Strong],[$S U(3)$],[Color representation, vertices and gauge constraints remain attached],
 [Gravity],[Frame / Spin connection],[Metric, stress-energy source and causal receiver remain attached],
)
#v(3mm)
#note([*Existing formal carrier.* `HolonicFourForceSectorCarrier` and gauge-covariance owners retain the common incidence and ordered transport; they do not erase the different actions or quantize gravity. A real Lorentzian stress source from complex fields is derived from a real action, with its conjugate channels retained. The holomorphic C³ fluid chart does not become that physical source merely by taking its real part.])
#v(3mm)
#note([Sources: #link("https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf")[Tong, Quantum Field Theory, §§1.3, 3.4, 6]; Holonics finite quantum transport, Yang–Mills covariance and four-force owners. ETP compares actual substitution/composition laws, beyond a shared graph silhouette.])
]
