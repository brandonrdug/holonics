#import "@preview/fletcher:0.5.8": diagram,node,edge
#let figure(name,width:90mm)=image("../../../rendered/receiver-engraving/"+name+".svg",width:width)
#let sequence-plates(title,eq,note)=[
#pagebreak(weak:true)
#title("25","Sequence is a cause of the fold and its subsequent conduct","The same six-site backbone and environment; changing the H/P order changes the energy landscape and kinetic return.")
#grid(columns:(1fr,1fr,1fr),gutter:8mm,align:center,
 [*Shared held starting chain*\ #v(2mm)#figure("seq_a_initial",width:80mm)],
 [*HHPHPH · one minimum-energy conformation*\ #v(2mm)#figure("seq_a_ground",width:80mm)],
 [*HPHHPH · one minimum-energy conformation*\ #v(2mm)#figure("seq_b_ground",width:80mm)],
)
#eq[$q=(r_0,…,r_5), quad r_0=0, quad r_1=(1,1,0), quad abs(r_(i+1)-r_i)^2=2, quad r_i!=r_j quad (i!=j)$]
#eq[$C_(s)(q)=sum_(0<=i<j<6, j>=i+2) 1_(s_i=s_j="H")1_(abs(r_i-r_j)^2=2), quad E_(s)(q)=-epsilon C_(s)(q), quad pi_(s)(q)=frac(b^(C_(s)(q)),Z_(s)(b))$]
#table(columns:(1fr,1fr,1fr),inset:4pt,stroke:1pt/4,
 [*Returned family*],[*HHPHPH*],[*HPHHPH*],
 [Anchored conformations],[12,711],[12,711],
 [Minimum-energy family],[16 configurations],[16 configurations],
 [Shortest permitted route to that family],[16 local moves],[20 local moves],
 [Minimum-energy probability at $b=2$],[$512/33391$],[$512/35911$],
)
#v(3mm)
#note([*Exact exterior physical chart.* FCC nearest-neighbor steps are the twelve permutations/signs of $(1,1,0)$; their cells have triangular faces. H/P supplies a declared hydrophobic/polar contact law. The first bond is held. Both inputs have four H and two P sites. The images show representatives of returned families, with a common receiver for the compact folds; they do not select a unique structure by its label. Color reads actual conditional mobility and contact-energy current through a fixed probe.])

#pagebreak()
#title("26","A fold is reached through actual kinetic passages","One shortest permitted source history for HHPHPH; each shown transition belongs to the full retained kinetic graph.")
#grid(columns:(1fr,1fr,1fr),gutter:8mm,align:center,
 [*Source · move 0*\ #v(2mm)#figure("fold_path_0")],
 [*A joined intermediate · move 8*\ #v(2mm)#figure("fold_path_8")],
 [*Arrival in the minimum-energy family · move 16*\ #v(2mm)#figure("fold_path_16")],
)
#eq[$P_(s)(q,q')=frac(1,48)min(1,2^(C_(s)(q')-C_(s)(q))), quad q' "is a legal local move"$]
#eq[$P_(s)(q,q)=1-sum_(q'!=q)P_(s)(q,q'), quad pi_(s)(q)P_(s)(q,q')=pi_(s)(q')P_(s)(q',q), quad p_(k+1)=P_s^T p_k$]
#grid(columns:(1fr,1fr),gutter:14mm,
 [*The sequence changes rates through physical contact.*
 #note([*Established-bounded.* The proposal clock has $4 times 12=48$ choices: four mobile sites and twelve FCC hops. A hop retains all bonds and exclusion; rejected proposals stay in the current state. At $beta epsilon=log 2$, every transition and population is rational. The enumerated graph is connected and has 79,476 directed legal moves.])],
 [*A short permitted history is a source-fibre representative.*
 #note([The displayed path is selected from legal histories by arrival length, with every edge having positive kinetic weight. It is not claimed to be the typical thermal trajectory. The full population, energy degeneracy, initial conditions and clock remain behind the view. No random sampling chooses the shown fold.])],
)
#v(4mm)
#note([Sources: #link("https://pubs.acs.org/doi/10.1021/ma00200a030")[Lau–Dill contact-model precedent]; #link("https://www.osti.gov/biblio/4390578")[Metropolis et al.]; the current construction uses its explicitly declared three-dimensional FCC chart.])

#pagebreak()
#title("27","Fold and ligand occupancy change the next available operation","The bound partner occupies a real site; a backbone hop that was permitted now returns to the held state.")
#grid(columns:(1fr,1fr),gutter:12mm,align:center,
 [*Unoccupied binding site · candidate hop has weight $1/96$*\ #v(2mm)#figure("ligand_free_annotated",width:82mm)],
 [*Ligand bound · the same hop has weight $0$*\ #v(2mm)#figure("ligand_bound_annotated",width:82mm)],
)
#eq[$r'_4 = r_4+(1,1,0)=r_5+d, quad d=(0,1,-1)$]
#eq[$E+S arrow.l.r^(k_("on")a(q))_(k_("off")) C arrow.r^(k_("cat")) E+P$]
#eq[$dot(x)=mat(-1,1,1;-1,1,0;1,-1,-1;0,0,1) mat(k_("on")a(q)E S;k_("off")C;k_("cat")C), quad x=(E,S,C,P)$]
#eq[$frac(d,d t)(E+C)=0, quad frac(d,d t)(S+C+P)=0$]
#grid(columns:(1fr,1fr),gutter:12mm,
 [#note([*Exact mechanochemical source.* A terminal ligand binds only in an unoccupied FCC direction. A bound fold move is retained only when the carried ligand also remains collision-free. The model keeps joint $(q,"free")$ and $(q,"bound",d)$ populations, product count and net substrate drawn. The displayed conservation equations apply to the reaction source; the experiment retains its substrate supply separately. Their exact ledger is $"bound"+"product"="drawn"$.])],
 [#note([*Proved-derived · Lean.* `ReactionCurrent` derives the conserved enzyme and substrate moieties from the actual stoichiometric source. The finite kinetic return distinguishes the two supplied sequences: $2^(-26)<Delta⟨P_24⟩<2^(-25)$. That small scalar difference accompanies a full retained difference in fold/occupancy history. Product is an expected turnover count, not a probability bounded by one.])],
)

#pagebreak()
#title("28","A causal thought chain is a changing operative body","Sequence, local organization and kinetic continuation are foundational HNN questions; the next operation consumes the actual returned state.")
#align(center,diagram(spacing:(10mm,12mm),node-stroke:black,node-fill:white,
 node((0,0),[Ordinary occurrence\ source + conditions],name:<source>,width:54mm,height:18mm),
 node((1,0),[Local current and contact\ $K,M,z,cal(F),kappa$],name:<body>,width:57mm,height:18mm),
 node((2,0),[Constitutive reaction\ admitted continuation],name:<reaction>,width:58mm,height:18mm),
 node((3,0),[Emission + successor\ $y,cal(A)^+,cal(P)$],name:<return>,width:55mm,height:18mm),
 edge(<source>,<body>,"->"),edge(<body>,<reaction>,"->"),edge(<reaction>,<return>,"->"),
 node((1,1),[Returned comparison\ observation + producing passage / cut],name:<compare>,width:72mm,height:18mm),
 edge(<return>,<compare>,"->",bend:25deg),
 edge(<source>,<compare>,[observation],"->",bend:-25deg),edge(<compare>,<body>,[Eros: develop],"->"),
))
#v(3mm)
#grid(columns:(1fr,1fr),gutter:14mm,
 [*One energy face does not determine the next fold.*
 #v(2mm)
 #grid(columns:(1fr,1fr),align:center,
 [#figure("fold_equal_a",width:59mm)\ $C(q_A)=1$],
 [#figure("fold_equal_b",width:59mm)\ $C(q_B)=1$],
 )
 #eq[$op("Pr")(C'=2|q_A)=0, quad op("Pr")(C'=2|q_B)=1/48$]
 #note([*Exact separator.* Including all self loops and rates, the two equal-contact states have different next-bin returns. Thus energy/contact count alone cannot close this kinetic dynamics. Equal fold and free/bound marginals can likewise conceal different binding flux.])],
 [*The operative chain carries its joining state.*
 #eq[$X arrow.l W_f arrow.r Y, quad Y arrow.l W_g arrow.r Z, quad W_(g ∘ f)=W_f times_Y W_g$]
 #eq[$(cal(A),o) arrow.r (y,cal(A)^+,cal(P)), quad q T_i=U_i q$]
 #eq[$z=(p,c), quad phi(z)=(c-p,c,p), quad hat(v)=c+M phi(z)$]
 #note([*HNN construction.* The shared object is caused source incidence, current, reaction and successor. A molecular codec may supply chemical constraints; text and acoustics supply their own situated sections. A causal thought trace retains the actual joins, conditions and changes that determine later conduct. Verbal output is one receiver of that structure.])
 #eq[$mu'=T mu, quad nu'=T nu+T_("emit")mu$]
 #note([The kinetic return tracks occupation and labeled output. Unbinding and catalysis can restore the same enzyme state while emitting different outputs.])
 #v(3mm)#note([*Concrete handoff.* Reuse normal-wave source action and continuation, the condition neighborhood, and the retained producing comparison. Bind exposure/codec associations to the actual source/current and material cut. The existing section-pair development port does not by itself attach an earlier prediction’s bounded joint to its returned observation. The revised AC blueprint names that remaining binding; this research does not restart the paused implementation.])],
)
]
