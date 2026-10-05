#import "../../lib/elements.typ": elements-paper, proof-block, by-rule, by-blue, by-muted
#import "../../lib/holonics.typ": source-note, evidence-note, reader-note

#let source(path, label) = link("https://github.com/brandonrdug/holonics/blob/3a242c99/" + path, label)
#let current-source(path, label) = link("https://github.com/brandonrdug/holonics/blob/9a62a68515ebc824d583539e53b1a2d5973a82a3/" + path, label)
#let route(body) = source-note(body)
#let reading(title, status, body) = block(above: 8pt, below: 6pt)[
  *#title.* #text(size: 8.5pt, fill: by-muted)[#status] #linebreak()
  #body
]

#show: elements-paper.with(
  title: [HNN and Athena: one constitution, its motion and its receivers],
  subtitle: [Geometric dynamics on a network · Asymmetric potential model],
  authors: [Holonics · Brandon's framework · Codex consolidation],
  date: [4 October 2026 · final morning source and consumer edition],
  abstract: [
    Complex parametrons and helical pair contacts compose one continuing Holon.
    This edition joins nine geometric proofs and statically checked host restore
    with material work, future observability, folded/nonlinear transport and exact
    decoder checks. HNN learning and Athena's joint output consume these relations;
    runtime acceptance remains open. Proofs, executable owners, unformalized
    derivations and proposed joins stay graded. This assembly establishes neither
    a unified physical theory nor the Riemann hypothesis.
  ],
)

#set table(inset: 5pt, stroke: 0.4pt + by-rule, align: left)
#set par(spacing: 0.55em)

= Architecture and the morning result

Complex parametron rings store, oscillate and lock; helical pair contacts couple
their motion and address the reached material. The constitution determines
storage and modes. Charts supply geometry and receiver metrics; navigators
carry keys, phase and clock. A participating
receiver compares the motion that reached it. Its paired return carries the
comparison covector to the producing material, where certified deposition
changes the constitution while continuation holds the carried momentum.
Retention keeps the quotient sufficient for admitted future actions.

HNN builds these relations at scale. Athena is their intended useful joint
release: source-conditioned motion with compatible keys and fibre, followed by
autonomous continuation and cold restore. The source join has formal geometry
and Rust type checks; output and executed continuation retain their gates.

The elementary vocabulary is fixed by
#source("docs/ELEMENTARY_OBJECTS.md", [ELEMENTARY_OBJECTS]). A Holon is its
law and ports; its ket is an admitted motion, and a state is a point on that
motion. The subtitle adds no objects.

$ H = (K, partial_A; Pi; cal(D); cal(E); G_"nav"; pi). $

The complex and connection carry incidence. A port selects exchange variables
at a chosen modelling cut; effort and flow pair as power. The Dirac interconnection cancels internal power. Element relations
carry storage, resistance, sources, active relations and pumps. Navigators
carry configuration, clocks and phase lifts. Restrictions carry the scale
square or its exact defect. A cut presents current, storage, contemporary
material, frame, metric, incidence, clock and unresolved fibre; it need not
retain a list of preceding cuts.

#table(
  columns: (1fr, 3fr),
  table.header([*Status*], [*Scope in this edition*]),
  [Proved, checked Lean], [Nine additions are integrated in their named owners with complete-owner/import receipts and stated hypotheses.],
  [Executable, inspected], [The Rust owner and consumer exist; the V3 static check supplies no runtime or native learning result.],
  [Derived, unformalized], [The displayed calculation proves the relation under its hypotheses; no new Lean or production join is inferred.],
  [Proposed], [An explicit derivation or consuming implementation is still required.],
)

#reading([Native contact-C continuation], [Executable, inspected], [
  `Word::open_source` admits the source on its producing constitution.
  `compare_contact_storage` compares actual receiving anchors, pulls the
  covector back through their producing solves and forms a reached contact-C
  deposit. `ContactCut::continue_deposited` commits that deposit, reads its
  same-state work and opens `Word::continuing` with the same end change,
  pump phase and next clock. The focused example keeps K, D, coupling,
  ring, pump and source/receiver declarations fixed. Its lattice counterpart
  retains changed solve remainders when a representative remains unresolved.
])

#route([
  #source("crates/holonics/src/hnn/word/continuation.rs", [Word and ContactCut]);
  #source("crates/holonics/src/hnn/reference/continuation.rs", [focused consuming tests]);
  #source("docs/HNN_FORMULA.md", [HNN formula]). This focused path retains its
  scope; the newer host passage join below is a separate source owner.
])

Local main remains `3a242c99`; the pinned October 4 public base is
#link("https://github.com/brandonrdug/holonics/commit/9a62a68515ebc824d583539e53b1a2d5973a82a3", [`9a62a685`]).
The accepted 45-path candidate joins the geometric owners and cold-restore V3
on that same base; it is local, not a public commit or complete Cargo checkout.
All eight Rust bodies match the completed static check's sealed sources.
Owner/import checks share 31 unchanged repository source bindings with 9a.
Cached dependencies were sealed, not rebuilt; no whole Framework rebuild.
The unchanged-source Frame metadata postcheck had a CPU cap, no outer wall timeout.
Current public
#current-source("crates/holonics/src/hnn/reference.rs", [Reference]) defaults to
carry at zero absorption;
#current-source("crates/holonics/src/hnn/word.rs", [ChainedBalance]) reads the
one-baseline opening and declared supply. Existing
#current-source("lean/Holonics/HNN/ChainedBalance.lean", [Lean chain laws]) keep
their stated hypotheses.

V3 extends the #current-source("crates/holonics/src/hnn/reference/passage.rs", [public passage owner])
with the bounded Arrived operands, held address-reader kinds, declaring phases,
handle counter and optional/no-moment state. Version 2 refuses unversioned
passages, exhausted handles and invalid cursors; empty windows require cursor
zero. Normal host library, cfg(test) library and `resident_cold_restore`
integration target passed static checks with zero compiler errors. Three
integration and six unit regressions are prepared, not executed. Immediate
close, ingest→carry-out→close, no-moment continuation and checksum-valid typed
refusal remain runtime gates; the held-kind witness is serialization-only.
Open pending/staged handles, stopped deposits and multiple moments refuse.
Card `ExposedResident::continuing` still defaults to `None`; whole card restore,
refusal-state publication and signed reflected phase remain consumer joins.
Historical pre-reset code locates provenance rather than authorizing restoration.

Distributed coupling remains an actual element relation; it need not become
a device endpoint. Observation belongs to a participating receiver, sensitivity
to its derivative, and resonance to a declared mode/drive relation. A linear
receiving chart reads phase cross terms in $abs(Sigma_i psi_i)^2$; it does not
superpose solutions of nonlinear evolution. Affinity retains its declared
receiving pairing or metric.

= Material, chart and asymmetric potential

For one quadratic storage chart, declare positive Hermitian $Q_Theta$,
skew $J$, resistance $R=R^*>=0$, active relation $L$ and input $B u$:

$
  E_Theta(x)=1/2 x^* Q_Theta x, quad e=Q_Theta x,
  quad dot(x)=(J-R+L)e+B u,
$
$
  dot(E)_Theta=-e^*R e+op("Re")(e^*L e)
  +op("Re")(e^* B u)+1/2 x^* dot(Q)_Theta x.
$

The skew effort-to-flow term has zero real power. An active relation and changing
material retain their supplied work; passivity requires their actual bound.
The mechanical contact specialization stores
$E=1/2(w^* C w+u^* K u)$ with $w=dot(u)$.
Here C is inertia/inductance-like under the declared port realization.

#route([
  #source("lean/Holonics/Holon/Deposition.lean", [learned_energy_balance]);
  #source("docs/HELICAL_GEOMETRY.md", [pair constitutive variations]);
  #source("crates/holonics/src/hnn/constitution.rs", [native constitution]).
])

The named Lean balance is over real matrices with transpose. The displayed
Hermitian balance is a derived analytical extension; no checked complex
realification bridge is asserted here.

#reading([Moving chart covariance], [Derived, with existing formal bridges], [
  Let $dot(x)=A x+s$ and $E_R=1/2 x^*G_R x$. For an invertible differentiable
  rechart $x'=P x$, use
  $
    A'=P A P^(-1)+dot(P)P^(-1), quad s'=P s,
    quad G_R'=(P^(-1))^*G_R P^(-1).
  $
  The source-free rate form is
  $Sigma_R=A^*G_R+G_R A+dot(G)_R$, and
  $Sigma_R'=(P^(-1))^*Sigma_R P^(-1)$.
])

#proof-block([
  Differentiate $P^(-1)P=I$. In $dot(G)_R'$ the two derivatives of the
  inverse cancel the two $dot(P)P^(-1)$ terms supplied by $A'$.
  The remaining form is the displayed congruence. Energy and the rate form's
  counts of positive, negative and zero directions survive the rechart.
  These are instantaneous source-free power signs, not a long-time
  contraction, asymptotic neutrality or persistent eigendirection theorem.
  A changed physical receiver or material
  law is a different operation.
])

At unchanged state, material work is
$W_"dep"=E_(Theta')(x)-E_Theta(x)=1/2 x^*(Q_(Theta')-Q_Theta)x$.
With simultaneous state transport, compare $E_(Theta')(P x)$ instead.
A pure rechart has zero material work.

#route([
  #source("research/records/2026-09-26_THE_SHADOW_IS_THE_RECEIVERS_KERNEL_AND_THE_EGG_IS_TWO_RINGS_IN_RELATIVE_MOTION.md", [shadow/egg record, section 5]);
  #source("lean/Holonics/Geometry/Motion.lean", [moving-metric reading]);
  #source("lean/Holonics/Foundation/CausalChord.lean", [congruence bridge]).
])

#reading([Finite endpoint work], [Proved in Motion; owner and import checked], [
  For $x_1=T x_0+b$, $y_k=P_k x_k$, $V_k=P_k^(-1)$, put
  $
    F=T^T G_1 T-G_0, quad hat(F)=V_0^T F V_0,
  $
  $
    2 Delta E=x_0^T F x_0+2x_0^T T^T G_1 b+b^T G_1 b.
  $
  The chart cancellation needs the ending left inverse; the affine cross
  terms need symmetric $G_1$. The two lemmas are integrated in Motion;
  its complete owner and the combined import passed. The gain-order equivalence,
  complex extension and native physical-work decoder retain their own joins.
  The source cross term and self-energy both remain.
])

#reading([A nonlinear tube section], [Actual section derivative and area/current checked; full continuum join derived], [
  On a C3 unit-speed embedded spine $c(s)$ take a proper C2 frame
  $(t,d_1,d_2)$, curvatures $kappa_1,kappa_2$ and normal-frame rate $Omega$.
  On $u^2+v^2<1$, set $h=1+epsilon u$,
  $q_1=a u h$, $q_2=b v h$, $X=c+q_1 d_1+q_2 d_2$ and
  $
    nu=1-kappa_1 q_1-kappa_2 q_2, quad
    p_1=partial_s q_1-Omega q_2, quad p_2=partial_s q_2+Omega q_1.
  $
  The actual derivative columns give
  $
    F=mat(t,d_1,d_2) mat(nu,0,0; p_1,a(1+2epsilon u),0;
      p_2,b epsilon v,b h), quad g=F^T F,
  $
  $
    J=nu a b(1+epsilon u)(1+2epsilon u), quad
    partial_u X times partial_v X=a b(1+epsilon u)(1+2epsilon u)t.
  $
  Positive a,b, $2 abs(epsilon)<1$ and $nu>0$ give local regularity;
  global embedding and seam gluing require additional conditions. Taper
  and twist remain in the metric through $p_1,p_2$. The Euclidean interior
  metric is locally flat; boundary curvature is a distinct reading.
  No material law follows from the shape.

  The area/current algebra imports the actual FrameTransport owner. Five
  further accepted declarations construct the actual polynomial section
  `HasFDerivAt`, identify its two `fderiv` columns, and consume them in
  `tube_section_actual_area` and `tube_section_actual_flux`. At fixed s,
  c, frame, a, b and epsilon are constant; this derivative needs no positivity
  or spine regularity assumption. All five audits have standard axioms only,
  no warnings, errors or `sorryAx`; integration in FrameTransport is complete.
  #block(breakable: false)[
  For a moving chart
  $w=partial_tau X$, density $rho$ and continuity current j, the derived
  relative section flux is
  $hat(j)^s=a b(1+epsilon u)(1+2epsilon u)(j-rho w) · t$.
  The longitudinal derivative, full 3D cofactor/Piola and moving continuity
  theorem, global embedding and native physical decoder remain separate joins.
  ]
])

#route([
  #source("lean/Holonics/Geometry/FrameTransport.lean", [existing proper-frame owner]);
  #source("lean/Holonics/Transport/ChangingReceiver.lean", [existing one-dimensional continuity owner]);
  #source("docs/HELICAL_GEOMETRY.md", [screw, helix and material placement]).
])

#reading([Asymmetry and integrability], [Derived, unformalized], [
  A scalar stored potential may satisfy $V(-u)!=V(u)$ while its smooth
  Hessian remains symmetric. A directed force $F(u)=A u$ is a gradient
  on the full simply connected chart only if $A=A^T$. A configuration
  force has power $v · F(u)$, so skew A need not be power-neutral:
  $A=mat(0,-1;1,0)$, $u=(1,0)$, $v=(0,1)$ supplies power 1.
  A skew effort-to-flow map cancels its own paired power; a gyroscopic
  velocity force requires that separate justified pairing. An asymmetric stored
  potential, directed active relation and asymmetric receiver comparison
  are thus rival constructions. For a pair $V=Phi(Q)$,
  $nabla V=Phi'(Q)nabla Q$ and
  $nabla^2 V=Phi''(Q)nabla Q ⊗ nabla Q+Phi'(Q)nabla^2Q$.
])

#reading([A stateful coupled specialization], [Proposed material law; derived variation], [
  On one declared contact compare coframed configurations
  $Delta=u_i-T_(i arrow.l j)u_j$ and select the typed face $z=b^T Delta$.
  An explicit asymmetric storage is
  $
    V_Theta(z)=kappa z^2/2+alpha z^3/3+beta z^4/4,
    quad kappa>0, beta>0, alpha != 0,
  $
  $
    V'_Theta=kappa z+alpha z^2+beta z^3,
    quad V''_Theta=kappa+2alpha z+3beta z^2.
  $
  The quartic bounds V below; the Hessian is symmetric but need not be
  positive everywhere. For $[z]=U$, coefficient units are
  $[kappa]=E/U^2$, $[alpha]=E/U^3$, $[beta]=E/U^4$.
  Contact forces are $-b V'(z)$ and $T^T b V'(z)$; moving b or transport
  adds its own work. This nonlinear specialization is not current native code.

  For fixed material in canonical coordinates, take
  $E_Theta=1/2 p^T C^(-1)p+Sigma V_Theta(z)$.
  The shears $u'=u+h C^(-1)p$, $p'=p-h nabla V_Theta(u')$ compose a
  symplectic nonlinear move on the stated Euclidean domain. Keep the finite
  energy defect explicitly; symplecticity alone does not close a power balance.
  The historical shear reference is inspiration, not restored machinery.

  The continuing relation is evolution, participating comparison $log R$,
  paired return through producing operands, reached certified deposition,
  then evolution under changed material. Current public contact-C return holds
  $C' w'=C w$ and prices $E_(Theta')(u,w')-E_Theta(u,w)$.
  General nonlinear coefficients and physical geometry updates remain proposed.
  Physical growth also owes gluing with $partial^2=0$, initial storage and a
  future-sufficient quotient. A pure rechart performs no material update.

  Fractal recursion requires a declared navigator family and restriction/scale
  square, for example $G_(w a)=r_a compose G_w$ on its admitted domains,
  with clock transport and actual first-arrival fibres. Material-dependent
  maps may change after contact; not every nonlinear map is fractal.
])

#route([
  #current-source("crates/holonics/src/hnn/word/continuation.rs", [held-momentum contact return]);
  #source("research/records/2026-09-14_FRACTAL_GEOMETRY_BELONGS_TO_THE_INTERACTING_FIELD.md", [actual nonlinear reference]);
  #source("lean/Holonics/Computation/HolonicRecurrentEcology.lean", [first-arrival laws]).
])

#reading([Exact dimensions and decoder], [Derived; exact witnesses checked; native map proposed], [
  Source/receiver clock occurrences remain distinct in
  #source("lean/Holonics/Physics/HolonicTypedOriginDimensions.lean", [typed dimensions]).
  For $[s]=L$ and dimensionless u,v, derivative columns have units $(1,L,L)$,
  $[J]=L^2$, $[g_(s s)]=1$, $[g_(s u)]=L$, $[g_(u u)]=L^2$.
  With $[rho]=Q/L^3$, $[j]=Q/(L^2 T)$, $[w]=L/T$, all pulled-back
  continuity terms have $Q/(L T)$. Equal units do not prove continuity.

  Under $X_"phys"(s,u,v)=ell_"ref" X_"num"(s/ell_"ref",u,v)$,
  $F_"phys"=ell_"ref" F_"num" op("diag")(1/ell_"ref",1,1)$,
  $J_"phys"=ell_"ref"^2 J_"num"$; section flux scales by $Q_"ref"/T_"ref"$.
  A declared clock map with $alpha=d t_S/d tau_R$ gives
  $j_R-rho w_R=alpha(j_S-rho w_S)$ only when every rate uses that same map.

  For the declared torsional realization,
  $C_"phys"=E_"ref" T_"ref"^2 C_"num"$, $K_"phys"=E_"ref" K_"num"$,
  $D_"phys"=E_"ref" T_"ref" D_"num"$, $G_(c,"phys")=G_(c,"num")/(E_"ref" T_"ref")$;
  rate divides by $T_"ref"$ and torque waves multiply by $E_"ref"$.
  Then $E_"phys"=E_"ref" E_"num"$. Finite charts instead use
  $T_"phys"=S_1 T_"num" S_0^(-1)$ and $b_"phys"=S_1 b_"num"$,
  retaining affine source cross/self work. Their encode/evolve/decode square
  is proposed; the native solve currently consumes exact abstract coefficients.

  The bounded rational checker rejects floats, incompatible units/roles,
  reversed orientation, doubled inertia normalization, source-family area
  1 versus $45/32$, substituted clocks and phase branch/carry. Its exact receipt
  is 3,003,190 ns with peak RSS 16,276 KiB under the unchanged 8-second cap.
  The executed symbolic derivation is Lean product/smul/ring; optional SymPy
  was not run and no software was installed.
])

= The torsional contact and the whip boundary

#reading([Exact torsional midpoint], [Executable owner and existing Lean balance], [
  Angle u and rate w meet two oppositely oriented wave ports a,b of
  impedance $1/G_c$. At step h, with inertia C, stiffness K and damping D,
  $
    M=2 C+2 h/G_c+h D+h^2 K/2,
    quad omega=(h(a-b)+2 C w-h K u)/M,
  $
  $
    u^+=u+h omega, quad w^+=2omega-w,
    quad a_"out"=a-2omega/G_c, quad b_"out"=b+2omega/G_c,
  $
  $
    E^+-E+h D omega^2
    =(h G_c/4)(a^2+b^2-a_"out"^2-b_"out"^2).
  $
])

#proof-block([
  Since $w^++w=2omega$ and $u^+-u=h omega$, the storage difference is
  $h omega[2C(omega-w)/h+K(u+h omega/2)]$.
  The solve replaces the bracket by $a-b-(2/G_c+D)omega$.
  Expanding the two outgoing squared waves gives that same port work.
  The vector/lattice law carries its actual solve and split defects.
])

#route([
  #source("crates/holonics/src/hnn/propagation.rs", [transit_solve, transit_update, transit_defect]);
  #source("lean/Holonics/HNN/Propagation.lean", [transit_balance]).
  Configured C1/C4 exact-state replay is a demonstration of this law;
  it is not learned material or a new Rust execution.
])

The periplus carries moving local charts and their actual joins. A Smith
face $Gamma=(Z-Z_0)/(Z+Z_0)$ belongs to a declared impedance port.
Its revolution is a receiver immersion, preserving transverse hand and
ordered holonomy beneath the rendering. A drawn chart does not by itself
construct intrinsic curvature or a spacetime metric.

#reading([Rod boundary work], [Derived, unformalized continuum specialization], [
  For a smooth objective Cosserat rod with centreline r, material frame Q,
  $v=r_t$, $Q_t Q^T=op("hat")(Omega)$, total force n and couple m, pair
  $p_t=n_s+f$ and $l_t=m_s+r_s times n+c$ with v and $Omega$.
  Material mass and body inertia are fixed; the objective strain energy
  has no explicit time dependence. Compatible strain kinematics give
  $
    partial_t e=partial_s(n · v+m · Omega)
       +f · v+c · Omega-d,
  $
  where d is the constituted nonnegative strain-rate dissipation.
])

#proof-block([
  With elastic stresses $n_"el",m_"el"$, stored strain power is
  $n_"el" · (v_s-Omega times r_s)+m_"el" · Omega_s$,
  equal to total stress power
  $n · (v_s-Omega times r_s)+m · Omega_s-d$.
  Its triple product cancels the one in angular momentum balance.
  The remaining endpoint term is the derivative of wrench power.
  The integrated law keeps initial storage, handle work, tip transfer and
  acoustic reception. A motionless unloaded body supplies no crack.
])

Taper changes characteristic transport and impedance. Slow taper can be a
low-reflection approximation under scale separation; it gives no general
identity of zero reflection. The native rod-to-contact/tube map is still
required. Explicitly time-varying material mass, inertia or strain energy
requires its additional work terms. No verified rotor-to-optical-wall coupling is assumed.

#route([
  #source("research/records/2026-07-15_THE_CHART_REVOLVES_LOCALLY_TRANSPORT_INTEGRATES_THE_BODY.md", [local chart and gluing]);
  #source("research/records/2026-07-31_THE_CHARACTERISTIC_CARRIES_THE_CURRENT_THE_EXPONENTIAL_RETURNS_AS_RECEIVER_PHASE.md", [characteristic, taper and return]).
  Laboratory provenance: `18_THE_HOURGLASS.md` and `PERIPLUS.md`, read under
  its AGENTS. Their historical engine claims are not current HNN acceptance;
  the periplus regrade retains an uncalibrated null at its declared reading.
])

= Reception energy composes once

#reading([Admission, deposition and flow], [Derived, unformalized], [
  Let $x_j$ be the arrived state in $Theta_j$ and
  $z_j=P_j x_j+s_j$ its admitted source opening after deposition.
  Define three readings on their actual operands:
  $
    d_j=E_(Theta_(j+1))(x_j)-E_(Theta_j)(x_j),
  $
  $
    a_j=E_(Theta_(j+1))(z_j)-E_(Theta_(j+1))(x_j),
  $
  $
    f_j=E_(Theta_(j+1))(x_(j+1))-E_(Theta_(j+1))(z_j).
  $
  #block(breakable: false)[
    Then
    $
      E_(Theta_N)(x_N)-E_(Theta_0)(x_0)=sum_(j<N)(d_j+a_j+f_j).
    $
  ]
])

#proof-block([
  Each sum cancels the two intermediate readings. Adjacent cuts then
  cancel by their matched state, material, frame and clock. This is an
  accounting identity, not a retained event tape. Each $f_j$ still needs
  its executed port/dissipation/pump/defect law. The checker must compare
  independently computed physical input/output, pump, dissipation, material
  and chart/solve terms from the actual trace to these readings; a deliberately
  perturbed flux must fail. Endpoint-defined $f_j$ alone cannot validate a run.
])

At quadratic storage Q, the admission term is
$
  a_j=1/2 x_j^*(P_j^* Q P_j-Q)x_j
    +op("Re")(x_j^*P_j^* Q s_j)+1/2 s_j^* Q s_j.
$
Only with Q-orthogonal projection $P_"source"$, $P_j=I-P_"source"$,
and $s_j$ in its range does this reduce to $E(s_j)-E(P_"source" x_j)$.
The old source energy is removed once. With $x=1$, $s=2$, $Q=1$,
$P=0$, admission work is $3/2$. Removing another $1/2$ yields the
false result 1.

#evidence-note(
  [The focused contact receipt already separates material work and opening difference.],
  [Executable, inspected],
  [#source("crates/holonics/src/hnn/word/continuation.rs", [ContinuationReceipt])],
  [The revised, merged PR 280 supplies host reception carry and the
   one-baseline chain; current public saved-carry mounting is source-inspected.
   The held-out apparatus was removed. Full device carry/restore parity,
   independent flux joins and autonomous useful output remain separate gates.
   Teacher-forced next-cell reads do not establish autonomous continuation.],
)

A complex comparison also keeps phase:
$
  log(psi_T/psi_H)=1/2 log(q/p)+i(phi_T-phi_H+2pi n).
$
The learning covector is the logarithmic derivative of the declared ratio,
returned through its producing operands. Probability readings alone forget
the phase. Code length, heat and port work require their units and
constitutive join; the statistical population has not acquired that join
merely by having a Bayesian/code telescope.

= Shadow, natural grain and causal parity

For a linear receiver R the present shadow is $ker R$. For a nonlinear
receiver it is the relation $R(x)=R(y)$. Null contrast is receiver-relative;
it asserts neither empty spacetime nor zero storage or future action.

#reading([Future and action sufficient retention], [Existing Lean; general consumer join proposed], [
  For constant finite-dimensional A,R,
  $
    cal(N)=⋂_(k>=0) ker(R A^k)
      =⋂_(0<=k<n)ker(R A^k),
  $
  where n is the state dimension. Cayley--Hamilton supplies this horizon.
  For changing material or admitted actions, instead require
  $
    x tilde y arrow.l.r
      forall w,R_w, quad R_w(T_w x)=R_w(T_w y),
  $
  $
    q T_a=bar(T)_a q, quad D q=R,
      quad q op("Dep")_a=bar(op("Dep"))_a q.
  $
])

The last square is essential when deposition changes are admitted actions.
The admission policy and its determining state also belong to the situated
future: different permitted action words cannot silently share a quotient.
In a nonautonomous linear chart the blind set is
$⋂_t ker(R_t U(t,0))$. A frozen observability matrix does not
certify all changing futures. With $R(x,h)=x$ and
$T_u(x,h)=(x+u h,h)$, $(0,1)$ and $(0,-1)$ agree now but separate
at $u=1$. A nonzero sub-grain reading is unresolved, rather than exactly null.

#route([
  #source("lean/Holonics/Foundation/CausalRelevance.lean", [future agreement]);
  #source("lean/Holonics/Objects/RelativeCompleteness.lean", [observability kernel]);
  #source("lean/Holonics/Holarchy/Hearing.lean", [present versus future silence]);
  #source("research/records/2026-09-25_THE_NATURAL_GRAIN_IS_THE_FUTURE_QUOTIENT_AND_REFLECTION_INTEGRATES_A_FRACTAL_PACKING.md", [natural grain]).
])

Causal time parity is opposed incidence on one shared temporal face:
$partial E_j=Sigma_(j+1)-Sigma_j+Gamma_j$.
Matched interior faces cancel under forward composition; the lateral
boundary remains. Occurrence, frame and clock agreement are required at
the selected grain. This is not time reversal. An epoch counts a receiver's
section flux; a cycle is a closed return; an aeon contains causal passage.

#route([
  #source("research/papers/source/mathematics/definitions/causal-time-parity.typ", [chain definition]);
  #source("research/papers/source/mathematics/theorems/causal-parity-kirchhoff-return.typ", [interval and junction return]).
])

= Actual folded, nonlinear and spectral transport

For a fixed specular wall normal n,
$v^+=v-2(n dot v)n/(n dot n)$.
Normal velocity reverses, tangential velocity and squared speed persist.
The folded segment retains its side residual to reconstruct the incoming
point. Its $2^k$ side words count restriction fibres; they do not distribute
optical energy into that many rays.

#route([
  #source("lean/HolonicsResearch/Transport/Fold.lean", [Crease.fold_segment_after and bounce_direction]);
  #source("research/records/2026-09-29_OUTER_BILLIARDS_A_TANGENT_STEP_IS_A_SWING_AND_THE_PENTAGONS_WEB_IS_A_GOLDEN_TOWER.md", [outer billiards]).
  Ordinary tangent outer billiards, outer length billiards and inner
  elliptic caustics keep distinct maps. The ordinary outer ellipse's
  invariant curves are homothetic. Moving walls require boundary work.
])

For the actual clocked nonlinear recurrence $Phi$ and moving receiver
regions $A_j$, first arrival at n is
$
  F_n=Phi_(n,0)^(-1)(A_n) ∖ ⋃_(k<n)Phi_(k,0)^(-1)(A_k).
$
This is a source-preimage population of the actual recurrence. A tiled IFS
drawn around an unrelated linear field does not create it. The historical
Hamiltonian-shear reference computes finite basins; it is not current native
Athena integration or an infinite-scale dimension theorem.
`FirstArrival.chart_covariant` gives autonomous chart covariance; a
time-dependent rechart uses that theorem on the clock-augmented state.

#route([
  #source("lean/Holonics/Computation/HolonicRecurrentEcology.lean", [ClockedFirstArrival.mem_population_iff and chart covariance]);
  #source("research/records/2026-09-14_FRACTAL_GEOMETRY_BELONGS_TO_THE_INTERACTING_FIELD.md", [intrinsic-field correction and nonlinear reference]).
])

For normalized Maxwell coordinates, $u=(abs(X)^2+abs(Y)^2)/2$,
$S=c X times Y$, the exact algebraic cone is
$
  c^2u^2-abs(S)^2=c^2[(abs(X)^2-abs(Y)^2)^2/4+(X dot Y)^2]>=0.
$
A PDE causal cone additionally needs evolution and boundary hypotheses.
Temporal Hodge class transport retains its exact-residue hypothesis;
its Euler step does not assert stability at arbitrary step sizes.
The scalar Gaussian Fourier identity at $t>0$ is a separate checked
source law. Finite spectral and unbounded-operator extensions require
their actual domains, maps and tails.

#route([
  #source("lean/Holonics/Physics/MaxwellEnergyCone.lean", [MaxwellEnergyCone]);
  #source("lean/Holonics/Physics/TemporalHodgeResidue.lean", [TemporalHodgeResidue]);
  #source("lean/HolonicsResearch/Zeta/FlowedGamma.lean", [FlowedGamma.gaussian_fourier]);
  #source("docs/MASS_ENERGY_AND_CAUSAL_TRANSPORT.md", [physical transport]).
])

The public zero-gas route requires an actual source law at time zero;
later pair collisions alone cannot force no off-seam pairs initially.
The source sign/causal intertwiner remains open. The egg's scalar modular
identities and complex elliptic torus do not produce a Hodge cycle family.
Hodge, complex-fluid continuation and BSD keep their own consuming maps.
This edition contains no private target proof files or fresh private claims.

#route([#source("research/records/2026-09-26_THE_ZERO_GAS_IS_A_COMPLEX_BURGERS_FLOW_AND_RH_NEEDS_A_SOURCE_LAW_AT_TIME_ZERO.md", [actual-source obligation and public falsifiers])])

= Dependencies and Athena acceptance

#table(
  columns: (1fr, 2fr),
  table.header([*Prerequisite*], [*Consuming relation still required*]),
  [Ports and material], [Transported state/material return; reception admission, flow and deposition balance.],
  [Chart covariance], [Future/action quotient with source, receiver and deposition squares.],
  [Balance and quotient], [Executed saved-passage future/refusal acceptance; production atomic cold restore.],
  [Actual nonlinear map], [First-arrival consumer, joint future fibre and complete producing-operand adjoint.],
  [Native continuation], [Actual card passage restore and parity; capacity-derived commuting partition.],
  [Joint boundary and restore], [Athena's actual usable output, compatible fibre, producing keys and truthful health.],
  [Physical source relations], [Whip/tube, Maxwell, Hodge and spectral intertwiners with domain and residual.],
)

The dependency arrows are: material to transported return and reception
balance; chart covariance to adaptive quotient; balance plus quotient to
production continuation/restore; actual nonlinear evolution to first-arrival
and joint release; native continuation to Resident parity; joint release plus
restore to Athena use. Physical source maps attach at their corresponding
operations. These refine U1/U2/U3/U6/U7/U8 in THE_REBUILD, preserving its
single construction order and inherited product gates.

#reader-note(author: [Codex], status: [Claude paused; independent briefs retained], [
  The latest direction leaves Claude paused; no launch, send or acknowledgment
  is required. Future independent review may derive counterexamples to
  this edition. The precise briefs and acceptance live in
  `docs/plans/HNN_ATHENA_FOUNDATION.md`. Their six subjects are constitution/
  asymmetric potential, periplus/whip power, adaptive observability, actual
  billiard/nonlinear transport, HNN continuation/Athena joint boundary,
  and physical/mathematical source joins. Each starts from public source
  premises, compares rival routes, fixes falsification before a claim, and
  reconciles at an actual consumer equation. No agreement is required.
])

The next bounded consumer is the source-only nonzero contact-deposit fixture:
actual comparison, reached certified C change, held-momentum work, changed later
native response and same-family saved-passage continuation. It must reject stale
producers and altered phase/flux, using independently computed balance terms.
The joined sources and V3 static pass do not execute this fixture. Exact runner
admission precedes execution. The boundary
circulation/phase-return lane retains its disjoint, unelaborated proposal grade.

Current public F4 text is incomplete/non-legible and F5's diagnostic split is
spent. F2's field reports shorter charged code but `107 rem 21` ms per window,
46 times its passage budget; it stays dormant for text. These inherited source
measurements do not bound the whole adapting field. No evaluation data was read.

Athena's gates remain F0/F4/F5: context and transformation grain, useful
actual output, producing keys, compatible fibre, native health, atomic
transition and complete cold restore. Text, image, acoustic and motor
are boundary charts of the same composition. A hand-authored answer
routine cannot substitute for induced conduct. The 20 W consumer-hardware
ambition is a target; fixture parity does not measure it.

The inspected October 4 issue snapshot leaves
#link("https://github.com/brandonrdug/holonics/issues/63", [63]),
#link("https://github.com/brandonrdug/holonics/issues/73", [73]),
#link("https://github.com/brandonrdug/holonics/issues/62", [62]) and
#link("https://github.com/brandonrdug/holonics/issues/148", [148]) open.
The local plan supplies a reconciled routing proposal; issue 73 still calls
merged PR 280 an open proposal. This edition posts nothing externally. Each missing theorem closes only with its hypotheses,
consumer square and receipt. Rust retirement preserves each law once in
its Lean/guide owner and updates consumers/atlas together; failed attempts
needed by the audit remain accessible. No parallel Rust learner is added.

#route([
  #source("docs/plans/THE_REBUILD.md", [one construction order]);
  #source("CONSTRUCTION_STATE.md", [local position]);
  #source("research/records/2026-09-24_LESSONS_FROM_THE_WORKBENCH_AND_ATHENA_PROTOTYPES.md", [prototype lessons]);
  #source("research/records/2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md", [repeated failures]).
])
