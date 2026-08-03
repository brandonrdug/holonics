#import "@preview/unequivocal-ams:0.1.2": theorem, proof
#import "../lib/holonics.typ": *

#let comparative = [
#pagebreak(weak: true)
= J5. Comparative geometry, physics, life, and culture <j5>

#local-contents((
  ([A visual grammar for relational geometry], <j5-visual-grammar>),
  ([Hypergraph rewrite and oriented comparison], <j5-hypergraph>),
  ([Rebase, retriangulation, and physical relocation], <j5-retriangulation>),
  ([Invariants retain the constrained directions], <j5-invariants>),
  ([Annular scale-turn recurrence and fractals], <j5-annulus>),
  ([Metric, curvature, and Ricci flow], <j5-curvature>),
  ([Physics bridges require domain law], <j5-physics>),
  ([Lightning and living terrain], <j5-life>),
  ([Comparative burden for a theory of everything], <j5-everything>),
))

The foundational calculus is deliberately thinner than any of its applications. This is a
strength only if comparison remains exact about what each domain adds. We use three relation
grades:

- an *exact formal match* identifies the same mathematical expression under a stated map;
- a *direct correspondence* preserves a named structure while leaving other structures outside
  the map; and
- a *structural resonance* is a hypothesis-generating analogy with a stated non-equivalence.

The grades do not form an automatic ladder. A beautiful structural resonance does not become an
exact match through repetition.

== A visual grammar for relational geometry <j5-visual-grammar>

The journal uses four visible primitives. A node is an actual occurrence only when the source
supplies that occurrence. A line is admitted incidence or transport only when its direction and
role are declared. A polygonal face records boundary, convex participation, or comparison
according to its caption; it never acquires all three readings automatically. A dashed line
marks a quotient, proposed bridge, world passage, or OPEN comparison and must be named locally.

#relation-cell-figure() <relation-cell>

@relation-cell is the general antecedent--consequent grammar. The relation occurrence, rather than
an arrow floating between private objects, is the middle of the diagram. This accommodates
arbitrary-arity hyperedges while retaining the distinction between event, causal dependency, and
receiver presentation @mathworld-hypergraph.

#simplex-face-figure() <simplex-face>

@simplex-face separates a convex simplex from a simplicial complex. The former is a geometric
realization with barycentric points; the latter additionally requires closure under faces and
actual common-face intersections @mathworld-simplex @mathworld-simplicial @mishra2025simplicial.
This distinction is central to the attention comparison in J3: normalized positive coefficients
give a convex point, but affine dependence can make the realized face degenerate.

#star-link-figure() <star-link>

@star-link adds the situated camera. A star answers which cells meet the selected occurrence; a
link answers what lies opposite that occurrence in those cells. They are useful local views of a
complex, not observer-independent identities of the whole. This is the visual discipline behind
sheet, seam, pin, fold, and receiver cross-section in the recent derivations.

#remark[
  Figures in this volume organize exact relations already stated in symbols or source data. Their
  coordinates, apparent distances, and visual symmetry are expository geometry and cannot become
  causal evidence.
]

== Hypergraph rewrite and oriented comparison <j5-hypergraph>

A conventional cellular automaton assigns local state to sites on a fixed lattice and evolves by
a chosen neighborhood rule. Triangular cells do not change that ontology by themselves. The
candidate Eros object is instead occurrence-relational: arbitrary-arity relations determine local
contact; actual update events replace relations; oriented incidence determines boundary; causal
dependency records which event used which material; and transport compares paths.

The Wolfram model makes a useful external distinction among spatial hypergraph, updating event,
causal graph, and multiway graph @wolfram2020. The first three have direct structural
correspondences here. A multiway system is an analysis of possible histories, not a requirement
that every possible match remain active inside Soma. Causal invariance is an additional
confluence obligation and cannot be inferred from deterministic scheduling.

#notation-table((
  [spatial hypergraph], [one relation cut; arbitrary local arity],
  [rewrite event], [actual local replacement under an admitted rule],
  [causal graph], [dependency among actual events],
  [multiway graph], [analytical population of alternative update histories],
  [oriented complex], [dimension, orientation, shared boundary, and $partial^2=0$],
  [transport], [what the admitted path does to a carrier],
))

The triangle is the smallest cell where boundary closure and route comparison can coexist:
$
  partial tau=a_12-a_02+a_01,
  quad
  Chi_tau=(T_(a_12)compose T_(a_01),T_(a_02)).
$
But the two readings remain distinct. Boundary closure follows from oriented incidence; path
commutation follows from the transport. A shared edge can also serve as a preserved interface for
a rewrite. None of these roles follows from three lines merely intersecting in a drawing.

#source-note[
  The full typed comparison is
  #link("../../RESEARCH/2026-07-21_THE_HYPERGRAPH_SUPPLIES_THE_REWRITE_THE_TRIANGLE_CARRIES_THE_COMPARISON.md")[
    The hypergraph supplies the rewrite; the triangle carries the comparison
  ]. It explicitly corrects the earlier tendency to use a strict category nerve or a triangular
  cellular automaton as the universal core.
]

== Rebase, retriangulation, and physical relocation <j5-retriangulation>

Three operations have often appeared under the single phrase “change of basis”:

1. *carrier rebase:* local coordinates change by invertible maps $G_x$, while incidence and the
   exterior relation remain fixed;
2. *retriangulation:* internal cells or factorization change inside one preserved exterior
   boundary; and
3. *physical relocation:* residency, communication geometry, length, or energetic cost changes.

In two dimensions, a $2 -> 2$ Pachner move exchanges the diagonal of a quadrilateral while holding
its exterior boundary. The $1 -> 3$ and $3 -> 1$ moves introduce or remove one interior vertex.
These are exact PL-topological operations under Pachner's hypotheses @pachner1991. They do not
preserve a chosen metric automatically, and they do not decide which later consequence matters.

#retriangulation-figure() <two-two-move>

#proposition[
  If a carrier rebase assigns an invertible map $G_x$ at every object and replaces edge transport
  $T_a:x -> y$ by
  $
    T'_a=G_y T_a G_x^(-1),
  $
  then every path comparison transforms covariantly:
  $
    T'_gamma=G_y T_gamma G_x^(-1).
  $
  Hence equality of parallel transports is preserved.
]

#proof[
  Along a composable path the adjacent factors $G_z^(-1)G_z$ cancel. Both parallel paths acquire
  the same left factor at the endpoint and right factor at the source, so one pair is equal
  exactly when the rebased pair is equal.
]

This proposition is the rigorous gauge face. A retriangulation needs a different proof: the
internal factorization must be replaced and its exterior transport shown to commute. Physical
relocation needs measurements of communication, memory movement, latency, or energy. Treating all
three as algebraic gauge hides the most interesting empirical question.

== Invariants retain the constrained directions <j5-invariants>

Let $(M^N,g)$ be a Riemannian manifold and
$I:M -> RR^k$ a regular constraint map. The active tangent space of the level set is
$
  D_x={v : dif I_x^a(v)=0 " for every " a},
  quad dim D_x=N-k.
$
The constrained directions have not vanished. They remain as normal directions, the value
$I(x)$, a coarea Jacobian, an orientation, and the receipt needed to sweep the fibers.

For the Euclidean $N$-ball,
$
  V_N(R)=c_N R^N,
  quad
  c_N=pi^(N/2)/Gamma(N/2+1),
$
and its boundary hyperarea is
$
  A_(N-1)(R)=N c_N R^(N-1)=(dif V_N)/(dif R).
$
Consequently,
$
  V_N(R)=integral_0^R A_(N-1)(r) dif r.
$
The final sphere does not reconstruct a labeled ball interior; the ordered radius family and the
normal sweep do. The Gamma recurrence gives
$
  V_(N+2)(R)=2pi R^2/(N+2) V_N(R),
  quad
  A_(N+1)(R)=2pi R V_N(R).
$
The visual intuition developed in 3Blue1Brown's high-dimensional sphere lesson is therefore
coupled here to an exact radial FTC and Gamma calculation, not used as proof authority
@threeblue-spheres.

#remark[
  The exponent $(lambda^N)^((N-1)/N)=lambda^(N-1)$ extracts codimension-one scale from an
  isotropic cube. For a ball, the coefficient $c_N$ must be retained. Equal scaling exponents do
  not identify cube and sphere constructions.
]

The coarea theorem supplies the general form:
$
  integral_M h(x)J_I(x) dif V_N
  =
  integral_(RR^k) (integral_(I^(-1)(c))h dif A_(N-k)) dif c.
$
This is an exact mathematical model of “a family of cuts carries a volume.” It becomes a holonic
application only when the receiver, constraint, orientation, and event which performs the hand-up
are also supplied.

== Annular scale-turn recurrence and fractals <j5-annulus>

The logarithmic lift from J4 has the geometry
$
  w=u+i theta,
  quad z=exp(w)=e^u e^(i theta).
$
An annulus is the quotient
$
  A(r,R) equiv {log r<"Re"(w)<log R}/(i Theta ZZ),
$
with conformal modulus
$
  mod A(r,R)=log(R/r)/Theta.
$
It retains a radial scale interval and a cyclic return. Exponentiation presents one nonzero face
while identifying lifts separated by a complete turn.

#scale-turn-figure() <scale-turn-geometry>

#definition[
  A *self-similar return at a declared cut* consists of a first-return map $F^q$, receiver
  landmarks, a chart $psi$, a multiplier $lambda$, incidence or winding, and the residual of the
  actual return. Visual resemblance alone is not a return law.
]

Near a suitable noncritical periodic point, Koenigs linearization may give
$
  psi(F^q(z))=lambda psi(z),
  quad lambda=exp(kappa+i omega).
$
Then
$
  psi(F^(q N)(z))=e^(N kappa)e^(i N omega)psi(z).
$
Here $kappa$ is logarithmic scale change and $omega$ is turn per return. In higher dimensions the
transport is generally ordered,
$
  v_N=J_N dots J_2J_1v_0,
$
and becomes a scalar power only in a commuting one-dimensional chart. Tan Lei's local asymptotic
similarity between Mandelbrot and Julia sets supplies a rigorous example of receiver-local
recurrence @tanlei1990; it does not license generic exact pixel copies.

#source-note[
  The scale-turn derivation, its corrections, and the fractal boundary are in
  #link("../../RESEARCH/2026-07-19_THE_ANNULUS_CARRIES_THE_SCALE_TURN_LIFT_THE_EXPONENTIAL_FOLDS_THE_FACE.md")[
    The annulus carries the scale-turn lift
  ].
]

== Metric, curvature, and Ricci flow <j5-curvature>

For a declared Riemannian receiver $(M,g)$, the metric compares tangent directions; the
Levi-Civita connection transports them; and the Riemann tensor measures noncommuting infinitesimal
transport. For a geodesic tangent $u$ and separation $xi$,
$
  "Gravitas"_gamma(xi)=nabla_u nabla_u xi=-R(xi,u) u
$
under the project's chosen sign convention. With an orthonormal transverse frame ${e_a}$,
$
  sum_a g("Gravitas"_gamma(e_a),e_a)=-"Ric"(u,u).
$
Ricci is the transverse trace of directional curvature, not the whole curvature operator.

Hamilton's Ricci flow
$
  partial_tau g=-2 "Ric"(g)
$
changes the comparison law itself @hamilton1982. This is an exact physical-mathematical
specialization after a Riemannian metric and its PDE have been supplied. It is not a universal
Soma update law. Perelman's Ricci-flow programme supplies a profound local-to-global example:
smooth evolution, curvature concentration, blow-up and scale rebase, controlled neck surgery,
component departure, continued flow, and topological accounting establish the Poincare result
@perelman2002 @perelman2003.

The distinctions matter:

- smooth Ricci flow preserves topology while it exists;
- surgery is the typed topological deed;
- normalization is a scale rebase;
- a soliton is return up to diffeomorphism and scaling; and
- extinction is not the same receiver as normalized persistence.

Poincare does not imply $P="NP"$, universal confluence, or trivial connection holonomy. It is a
rigorous example in which local evolution and controlled singular transformation expose a global
invariant without enumerating all presentations.

== Physics bridges require domain law <j5-physics>

In a nonlinear sigma model, the target metric is a coupling and the leading metric beta function
contains the Ricci tensor, subject to scale conventions, field redefinitions, and higher
corrections @friedan1985. Under its Abelian-isometry hypotheses, T-duality exchanges circle
momentum and winding and acts on the full background, not only the radius. Flow, singularity,
rebase, duality, and return are therefore different deeds.

For an unwarped product $M_11=M_10 times S_R^1$,
$
  dif V_11=R dif theta dif V_10,
  quad
  V_11=2pi R V_10.
$
Dimensional reduction is fiber integration. At low enough receiver energy the translation-
invariant zero mode may be active while nonzero modes retain momenta $n/R$. The circle direction
is dormant at that receiver, not deleted from the construction. Witten's Type-IIA/eleven-
dimensional relation supplies a typed physical instance of this principle @witten1995.

No such correspondence makes software arcs physical strings or makes receiver-relative
compression a law of spacetime. A physical bridge owes at least:

1. mathematical objects and maps;
2. dimensions and units;
3. dynamical law and admissible initial/boundary conditions;
4. limiting agreement with established theory; and
5. a discriminating observation not already inserted as source structure.

== Lightning and living terrain <j5-life>

Lightning is a materially grounded example of a path changing the terrain later current receives.
A leader changes ionization, space charge, conductivity, temperature, and channel geometry; later
leaders and the return stroke propagate through that changed medium. The structural sequence is
$
  "field + atmosphere" -> "leader founding" -> "changed conductive terrain",
$
$
  "changed terrain" -> "later ride or new founding" -> "attachment",
$
$
  "attachment" -> "finite return" -> "material consequence".
$
This is a direct correspondence to the event/Standing/consequence circuit at the causal grain.
The literal law remains Maxwell, plasma, chemical, thermal, and gas-dynamic physics. Channel
curvature, an effective transport metric, Ricci curvature, and spacetime curvature are four
different receiver faces.

The same discipline applies to biology and culture. Niche construction, development, ecological
inheritance, distributed cognition, ritual, language, and institutions can preserve relations
through changing constituents. They become holonic comparisons only after identities,
transmission channels, receiver cuts, causal contrasts, and failure cases are specified.
Narrative continuity is not automatically a biological lineage; cultural resemblance is not
automatically common ancestry; and a useful metaphor is not a mechanism.

#source-note[
  The geometry/physics chain is developed in
  #link("../../RESEARCH/2026-07-18_THE_HYPERAREA_IS_THE_INVARIANT_FIBER_THE_SWEEP_CARRIES_THE_VOLUME.md")[
    The hyperarea is the invariant fiber
  ] and
  #link("../../RESEARCH/2026-07-19_THE_RICCI_TRACE_CHANGES_THE_RECEIVER_THE_SINGULAR_NECK_REBASES_THE_BODY.md")[
    The Ricci trace changes the receiver
  ]. Their strongest equations are retained here; their broader “one chain” language is narrowed
  to typed correspondences.
]

== Comparative burden for a theory of everything <j5-everything>

The hypothesis of everything is best stated as a research posture: one relational grammar may
coordinate mathematics, computation, life, cognition, and physics without making any application
the definition of the grammar. At present, the programme has:

- a receiver-relative event calculus;
- exact local constructions in several mathematical charts;
- a production machine with bounded measurements; and
- disciplined bridges to established domain theories.

It does not yet have a physical action, unit system, quantum/statistical limit, experimentally
novel prediction, or falsification result spanning those domains. “Relational unification
programme” is therefore the strongest licensed description. The missing physical relations are
scientific work to perform, not rhetorical gaps to close.

#evidence-note(
  [The same event calculus admits several rigorous specializations without identifying them.],
  [Exact matches and direct correspondences where maps are written; structural resonance
  elsewhere.],
  [Hypergraph/rewrite, coarea, annulus, Ricci-flow, compactification, and lightning source routes.],
  [No universal manifold, field equation, biological mechanism, cultural taxonomy, or physical
  theory of everything is established.],
)
]
