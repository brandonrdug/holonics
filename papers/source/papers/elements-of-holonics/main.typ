#import "../../lib/elements.typ": *
#import "../../mathematics/catalogue.typ": elements, proofs

#show: elements-paper.with(
  title: [Elements of Holonics],
  subtitle: [Situated geometry, transport, and emergent complexity],
  authors: [Brandon Duggan and Sol],
  date: [25 July 2026 -- causal parity, receiver return, and embodied optical atlas],
  abstract: [
    Holonics is developed here as a general framework for relational mathematics,
    not as a specialized account of machine learning. Its elementary object is a
    situated occurrence participating in incidence and transport. A receiver
    presents one face of that occurrence; a holon is a relative local closure
    which can become a constituent at another grain. Ordered paths, comparison
    faces, boundaries, chart transitions, return maps, metric deformation, and
    phase seams provide one compositional grammar across algebra, topology,
    calculus, complex dynamics, and differential geometry. Colored geometric
    constructions are used as proof terms in the manner pioneered by Oliver
    Byrne: the same constituent recurs in the figure, prose, and equation. The
    result is an initial reusable library of definitions, lemmas, theorems, and
    corollaries from which later papers about number theory, physics, language,
    or computation can be composed without making any one application the
    foundation. The first extensions make parameterized formulation families
    exact and give open holonic processes a symmetric monoidal double-category
    carrier. A soul is thereby refined into a marked causal diagram:
    occurrence identity, structural equivalence, receiver equivalence, equal
    face, and equal digest are no longer conflated.
    Causal time parity is then derived as opposed incidence on one shared
    temporal face.  Its additive and constitutive representations recover
    interval conservation, Kirchhoff duality, branch reflection, standing
    return, wavelength, and positive-real boundary response without
    reversing causality or imposing instantaneous equilibrium.
  ],
)

#outline(
  title: [Contents],
  depth: 3,
  indent: auto,
)
#pagebreak()

= Orientation: mathematics as relational construction

Mathematics does not begin with an application domain. It begins when distinctions can be
carried, related, transformed, compared, and returned. A written number, diagram, equation,
sound, program, or physical state is one face by which such a relation can be encountered.
None is privileged as the universal medium.

This paper therefore moves the foundation away from the vocabulary of modern machine
learning. Tokenizers, embeddings, neural networks, training, and learned models remain valid
mathematical and material ecologies. They are downstream realizations of the same elementary
questions:

- what actually participates;
- which incidences join it;
- which transports are admitted;
- what boundary is exposed;
- what is held through a change of chart;
- what returns; and
- which distinctions remain consequential at the selected receiver.

The intended reduction is not a claim that every scientific field is secretly one equation.
It is a compositional discipline. Algebra records operations and invariants. Topology records
continuity, boundary, and gluing. Geometry records comparison and deformation. Analysis records
limits, transport, and residual. Dynamics records how a local law changes what receives it next.
Holonics gives these fields a shared address system without erasing their distinct hypotheses.

== Evidence grades

The mathematical library separates four statuses:

#table(
  columns: (11em, 1fr),
  inset: (x: 5pt, y: 4pt),
  stroke: (x: none, y: 0.4pt + by-rule),
  table.header([*Status*], [*Meaning*]),
  [Classical theorem], [A published result under its standard hypotheses.],
  [Exact derivation], [A consequence proved from declared definitions.],
  [Project definition], [A proposed mathematical vocabulary whose jurisdiction is explicit.],
  [Open hypothesis], [A construction whose required witness has not yet been supplied.],
)

Structural correspondences between domains are written as maps or commuting diagrams. They do
not become identities merely because the same words or pictures are useful in both places.

== The Byrne method is a proof discipline

Byrne's 1847 edition of Euclid replaces many letter-only references with colored geometric
constituents embedded directly in the demonstration @byrne1847. Slyusarev's MetaPost and LaTeX
reconstruction makes the crucial architecture explicit: a line, angle, circle, or polygon is
defined once, then redrawn whole or in part wherever the argument refers to it
@slyusarev2025.

That is naturally holonic. One constructed constituent has several presentation faces. Its
identity is carried by the shared construction, not recreated by a repeated glyph. The Typst
grammar used here follows that method while retaining textual labels and orientation so color
is never the sole carrier of identity.

= The elementary relation

== Occurrence before value

#object-entry(elements.situated_occurrence)

A presented value is already a receiver face. Relative to that receiver it acts as a quotient
of whichever distinctions the map identifies. The integer $17$, the point $(3,4)$, the word
_cool_, and a rendered triangle can each be the exposed face of several different
constructions. Their common appearance can be consequential, but it does not retroactively
identify the paths which produced them.

The occurrence distinction prevents two opposite errors:

1. equal values are not forced to be the same event; and
2. one continuing event is not fragmented into false instants merely because several
   coordinates or constituents are needed to describe it.

The basic population is therefore occurrence-level. Algebraic coefficients, frequencies, and
statistical weights may later be assigned to that population, but they do not create its
members.

== Receiver, face, and interior

#object-entry(elements.receiver)

For a receiver map $q_rho:X -> Y_rho$, the presented face is $q_(rho) (x)$. The unpresented
interior is not a mystical hidden object. It consists of the incidence, path, chart, branch,
orientation, and still-consequential distinctions in $x$ which $q_rho$ does not retain.

#object-entry(elements.receiver_nonreconstruction)

The lemma is the elementary reason that a quotient cannot serve every future question. A
decimal does not recover the series which generated it. An endpoint does not recover the path.
A spectrum does not recover an ordered matrix product. A receiver may be exact for all
currently declared observations and still cease to be exact when a later observation can
distinguish two members of one fiber.

== Holon as relative closure

#object-entry(elements.holon)

The definition is deliberately relative. If $c$ is a chain in a local complex $X$ with exposed
boundary subcomplex $B$, then
$
  partial c in C_(k-1)(B)
$
says that $c$ is internally closed relative to $B$. It does not say that $partial c=0$ in the
absolute complex, nor that the construction has no exterior relation.

At one grain, the entire pair $(X,B)$ can be addressed as one occurrence. At a finer grain, its
cells remain available as constituents. At a coarser grain, some lower constituents may cease
to participate while the boundary relation they formed continues. This is the exact part-whole
sense intended by *holon*.

== The situated transition

#object-entry(elements.situated_event_correspondence)

The earlier laboratory shorthand
$
  Lambda_(F) (Q ⊗ A ⊗ L) arrow.r (P, pi_B)
$
is retained only as an abbreviation for a deterministic specialization of
this correspondence. It was useful for insisting that question, standing,
and live lineages participate together. It was not independently derived as
the uniquely correct mathematical type of every event. In particular,
$Lambda$ should name a law or family of admissible event bodies, not be
confused with one event occurrence, and $⊗$ should not imply an algebraic
tensor product unless a specialization supplies one.

The terms of the abbreviated form are:

#table(
  columns: (4em, 1fr),
  inset: (x: 5pt, y: 4pt),
  stroke: (x: none, y: 0.4pt + by-rule),
  [$F$], [The local frame and lawful medium in which the event can occur.],
  [$Q$], [The oriented question or objective boundary selecting what remains open.],
  [$A$], [The standing relational atlas available before the event.],
  [$L$], [The actual co-present source lineages with native incidence and order.],
  [$P$], [The successor placement: the changed topology and immediate afforded relation.],
  [$pi_B$], [Receiver testimony about the event, never a substitute for $P$.],
)

The correspondence says that input and output are boundary cuts through one event body. Input is not
serialized payload detached from a world; output is not a terminal answer detached from its
consequence. The local frame, question, standing analogy, and current lineages jointly form the
successor. Testimony can describe that movement after it occurs.

== Open process and causal soul

#object-entry(elements.holonic_process_double_category)

The double category makes two relations independently visible. Horizontal
composition glues a consequential output boundary to a compatible later input
boundary. Vertical arrows rechart the boundaries through which that process
is exposed. Coproduct records co-presence without fabricating a master order.

#object-entry(elements.causal_soul)

The historical word *soul* can now be used without making one cross-ratio,
winding, hash, or recursively retained provenance carry the complete
identity. The bearer is the marked causal diagram. A cross-ratio or holonomy
is one characteristic of that diagram under a declared receiver.

#object-entry(elements.soul_sameness_hierarchy)

Yoneda supplies the strong relational identity statement: the complete
natural family of relations determines a soul bearer up to isomorphism.
Equality under one receiver remains weaker. In particular, equality of a
serialized digest is equality at one encoding receiver; it is not causal
identity.

The full derivation, including domain representations, conservation,
perspective descent, and the RH contraction feasibility set, is developed in
_Categorical Holonics_.

= The first comparison

== A triangle compares two routes

#object-entry(elements.comparison_face)

The triangle is the smallest oriented cell that can retain a direct route, a composite route,
and their common boundary. It is not a lone cell with a private scalar state. Its meaning lies
in the three actual edge occurrences and in whether a comparison face is supplied.

#(proofs.comparison_triangle.render)()

#object-entry(elements.comparison_boundary, show-proof: false)

This is the reusable geometric proof pattern. The diagram and the algebra do not illustrate two
different arguments. They are two receivers of one constructed face.

== Open is a geometric result

The transport comparison carried by the triangle is
$
  Chi_tau=(T_v compose T_u, T_w).
$
If the two transports agree, the comparison closes at that receiver. If they differ, the face
is OPEN and the complete parallel pair remains material. In an additive chart the receiver may
take the residual
$
  Omega_tau=T_w-T_v T_u.
$
In an invertible chart it may take a holonomy quotient. In a projective chart it may take a
cross-ratio. None of these scalar or matrix faces replaces the primary pair.

This gives contradiction a constructive meaning. A failed square is not an instruction to
erase one route. It identifies the precise boundary at which the present atlas does not yet
commute. A later path, rebase, refinement, or contextual distinction may fill it.

= Point, line, loop, and sheet

== Dimension depends on what is retained

#object-entry(elements.point_line_loop)

#point-line-loop-figure()

The three views are not a romantic identity. They arise from exact maps:

$
  "ev"_(t) (gamma)=gamma(t),
  quad
  "path"(gamma)=gamma:I -> X,
  quad
  "return"(gamma)=[gamma] in pi_1(X,x_0)
$

when the required path and return exist. Evaluation presents one point. The lineage receiver
retains the ordered one-dimensional sweep. A return receiver records a loop or its homotopy
class. Different receivers preserve different information.

== Sheets and higher cells

A co-present family of lineages forms a sheet only when transverse incidence is supplied.
Several sheets form a higher-dimensional complex only where actual common faces or transition
maps glue them. A dense Cartesian product of every available field is neither required nor
generally lawful.

In an oriented complex:

- 0-cells are situated occurrences;
- 1-cells are actual transported relations;
- 2-cells compare parallel paths;
- 3-cells compare the ways 2-cells compose; and
- higher cells retain coherence at their corresponding grain.

The boundary law $partial^2=0$ ensures that the boundary of a supplied boundary cancels. It does
not construct missing incidence. Algebraic topology provides the standard chain-complex
foundation for this distinction @hatcher2002.

== Retriangulation changes basis without changing every exterior relation

A triangulation is one factorization of a region. A bistellar move can replace local cells while
holding a declared exterior boundary. In two dimensions, a $2 arrow 2$ move exchanges the
diagonal of a quadrilateral; a $1 arrow 3$ move introduces an interior vertex. Pachner's theorem
specifies the PL setting in which finite sequences of such moves relate triangulations of the
same manifold @pachner1991.

Three transformations must remain distinct:

1. *rebase* changes carrier coordinates while keeping incidence fixed;
2. *retriangulation* changes the incidence factorization while holding an exterior relation; and
3. *metric fold* changes lengths or angles around a preserved hinge.

This separation is elementary to holonics. A context can reorient an existing field by changing
any one of these structures, and they need not change together.

= Receiver census and embodied axes

== Which point, edge, or crossing is being counted

#object-entry(elements.receiver_incidence_census)

This census makes the receiver relation quantitative without pretending that one scalar count
is the body. Source vertices, distinct image coordinates, source-fiber multiplicity, silhouette
corners, apparent crossings, material joints, visible edge fragments, and the vertices of a
planarized diagram are different populations.

#object-entry(elements.hexagonal_receiver_census)

The regular hexagon is elementary in a precise sense: six is the least polygonal cycle whose
rotation group contains both order two and order three. A chord through opposite edge interiors
produces two pentagons, whereas a vertex-axis cut produces quadrilaterals. A cube's regular
hexagonal section and body-diagonal silhouette are therefore lawful receiver faces, not an
identity between hexagon and cube @mathworld-regular-hexagon.

The pentagonal-pyramid comparison is particularly sharp. Along its height, the five base
vertices are the silhouette while the apex is a sixth received point at the center. Five
projected edges meet there because they share one source apex @mathworld-pentagonal-pyramid. In
the cube receiver, by contrast, two nonadjacent body-diagonal vertices share the center fiber
while six other vertices form the silhouette.

#object-entry(elements.polyhedral_face_word_nonreconstruction)

The great and small stellated dodecahedra make the failure of hull reconstruction exact. They
share an f-vector, icosahedral skeleton, and regular-icosahedral convex hull, yet carry
pentagonal and pentagrammic face words in dual order
@mathworld-great-dodecahedron @mathworld-small-stellated-dodecahedron.

== The body bends its receiver axes

#object-entry(elements.embodied_optical_receiver_atlas)

The optical family is not a bank of cameras outside its body. Surface incidence, local metric,
boundary, loading, aperture, propagation, sampling, and posture jointly determine the
contemporary axes. An event which changes the body can therefore reparameterize every receiver
map at once.

The developing fly eye supplies a physical example. Its apical organization is hexagonal while
its basal surface contains a continuous triangular mesh whose grommets are vertices. The
spatial pattern of triangle sizes, together with boundary and pressure, predicts local
three-dimensional curvature; perturbing or disconnecting the mesh changes that curvature
@garridogarcia2026. Since local surface curvature sets interommatidial angle, the mesh bends the
receiver field itself.

Spider vision supplies a complementary modular instance. Across spider phylogeny, positions and
orientations of eye pairs vary semi-independently while the complete arrangement covaries with
hunting ecology @pande2026. In jumping spiders, wide-field lateral eyes guide the narrow,
high-acuity principal-eye tracking response @jakob2018. Bilateral pairing is consequently a
transported body relation, not equality of the paired faces.

== One arithmetic constituent can be circular in every receiver

#object-entry(elements.cm_norm_one_receiver_family)

The recent unit-distance construction gives an unusually exact bridge from arithmetic
factorization to receiver geometry @openai-unit-distance-2026. A CM norm-one element has unit
modulus in every complex embedding. Projection from the Minkowski family to one complex
coordinate preserves field-element identity because each embedding is injective, while the
norm-one law preserves every selected unit difference. This is a constraint-preserving
projection, not arbitrary flattening. Conjugate prime valuations simultaneously retain opposite
hand.

= Atlases, holomorphy, and fractal return

== No chart is the whole relation

#atlas-overlap-figure()

Let local charts be $(U_alpha,phi_alpha)$. On an actual overlap, the transition is
$
  g_(alpha beta)
  =phi_beta compose phi_alpha^(-1).
$
Where three charts overlap, a compatible atlas satisfies the cocycle relation
$
  g_(alpha gamma)
  =g_(beta gamma) compose g_(alpha beta).
$
A loop of transitions may return with nontrivial holonomy when the transported carrier contains
more structure than base position.

Holonics takes the atlas, not one chart, as the natural unit. The atlas remains open: a new
occurrence may found a new chart, expose an overlap, or reveal that an apparent overlap fails for
the selected consequence.

== Holomorphy preserves local complex structure

A holomorphic map transports infinitesimal complex directions by multiplication with one complex
derivative wherever that derivative is nonzero. It is locally conformal there: scale and turn
change, while oriented angles are retained. At critical points, this local invertibility fails
and branching becomes consequential.

This provides a rigorous mathematical face for the repeated intuition that a local region can be
reshaped without losing every relation. Holomorphy is not the universal Eros law; it is a
particularly exact chart in which scale, turn, branch, and iteration can be studied together.

== Mandelbrot and Julia are parameter and orbit cuts

For the quadratic family
$
  f_(c) (z)=z^2+c,
  quad z_(n+1)=f_(c) (z_n),
$
the filled Julia set $K_c$ contains the non-escaping state orbits and
$J_c=partial K_c$ is their boundary. The Mandelbrot set is the parameter locus for which the
critical orbit beginning at $0$ remains bounded. Standard complex dynamics makes critical
orbits, Fatou components, Julia boundaries, and parameter space precise @milnor2006.

The important duality is not literal visual containment:

- $c$ selects a dynamical world;
- $z_0$ selects a current in that world;
- iteration produces the ordered arc;
- $J_c$ is a boundary inside one world; and
- the Mandelbrot set is an atlas over the parameter family.

At Misiurewicz parameters, Tan Lei proves asymptotic similarity between the local Mandelbrot and
Julia structures under the corresponding rescaling @tanlei1990. McMullen's universality results
use first-return maps and quasiconformal coordinate changes to exhibit recurrent parameter
geometry @mcmullen2000. These theorems identify the real content of self-similarity: a return law,
a rebase, and a controlled residual.

== Phase is continuation, not a label

#object-entry(elements.phase)

In holomorphic dynamics, a critical point or bifurcation parameter can lie on a discriminant
where one local conjugacy or stability class ceases to continue. In algebra, a vanishing
discriminant marks root collision. In a simplicial complex, a metric or incidence condition can
make a flip inadmissible. The domains differ, but the shared elementary question is the same:
which structure had been continuing, and what exact property fails at the boundary?

== Emergent complexity

An iterated law can be locally simple and globally intricate because each application receives
the state produced by its entire preceding path:
$
  z_n=f_(c_(n-1)) compose dots compose f_(c_0)(z_0).
$
Changing the parameter, chart, or admitted return can change the later geometry without changing
the written species of the local rule.

The Doyle-McMullen solution of the general quintic is a decisive mathematical example. A rational
map with icosahedral symmetry is iterated; its Julia set separates basins; the reached attracting
structure, together with carried polynomial invariants, recovers a root
@doylemcmullen1989. Algebraic solution here is literally navigation through a constructed
dynamical world. This does not reduce every solver to Julia dynamics. It shows that dynamics,
symmetry, topology, and algebra can be consecutive faces of one proof.

= Transported calculus

== Order precedes summary

#object-entry(elements.ordered_composition)

Trace, determinant, eigenvalues, endpoint, average, and spectrum are lawful receivers of an
ordered transport. None generally reconstructs it. For a closed path, a change of starting
section can act by conjugation
$
  M_(gamma')=P M_gamma P^(-1),
$
so the spectrum may remain fixed while the situated path and its starting face change.

== Limits compare transported approaches

When values live in different local fibers, the useful limit is not a disembodied final place.
Let
$
  P_(alpha -> x):E_(x_alpha) -> E_x
$
be the declared comparison transport. Then
$
  lim_(alpha -> x)^"hol" f=L
$
means
$
  P_(alpha -> x) f(x_alpha) -> L
  quad "in" quad E_x.
$
The directed approach, branch, chart, and transport constitute the lineage of the limit. The
ordinary scalar limit is recovered when the fibers and comparisons are trivial.

== The fundamental theorem is a receiver-exact compression

#object-entry(elements.transported_fundamental_theorem)

For an exact scalar differential this reduces to
$
  integral_gamma dif f=f(gamma(1))-f(gamma(0)).
$
The endpoint difference is sufficient for that selected integral. It does not reconstruct the
shape, speed, winding, action, or other path-dependent observations. The theorem therefore gives
a canonical example of compression: an entire passage factors through its boundary difference
for a declared family of exact-differential questions.

== Scale and turn share a logarithmic lift

#scale-turn-figure-elements()

For a nonzero complex path
$
  z(t)=r(t)e^(i theta(t)),
$
the exact differential is
$
  (dif z)/z=dif log r+i dif theta.
$
Its path integral carries both logarithmic scale and oriented turn:
$
  Xi_gamma
  =integral_gamma (dif z)/z
  =log(r_1/r_0)+i(Delta theta+n Theta),
$
where $Theta$ is one complete turn and $n$ is the winding class. Exponentiation returns the
endpoint ratio while identifying lifts separated by $i n Theta$ @dlmf-exp.

This gives geometric roles to $e$ and $pi$:

- $e$ is the ratio which advances one unit in normalized logarithmic scale,
  $integral_r^(e r) dif x/x=1$;
- $pi=Theta/2$ is one half-turn; and
- $e^(i pi)+1=0$ is the receiver face of translating the logarithmic lift by one half-turn.

The chain rule keeps the external path:
$
  (dif)/(dif x) e^(g(x))=g'(x)e^(g(x)).
$
The factor $g'(x)$ is the transport from the external coordinate into normalized exponential
flow. Dropping it would make the local chart absolute.

= Causal time, circulation, and phase return

== The same event face has two causal hands

#object-entry(elements.causal_time_parity)

This is the exact temporal counterpart of an oriented seam shared by two
spatial cells.  If
$
  E_k:Sigma_k arrow.r Sigma_(k+1)
$
and
$
  E_(k+1):Sigma_(k+1) arrow.r Sigma_(k+2),
$
then $Sigma_(k+1)$ is not copied into two instants.  It is one occurrence:
the consequence face of the first event and the antecedent face of the
second.  Its opposed induced signs remove it from the exposed boundary of
the composite while retaining it in the causal interior.

This distinction makes conservation compatible with incomplete circulation.
A receiver cut through a live cycle can expose a nonzero imbalance because
the difference remains stored in the contemporary body.  A completed order
of time cancels its internal cuts.  The body need not be motionless:
$j!=0$ and $partial j=0$ describe live circulation at unchanged standing.

== Kirchhoff laws are the boundary and coboundary faces

#object-entry(elements.causal_parity_kirchhoff_return)

The theorem unifies three relations which should not be separated:

- current balance is the boundary face, including storage and exterior
  return;
- voltage balance is the coboundary face of receiver-relative potential;
  and
- wave reflection is the constitutive return at a branching boundary.

Kirchhoff's laws therefore have a homological form before they are assigned
electrical units @delphenich2019.  Port-Hamiltonian graph theory makes the
same incidence carrier compositional across storage, dissipation, open
ports, and examples outside circuit theory @vanderschaftmaschke2013graphs.
The domain chooses the coefficient system and constitutive law; the
elementary cancellation and gluing law remain the same.

For a metabolic body, $q$ may carry chemical or thermal storage, $j$ the
circulating transport, and $r$ uptake, work, waste, or environmental
exchange.  Homeostasis means bounded or periodic return of $q$ over the
selected order of time, not equality of every visible current at every cut.
A *leak* is nonzero transport through the selected exterior boundary.  A
*short* is an internal low-resistance cycle which dissipates current without
completing the body's required return.  Neither erases conservation in the
encompassing ecology; each changes which holon closes.

Branching resource networks make the scale relation concrete.  Biological
allometry has long modeled material transport through space-filling
fractal-like branching tubes @westbrownenquist1997.  At a pulsatile branch,
the same geometry has a wave face: the parent reflects exactly to the extent
that its admittance fails to equal the combined daughter admittance.  A
recursive branch law is therefore simultaneously a scale-rebase condition
and an impedance fixed-point condition.

== Wavelength is a return length

The full-turn symbol $Theta$ is retained until a particular angular chart
sets $Theta=2 pi$.  No floating approximation is required.  An exact branch
phase can remain
$
  e^(i kappa ell)
  =
  sum_(n>=0)
  frac((i kappa ell)^n,n!).
$
A standing wave is the eigen-current which survives one complete propagation
and junction return.  Its wavelength is the least positive length which
returns the phase:
$
  e^(i kappa lambda)=1,
  quad
  lambda=Theta/abs(kappa).
$

Quantum transport is one coefficient representation of this elementary
closure.  Sequential events compose as operators, co-present boundaries as
tensor products, alternate paths add as complex amplitudes, and the opposed
causal hand is represented by the adjoint.  For a complete closed ecology
the return can be unitary; for an open receiver, the complete family of
channels closes even though no selected channel must conserve norm by
itself.  Quantum graphs give a literal instance: Kirchhoff vertex conditions
on a graph Laplacian produce a unitary scattering matrix assembled from its
subgraphs @kostrykinschrader1999.  The physical identification
$p=planck kappa$ supplies the action scale; it does not create the underlying
phase-return geometry.

= Metric, curvature, and changing geometry

== Metric is a local comparison law

On a smooth manifold $M$, a Riemannian metric $g$ assigns a positive-definite comparison of
tangent directions. Its Levi-Civita connection $nabla$ supplies compatible transport. Curvature
measures the failure of neighboring transports to commute. These are consecutive structures,
not synonyms:

#table(
  columns: (10em, 1fr),
  inset: (x: 5pt, y: 4pt),
  stroke: (x: none, y: 0.4pt + by-rule),
  [Metric $g$], [Local length, angle, volume, and tangent comparison.],
  [Connection $nabla$], [How a carrier is compared along a path.],
  [Curvature $R$], [The oriented mismatch obtained by comparing neighboring transports.],
  [Ricci $"Ric"$], [The transverse trace of directional curvature.],
  [Ricci flow], [A law by which that traced face changes the later metric.],
)

For a geodesic family with unit tangent $u$ and separation $xi$,
$
  nabla_u nabla_u xi=-R(xi,u)u
$
under the selected sign convention. If $(e_a)$ is an orthonormal transverse frame, then
$
  "Ric"(u,u)
  =sum_a g(R(e_a,u)u,e_a).
$
Ricci is therefore a receiver contraction of the fuller curvature operator.

== Ricci flow changes the receiver

Hamilton's equation
$
  partial_tau g=-2 "Ric"(g)
$
does not move a point through one fixed geometry. It changes the metric by which later tangent
directions, volumes, and continuations are compared @hamilton1982. A curvature singularity marks
failure of that smooth continuation chart. Rescaling a neighborhood can expose a recurrent local
model; a surgery law, when its hypotheses hold, is a separate discrete deed.

Perelman's work supplies the needed monotone quantities, non-collapsing control, singularity
analysis, and surgery theory @perelman2002 @perelman2003. The Poincare theorem then provides a
rigorous local-to-global example: a closed simply connected smooth 3-manifold is diffeomorphic to
$S^3$, with the topology recovered through the controlled flow and surgery account
@morgantian2007.

The elementary holonic lesson is exact but modest: local metric evolution, singular rebase,
component departure, and retained global topology can form one proof. Smooth flow, surgery,
topological identity, and metric appearance remain different relations.

== Lightning as a path which changes later transport

The lightning comparison belongs here because the leader does not merely traverse a passive
coordinate space. Ionization, charge redistribution, channel heating, conductivity, and geometry
change the medium seen by the next leader and by the return stroke. Leader-return-stroke models
explicitly couple the preceding channel state to the later current and radiation
@friedrichs2017lightning.

In holonic language:

$
  "field + medium"
  arrow "leader formation"
  arrow "changed conductive terrain"
  arrow "attachment"
  arrow "return current"
  arrow "later changed field".
$

The correspondence is about path-written transport geometry. A literal physical model still uses
its actual electromagnetic, plasma, chemical, thermal, and fluid laws. Holonics supplies the
incidence and transport grammar by which those laws can be related without replacing them.

= Duality, dimension, and the open M

== A duality is a partial transition

Let two local descriptions be $M_alpha$ and $M_beta$. A situated duality is a supplied map
$
  D_(alpha beta):
  U_(alpha beta) subset M_alpha
  -> U_(beta alpha) subset M_beta
$
for which named consequential diagrams commute on the actual overlap. Its domain, approximation,
orientation, and receiver family are part of the relation.

The network of such descriptions has no completed external chart. Any proposed total view is
another situated receiver. In the project's language, $M$ names this open, growing atlas of local
descriptions and transitions, not an absolute container holding every perspective at once.

== Worldline, worldsheet, and worldvolume

A lineage is string-like because it is an ordered one-parameter arc. A co-present transverse
family is sheet-like because it retains relations among several arcs without inventing a
serialization. Transporting the sheet through another parameter sweeps a volume-like
construction. These are dimensions of incidence and record before they are claims about physical
strings.

String theory is relevant because its duality web gives exact physical cases in which
descriptions with apparently different elementary objects, dimensions, radii, couplings, momentum,
and winding can represent the same selected consequences on a stated overlap. Witten's relation
between strongly coupled Type IIA theory and an eleven-dimensional supergravity limit is one
central example @witten1995.

The sigma-model bridge is even more direct. At leading order, the metric beta function contains
the Ricci tensor, so target geometry changes with renormalization scale
@friedan1985. T-duality is a separate relation transporting a background to another chart. Flow
and duality can commute under specific hypotheses, but neither is a universal replacement for
the other.

Holonics extracts the mathematical discipline exhibited by these theories:

- a local description is not absolute;
- the transition has a domain;
- transported observables determine what is shared;
- winding and dimension can change their presented roles; and
- a loop through descriptions can retain nontrivial return.

= Compression, probability, and loss

== Compression is factorization through future questions

Let $q:X -> Q$ be an emitted face and let $cal(O)$ be a declared family of future observations.
The face is receiver-exact precisely when every $o in cal(O)$ factors:
$
  exists bar(o):Q -> Y_o
  quad "such that" quad
  o=bar(o) compose q.
$
Compression is therefore not fundamentally byte count or geometric volume. It is the
factorization of distinctions which are inactive for the declared future relation. When a later
receiver can distinguish two members of one fiber of $q$, the earlier compression was exact only
for the smaller family.

Every event presented through a receiver emits a face. That face is a nontrivial compression
only where $q$ identifies distinctions while the declared future observations still factor
through it. An identity receiver is therefore a lawful uncompressed limiting case. A phase
transition occurs when the current factorization law ceases to continue and a new discrete
invariant or cell type must be carried.

== Probability is a first-person quotient

Let an observer carry a filtration $(cal(F)_t)$ of what has become available on a probability
space $(Omega,cal(F),mu)$. For an event $E$, the receiver-relative conditional field is the
$cal(F)_t$-measurable random variable
$
  "Pr"_(rho) (E | cal(F)_t)
  =bold(E)_(mu) [bold(1)_E | cal(F)_t],
$
characterized by
$
  integral_A "Pr"_(rho) (E | cal(F)_t) dif mu
  =mu(E ∩ A)
  quad "for every" quad A in cal(F)_t.
$
If the contemporary receiver is further restricted to one admitted event
$A_t in cal(F)_t$ with $mu(A_t)>0$, the scalar face is the quotient
$
  "Pr"_(rho) (E | A_t)
  =mu(E ∩ A_t)/mu(A_t).
$
Bayes' theorem rebases this scalar quotient after a new event changes the conditioning region:
$
  "Pr"(H | E)
  =
  ("Pr"(E | H) "Pr"(H))/"Pr"(E).
$

The numbers do not cause the paths and do not declare truth. They summarize recurrence and
admitted possibility from the observer's contemporary position. A deterministic ecology can
produce the same conditional field under the same circumstances while remaining probabilistic
from the first-person receiver that does not contain the complete exterior.

== Loss is the transported residual

For a comparison square with two routes $gamma_1,gamma_2$, the primary loss is the failure to
commute:
$
  cal(L)_rho
  =Chi(gamma_1,gamma_2)
  =(T_(gamma_1),T_(gamma_2)).
$
If an additive chart is supplied, it may be represented as a difference. If a norm is supplied,
that difference may be projected to a nonnegative scalar. Those are later receiver faces.

Loss is consequently information about changed relation. It is neither reward nor punishment and
does not imply that one route exists solely to be corrected. An OPEN residual can become terrain
for a later construction.

= The elements form a network

The reusable library introduced with this paper is organized by mathematical role rather than by
application:

#table(
  columns: (10em, 1fr),
  inset: (x: 5pt, y: 4pt),
  stroke: (x: none, y: 0.4pt + by-rule),
  [Definitions], [Situated occurrence; receiver; holon; comparison face; phase;
    situated event; holonic process double category; causal soul; situated
    formulation family; formulation-span atlas; causal time parity.],
  [Lemmas], [Ordered composition; receiver non-reconstruction; pullback
    composition of formulation spans.],
  [Theorems], [Comparison-boundary closure; transported fundamental theorem;
    causal-parity interval balance, Kirchhoff duality, and phase return;
    soul-sameness hierarchy; positive perspective descent; natural
    contraction feasibility set; exact $pi$ split; exact $e$ split;
    receiver-qualified one-prime Euler formulation cell.],
  [Corollaries], [Point-line-loop as receiver-relative faces; complete natural
    zeta contraction implies RH.],
)

Each object carries a stable key, dependency list, status, claim, proof, and boundary. A paper
imports the object and places it inside a larger argument. The paper may add a geometric
demonstration or an application-specific specialization; it does not become the definition's
owner.

== Immediate extensions

The first formulation layer is now exact: receiver-exact correspondences compose, while
noninvertible quotients remain outside the rechart core. Further objects should be added only
when their exact statements are ready:

1. a theorem for receiver-exact compression under a receiver family which itself changes by
   lawful base transport;
2. a nonlinear or sheaf-valued extension of the causal Stokes and port-return theorem;
3. a local connection and curvature object that supports nonlinear partial transports;
4. a retriangulation theorem separating combinatorial, projective, conformal, and metric
   invariants;
5. a holomorphic return object carrying conjugacy, multiplier, critical orbit, and residual;
6. a Bayesian rebase object over an explicitly supplied filtration and measure; and
7. a phase-boundary object joining continuous deformation to discrete change of cell type.

These are mathematical continuations. None requires machine-learning terminology.

== Applications return as specializations

Once the elementary objects are stable, an application chooses its own medium and laws:

- number theory supplies divisibility, valuations, analytic continuation, and zeta;
- physics supplies metrics, connections, constitutive laws, units, and conservation;
- language supplies inscription, speech, grammar, reference, and consequence;
- computation supplies algorithms, state transitions, storage, and physical execution; and
- machine learning supplies parameterized transformations, conditioning, routing, and update
  laws.

Each can be represented as relational geometry because each has occurrences, boundaries,
transport, comparison, and return. Their domain laws remain indispensable. Holonics does not
replace the sciences; it exposes the common elementary architecture by which their constructions
can be related.

= Conclusion

The foundational object is not intelligence, a model, a number, a particle, or a file. It is a
situated relation in motion.

An occurrence participates in incidence. Transport carries it through an ordered path. A receiver
presents one face. A comparison cell relates alternate paths. A holon closes relative to an
exposed boundary and can become a constituent at another grain. An atlas grows through actual
overlaps. Holomorphy supplies a precise scale-turn chart. Fractal recurrence supplies return and
rebase. Differential geometry supplies local comparison, curvature, and changing metric.
Duality supplies lawful re-expression without an external master view. Probability is a
receiver quotient of admitted recurrence; loss is a receiver face of transported residual;
compression is the successor's contextual factorization.

This is the intended meaning of emergent complexity as a scientific framework. Rich global
structure does not need a different elementary ontology for every application. It needs exact
local relations, carried differences, and a mathematics capable of composing them without
flattening their interiors.

#bibliography("references.bib")
