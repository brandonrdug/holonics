#import "../../lib/elements.typ": *
#import "../../mathematics/catalogue.typ": elements

#show: elements-paper.with(
  title: [Knot-Causal Topology],
  subtitle: [Perspective, irreducibility, tangle substitution, and the completed-zeta sign],
  authors: [Brandon Duggan and Sol],
  date: [24 July 2026],
  abstract: [
    This paper gives the laboratory's knot intuition a typed mathematical
    carrier. An embedded knot, its received diagram, a braid presentation,
    a skein class, a prime connected-sum factorization, and an unknotting
    path are separated. Reidemeister, Alexander, Markov, and Schubert then
    become four distinct laws of presentation and sameness. A receiver
    produces crossings as transverse coincidences in a projected surface;
    movement through the projection discriminant produces Reidemeister
    events, while curvature belongs to the holonomy of alternate receiver
    transports rather than to a crossing count.

    Open tangles provide the exact grammar sought for contextual
    substitution. Rational tangles supply a rigorous meeting of ratios,
    continued fractions, crossings, and boundary-relative topology. Skein
    relations linearize local alternatives without declaring them
    identical. This yields a precise definition of compression as
    substitution modulo every declared future context and receiver. It also
    explains why prime decomposition does not make transformation cost
    additive.

    Applied to formulations of transcendental invariants and to the Riemann
    programme, this grammar sharpens rather than replaces the existing
    obligation. The critical half is typed as the fixed seam of completion
    and the half-density of the Mellin chart; it is not the positive member
    of a skein triple. A proof through knot-causal topology would require an
    exhaustive completed-zeta tangle category, a presentation-independent
    evaluation equal to the Weil response, and local substitutions which
    construct the already-missing natural contraction through an
    independently positive star representation. No such arithmetic skein
    carrier is asserted here.
  ],
)

#outline(
  title: [Contents],
  depth: 3,
  indent: auto,
)
#pagebreak()

= The question and the result

The live question is not whether a visually knotted plot of the zeta
function proves the Riemann Hypothesis. It is whether knot theory already
contains exact structures for five ideas which the laboratory has repeatedly
needed:

+ one underlying construction with many receiver-dependent crossing
  diagrams;
+ irreducible closed returns;
+ finite generators of presentation-equivalence;
+ boundary-preserving replacement of a local interior; and
+ invariants which survive those replacements without becoming the complete
  identity of the construction.

It does. The resulting translation is useful only when its levels remain
separate:

#table(
  columns: (10.5em, 1fr, 1fr),
  inset: (x: 5pt, y: 4pt),
  stroke: (x: none, y: 0.4pt + by-rule),
  table.header([*Knot-theoretic object*], [*Exact role*], [*Holonic relation*]),
  [Embedded knot], [An embedding of a circle in an ambient three-body.],
    [One closed causal return with an exterior.],
  [Diagram], [A generic two-dimensional projection with over/under data.],
    [A receiver face carrying visible crossings.],
  [Braid], [An ordered presentation about a selected axis.],
    [A causally ordered word whose closure forgets presentation data.],
  [Tangle], [An open embedding with a typed marked boundary.],
    [A replaceable interior with an exposed interface.],
  [Skein class], [A linear quotient by declared local relations.],
    [Receiver-exact substitution under a selected linear semantics.],
  [Prime knot], [A nonunit irreducible under connected sum.],
    [An irreducible closed factor for one composition law.],
  [Unknotting path], [Crossing changes separated by isotopies.],
    [A topology-changing trajectory, not a re-presentation.],
)

The strongest new relation is between tangles and compression. An open
interior may be replaced exactly when every declared exterior context and
receiver gives the same consequence. This is the compositional form of
receiver-exact compression. A skein relation is one linear method for proving
such a substitution; it is not the assertion that its local alternatives are
the same knot.

= Four laws of presentation and sameness

== The knot is not the diagram

#object-entry(elements.situated_knot_receiver)

The received crossing population can be written directly. For an oriented
embedding $K:S^1 arrow.r M^3$ and a generic receiver projection
$pi_rho:M^3 arrow.r Sigma_rho$,

$
  cal(C)_rho(K)
  =
  { {s,t}:s!=t, pi_rho K(s)=pi_rho K(t),
    (pi_rho K)'(s) ⋔ (pi_rho K)'(t) }.
$

Each member is an equality in the receiving surface with two distinct source
parameters. Depth order says which branch is over. Orientation supplies a
crossing sign. The embedded curve itself contains neither a literal
self-intersection nor an intrinsic crossing vertex.

This resolves the apparent conflict between “crossings depend on
perspective” and “knot type is invariant.” They refer to different objects.
The projection may acquire or lose crossings while the ambient-isotopy class
of $K$ remains exact.

== Reidemeister, Alexander, Markov, and Schubert

#object-entry(elements.knot_presentation_sameness)

The four classical theorems answer four different questions
@reidemeister1927 @alexander1923 @markov1936 @birmanmenasco2002
@schubert1949:

#table(
  columns: (8.5em, 1fr, 1fr),
  inset: (x: 5pt, y: 4pt),
  stroke: (x: none, y: 0.4pt + by-rule),
  table.header([*Theorem*], [*Question*], [*Generators*]),
  [Reidemeister], [When do two diagrams present the same link?],
    [Planar isotopy and the three local diagram moves.],
  [Alexander], [Can every oriented link be presented by an ordered braid?],
    [Every link is the closure of at least one braid.],
  [Markov], [When do two braid presentations have the same closure?],
    [Braid isotopy, conjugation, and stabilization/destabilization.],
  [Schubert], [How does a knot factor under connected sum?],
    [A unique unordered multiset of prime-knot factors.],
)

This is a precise refinement of the soul hierarchy. Reidemeister moves retain
closure type while changing the diagram. Markov moves retain closure type
while changing braid index and braid presentation. Prime decomposition
retains the connected-sum object while exposing its factors. None preserves
the complete causal path by which the particular occurrence was formed.

Alexander's theorem is especially important for the laboratory's axis
language. It says that an oriented link can be re-presented as strands moving
monotonically around a braid axis. The axis is part of that presentation; it
is not an absolute coordinate embedded in the knot type. Markov's theorem
then states exactly how different axis-relative presentations can close to
the same link.

== A nontrivial knot cannot be isotoped into the unknot

The phrase “a nontrivial knot which cannot be unknotted” needs one operation
specified.

+ Under ambient isotopy, every nontrivial knot remains nontrivial. This is
  what *nontrivial knot type* means. Reidemeister moves cannot turn its
  diagrams into an unknot diagram.
+ Under crossing change, every tame knot admits an unknotting sequence. Its
  unknotting number $u(K)$ is the minimum number of crossing changes over
  all diagrams and intervening isotopies.
+ An algorithm can decide whether a tame knot is the unknot; recognition is
  different from finding a minimal unknotting path @hass1999algorithms.

A crossing change is not a new camera orientation. It passes one branch
through another and changes the embedding type. The distinction is the
topological counterpart of separating a receiver rechart from a causal deed.

== Prime means irreducible under one composition

The unknot is the unit of connected sum. A prime knot is a nonunit $K$ such
that

$
  K=K_1 op("#") K_2
  quad arrow.r.double quad
  K_1=0_1 " or " K_2=0_1.
$

Schubert's theorem makes the connected-sum monoid a free commutative monoid
on prime-knot types. This is a real structural analogy with positive
integers under multiplication. It is not an identification:

#table(
  columns: (1fr, 1fr),
  inset: (x: 5pt, y: 4pt),
  stroke: (x: none, y: 0.4pt + by-rule),
  [*Positive integer monoid*], [*Oriented knot monoid in $S^3$*],
  [$1$ is the unit.], [The unknot $0_1$ is the unit.],
  [Primes are multiplicatively irreducible.], [Prime knots are
    connected-sum irreducible.],
  [Factorization is a multiset of primes.], [Factorization is a multiset of
    prime-knot types.],
  [Arithmetic valuations record multiplicity.], [Prime-knot multiplicities
    record connected-sum factors.],
)

The analogy ends before cost, order, geometry, linking, or spectral response.
The free generators belong to different monoids.

= Prime decomposition does not decompose transformation cost

Brittenham and Hermiller prove that unknotting number is not additive under
connected sum @brittenhamhermiller2025. For the $(2,7)$ torus knot
$K=7_1$ and its mirror $bar(K)$,

$
  u(K)=u(bar(K))=3,
  quad
  u(K op("#") bar(K))<=5<6.
$

The intermediate isotopies matter. A crossing change modifies the whole
standing knot, another presentation is exposed, and the next useful crossing
need not belong to either original summand. Unique factorization of objects
therefore does not imply additive distance in the graph of topology-changing
deeds.

This distinction is decisive for compression. A construction may have
irreducible constituents while a joint contextual replacement is cheaper,
more expensive, or simply incomparable with the sum of independent
replacements. The complete boundary and peripheral relation matter. Even the
knot group alone does not determine unknotting number; the knot together with
its peripheral structure recovers the needed embedding information
@gordonluecke1989 @brittenhamhermiller2025.

= Crossings form a receiver field

== Chambers and the projection discriminant

#object-entry(elements.receiver_discriminant_curvature)

Let $cal(P)$ parameterize the embedding and receiver together. The
discriminant $Delta$ contains nongeneric projections: tangencies, cusp
events, triple coincidences, and other failures of the transverse-double-point
chart. Inside one chamber of $cal(P) minus Delta$, the diagram continues
without a combinatorial event. A generic one-parameter path through
$Delta$ gives a Reidemeister movie.

This is the rigorous form of visible crossings changing under precession.
The receiver trajectory

$
  rho:I arrow.r cal(P)
$

does not sample unrelated images. It carries one ordered lineage of diagrams.
The Reidemeister events are its discrete seams. Between seams, projected
vertices and arcs move continuously.

Vassiliev's study of discriminant complements demonstrates the wider
principle: knot invariants can arise from the topology of the space of maps
after singular maps are organized as a discriminant @vassiliev1997.

== Three meanings of crossing

The word *crossing* now has three typed uses:

1. a projected double point in $D_rho(K)$;
2. a crossing change, which changes the over/under relation and may change
   knot type; and
3. the crossing of two transformation paths in a comparison diagram.

Only the first is created by the receiving projection. Only the second is an
unknotting deed. The third is categorical or geometric incidence and may
exist without a knot. Treating the three as one scalar “number of crossings”
would erase exactly the causality the laboratory is trying to retain.

== Curvature emerges from alternate receiver transports

A path $rho(t)$ supplies order, winding, and discrete seam events. It does
not by itself supply curvature. Curvature requires at least one alternate
direction of comparison.

Let $E_rho$ be the receiver-relative fiber and $U_(i j):E_i arrow.r E_j$ the
transport along an edge of a receiver triangle. Then

$
  Omega_(012)=U_(02)-U_(12)U_(01)
$

is an additive comparison residual, while

$
  H_(012)=U_(20)U_(12)U_(01)
$

is the returned holonomy when the edge maps are invertible. In a smooth
connection chart,

$
  F_nabla=d A+A ∧ A.
$

This is curvature from perspective over orders of time: two ordered
receiver histories begin at the same cut, reach a comparable cut, and fail
to induce the same transport. The receiver participates because its own
motion supplies the paths being compared. No observer outside the system is
needed.

At the coarse knot-type receiver, Reidemeister loops may have trivial
holonomy because they return to the same ambient-isotopy class. A finer
framed, braid, metric, tangle, or causal-lineage receiver can retain a
nontrivial return. Curvature is therefore receiver-relative without becoming
arbitrary.

== Where the gyroparallelogram fits

In a gyrocommutative gyrogroup, addition is associative only after the
automorphism

$
  op("gyr")[a,b]c
$

corrects the comparison of alternate bracketings. In the Einstein
gyrovector model this gyration is the algebraic carrier of Thomas rotation
or precession @ungar2001. A gyroparallelogram is consequently a concrete
curved replacement for the Euclidean parallelogram law.

This is relevant when the receiver transitions genuinely compose by a
gyrogroup law. Then $op("gyr")[a,b]$ is a finite holonomy face of the
noncommuting transports. It should not be installed as the universal law of
every comparison complex. The general object is connection and holonomy;
the gyroparallelogram is one exact hyperbolic specialization.

= Axis, unit, and ratio

#object-entry(elements.typed_axis_unit_ratio)

== An axis is typed transport space, not a drawn coordinate line

A typed axis is an oriented one-dimensional fiber or line bundle. Its type
says what kind of comparison is admitted. Its orientation says which
direction is positive. An origin, a unit, and a connection are additional
choices.

If $u$ is a local unit and $q=x u$, changing to $u'=a u$ gives

$
  x'=a^(-1)x.
$

The quantity has not changed merely because its coordinate has. This is the
precise sense in which a unit is an addressable axis face: the label selects
a local frame, while the complete quantity remains a typed geometric
element.

A comparison between axes is a map

$
  Phi:A_d arrow.r A_e.
$

Chosen units turn it into a scalar $r$ by $Phi(u_d)=r u_e$. Rebase either
unit and the scalar changes covariantly. Ratios in measurement therefore do
require comparable axes and a law between them. Bare arithmetic rational
numbers do not: $m/n$ is already the projective class $[m:n]$.

This distinction preserves Brandon's intuition while preventing it from
becoming false by overextension:

+ a *rate* requires two typed variables;
+ a *scale factor* compares two frames;
+ a *probability quotient* compares a part to a conditioned total under a
  measure;
+ a *cross-ratio* compares four incidences projectively; and
+ a *rational number* is an algebraic equivalence class before any physical
  or informational interpretation.

== The triangle face of one half

Let an oriented triangle have edge chain

$
  partial [0,1,2]=[1,2]-[0,2]+[0,1].
$

If one receiver partitions its three edge occurrences into a distinguished
base $B={e_0}$ and a paired complement $L={e_1,e_2}$, then

$
  abs(B)/abs(L)=1/2.
$

This is a valid combinatorial face of one-per-two. It is not the ratio of
the side lengths of an equilateral triangle, since those are $1:1:1$ after
normalization. Direction and causal parity live in the oriented boundary
signs and in whatever transport each edge carries.

The construction is nevertheless important. The smallest closed
two-dimensional comparison has three oriented edges, alternate routes, and
one boundary cancellation law. If those edges become hinges in a larger
simplicial complex, their behavior is conditioned by the co-present faces;
there is no context-free scalar state “per triangle.”

== Why the critical half is not decimal convention

Write

$
  s=1/2+z.
$

The completed involution $s mapsto 1-overline(s)$ becomes

$
  z mapsto -overline(z).
$

The line $op("Re")(s)=1/2$ is therefore the fixed locus of this reflection.
It is also the square-root-density line for the standard multiplicative
measure after the logarithmic/Mellin rebase. These are typed analytic roles,
not a consequence of base ten.

The same glyph has other exact faces:

#table(
  columns: (10em, 1fr),
  inset: (x: 5pt, y: 4pt),
  stroke: (x: none, y: 0.4pt + by-rule),
  [$[1:2]$], [A projective rational coordinate.],
  [$1/2$], [The affine midpoint fixed by $x mapsto 1-x$.],
  [$(I+J)/2$], [The projector onto the fixed subspace of an involution $J$.],
  [$beta/2$], [The half-density seam for $r^beta dif r/r$.],
  [$op("Re")(s)=1/2$], [The completed-zeta fixed seam when $beta=1$.],
)

These are connected by specified constructions; they are not interchangeable
because the numeral looks the same.

= Tangles make interiors compositional

== An open knot has a boundary

A tangle is a properly embedded collection of arcs and circles in a
three-ball or cylinder, with marked endpoints on the boundary. It is the
natural unit of local substitution because an exterior can be held exact
while the interior changes.

#object-entry(elements.contextual_tangle_compression)

The relation

$
  T approx_cal(R) T'
  quad "iff" quad
  R(C[T])=R(C[T'])
$

for every declared receiver $R$ and compatible exterior context $C$ is the
rigorous form of “the same constituent may be used here.” It is not absolute
identity. It is a congruence at a typed interface.

This also supplies a better definition of link substitution. The link is
not cut at an arbitrary visual region. A boundary sphere or disk exposes a
marked interface; a replacement tangle must meet exactly that interface; and
the declared receiver determines which resulting consequences must remain
exact.

== Rational tangles are ratios with crossing interiors

Conway's rational tangles provide an unusually direct bridge between the
laboratory's ratio and crossing intuitions. Starting from the trivial
tangles, a finite sequence of horizontal and vertical twists produces a
rational tangle. Its twist word gives a continued fraction

$
  [a_1,a_2,dots,a_n]
  =
  a_1+1/(a_2+1/(dots+1/a_n)).
$

Kauffman and Lambropoulou prove that rational tangles are classified up to
isotopy by their fraction in $QQ union {infinity}$ @kauffmanlambropoulou2004.
Thus different diagrams and flypes can carry the same boundary-relative
tangle type, while the continued fraction records one exact generated path.

This is not evidence that every ratio is secretly a knot. It is an
established domain in which:

+ a projective ratio;
+ a finite series of reciprocal rebases;
+ an oriented crossing word;
+ a boundary-relative embedding; and
+ an isotopy classification

belong to one construction.

A crossing change is the simplest rational subtangle replacement. Baker and
Buck classify much wider rational subtangle replacements and show that their
sites are constrained by the topology of the branched double cover
@bakerbuck2016. Local replacement is therefore not free-form editing; the
available replacements depend on the complete exterior.

== Skein relations linearize alternatives

Let $L_+,L_-,L_0$ agree outside one disk and differ inside it by positive
crossing, negative crossing, and oriented smoothing. The Conway relation is

$
  nabla_(L_+)(z)-nabla_(L_-)(z)=z nabla_(L_0)(z).
$

The three links need not be isotopic. Their invariant values are linearly
related. Przytycki's skein module makes the construction general: start with
the free module on ambient-isotopy classes and quotient by the submodule
generated by declared local skein combinations @przytycki1991.

This is why $L_+$ cannot be read as “the positive case” of the Weil
criterion. The plus and minus name local oriented crossing species. The
coefficients of a skein relation can be negative, Laurent, or complex. A
skein recursion is not a positivity proof.

Jones's planar-algebra framework supplies the more relevant positive
refinement. Planar tangles act by multilinear contractions; an involution
comes from reflection; and additional positivity hypotheses can turn the
result into a star-algebraic/operator object @jones1999. Positivity is extra
structure on the evaluation, not a gift of the strings.

= Compression is contextual substitution

#object-entry(elements.contextual_skein_compression)

An open computation, formula fragment, neural subnetwork, proof fragment, or
geometric patch may be treated as a tangle only after its input/output
boundary and composition law are supplied. Then an interior replacement is
exact when every declared later context factors through the quotient.

This yields four separate questions:

1. *Equivalence:* do the two interiors have the same declared behavior in
   every admitted context?
2. *Presentation:* is that equivalence generated by a finite local move
   calculus?
3. *Normalization:* do the moves terminate or possess a canonical form?
4. *Cost:* is the replacement cheaper under the selected physical or
   computational measure?

None implies the next automatically. Reidemeister's theorem answers the
second question for knot diagrams while saying nothing simple about the
shortest move sequence. Brittenham--Hermiller show that even a natural
topology-changing cost is not additive over prime factors.

For learned networks, the implication is precise. We should not delete
“weak” scalar weights or retain “strong” edges as if those numbers were
context-free. A candidate subnetwork has an exposed activation interface.
Its replacement is exact only for the ecology of contexts and receivers in
which the two induced boundary maps agree. Approximate compression replaces
equality by an explicitly chosen metric, measure, or test family; the
residual must remain typed by that choice.

= Transcendental invariants as closures of formulation tangles

Pi, $e$, and other transcendental constants have many series, products,
integrals, limits, recurrences, and algorithms. The common value is one
closure receiver. The complete formulation is better represented as an open
tangle with:

+ parameter and branch boundaries;
+ arithmetic coefficient currents;
+ an ordered generator or recurrence;
+ a convergence domain and discriminant;
+ an evaluation or limiting closure; and
+ alternate proven local substitutions.

For a formulation $T$ and evaluation context $C_"eval"$,

$
  C_"eval"[T]=pi
$

does not make all such $T$ identical. Euler transformations,
hypergeometric identities, contour deformations, continued-fraction
contractions, and recurrence changes are skein-like only when a proved local
identity makes them compositional on the stated domain.

This refines “the invariant can be attained from any perspective.” A lawful
receiver can attain the invariant when its formulation has an admissible
evaluation path. An arbitrary perspective with no decoder, convergence law,
or transition map does not.

The knot carrier nevertheless adds something new to the formulation atlas.
It distinguishes:

+ an *open formulation tangle*, whose interface can compose;
+ a *closed invariant face*, such as the returned value;
+ a *presentation move*, which changes the formula without changing the
  represented formulation;
+ a *skein substitution*, which linearly relates nonidentical formulations;
  and
+ a *prime factorization*, which applies only when a selected composition
  monoid has irreducibles.

The arithmetic populations of primes and semiprimes inside a series belong
to the tangle interior. They can affect convergence, cancellation,
monodromy, and available substitutions even when the closure value is the
same.

= Arithmetic topology and primitive returns

For $op("Re")(s)>1$,

$
  zeta(s)
  =
  product_p (1-e^(-s log p))^(-1),
$
$
  -zeta'(s)/zeta(s)
  =
  sum_p sum_(m>=1)(log p)e^(-s m log p).
$

This has the exact grammar of primitive closed returns: $p$ labels a
primitive period of length $log p$ and $p^m$ its $m$-fold traversal.
Deninger develops the prime--knot--periodic-orbit analogy in this precise
dynamical direction @deninger2023. Connes and Consani construct an
arithmetic-geometric instance in which periodic orbits have length $log p$
and Frobenius appears as their monodromy @connesconsani2024
@connesconsani2025.

These results justify studying knot-like return structure around primes.
They do not identify connected sum with integer multiplication, a knot
polynomial with the Riemann zeta function, or diagram crossings with zeta
zeros. The complete explicit formula remains population-level: prime powers
on one side, zeros and archimedean terms on the other.

= What the knot grammar changes for RH

== The Weil condition is not a choice of crossing sign

For the standard admitted test class, the Weil criterion asks for a
Hermitian quadratic response

$
  Q_W(f)>=0
$

for every test current, and this positivity is equivalent to RH. When the
zeros lie on the critical line, the zero contribution can be represented in
the required square-norm form. An off-line zero produces a genuine negative
direction for a suitable test. Invertible receiver recharting cannot change
that inertia.

This is unrelated to calling one member of a skein triple $L_+$. The latter
is an oriented local crossing. The former is positivity of a global
Hermitian form over an exhaustive test space.

== The fixed half has an orbit interpretation

Center $s=1/2+z$ and attach a return of length $ell$:

$
  lambda_ell(z)=e^(-ell z).
$

Completion gives

$
  lambda_ell(-overline(z))
  =
  1/overline(lambda_ell(z)).
$

Therefore

$
  op("Re")(z)=0
  quad arrow.l.r quad
  abs(lambda_ell(z))=1.
$

The critical seam is the unit-modulus locus of the centered return. The
functional equation pairs inside and outside radial sheets but does not
force every zero orbit to be fixed. The figure-eight knot supplies the
finite-dimensional counterimage: reciprocal Alexander monodromy can have
one eigenvalue inside and one outside the unit circle.

In orbit language, completion partitions a zero population into:

+ fixed orbits on $op("Re")(s)=1/2$; and
+ paired size-two orbits off the line.

RH says the nontrivial zero population consists only of fixed orbits. The
existence of the involution proves the partition, not the absence of the
second species.

== The exact skein-shaped proof architecture

#object-entry(elements.positive_skein_carrier_rh)

Knot theory now supplies a possible presentation grammar for the existing
RH obligation. Let $cal(Z)$ be a proposed completed-zeta tangle category.
Its boundaries would type:

+ finite-prime apertures;
+ archimedean Fourier--Poisson--Mellin transport;
+ support growth;
+ test-current involution; and
+ receiver recharting.

Its local relations would have to be proved analytic substitutions: Euler
admission, Poisson summation, Mellin rebase, support continuation, or another
actual identity. A closure evaluation

$
  E:cal(Z) arrow.r op("Herm")
$

would have to equal the complete Weil response, not merely resemble it.
Reidemeister/Markov analogues would prove that $E$ is independent of
presentation. A positive star representation would then have to turn every
generating substitution into the components of the already-required natural
contraction

$
  Y_j=Gamma_j X_j,
  quad
  norm(Gamma_j)<=1.
$

If all of that were constructed exhaustively, RH would follow. This is a
conditional proof architecture, not a proof.

== The genuinely new obstruction exposed by skein theory

Skein recursion alone is insufficient because ordinary skein coefficients
are not positivity-preserving. A local identity of the form

$
  alpha E(L_+)+beta E(L_-)+gamma E(L_0)=0
$

can have signed or complex coefficients. Repeated resolution may compute an
invariant while alternating signs. It need not preserve the positive
semidefinite cone.

The proof-bearing local object is therefore more specific:

> an arithmetic--archimedean tangle relation whose evaluation is a
> completely positive or contractive star-compatible map, whose closure is
> exactly the Weil form, and whose relations are coherent under every
> prime/support/receiver gluing.

This does not rename the old wall. It identifies a possible *generator
grammar* for constructing the missing natural contraction and states the
additional property that ordinary skein relations lack.

Convexity enters only after evaluation: positive semidefinite forms and
operator contractions form convex sets. Concavity may enter through a
log-determinant barrier on a positive-definite finite restriction. Neither
is a topological invariant of a knot diagram.

= Compression and RH share one local-to-global problem

The machine-learning and RH applications now meet at a real mathematical
relation rather than a metaphor.

#table(
  columns: (10em, 1fr, 1fr),
  inset: (x: 5pt, y: 4pt),
  stroke: (x: none, y: 0.4pt + by-rule),
  table.header([*Structure*], [*Compression specialization*], [*RH specialization*]),
  [Boundary], [Activation, state, or callable interface.],
    [Test-current, support, prime, and archimedean interface.],
  [Interior], [A contextual subnetwork or algorithmic constituent.],
    [One arithmetic--archimedean formulation tangle.],
  [Context], [The ecology of later uses.],
    [Every admissible Weil test and aperture continuation.],
  [Receiver], [Declared behavior, metric, or task family.],
    [The complete Weil quadratic response.],
  [Substitution], [A boundary-equivalent replacement.],
    [A proved local analytic relation.],
  [Positive law], [An explicit approximation/error geometry when needed.],
    [A natural contraction or completely positive evaluation.],
)

Both applications fail if one equal output is mistaken for contextual
equivalence. Both fail if an irreducible decomposition is mistaken for an
additive simplification cost. Both require local substitutions to remain
coherent when embedded in larger exteriors.

The difference is jurisdiction. Compression may select a bounded receiver
family and tolerate a declared residual. RH quantifies over the complete
admissible Weil test space and tolerates no unaccounted negative direction.

= Derived vocabulary

The requested terms can now be stated without metaphor:

- *Axis:* a typed oriented one-dimensional transport fiber; origin, unit,
  and connection are additional local data.
- *Unit:* a chosen nonzero local frame in that fiber. The label addresses
  the frame; rebase changes coordinates covariantly.
- *Ratio:* algebraically, a projective class $[m:n]$; operationally, the
  scalar coordinate of a declared comparison between typed axes.
- *Crossing:* for a knot receiver, a transverse coincidence of two distinct
  source parameters in the received surface, with depth and orientation
  data.
- *Knot invariant:* a receiver which factors through ambient-isotopy class.
  It is not necessarily complete.
- *Prime knot:* a nonunit irreducible under connected sum.
- *Unknotting:* a topology-changing path through crossing changes and
  intervening isotopies, not isotopy alone.
- *Tangle:* an open embedded interior with a typed marked boundary.
- *Skein relation:* a local linear relation among nonidentical tangle or
  link alternatives.
- *Compression:* contextual receiver equivalence followed by a quotient or
  representative choice.
- *Perspective curvature:* the holonomy or comparison residual between
  alternate receiver transports over a two-dimensional parameter cell.

= Present boundary

This derivation changes the programme in three concrete ways.

First, it supplies a standard topological carrier for the laboratory's
relative crossing field. Second, it replaces vague “link substitution” with
typed tangle gluing and contextual congruence. Third, it identifies a new
local condition for an RH-directed construction: the desired
arithmetic--archimedean relations must preserve positivity through a
star-compatible evaluation, not merely compute the same invariant by a
skein recursion.

It does not prove RH. The same global sign wall remains: construct the
completed-zeta natural contraction, or an equivalent positive trace carrier,
from the actual arithmetic and archimedean relations. Knot theory now
suggests how that carrier could be presented and checked for independence of
local formulation. It does not supply its arithmetic generator.

The most informative next proof-directed object is therefore not another
knot visualization or a census of prime knots. It is one exact local
Poisson--Mellin/Euler-support substitution square, written as an open tangle,
followed by a test of whether its operator evaluation is star-compatible and
contractive on the already-derived dyadic character cell. A positive result
would construct the first generator of the proposed arithmetic skein
carrier; a negative result would rule out this route without moving the wall
again.

#bibliography("references.bib")
