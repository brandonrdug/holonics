#import "../../lib/elements.typ": *
#import "../../mathematics/catalogue.typ": elements

#show: elements-paper.with(
  title: [Categorical Holonics],
  subtitle: [Causal souls, situated perspectives, and the emergence of domain law],
  authors: [Brandon Duggan and Sol],
  date: [26 July 2026],
  abstract: [
    This paper gives the laboratory's agnostic causal-compositional thesis a
    categorical carrier. A holonic process is represented as an open,
    boundary-typed construction; sequential events compose by lawful gluing,
    independent constructions compose monoidally, and actual co-presence is
    supplied by a typed interaction pattern. Evolution shape, parameter
    ecology, receiver fiber, local observation, and physical realization
    remain distinct compositional structures. A soul is refined from a scalar invariant or stored
    provenance into a marked causal diagram. Strict occurrence identity,
    soul-equivalence, receiver equivalence, equality of one face, and equality
    of a serialized digest are thereby separated. Yoneda's lemma explains the
    valid sense in which a construction is determined by all of its relations,
    while structured cospans and black-box functors explain how interiors can
    compose or lawfully depart. A global face is defined only as compatible
    local transport across a cover of one declared boundary; no absolute total
    field is postulated.

    The framework does not assert one equation for every domain. A domain is a
    representation of the causal carrier into its own algebraic, analytic,
    geometric, logical, physical, or computational category. Conservation,
    time reversal, holonomy, metric, and field equations emerge only after that
    representation supplies their hypotheses. Applied to the laboratory's
    Riemann programme, the receiver-dependent sign problem becomes one
    coherent convex feasibility object: a natural family of contractive
    fillers between the already-derived completed-zeta amplitude functors.
    This is a sharper form of the existing Weil-positivity obligation, not a
    proof of RH.
  ],
)

#outline(
  title: [Contents],
  depth: 3,
  indent: auto,
)
#pagebreak()

= The question being answered

The Universality Machine is not a proposal that one indiscriminate equation governs
mathematics, physics, language, biology, and computation. It is a proposal for a common
*causal-compositional carrier*: a way to state what is exposed, what is joined, what is
transported, what changes under perspective, what returns, and what remains open. Each domain
still supplies the objects and laws which make those verbs meaningful.

This distinction corrects two opposite reductions.

First, physics is not the foundation from which the other domains are metaphorically copied.
Orientation, reciprocal passage, closed return, and accumulated turn are pre-domain structures.
A physical representation may turn them into current, phase, stress, curvature, or conservation
only after it supplies units, a metric, a constitutive law, and dynamics.

Second, category theory is not a vocabulary replacement which makes all structures equivalent.
It is useful here because it separates:

- an object from one presentation of it;
- a process from its source and target;
- sequential composition from co-presence;
- a coordinate change from a causal event;
- a local invariant from the diagram which carries it; and
- structural equivalence from literal occurrence identity.

Riehl's account of Yoneda, naturality, equivalence, the category of elements, and Kan extension
provides the general language @riehl2016. Fong's decorated cospans and Baez--Courser's structured
cospans provide compositional carriers for open systems @fong2015 @baezcourser2020. They are
external mathematics used to sharpen the laboratory's own definitions; they are not being
claimed as novel results of this paper.

The contemporary refinement uses functorial evolution shapes @wang2026, enriched
parameter semantics @rosswesley2026, double-operadic interaction doctrines
@libkindmyers2025, oriented fibrations @gepnerheine2026, sheaf gluing and contextual
obstruction @sargsyan2026, synthetic information order @xue2026, and doctrinal type
spaces @abbadiniguffanti2026. These sources do not collapse into one universal category.
Each supplies one typed compositional direction which the earlier carrier had made too
coarse.

= The holonic process carrier

== Open construction has two categorical directions

#object-entry(elements.holonic_process_double_category)

The double-category form matters. A one-category process notation can record

$
  a arrow.r^X b,
$

but it tends to conflate a process from $a$ to $b$ with a recharting of the boundaries
themselves. The double category keeps them perpendicular:

#table(
  columns: (9em, 1fr, 1fr),
  inset: (x: 5pt, y: 4pt),
  stroke: (x: none, y: 0.4pt + by-rule),
  table.header([*Direction*], [*Carrier*], [*Holonic reading*]),
  [Horizontal], [Decorated open construction], [A causal process with exposed input and output.],
  [Vertical], [Boundary map], [A lawful rechart, restriction, or change of exposed interface.],
  [2-cell], [Commuting apex map], [A comparison which preserves the named boundaries and decorations.],
  [Monoidal], [Coproduct/juxtaposition], [Plural systems are available together without asserting contact.],
  [Interaction], [Operadic or double-category action], [A supplied wiring, sharing, lens, or incidence pattern makes systems meet.],
)

The standard structured-cospan theorem says that under finite-colimit and preservation
hypotheses, these objects form a symmetric monoidal double category @baezcourser2020. That
theorem does not decide the laboratory's decorations. Orientation, native partial order,
parameters, open residuals, receiver family, and consequential boundary must be chosen because
they are exactly the distinctions the intended use can still observe.

Coproduct is therefore not the definition of co-presence. It supplies independent
juxtaposition. Actual contact is an action of a separately declared interaction doctrine:
port-plugging, variable sharing, guarded incidence, lenses, or another typed interface pattern
@baez2026 @libkindmyers2025. This distinction blocks the construction error in which an
application injects unrelated objects and calls their shared container a manifold.

== Lambda is an enriched situated move

The historical expression

$
  Lambda_F(Q ⊗ A ⊗ L) arrow.r (P,pi_B)
$

is therefore best read as a compact presentation of one selected horizontal cell, not as the
definition of the category and not as a universal tensor equation. In a specialization:

- $Q$ is the oriented question or frame pressure entering the source boundary;
- $A$ is standing relation available at that boundary;
- $L$ is the live source incidence and native chronology;
- $P$ is the consequential outgoing boundary; and
- $pi_B$ is testimony under a named receiver.

The symbol $⊗$ is lawful only when the chosen monoidal product really models their
juxtaposition and the interaction doctrine supplies their actual meeting. A pushout is lawful
only when the chosen boundary maps really license their composition. When those hypotheses
fail, the result is an OPEN comparison, not permission to silently glue.

The parameter population is not a passive Cartesian tuple. Let $cal(P)$ be a monoidal
parameter category and let process homs be $cal(P)$-enriched. Then one parameterized move is
a generalized element

$
  kappa:P arrow.r underline("Hom")(a,b).
$

Sequential composition uses the enrichment. Copying, retaining, or discarding $P$ is legal
only when its carried comonoid or resource structure permits it @rosswesley2026. A reusable
law, a singular occurrence, a live lineage, and a persistent control therefore need not have
the same copying and departure behavior.

== Evolution shape and realization

Let $cal(S)$ name the stages and admissible evolutions of one causal algorithm. A realization
in a coefficient category $cal(C)$ is a functor

$
  X:cal(S) arrow.r cal(C).
$

The shape says which continuations compose; the coefficient category says what those
continuations are made of. One shape may therefore be realized as exact geometry, a state
machine, a physical circuit, or another domain without identifying those realizations
@wang2026. A CPU and a GPU implementation are related only where a natural comparison or
refinement preserves the declared boundary conduct.

== Holon is a bounded open subdiagram

The elementary holon

$
  H_rho=(X,B_rho,cal(T),q_rho)
$

now has a precise categorical home. It is a locally closed, receiver-bounded subdiagram of the
open process carrier. Its wholeness is relative to $B_rho$ and the admitted transport
family $cal(T)$. It can be a horizontal process at one grain and one participating
decoration of a larger horizontal process at another.

This retains the project's refusal of a global ownership tree. Overlapping holons, plural
parents, returned loops, and a constituent which later departs are ordinary diagrammatic
possibilities.

= Perspective is an internal functor

== A receiver must preserve the composition it claims to observe

An elementary receiver is a supplied map

$
  q_rho:X arrow.r Y_rho.
$

For a sequence of open processes, a stronger claim is needed. A receiver is compositional on a
declared process region only when it extends to a functor

$
  R_rho:op("HolProc")_cal(D)^0 arrow.r cal(V)_rho
$

from the relevant horizontal bicategory into a category of faces. Functoriality says that the
receiver's presentation of a lawful composite agrees with composition of the presentations:

$
  R_rho(Y compose X)
  =
  R_rho(Y) compose R_rho(X).
$

This is not demanded of every instrument. If it fails, the difference is precisely a
composition residual at that receiver. The receiver remains inside the system because its
functor, domain, and failure are all part of the represented event.

== Recharting is oriented naturality, not an exempt camera

Suppose two receiver species $R_rho$ and $R_sigma$ are comparable. A lawful systematic
translation is a natural transformation

$
  eta:R_rho arrow.r.double R_sigma.
$

For every admitted process $f:X arrow.r Y$, strict naturality is the commuting square

$
  eta_Y compose R_rho(f)
  =
  R_sigma(f) compose eta_X.
$

This is the exact counterpart of saying that the camera is not outside the geometry. Changing
the receiver changes the presented face according to a law which must commute with the process
being observed. More generally the receiver can be lax or oplax: an oriented 2-cell retains
the directed difference between the two passages. If no such cell is supplied, the square is
OPEN; no absolute image repairs it.

Let $cal(R)$ be the receiver category and

$
  p:cal(E) arrow.r cal(R)
$

the fibration of receiver-local ecologies. Its fiber $cal(E)_rho$ contains the constructions
available to $rho$; cartesian or cocartesian lifts state how they transport along a receiver
change. The Grothendieck construction assembles this indexed atlas while oriented fibrations
retain lax and oplax comparison @gepnerheine2026. Its total category is bookkeeping for all
fibers, not a privileged total observer.

= Global is transported local assembly

#object-entry(elements.receiver_indexed_holonic_system)

The word *global* is used here only relative to one declared region $U$. The region has a real
boundary and a receiver cover ${U_i arrow.r U}$. A global face is a section over $U$ assembled
from compatible local sections. It is not “absolutely true everywhere” and it is not a total
field containing every potential relation.

#object-entry(elements.local_global_holon_assembly)

This is the categorical form of the holon. A whole is locally composed and relatively closed
at one grain. A global invariant emerges when a local standing transports across the complete
contemporary cover and remains compatible on every overlap. Without local sections there is
nothing to globalize. With a nontrivial return around an overlap cycle, pairwise local
testimony can remain valid while no global section exists @sargsyan2026.

The present question and exposed boundary select an admitted evolution subdiagram
$cal(S)_F$. The surrounding categories can contain indefinitely many potential arrows, but
only those which factor into the contemporary construction are causally relevant. This is how
a constrained three-body system avoids enumerating every possible three-body history: the
parameterized inertial currents and current boundaries carry the actual trajectory, while
irrelevant potential branches never enter the active factorization.

= Soul is causal diagram, not checksum

== The categorical refinement

#object-entry(elements.causal_soul)

The historical record uses *soul* for several related but nonidentical things:

- the complete worldline or construction;
- the cross-ratio $chi$ transported across a frame;
- winding or holonomy deposited by a loop;
- a topological obstruction not readable from one boundary;
- the distinction between equal face and different construction; and
- in older software, recursively retained provenance.

No one scalar can carry all of these meanings. The categorical refinement makes the causal
diagram primary. Cross-ratio, winding, holonomy, cohomology class, monodromy, and spectrum become
characteristics obtained from that diagram under particular functors.

This also preserves the strong intuition behind “every transformation makes a new soul.”
A new event is a new situated occurrence even when its causal diagram is isomorphic to an
earlier one. Structural recurrence is soul-equivalence; it is not numerical identity and it is
not the return of the original occurrence.

== Seven different claims of sameness

#object-entry(elements.soul_sameness_hierarchy)

The resulting hierarchy is:

#table(
  columns: (9.5em, 1fr, 1fr),
  inset: (x: 5pt, y: 4pt),
  stroke: (x: none, y: 0.4pt + by-rule),
  table.header([*Sameness*], [*What is preserved*], [*What it does not imply*]),
  [Occurrence identity], [The same situated event token and marked diagram.],
    [That every later presentation is unchanged.],
  [Soul-equivalence], [The complete marked causal diagram up to natural isomorphism.],
    [Literal recurrence of one event.],
  [Doctrinal equivalence], [The same predicates in one declared observational language.],
    [Equivalence under a richer doctrine.],
  [Observational equivalence], [Isomorphic algebras of admitted observations.],
    [Isomorphism of the complete causal diagram.],
  [Receiver equivalence], [The diagram after one compositional receiver functor.],
    [Equivalence under other receivers.],
  [Equal face], [One selected output, value, spectrum, image, or label.],
    [Equal causal interior.],
  [Equal digest], [One serialized byte face after a digest receiver.],
    [Structural or causal identity.],
)

Yoneda gives the correct strong statement. A soul bearer is determined up to isomorphism by
its *complete natural family of relations* to every other object in its category @riehl2016.
It is not determined by one characteristic. Thus the project's relational intuition is
mathematically sound when “all relations” means a representable functor and when the
category's markings retain the distinctions at issue.

It follows immediately that $chi$ should no longer be parenthetically defined as “the soul.”
The disciplined statement is:

$
  chi:cal(D)_"soul" arrow.r cal(V)_chi
$

is a soul characteristic. It identifies soul-equivalence only on a subcategory where
$chi$ has been proved conservative. The same applies to winding and holonomy.

Doctrinal type spaces add an exact intermediate relation: models can be identified by every
formula expressible in one context-indexed doctrine @abbadiniguffanti2026. Synthetic domain
theory supplies another: a sobriomorphism preserves the complete observational algebra even
when the underlying objects are not literally equal @xue2026. Both are lawful
receiver-relative compressions. Neither replaces the marked causal soul.

== Exact SHA-256 audit

The audit finds no SHA-256 dependence in the production `LiveCurrentMachine` relation which
could define a Soma soul. Current SHA uses fall into three different scopes:

1. report and artifact integrity;
2. provenance or content-addressed handles in bounded experiment worlds; and
3. a serialized-construction fingerprint in the standalone geometry laboratory.

Some bounded staging testimony still carries the legacy field name
`debug_identity_sha256`. Those values do not decide identity in the direct machine and must be
read only as digest witnesses; renaming historical observation schemas is a separate cleanup,
not a causal correction.

The third scope was mislabeled in the interface as “construction identity” and was used to
decide whether two adjacent moments had the same body. It is only

$
  h compose E:
  cal(D)_"construction" arrow.r op("Digest"),
$

where $E$ is RON serialization and $h$ is SHA-256. Even identical serialization would be
identity only in the chosen archive encoding, not soul identity. Digest equality is weaker
again. The correct exact comparison for two resident construction values is their structural
equality in the declared Rust type; the digest can remain a compact archive-integrity witness.

= Compression and annihilation

Fong and Sarazola call the compositional passage from an internal network to its externally
observable behavior a black-box functor @fongsarazola2020. That is a useful standard carrier for
the laboratory's compression law:

$
  B:cal(H)_"interior" arrow.r cal(H)_"behavior".
$

The functor can preserve composition while discarding internal structure. Holonic compression
adds one crucial qualification: the target receiver family must be named. If every admitted
future receiver $R_rho$ factors as

$
  R_rho=bar(R)_rho compose B,
$

then distinctions inside the fibers of $B$ may depart at that scope. If a later receiver does
not factor, the old compression claim never covered it.

Annihilation is therefore not deletion from an absolute universe. It is departure of a
distinction from the active factorization after opposed contributions close or after no declared
future process depends on it. The world or archive may still retain a material witness. Soma
need not retain it as active topology.

Synthetic domain theory makes the growth face precise. An information order
$x subset.eq y$ says that $y$ extends the distinctions already carried by $x$.
Under its explicit axioms, paths can witness this order and higher simplices can carry the
observational content of their spines @xue2026. Holonics adopts the typed extension relation,
not the unrestricted claim that every geometric path is information growth.

= How domain laws emerge

== A domain is a representation, not an analogy label

Let $bb(H)_phi$ be the sub-double-category on one phase: the largest region on which a
declared law class continues. A mathematical or scientific domain supplies a representation

$
  Phi_D:bb(H)_phi arrow.r bb(K)_D.
$

The target $bb(K)_D$ may be:

- groups, rings, modules, schemes, or derived categories in algebra;
- chain complexes, homology, homotopy types, or cobordisms in topology;
- normed spaces, kernels, operators, and measures in analysis;
- manifolds, bundles, connections, and curvature in geometry;
- propositions, proofs, and substitutions in logic;
- state spaces and transition systems in computation; or
- fields, observables, units, metrics, and actions in physics.

The representation explains why the same causal grammar is mathematically useful in every
domain without saying that their equations are identical.

== Ordered execution separates carried transport from consequence

#object-entry(elements.ordered_causal_execution)

This representation makes an algorithm more than an input--output table.  If
$cal(I)$ is the category generated by an algorithm's primitive instructions,
branches, joins, and declared relations, then the algorithm is a functor
$
  A_"alg":cal(I) arrow.r op("HolProc")_cal(D),
$
and its domain execution is $Phi_D compose A_"alg"$.  Proving a law on the
generating events and proving that the declared squares commute therefore
proves it for every composite execution.  No empty initial state is implied:
the source object, its distinctions, and its constraints are supplied before
$Lambda_F$ selects a move.

The signed category and its positive subcategory must remain distinct.  In a
logic representation, an indefinite residual may expose a failed commuting
square.  In an analytic representation, it may expose a negative test
direction.  In either case the causal process still exists.  Positivity is a
property of the represented event to be derived, not part of the definition
of causality.

== Conservation is a natural invariant

For a state functor $Z_D:cal(Phi)_D arrow.r cal(A)_D$, a conserved quantity with value object
$C$ is a natural transformation to the constant functor:

$
  c:Z_D arrow.r.double Delta C.
$

For every admitted event $f:x arrow.r y$,

$
  c_y compose Z_D(f)=c_x.
$

This naturality equation is the general categorical shape of conservation. It becomes charge,
momentum, probability mass, homology class, parity, degree, or another invariant only in a
representation which supplies that meaning.

The chain identity $partial partial=0$ is a particularly important representation. When a
domain maps events to chains and a current to a cycle, boundary cancellation can yield a
conservation law. But $partial partial=0$ alone is not a universal scalar balance for every
system.

== Time parity and theta are pre-domain structure

An oriented process category may carry a partial dagger

$
  (-)^dagger:X:a arrow.r b
  quad mapsto quad
  X^dagger:b arrow.r a.
$

This is the abstract content of time parity or hand reversal. It says which orientation is
reversed and how composition reverses:

$
  (Y compose X)^dagger=X^dagger compose Y^dagger.
$

It does not assert that every process is physically reversible or that $X^dagger X$ returns
the original occurrence. Dissipation, noninvertibility, an OPEN seam, or a changed world can
remain.

Likewise, $Theta$ is best represented as the holonomy of a connection or as a functor from a
loop groupoid into a structure group:

$
  op("Hol")_nabla:Pi_1(cal(M),x) arrow.r G.
$

It accumulates return under the selected connection. A physical representation may relate this
turn to phase, curvature, or action. A number-theoretic representation may relate it to
monodromy. A geometric representation may relate it to parallel transport. No one such image is
the universal meaning of $Theta$.

The proposed physical schema

$
  G=2^2 theta T
$

is therefore interpreted as a possible equation *inside a declared physical representation*:
$2^2$ marks a differential surface face, $theta$ its accumulated turn, and $T$ a typed
source/transport object. The agnostic carrier neither asserts nor rejects that field equation
without the metric, units, source law, and dynamics which give the symbols physical meaning.

== A phase law is naturality on a restricted category

An emergent law is not merely a frequent scalar pattern. On a phase subcategory, it is a
natural transformation, invariant, factorization, or commuting family which:

1. is defined on actual events of the phase;
2. composes with those events;
3. is covariant under admitted recharts;
4. predicts or constrains returned consequences; and
5. fails in a typed way at the phase seam.

This definition applies equally to an algebraic identity, a differential equation, a geometric
connection, a logical substitution law, or a physical conservation law. Holonics supplies the
grammar of emergence; the domain representation supplies the content.

= Convexity, concavity, and perspective

== The correct convex object is a cone of forms

For a fixed test space $V$, positive semidefinite Hermitian forms form the closed convex cone

$
  op("PSD")(V)
  =
  {Q: Q(f,f)>=0 " for every " f in V}.
$

If $Q_0,Q_1 in op("PSD")(V)$ and $0<=t<=1$, then

$
  (1-t) Q_0+t Q_1 in op("PSD")(V).
$

This is the exact convexity relevant to the laboratory's sign questions. For an indefinite
form $Q$, the set ${f:Q(f,f)>=0}$ need not be convex. It can be a two-sheeted or
double-cone geometry. Thus the intuition about convex and concave regions is useful, but the
object must be chosen correctly: the convex space is primarily the space of admissible forms or
contractive fillers, not automatically the positive vector region of one indefinite form.

== Perspective cannot change inertia

#object-entry(elements.positive_perspective_descent)

A lawful receiver change carries the *same anchored form* by congruence. Positivity then descends
across compatible charts, while a real negative direction remains negative in every invertible
rechart. Relativity means that the chart, anchor, and transition are explicit. It does not mean
that sign can be selected freely.

This is precisely where a perspective-based RH argument must be disciplined. Local positive
forms can prove a global sign only when:

- they are restrictions of the same response;
- their transitions preserve that response;
- the cocycle closes on triple overlaps; and
- the charts exhaust every admitted test direction.

Otherwise the construction has changed the form rather than viewed it.

== Where concavity can enter

On the interior of a finite-dimensional positive-definite cone,

$
  Q mapsto log det Q
$

is concave. It can act as a barrier or volume potential when searching a finite family of
positive forms. Approaching a singular seam sends this quantity toward $-infinity$.

That makes concavity potentially useful for detecting phase boundaries, choosing central finite
fillers, or studying monotone deformation. It does not by itself prove that the limiting form
never acquires a negative direction. The sign theorem remains a cone-membership statement.

= The Riemann Hypothesis under this carrier

== The fixed object is the completed Weil response

Let $Q_W$ denote the completed Weil Hermitian response on its admitted test space. Under the
standard hypotheses, Weil positivity is equivalent to RH @weil1952 @lagarias2007:

$
  "RH"
  quad "iff" quad
  Q_W(f,f)>=0
  quad "for every admitted" f.
$

The laboratory's receiver geometry does not change this Weil form. It explains how its
arithmetic, archimedean, support, and receiver presentations must be anchored if they are to
test that same form.

== The theta current is one positive-lift question

#object-entry(elements.theta_positive_execution_lift)

This places the completed theta reduction directly inside the process
carrier.  The infinitesimal event already exists in the signed execution
category.  RH says exactly that its complete cross-receiver residual lies in
the positive subcategory.  The missing object is therefore an explicit
source-derived residual executor, not a declaration that every Eros event is
positive and not an independently selected contraction at every receiver.

== The existing amplitude balance already has a factorization theorem

The current semilocal successor theorem has derived

$
  D_j(f)=norm(X_j f)^2-norm(Y_j f)^2.
$

For one index $j$, $D_j>=0$ is equivalent to a contraction

$
  Gamma_j X_j=Y_j,
  quad
  norm(Gamma_j)<=1.
$

This is a direct instance of the operator factorization principle established by Douglas
@douglas1966. The contraction is therefore not a metaphor and not an arbitrary new carrier. It
is the exact algebraic object equivalent to the desired local norm domination.

The remaining problem is that prime admission, support growth, and receiver recharting produce
many related indices. Independently choosing one $Gamma_j$ at every index can destroy the
composition law which makes them one completed response.

== The new object is one natural contraction feasibility set

#object-entry(elements.natural_contraction_feasibility)

The category $cal(J)$ should be generated by the actual transitions already present in the
zeta construction:

- adjoining a finite prime place;
- enlarging a support aperture;
- applying Fourier--Poisson--Mellin return;
- changing a formulation chart while retaining the anchored current; and
- restricting to a bounded exact probe.

The existing amplitudes must be shown to form natural transformations

$
  X:cal(T) arrow.r.double cal(K)_X,
  quad
  Y:cal(T) arrow.r.double cal(K)_Y.
$

The proof-bearing candidate is then not a list of scalars. It is a natural transformation

$
  Gamma:cal(K)_X arrow.r.double cal(K)_Y
$

whose components obey both the local factorization and every commuting square.

For a finite subdiagram this is a convex semidefinite feasibility problem:

$
  Gamma_j X_j=Y_j,
  quad
  cal(K)_Y(a) Gamma_j=Gamma_k cal(K)_X(a),
  quad
  mat(1,Gamma_j^*;Gamma_j,1) >= 0.
$

The first two constraints are affine. The third is a linear matrix inequality. Their
intersection is convex. This is the rigorous convex geometry behind the user's hunch.

There is also an exact compactness reduction: if every finite collection of the naturality,
factorization, and contraction constraints is simultaneously feasible, weak-operator
compactness yields a coherent global family. This does *not* license finite sampling. It says
that a proof may target an arithmetic construction or monotone extension theorem guaranteeing
all finite compatibilities, rather than conjuring one infinite matrix at once.

== Exact RH consequence and unchanged wall

#object-entry(elements.natural_contraction_rh)

This changes the shape of the research programme in one substantive way:

> the missing zeta object is a coherent point of an explicitly convex natural-contraction
> feasible set, not a favorable scalar perspective and not an unstructured collection of local
> positive charts.

It does not yet move the truth value of RH. Nonemptiness of the feasible set must still be derived
from the completed arithmetic and archimedean relation. The first useful attack is therefore:

1. define the exact index category $cal(J)$ from the already-derived prime/support/receiver
   transitions;
2. prove that $X$ and $Y$ are natural on a common completed domain;
3. calculate the finite candidate feasible set for the dyadic cell together with its first
   support-growth and Poisson--Sonin squares;
4. determine symbolically whether those constraints are compatible; and
5. either derive the first genuine arithmetic filler or obtain a finite exact obstruction to
   this route.

This is preferable to another prime image or finite zero sweep because either result changes the
operator proof path: a filler supplies the first coherent component, while an obstruction rules
out the present factorization architecture.

= What this generalization now permits

The carrier can be used without routing every question through physics or machine learning:

#table(
  columns: (8em, 1fr, 1fr),
  inset: (x: 5pt, y: 4pt),
  stroke: (x: none, y: 0.4pt + by-rule),
  table.header([*Domain*], [*Representation*], [*Holonic question*]),
  [Algebra], [Operations, ideals, modules, Galois actions.],
    [Which presentations are isomorphic, quotiented, or obstructed?],
  [Geometry], [Charts, bundles, metrics, connections, curvature.],
    [Which receiver changes preserve incidence, length, angle, or holonomy?],
  [Topology], [Chains, homology, fundamental groupoids, cobordisms.],
    [What survives deformation, gluing, return, or boundary?],
  [Analysis], [Measures, kernels, operators, limits, semigroups.],
    [Which endpoint faces exactly factor a transported interior?],
  [Logic], [Contexts, predicates, substitutions, proofs.],
    [Which squares commute, and what OPEN obligation blocks a filler?],
  [Number theory], [Valuations, local factors, characters, trace formulas.],
    [How do finite and archimedean places assemble one anchored response?],
  [Physics], [Fields, units, actions, metrics, constitutive laws.],
    [Which categorical invariants become measured conservation laws?],
  [Computation], [Programs, state transitions, encodings, executions.],
    [Which algorithms are equivalent under a declared behavioral receiver?],
)

The common framework is consequently not “everything is the same.” It is a calculus for saying
*which relation of sameness is being used, which transport makes it lawful, and which
distinctions remain consequential*.

= Conclusion

Categorical holonics makes five corrections precise.

First, the Universality Machine is an agnostic causal complex. Domain law appears through a
representation of that complex, not through one universal equation.

Second, a receiver is part of the event. Its strongest lawful form is a functor, and a change of
perspective is a natural transformation whose square may commute or remain OPEN.

Third, a soul is a marked causal diagram. Cross-ratio, winding, holonomy, value, and digest are
characteristics of that diagram. Yoneda supports relational identity only at the level of the
complete representable relation, not one selected face.

Fourth, a global holon is transported local assembly over a boundary-defined region. Evolution,
interaction, parameterization, receiver transport, observation, and physical realization are
separate compositional directions. No total field or absolute camera is introduced by collecting
their fibers.

Fifth, the RH perspective programme now has an exact convex object. The complete zeta
amplitudes must admit one natural contractive filler across prime, support, and receiver
transitions. Positive perspective descent explains why lawful charts preserve sign; the natural
contraction feasibility set explains what must be constructed. Convexity is structural here.
It is not a cone because the fixed equation $Gamma X=Y$ is generally inhomogeneous. Concavity may
guide finite interior geometry, but the proof remains the nonemptiness of the anchored cone.

#bibliography("references.bib")
