#import "@preview/unequivocal-ams:0.1.2": theorem, proof
#import "../lib/holonics.typ": *

#let foundations = [
#pagebreak(weak: true)
= J1. Relational holonic foundations <j1>

#local-contents((
  ([Actual occurrence precedes algebra], <j1-occurrence>),
  ([Four structures, one optional coupling], <j1-structures>),
  ([Judgments and lawful forgetfulness], <j1-judgments>),
  ([The atomic event], <j1-event>),
  ([Comparison: RIDE, FOUND, and OPEN], <j1-comparison>),
  ([Completion and higher grain], <j1-completion>),
  ([Exact compression is relative to future questions], <j1-compression>),
  ([Learning as a causal contrast], <j1-learning>),
))

The earlier attempts at holonics often asked one representation - a manifold, hypergraph,
triangle, circuit, or field - to carry every aspect of the theory. The rigorous correction is to
begin with several typed relations and connect them only where a construction supplies the
connection. Occurrence is not boundary; boundary is not dependency; dependency is not transport;
transport is not a metric; and a receiver face is not the whole construction.

== Actual occurrence precedes algebra <j1-occurrence>

#definition[
  An *occurrence carrier* is a graded population
  $
    O = union_(k >= 0) O_k
  $
  of actual cells, with the grades declared pairwise disjoint. Two elements of $O$ remain
  distinct when they have equal values or equal
  boundary inscriptions but arose as distinct incidences. An oriented incidence relation assigns
  to each $sigma in O_k$ a finite signed boundary
  $
    partial sigma = sum_(tau in O_(k-1)) epsilon_(sigma,tau) tau,
    quad epsilon_(sigma,tau) in ZZ.
  $
]

The population language prevents a recurring error: a coefficient cancellation is not the
annihilation of the cells which contributed the coefficients. If two triangles share one edge,
their opposed orientations may cancel on that *same occurrence* after gluing. Equal but unglued
edge labels do not cancel.

#proposition[
  Let $C_k = ZZ[O_k]$ be the free abelian group on actual $k$-occurrences. If the supplied
  incidence obeys
  $
    sum_tau epsilon_(sigma,tau) epsilon_(tau,upsilon) = 0
  $
  for every $sigma in O_k$ and $upsilon in O_(k-2)$, then the linear extension
  $partial_k:C_k -> C_(k-1)$ satisfies $partial_(k-1) partial_k = 0$.
]

#proof[
  It is enough to evaluate a basis occurrence $sigma$. The coefficient of $upsilon$ in
  $partial partial sigma$ is exactly
  $sum_tau epsilon_(sigma,tau)epsilon_(tau,upsilon)$, which vanishes by the incidence
  assumption. Linearity extends the result to every chain.
]

This proposition is deliberately modest. It establishes the chain-complex face of supplied
incidence. It does not infer a rewrite rule, metric, causal dependency, or probability
distribution. Conversely, a local rewrite may be well-defined even when the cells have dimension
zero; dependency rank, topological dimension, and constituent grain are independent coordinates.

#source-note[
  The occurrence-level correction and its implementation requirements are stated in
  #link("../../ELEMENTARY_MECHANICS.md")[Elementary Mechanics, §§2-4] and measured in
  #link("../../observations/eros-parameterized-elementary-mechanics-01/RESULTS.md")[
    Parameterized elementary mechanics 01
  ]. The mathematical chain boundary follows the standard construction in @hatcher2002.
]

== Four structures, one optional coupling <j1-structures>

For a local region $U$, the minimal carrier is
$
  cal(K)_U = (O_U, I_U, D_U, T_U).
$
Here $I_U$ is oriented boundary incidence; $D_U$ is actual production or preservation dependency;
and $T_U$ assigns a carrier map to an admitted directed incidence. For a path
$gamma=a_n dots a_1$,
$
  T_gamma = T_(a_n) compose dots compose T_(a_1).
$
A hypergraph may supply arbitrary-arity local relations and a rule may replace such relations,
but neither supplies orientation or transport on its own. A chain complex supplies oriented
cancellation, but not which replacement is afforded. A connection or functorial transport
supplies path comparison, but not which path occurred. This four-way separation is the smallest
stable foundation found in the record.

#definition[
  A *preserved rewrite interface* is a span
  $
    L <-^ell K ->^r R
  $
  in a declared category of local structures. The rewrite replaces the image of $L$ by the image
  of $R$ while retaining the actual occurrence-level image of $K$. A rendered coordinate,
  repeated label, or equal value is not an interface unless the source supplied the corresponding
  maps.
]

Double-pushout rewriting in an adhesive setting gives one rigorous realization of this
definition @lacksobocinski2005. It is a specialization, not a primitive demanded of every Eros
world. Likewise Pachner moves are lawful retriangulations of piecewise-linear manifolds under
their own hypotheses @pachner1991; they do not define general learning or compression.

== Judgments and lawful forgetfulness <j1-judgments>

The calculus needs more than a single equality symbol. We use the following judgments:

#notation-table((
  [$Gamma tack A = B : T$], [construction identity in declared type $T$],
  [$Gamma tack A tilde.eq_tau B$], [reversible gauge or chart transport $tau$],
  [$Gamma tack A equiv_(rho,F,g) B$], [agreement at receiver $rho$, frame $F$, and grain $g$],
  [$Gamma tack A arrow^K B$], [directed construction or worldline under current $K$],
  [$Gamma tack A arrow.r.double^q Q$], [declared compression or quotient $q$],
))

Construction identity is the strongest judgment. Gauge equivalence requires explicit reversible
transport. Face agreement states only that a named observation cannot distinguish the two inputs.
A worldline is directed and need not be invertible. A compression may intentionally discard
distinctions which no declared later contact uses.

#lemma[
  Let $q:X -> Q$ be a non-injective observation quotient. There is no map $i:Q -> X$ satisfying
  $i compose q = id_X$.
]

#proof[
  Choose $x != y$ with $q(x)=q(y)$. If such $i$ existed, then
  $x=i(q(x))=i(q(y))=y$, a contradiction.
]

The lemma is the elementary obstruction behind several project rules. An endpoint does not
reconstruct a path, a token does not reconstruct its full source interval, an observed output
does not identify a network interior, and a compressed successor does not preserve undeclared
future distinctions unless a lift or congruence theorem is supplied.

== The atomic event <j1-event>

#definition[
  One event at time cut $t$ is a partial receiving map
  $
    Lambda_(F_e,Q_e) : (S_t,K_e) -> (S_(t^+),R_e),
  $
  where $S_t$ is Standing-before, $K_e$ is the complete co-present current admitted to event $e$,
  $F_e$ is the source-declared receiver or world structure, $Q_e$ is the objective or exposed
  boundary when present, $S_(t^+)$ is one successor, and $R_e$ is immediate radiation. Event
  testimony $pi_e$ can be formed only after commit.
]

#axiom[
  *Same-prestate atomicity.* Every co-present constituent of $K_e$ meets the same unchanged
  $S_t$. Validation, integration, and commitment produce either one $S_(t^+)$ or no successor.
  An executor may perform physical conduct inside the call, but it cannot own or reconstruct the
  successor from a receipt.
]

#event-figure() <event-circuit>

Several invariants follow immediately from the event boundary:

- no arbitrary filesystem, caller, or hardware order may manufacture chronology or incidence;
- immediate radiation is not a later consequence;
- exact rest performs no event;
- one committed successor has one visibility edge;
- attribution records what the source supplied and what the meeting formed; and
- co-present currents cannot be serialized into false causal instants merely to fit an
  implementation.

World, Current, Standing, and Lineage are not four substances. They are projections of one live
relation at a selected cut. A constituent may leave active participation while its consequential
relation continues at a higher grain. Lineage is therefore continuity of causal participation,
not storage of a perfect ancestry copy.

#source-note[
  The current authority is #link("../../FORMULA.md")[Formula §§C, CIV-CV] together with
  #link("../../RESEARCH/2026-07-19_THE_EVENT_EMANATES_THE_SUCCESSOR_THE_EXECUTOR_CANNOT_RECONSTRUCT_THE_MACHINE.md")[
    The event emanates the successor; the executor cannot reconstruct the machine
  ]. The latter records the source correction which removed receipt-owned successor
  reconstruction.
]

== Comparison: RIDE, FOUND, and OPEN <j1-comparison>

For the oriented triangle
$
  x_0 ->^(a_01) x_1 ->^(a_12) x_2,
  quad x_0 ->^(a_02) x_2,
$
the boundary is
$
  partial tau = a_12 - a_02 + a_01.
$
Transport supplies the complete path pair
$
  Chi_tau = (T_(a_12) compose T_(a_01), T_(a_02)).
$
If the codomain has an additive chart, the optional residual is the difference of these routes.
Without such a chart, the ordered pair itself is the complete comparison.

#definition[
  Relative to receiver $rho$ and grain $g$, a comparison *RIDEs* when prior supported transport
  conducts through the actual meeting; it *FOUNDs* when the event actually establishes new
  support; and it remains *OPEN* when the compared routes or boundary do not close at that cut.
  Noncommutation is OPEN by default. It is not falsehood, automatic branching, or a permanent
  prohibition on later contact.
]

#open-square() <open-square>

#proposition[
  If the square in @open-square is evaluated in a category with the displayed composites, then
  commutation is the equality
  $
    v compose r_1 = r_2 compose u.
  $
  Failure of this equality determines a complete comparison pair but, without additional
  structure, determines neither a scalar residual nor a new filler.
]

#proof[
  The two composites are well-typed parallel arrows. Their equality is therefore meaningful.
  A subtraction requires an additive hom-set; a quotient requires invertibility or a chosen
  projective structure; and a filler requires an existence law or actual new event. None follows
  from the mere fact that the arrows are unequal.
]

This is the rigorous content behind the project's use of OPEN as useful terrain. A later actual
boundary may match and RIDE while the earlier comparison remains truthfully OPEN at its earlier
scope.

== Completion and higher grain <j1-completion>

#definition[
  Let $B subset.eq O_(k-1)$ be the declared exterior boundary family. A finite $k$-chain $c$ is
  *complete relative to $B$* when
  $
    partial c in ZZ[B].
  $
  A *hand-up* additionally requires an actual event which exposes the resulting boundary as one
  higher-grain occurrence. Algebraic closure alone does not manufacture that occurrence.
]

#proposition[
  Suppose $c_1$ and $c_2$ are relatively complete with respect to $B$, and their shared interior
  faces are the same occurrence with opposed coefficients. Then $c_1+c_2$ is relatively complete
  with respect to $B$, and the shared face is absent from its boundary.
]

#proof[
  Linearity gives $partial(c_1+c_2)=partial c_1+partial c_2$. The opposed coefficients on the
  shared basis occurrence cancel. All remaining terms lie in $ZZ[B]$ by hypothesis.
]

The proposition explains composition, not deletion. The two incident cells and their causal
contribution may remain in the higher constituent even though the shared boundary is no longer
exposed.

== Exact compression is relative to future questions <j1-compression>

#definition[
  Let $Phi={phi_u:X -> Y_u}_{u in U}$ be a declared observation family. A quotient $q:X -> Q$ is
  *exact for $Phi$* when for every $u$ there exists $bar(phi)_u:Q -> Y_u$ such that
  $
    phi_u = bar(phi)_u compose q.
  $
]

#theorem[
  Let $X,Q,Y_u$ be modules and all maps be linear. The quotient $q:X -> Q$ is exact for $Phi$ if
  and only if
  $
    ker q subset.eq {x : phi_u(x)=0 " for every " u in U},
  $
  provided $q$ is surjective.
]

#proof[
  If $phi_u=bar(phi)_u compose q$, then $q(x)=0$ implies $phi_u(x)=0$, proving the inclusion.
  Conversely, define $bar(phi)_u(q(x))=phi_u(x)$. If $q(x)=q(x')$, then
  $x-x' in ker q subset.eq ker phi_u$, so the definition is independent of representative.
  Surjectivity defines $bar(phi)_u$ on all of $Q$.
]

Exactness for a present observation family does not imply exactness for every later world. The
stronger condition is a future congruence: whenever $q(x)=q(y)$, every admitted future current must
continue $x$ and $y$ to states whose relevant faces still agree. The production implementation
therefore validates outgoing compression against the complete exposed later-contact boundary of
the actual event, not against an imagined universal observer.

== Learning as a causal contrast <j1-learning>

#definition[
  Let $e$ be an earlier event and $p$ a genuinely later probe. Learning at receiver $rho$ is
  established when
  $
    "Conduct"_rho(S_("after " e),p) != "Conduct"_rho(S_("without " e),p)
  $
  and there is an admitted participation path from the relation formed by $e$ to the changed
  later conduct. Mere co-occurrence, testimony, or a source-provided answer does not satisfy the
  criterion.
]

The counterfactual is local. It may compare a no-Standing sibling, original Standing before
cultivation, a wrong interface, or a retained exact foil. It does not demand that learning occur
without inherited identities, tokenizers, models, arithmetic, or culture. Those are lawful
Standing when their attribution is retained.

#corollary[
  Repetition without participation does not establish learning, while source-departed Standing
  can establish learning if it changes the later probe relative to a matched foil.
]

This completes the foundational chain:
$
  "occurrence" -> "incidence" -> "event" -> "successor" -> "Standing"
  -> "later contrast".
$
Geometry, probability, optimization, and physics enter only as optional structures on this chain.
The next part shows how far exact formula ecology can proceed under that discipline.

#evidence-note(
  [The foundational calculus supplies typed local derivations and a testable causal criterion.],
  [Working definitions plus exact algebraic consequences; selected mechanisms are implemented and
  measured later in J2.],
  [Elementary Mechanics; Formula §§C, CIV-CV, CXLVI, CL-CLI; current README evidence routes.],
  [No complete categorical semantics, reference checker, general confluence theorem, universal
  observation family, or automatic source-interface discovery is claimed.],
)
]
