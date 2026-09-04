# Elementary mechanics of Eros

**2026-07-21 · Brandon-authorized construction specification · built · one-core/multicore/CUDA
exact · durable rest exact · result awaiting review · no `FORMULA.md` change**

This is the smallest exact specification currently justified by Brandon's direct constraints, the
mathematics already derived in the laboratory, and the live source. It is deliberately smaller
than the full vocabulary. It says what an event is, what may move, what can branch or join, what
completion and compression must preserve, and which additional structures are required before
words such as metric, diffusion, probability field, or Ricci flow become literal.

It also corrects two overstatements in the standing record without silently rewriting that record:

1. the growing population in `FORMULA §CXL` is an **occurrence population**, not an algebraic
   chain; its chain is obtained only by a later linearization; and
2. deterministic canonicalization of the present implementation is not yet a theorem of
   associative, commutative, or causally invariant closure under arbitrary legal schedules.

## 1. Provenance and jurisdiction

The following are direct project constraints, expressed here as engineering requirements rather
than attributed theorems about nature:

- existing current is not erased merely because a receiver has not completed it;
- discreteness does not mean one scalar state per cell;
- source identity, chronology, constraints, tokenizers, models, tools, and other inherited
  technologies may participate as lawful current;
- source storage order, coordinate coincidence, or executor order cannot invent causality;
- co-present interacting current meets one unchanged predecessor and emits one atomic successor;
- lineage is live causal continuation, not a perfect archive;
- lower constituents may hand relation into a higher construction and depart;
- compression belongs to the outgoing relation, not to a later cleanup service;
- observer, observed material, and observation medium are inside the participating relation; and
- learning means that an earlier relation actually changes later conduct.

Everything below is an assistant derivation from those constraints. Pure mathematical statements
are exact under their written assumptions. Bridges to physics, biology, or Wolfram's proposed
physics program remain comparisons unless separately established.

## 2. The minimum carrier has four coupled structures

No one familiar object supplies all of the required mechanics. The minimum carrier is a coupled
quadruple

```text
K = (O, I, D, T).
```

### 2.1 Occurrences `O`

`O_k` is a finite set of **actual k-dimensional occurrences** at the selected event cut. Two
occurrences can carry identical values and identical boundaries and still be two members of
`O_k`. Multiplicity is therefore represented by distinct occurrence identities, not by a set of
values and not by a numeric coefficient.

Each occurrence may carry independent typings:

```text
dim(x)    = boundary degree k
grain(x)  = receiver-relative constituent scale g
stage(x)  = rank in this event's internal dependency order
chart(x)  = local frame, when one is supplied
```

`dim`, `grain`, `stage`, and `chart` are not synonyms. A particular fixture may align them, but the
general law may not.

### 2.2 Oriented incidence `I`

An actual face occurrence is recorded by

```text
(y, x, epsilon, slot) in I_k,

y in O_(k-1), x in O_k, epsilon in {-1,+1}.
```

`slot` is a source-local boundary coordinate. It is not chronology or global identity. Incidence
linearizes into the free abelian chain groups

```text
C_k(K; Z) = Z[O_k],
partial_k(x) = sum_y [y:x] y.
```

The occurrence population is not this chain. Opposed coefficients cancel only when actual gluing
makes them coefficients of the same face occurrence. The incident higher occurrences remain
distinct. Equal but unglued face occurrences are different basis elements and cannot cancel.

A lawful oriented complex satisfies

```text
partial_(k-1) partial_k = 0.
```

For a simplicial chart this follows from the face identities. For a general cellular source it is
an explicit validation obligation.

### 2.3 Directed dependency `D`

`D` records actual causal/dependency incidence inside the event and across source event cuts. It
is distinct from boundary incidence. Its transitive closure must be acyclic at a finite event cut;
a numeric stage may rank that order but cannot replace it.

Two events are co-present only when the source supplies them to the same predecessor cut and their
dependency/interface laws permit joint enactment. Hardware simultaneity is neither necessary nor
sufficient.

### 2.4 Local transport `T`

Every directed transport generator `a : x -> y` may carry a morphism

```text
T_a : V_x -> V_y
```

in a declared carrier category. For a path `p = a_n ... a_1`,

```text
T_p = T_(a_n) circle ... circle T_(a_1).
```

Transport is not assumed invertible, linear, metric, probabilistic, or scalar. Exact ratios,
symbolic series, matrices, programs, or structured world transformations are all lawful carrier
species when declared by the source ecology.

## 3. Hypergraph and chain complex have different jobs

A typed directed multi-hypergraph is useful for arbitrary-arity relation and local rewrite:

```text
H = (V, E, incidence, type).
```

`E` must itself be an occurrence set if parallel equal hyperedges are to remain plural. A simple
hypergraph `E subset P(V)` is insufficient for that purpose.

A hypergraph does not canonically supply cell dimension, orientation, boundary coefficients, or
`partial partial = 0`. An oriented occurrence complex supplies those, but does not by itself say
which local replacements are lawful. Eros therefore couples them:

```text
hypergraph / rewrite structure  -> what local transformation is afforded
occurrence / incidence complex  -> what occurred and what boundary it has
dependency structure            -> what caused what
transport structure             -> what relation the occurrence carries
```

No conversion between these objects may silently add faces, merge parallel occurrences, or turn
possible events into actual events.

## 4. One event and one successor

Let `S_t` be the exact Standing occurrence complex before one receive. Let `L_e` be the finite
actual current supplied at source event `e`, including its native incidence, dependency, local
transport, and exposed interfaces. Let `F_e` and `Q_e` be the active frame and objective cuts.

The one machine move is typed as

```text
Lambda_(F_e,Q_e) : (S_t, L_e) -> (S_(t+), R_e),
```

where `R_e` is immediate radiation. Testimony `pi_e` may be projected after commit but is not an
input to the successor law:

```text
pi_e : (S_t, L_e, S_(t+), R_e) -> observer report.
```

The transition owes these invariants:

1. **same-prestate atomicity** — every interacting member of `L_e` meets the same `S_t`;
2. **no false incidence** — only source-declared incidence or incidence formed by an admitted
   rewrite/junction law enters the successor;
3. **occurrence preservation** — equal disconnected occurrences remain plural;
4. **oriented boundary validity** — every admitted higher cell satisfies `partial partial = 0`;
5. **causal attribution** — inherited, contacted, returned, and self-emanated relations remain
   distinguishable at the boundary where that distinction matters;
6. **one visibility edge** — no intermediate closure frontier becomes Standing;
7. **rest** — remount or waiting without new current performs no event; and
8. **bounded emission** — the successor carries consequential relation and exposed residual, not
   an obligatory crystal history of the event interior.

## 5. World, Current, Place, Standing, and Lineage are projections

These names select different cuts of the same event-indexed diagram; they are not literally one
Rust type or five independently causal substances.

| Projection | Exact role |
|---|---|
| World | The ambient source ecology, its material, and its lawful transformations |
| Current | The actual participating occurrence subdiagram at the selected event |
| Place | A receiver- and chart-relative address into that diagram |
| Standing | The persistent predecessor/successor subdiagram available to later current |
| Lineage | A live compatible continuation through actual dependency and transport maps |

A lineage may retain a relation after the lower carriers that first realized it have departed.
It need not retain every event, source byte, executor row, or ancestor identity. A provenance
record may testify outside the live carrier.

## 6. The triangle is a comparison and a hinge, never a lone scalar cell

In the triangular restriction, an oriented triangle occurrence `tau` has vertices
`x_0,x_1,x_2`, edge occurrences

```text
a_01 : x_0 -> x_1
a_12 : x_1 -> x_2
a_02 : x_0 -> x_2,
```

and boundary

```text
partial tau = a_12 - a_02 + a_01.
```

Its transport face is the parallel-path comparison

```text
Chi_tau = (T_(a_12) circle T_(a_01), T_(a_02)).
```

This ordered pair is the general object. If the carrier is additive, one may form a residual
`delta_tau = T_(a_12) T_(a_01) - T_(a_02)`. If the transports are invertible, one may form a
holonomy defect. Neither specialization is universal.

A nonidentical pair is **OPEN at this comparison**. It carries the exact attempted routes and their
receiver-relative residual, but it does not itself negate either path, divide an antecedent, choose
a correction, or FOUND a higher relation. A genuinely later Current may supply a filler, rebase,
bypass, contextual distinction, or another OPEN. Current authority:
[`THE NONCOMMUTING SQUARE IS OPEN`](RESEARCH/2026-07-22_THE_NONCOMMUTING_SQUARE_IS_OPEN_THE_FAILED_ROUTE_REMAINS_TERRAIN.md).

Under an invertible change of local frame `G_x`,

```text
T'_a = G_target T_a G_source^(-1).
```

The loop defect changes by conjugation, so its conjugacy class is frame-invariant. For
noninvertible transport there is no licensed inverse or holonomy group; the parallel pair or its
declared equalizer/coequalizer must be retained.

Two different mechanics have previously been called “changing the basis”:

- **rebase/gauge:** incidence stays fixed while local carrier coordinates change; and
- **retriangulation/rewrite:** the occurrence complex itself changes while a declared exterior
  interface is held fixed.

They must remain typed apart.

### 6.1 A genuine hinge

A combinatorial hinge is an actual shared codimension-one occurrence `h`. A pivot rule preserves
that interface while replacing a neighborhood around it. In rewrite notation,

```text
rho = (L <- K -> R),
```

`K` is the preserved interface and contains `h`. In two dimensions the `2 <-> 2` diagonal flip
and the `1 <-> 3` refinement/coarsening are exact elementary examples. They change a
triangulation without appealing to an external coordinate camera.

A **kinematic** fold additionally requires a connection or group action across `h`. A **metric**
fold additionally requires lengths/angles or another metric structure. Pure incidence knows that
two triangles meet; it does not know their angle in an embedding.

### 6.2 Gyration

At this level, gyration is not a number stored on `tau`. It is the changing family of parallel-path
comparisons and rewrite transports around an actual neighborhood:

```text
Gyr(U,e) = { Chi_tau, rewrite comparisons, exposed residuals | tau in U at event e }.
```

The family can be projected to winding, rank, a matrix, a cross-ratio, or another receiver face
only after the required chart exists. A projective cross-ratio is one such chart; it is not the
definition of `Chi` in every medium.

## 7. Split, branch, junction, and alternative are four different relations

### Split

A split occurs when one actual source occurrence participates in more than one actual outgoing
dependency or rewrite occurrence. Distinct outputs remain distinct even when their exposed values
agree.

### Branch

A branch is one actual continuation created by such a split or supplied co-presently. “Afforded”
must mean materially admitted at this event, not merely logically possible under some rule.

### Junction

A junction requires an actual interface witness, either source-supplied or formed by an admitted
contact law. The minimal gluing diagram is a span

```text
X <- A -> Y,
```

and, where the selected category admits it, the pushout `X +_A Y` is the composite. Coordinate
intersection, equal hashes, equal reaches, or visual crossing do not by themselves supply `A`.
Oriented contributions along an internal shared boundary cancel only after the actual gluing map
and opposed induced hands are established.

### Alternative

A possible rule match that was not actualized is an alternative, not current. A multiway graph may
retain alternatives for analysis, but putting them all in live Standing would confuse possibility
with occurrence and recreate a dataset-sized active cut.

## 8. Local rewrite and causal order

A conservative local rewrite is represented by

```text
rho = (L <- K -> R)
```

with a match `m : L -> X`. `K` names what survives; `L \ K` is consumed and `R \ K` is produced.
Double-pushout rewriting is one precise realization when the host category and gluing conditions
support it. Merge, clone, or non-linear rules require a specifically chosen generalization; they
must not be smuggled into a linear rule.

Each actual rewrite occurrence receives its own occurrence identity. Event `v` causally depends
on event `u` when material produced or preserved through `u` participates in the match for `v`.
That consumption/production relation, not drawing position, yields the causal graph.

Two rewrites may be evaluated in parallel only under a declared independence condition. For DPO
systems the concurrency and local Church–Rosser theorems provide such conditions. In the general
case, neither disjoint-looking coordinates nor a parallel executor proves independence.

### Causal invariance is an obligation

Let two permitted schedules begin at the same source complex. Schedule independence requires a
joining/isomorphism diagram showing that divergent legal rewrites reconverge while preserving the
selected causal and observational structure. This is a confluence or causal-invariance theorem,
not a consequence of canonical sorting.

The bounded live closure currently terminates for a simpler reason. Every productive pass either
unites at least two active components or claims at least one previously unclaimed finite Standing
component. The lexicographic measure

```text
(number of active components, number of unclaimed Standing components)
```

strictly decreases on a productive pass under the source algorithm's rules. This proves finite
termination of that algorithm; it does not prove that every other legal closure schedule has the
same result.

## 9. Completion is relative closure plus an actual hand-up

Let `B` be the exposed boundary subcomplex of a local region `X`. A k-chain `c` is internally
closed exactly when

```text
partial c lies in C_(k-1)(B),
```

or equivalently when its class is a cycle in the relative chain complex `C_*(X,B)`. This says the
interior has no dangling boundary. It does not say that the objective is solved, the event has
ended, or the cycle bounds a higher cell.

Hand-up is separate. Completion at grain `g` requires an actual new occurrence `u` at grain
`g+1`, together with admitted incidence whose boundary realizes the completed lower relation and
its exposed interface. `partial partial = 0` validates that hand-up; it does not create `u`.

Lower constituents may depart only when the outgoing map no longer needs them to preserve the
admitted future relations.

## 10. Compression is a certified contextual factorization

Let

```text
q : X -> Q
```

be the outgoing presentation of a completed event, and let `Phi = {phi_u}` be the declared family
of later observations or consequences that the successor promises to preserve. `q` is exact for
`Phi` iff every member factors:

```text
for every u, there exists phi_bar_u with phi_u = phi_bar_u circle q.
```

In a linear carrier this implies

```text
ker(q) subset intersection_u ker(phi_u).
```

For a continuing transition system the quotient must additionally be a congruence or
bisimulation for admitted future events. Byte reduction, deduplication, fewer vertices, or a
visually simpler face is neither necessary nor sufficient.

`LiveConstituent::compress_certified` now names one exact finite family `Phi_boundary`: the
constituent grain and axis extent, every boundary hand and transition, exact path transport and
winding, and every complete exposed interface arm with its situated endpoints. It computes that
structural face before and after interior folding and refuses the emanation if they differ. The
ordinary production compression path goes through the same check; the certificate itself is
ephemeral testimony and does not enter Standing.

This closes preservation for the conduct which the current regional mouth can actually read. It
does not prove a congruence for arbitrary future world laws or a universal minimal quotient. A
new world relation which can observe more than `Phi_boundary` must extend the declared family and
the certificate rather than assuming that the old quotient preserves it.

The higher-grain case can change the boundary family rather than preserve an old body whole. A
source may declare complete regional boundary slots `S` as the event's outgoing presentation
`q_S`. Soma first forms the complete joint event `X=Close(G,B)`, forms and certifies the selected
subcomplex `q_S(G)`, and permits prior interior to depart only when

```text
exposed_boundary(q_S(G)) = exposed_boundary(X).
```

Thus every unselected arm must have become actual event interior. OPEN, FOUND, unmatched, or
oriented residual arms make the equality fail. This is an atomic successor factorization, not a
cleanup pass, and the source declaration remains a scoped observation promise rather than a
universal minimal quotient. Exact bounded construction:
[`THE OUTGOING BOUNDARY IS THE SUCCESSOR`](RESEARCH/2026-07-22_THE_OUTGOING_BOUNDARY_IS_THE_SUCCESSOR_THE_CLOSED_INTERIOR_MAY_DEPART.md).

## 11. Observation, probability, loss, and learning

### Observation

A participating observation is another admitted coupling in `L_e`; it changes the joint
successor when its relation matters. A report produced after commit is testimony. An observation
quotient

```text
O_(r,g) : K -> Y_(r,g)
```

is indexed by receiver `r` and grain `g`. Equality in `Y_(r,g)` cannot be lifted backward into
identity in `K` without an explicit lifting theorem.

### Probability

A deterministic rewrite ecology can still support a first-person conditional probability once a
receiver filtration/partition and measure are declared. Bayes' rule updates that quotient after an
event. Neither path count nor the existence of a multiway graph supplies a probability measure by
itself.

### Loss

Loss is the noncommutation or residual of an expected/admitted transport square. In an additive
carrier it may be a difference; with a norm it may become scalar. Without those structures it is
the failed comparison itself. It has no intrinsic reward, punishment, truth, or moral valence.

### Learning

For matched worlds differing only by an earlier event `e`, learning at a later probe `p` is the
causal statement

```text
Conduct(S_after_e, p) != Conduct(S_without_e, p)
```

at a declared consequential face, with a path showing how relation from `e` participates. This
definition does not supply a general developmental update law. Current Soma has bounded examples
of the causal minimum; broad transferable learning remains open.

## 12. Optional mathematical layers

The base mechanics licenses, but does not automatically contain, the following layers.

| Additional structure | What it enables | What is absent without it |
|---|---|---|
| Semi-simplicial face maps | Exact simplex occurrences with parallel equal simplices and automatic `partial^2=0` | Arbitrary irregular cells or rewrite law |
| Hypergraph rewrite rules | Arbitrary-arity local replacement and causal dependency | Orientation, boundary, metric, confluence |
| Sheaf/cosheaf on the complex | Compatible local data and local-to-global obstruction | Dynamics or probability by itself |
| Additive cochains | `d`, residual cochains, discrete Stokes | Nonlinear/noninvertible transport |
| Connection/groupoid | Rebase, parallel transport, holonomy | Length, angle, diffusion |
| Metric/Hodge star | Codifferential, Laplacian, energy, diffusion | Canonical choice of weights or physical units |
| Parameter family + discriminant | Phase strata and typed phase transitions | A universal phase label |
| Measure/filtration | Conditional probability and Bayesian quotient | Ontic chance or action selection |
| Discrete curvature law | A selected curvature observable or flow | Canonical Ricci tensor/flow from incidence alone |

For an abelian connection cochain `A`, the triangle curvature can be `F=dA`. For a metric complex,
one may define a selected discrete Laplacian and diffusion. A discrete Ricci flow needs an explicit
metric, curvature definition, and update law; multiple inequivalent discretizations exist. None is
forced by the incidence carrier.

## 13. Self-similarity and phase

Visual recurrence is evidence to inspect, not a theorem. A self-similar return needs an explicit
restriction/rebase map, for example a semiconjugacy

```text
q circle F^n = G circle q
```

or a conjugacy when `q` is invertible. The occurrence at the later event remains distinct even
when the transported law recurs.

Given a parameter base `B`, a family of local laws `Lambda_b`, and a declared equivalence of their
transport structure, a phase is a connected component of the region where that equivalence
continues. The discriminant is where the required rank, incidence, transport, or continuation map
fails. “Phase” is therefore relative to the chosen family and invariants.

## 14. Source conformance at this cut

| Obligation | Current grade | Exact boundary |
|---|---|---|
| Plural occurrence identity | Implemented and bounded measured | Event-local cells and disconnected equal live constituents remain plural |
| Oriented incidence and `partial^2=0` | Implemented for source `Boundary` incidence | Dependency and live transport incidence are not one unified chain complex |
| Independent cell coordinates | Implemented and bounded measured | `dependency_rank`, topological `dimension`, and constituent `grain` are supplied independently; aligned charts remain an explicit convenience constructor |
| Internal dependency | Implemented in bounded event complexes | `dependency_rank` orders the event-local relation; no general external event-structure object exists |
| Local exact transport | Implemented | `SparseTransport` and path products are specialized Soma carriers |
| Triangle/path comparison | Implemented and bounded host/CUDA/rest measured | `ParallelPathComparison` retains both complete routes; `Chi` is its optional projective projection and can persist independently of a deed. Noncommutation remains OPEN without FOUND; only an actual commuting comparison RIDEs |
| Split and joint regional junction | Bounded implemented and host/CUDA measured | Only equal source-declared `InterfaceCapability` values admit a seam; projection, reach, coordinate, and grain equality do not |
| Grain hand-up | Implemented in regional composition | Grain is independent of topological dimension; no universal law is asserted between them |
| Finite closure termination | Derivable for the implemented closure | General confluence, associativity, and causal invariance are unproved |
| Outgoing compression | Implemented with an exact structural certificate; source-declared higher-grain boundary replacement is bounded host-measured | `Phi_boundary` covers current later-contact conduct; arbitrary future-world congruence remains open |
| Exact rest/remount | Implemented and bounded measured | Does not establish persistent device-resident regional ecology |
| Local rewrite occurrence | Implemented as source-declared `RewriteInterface` incidence | Soma receives an actual rewrite and preserved interface; it does not search or own a universal DPO rule system |
| Metric, diffusion, probability field, Ricci flow | Absent by design | Each requires an explicit optional layer and application law |
| General learning law | Open | Only bounded causal learning species are measured |

## 15. Proof and construction ledger

### Exact under written assumptions

- semi-simplicial face identities imply `partial^2=0`;
- oriented gluing across one actual shared face cancels that internal boundary;
- discrete Stokes follows from cochain duality: `d omega(c) = omega(partial c)`;
- invertible local rebase conjugates loop holonomy;
- the implemented joint-closure algorithm terminates under its finite monotone measure; and
- the factorization condition above is necessary and sufficient for exact preservation of the
  declared observation family `Phi`.

### Conditional external theorems

- DPO concurrency/local Church–Rosser results apply only in their adhesive-category and matching
  hypotheses;
- Pachner moves relate triangulations under their standard PL and boundary hypotheses but do not
  supply Eros's transport law;
- Ricci flow, Hodge theory, and manifold theorems apply only after their metric/smooth hypotheses
  are actually constructed.

### Still open

- a general source rule/match language when an application needs Soma to receive more than an
  already-actualized rewrite occurrence;
- confluence or causal invariance of interacting regional rewrites;
- a compression congruence for future world laws beyond the exact current boundary family;
- a derived relation between organizational grain and topological dimension;
- a general developmental/training law that recruits, retains, and releases useful structure;
- a grounded metric/diffusion layer, if an application requires one; and
- universality, physical identity, and the Riemann Hypothesis bridges.

## 16. Bounded acceptance at this construction cut

The implemented cell closes the smallest generalized carrier, not every optional rewrite theorem:

1. one triangular world supplies 21 cells and 27 oriented incidences with `partial^2=0`;
2. one contrasting local-rewrite world supplies 12 cells and 6 incidences, holds dimension `0`
   while dependency rank and grain change, and marks the preserved interface explicitly;
3. only equal declared interface capabilities join; the older reach/grain inference is removed;
4. both worlds pass the exact `Phi_boundary` preservation check, and the rewrite cell returns its
   structural certificate explicitly;
5. one-core host, eight-core host, and CUDA return identical radiation and Standing; and
6. the joint two-world successor crosses exact durable rest/remount; and
7. an OPEN comparison carries exact residual without FOUND, survives rest/remount, participates in
   later production conduct, and RIDEs only under an actual later matching boundary.

Still outside this cut are a universal rewrite matcher, arbitrary critical-pair enumeration,
confluence/causal-invariance proofs, metric hinge kinematics, diffusion, and a congruence theorem
for future world relations not represented in the current live boundary.

Exact OPEN/later-boundary construction:
[`THE OPEN COMPARISON STANDS`](RESEARCH/2026-07-22_THE_OPEN_COMPARISON_STANDS_THE_LATER_BOUNDARY_MUST_ACTUALLY_MATCH.md)
and [`open comparison Standing 01`](observations/eros-open-comparison-standing-01/RESULTS.md).

## 17. Decisive external references

- Wolfram Physics Project, [local relation rewriting](https://www.wolframphysics.org/technical-introduction/basic-form-of-models/first-example-of-a-rule/),
  [updating events and causal dependence](https://www.wolframphysics.org/technical-introduction/the-updating-process-in-our-models/updating-events-and-causal-dependence/),
  [multiway systems](https://www.wolframphysics.org/technical-introduction/the-updating-process-in-our-models/multiway-systems-for-our-models/), and
  [causal invariance](https://www.wolframphysics.org/technical-introduction/the-updating-process-in-our-models/causal-invariance/index.html).
- MathWorld, [Hypergraph](https://mathworld.wolfram.com/Hypergraph.html),
  [Cellular Automaton](https://mathworld.wolfram.com/CellularAutomaton.html),
  [Simplex](https://mathworld.wolfram.com/Simplex.html), and
  [Simplicial Complex](https://mathworld.wolfram.com/SimplicialComplex.html).
- Stephen Lack and Paweł Sobociński,
  [*Adhesive Categories*](https://www.brics.dk/RS/03/31/), for the categorical setting in which
  DPO rewriting admits concurrency and local Church–Rosser theorems.
- Paolo Baldan, Davide Castelnovo, Andrea Corradini, and Fabio Gadducci,
  [*Left-Linear Rewriting in Adhesive Categories*](https://arxiv.org/abs/2407.06181), for the care
  required once merging enters rewrite independence.
- Allen Hatcher, [*Algebraic Topology*, Chapter 2](https://pi.math.cornell.edu/~hatcher/AT/ATch2.pdf),
  for oriented chains, boundaries, homology, and relative homology.
- Udo Pachner,
  [*P.L. Homeomorphic Manifolds are Equivalent by Elementary Shellings*](https://doi.org/10.1016/S0195-6698(13)80080-7),
  for the exact PL boundary of bistellar/Pachner moves.
- David I. Spivak and Brendan Fong,
  [*An Invitation to Applied Category Theory*](https://arxiv.org/abs/1803.05316), for compositional
  spans, cospans, and system interfaces.
- Mathieu Desbrun, Eva Kanso, and Yiying Tong,
  [*Discrete Differential Forms for Computational Modeling*](https://arxiv.org/abs/math/0508341),
  for the extra structures required by discrete exterior calculus.
