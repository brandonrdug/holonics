# Curvature itself returns the Bianchi identity, the tail is irrelevant at every event, and divergence-freeness is the cell current law

**Date:** 2026-09-01
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job counts below)
**Provenance:** Brandon, 2026-09-01: *"if you could proceed with building *curvature itself*, that's certainly a necessity, and I wonder how that could've been missing till now. That, and your suggested … join theorem … and the relevance theorem"*; *"I called it a *relevance theorem*, because I wanted you to derive it."* Assistant derivation for the proofs.
**Band:** CURVATURE DIFFERENTIAL BUILT / BIANCHI PROVED / GAUGE COVARIANCE ON THE FOUR-FORCE CARRIER / PER-EVENT TAIL IRRELEVANCE PROVED / RELEVANCE CONTROL RETURNS STATEMENT B / CELL CURRENT LAW PROVED / FINITE FREQUENCY REACH PROVED / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN AT BRANDON'S DIRECTION

---

## Present question

[definition] Three surveys of the tree (Hodge owners, the Navier--Stokes posing, canon on the
continuum) returned that curvature existed only as a returned holonomy defect on an addressed
face and, in Rust, as the abelian `F = da` with the commutator measured but never differentiated;
that the divergence-free condition was proved as a trace, as a per-mode orthogonality, and as
periodic face cancellation, but never as the current law on one cell; and that Brandon's relevance
hypothesis had six prose statements in canon and no theorem. Brandon asked for all three.

## Return

[proved-derived; formal-checked] `HolonicConnectionCurvature.lean`. A connection is one component
`A_i : ℝⁿ → 𝔤` per coordinate, `𝔤` any normed `ℝ`-algebra, the bracket the ring commutator.
`curvature A i j = ∂_i A_j − ∂_j A_i + [A_i, A_j]`; `covariantDerivative A i X = ∂_i X + [A_i, X]`.
`bianchi`: `D_i F_jk + D_j F_ki + D_k F_ij = 0` for every `C²` connection. The proof spends exactly
the symmetry of second differentials (`ContDiffAt.isSymmSndFDerivAt`) and the Jacobi identity of
the commutator (`noncomm_ring`). `curvature_eq_of_commute` returns the abelian `F = dA`. On the
discrete side `gaugeTransform` conjugates every edge transport of a `FourForceCarrier` by a vertex
gauge, and `returnedCurvature_gaugeTransform` proves the face return conjugates by the gauge at the
far vertex; `returnedCurvature_gaugeTransform_eq_one_iff` makes flatness gauge-invariant. The
group identity `gauge_face_identity` carries `[propext]` alone.

[proved-derived; formal-checked] `NavierStokesTailRelevance.lean`. `tailMass solution N t` is Sol's
coefficient tail mass over the complement of the cube of radius `N`, read as a function of time.
`tendsto_frequencyCube_atTop`: the cubes are cofinal among finite frequency populations.
`tendsto_tailMass_atTop`: at every interior time the tail mass tends to zero as `N` grows. This is
per-event irrelevance: once the addressed band is wide enough no receiver at that event separates
the tail. It spends only Sol's absolute summability and the cofinality of the cubes.
`TailRelevanceControl`: for every admitted positive-viscosity solution some radius has a tail mass
that is measurable, continuous, and interval-integrable on a terminal tail.
`statementB_of_tailRelevance : TailRelevanceControl → StatementB` and
`officialProblem_of_tailRelevance`, through the aligned strain budget with
`relevanceBudget = 3² · (2π · G(N) · 3·√(2·E(0)) + tailMass N t)`.

[proved-derived; formal-checked] `NavierStokesCellCurrentLaw.lean`. `faceFlux v i side` is the
flux of the `i`-th component through the face `x_i = side` of the unit cell; `faceBalance` is the
outgoing minus incoming flux over the six faces. `integral_divergence_unitCube_eq_faceBalance`: the
integrated divergence is the face balance, for every `C¹` field, no periodicity.
`faceBalance_eq_zero_of_divergenceFree` and `faceBalance_eq_zero_of_initialVelocityCondition`:
a divergence-free field has zero face balance on the cell. That is Kirchhoff's current law on the
cell, the no-storage case of continuity, and incompressibility is exactly zero storage of mass.

[proved-derived; formal-checked] `NavierStokesFrequencyReach.lean`. The only nonlinear channel
between frequency populations is the closed triad `p + q + k = 0`.
`receiver_mem_frequencyCube_of_closed`: legs within radii `a` and `b` feed a receiver only within
radius `a + b`. `tail_fed_only_through_tail`: a receiver outside the cube of radius `2N` has no
closed triad with both legs in the band of radius `N`. `reach_subset_frequencyCube`: `m`
interactions from the band reach at most radius `2^m · N`. Relevance propagates outward one shell
at a time; there is no any-to-any transfer. Build `3564` jobs, axioms
`[propext, Classical.choice, Quot.sound]`.

[established-bounded; measured] `lake build` of the three modules completes at `4072` jobs
(curvature) and `4037` jobs (relevance and cell law); all three registered in
`ElementaryHolonics.lean`. Axiom audit for every theorem named above:
`[propext, Classical.choice, Quot.sound]`. No `sorry`, no `native_decide`.

## The relevance theorem, read once

[interpretation] The Clay posing assumes `C^∞` everywhere and calls (2) incompressibility. On the
torus the continuum enters this route at exactly one place. The full strain reading at an event is
its finite addressed band plus its addressed convergent tail; the exterior face is paid at `t = 0`;
the tail is irrelevant at every event. What the official alternative asks is that the tail's
irrelevance be uniform in time up to `T`. "The tail never acquires a separating word before `T`"
is the interval integrability in `TailRelevanceControl`. A blow-up on this route would have to be
the tail becoming relevant, and it would have to be caused: the only channel into the tail is the
addressed nonlinear transfer through closed frequency triads, which is the cell current law in
frequency. Nothing here rules that out; it names where it would have to happen.

## What this does not establish

[open] `TailRelevanceControl` is not inhabited. No continuity or measurability of the tail mass in
time is proved; both are hypotheses of the control. No general-grid cell population is built; the
cell law is proved on the unit cell and the periodic identification of opposite faces remains
Sol's theorem. Nothing here claims Navier--Stokes regularity or a Yang--Mills construction; the
curvature owner has no action, no representation, and no continuum limit.

## Owners

[definition] `ElementaryHolonics/Millennium/HolonicConnectionCurvature.lean`,
`ElementaryHolonics/Millennium/NavierStokesTailRelevance.lean`,
`ElementaryHolonics/Millennium/NavierStokesCellCurrentLaw.lean`,
`ElementaryHolonics/Millennium/NavierStokesFrequencyReach.lean` (all new; registered). Sol's MVF6
release and the `Close MVF` commit each stashed the untracked Millennium-line work; both times it
was restored from the stash without dropping the stash. No Rust source changed.
