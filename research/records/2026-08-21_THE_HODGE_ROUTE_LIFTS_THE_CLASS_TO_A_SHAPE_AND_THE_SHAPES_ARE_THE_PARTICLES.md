# The Hodge route lifts the class to a shape, and the shapes are the particles

**Date:** 2026-08-21
**Kind:** a problem-specific route chart, the second of the pair with
[`2026-08-21_THE_RIEMANN_ROUTE_RUNS_FROM_A_KERNEL_CHECKED_ANCHOR_TO_A_REALIZER_AT_THE_ARCHIMEDEAN_PLACE.md`](2026-08-21_THE_RIEMANN_ROUTE_RUNS_FROM_A_KERNEL_CHECKED_ANCHOR_TO_A_REALIZER_AT_THE_ARCHIMEDEAN_PLACE.md).
Stations are founded terrain; rungs are named open constructions with falsifiers; **it schedules
nothing.** [`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Exterior mathematical material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
No engine source is touched; the Lean tree is read, not extended, by this deposit.
**Truth grades:** `proved-derived` for the cited Lean theorems; `proved-standard` for every imported
classical theorem, cited at its station; `established-bounded` for the engine owners read at
source; `interpretation` for the particle reading and every correspondence marked as such; `open`
for every rung.
**Boundary, first:** nothing here claims movement on the Hodge conjecture.

---

## 0. Provenance — the shapes are the particles, and identity changes under refraction

**Brandon, directly, 2026-08-21:**

> *"Intuitively I keep reaching for geometric shapes like polygons and how they relate to
> polynomials so that we can couple the algebra and geometry, and then if you imagine that there's
> some way to integrate polygons into convex hulls that describe the potential of a shape that
> contains a volume, it is like integrating into a polyhedron, and to further that you can
> integrate into polytopes (topology, simplicial complex). I am pretty sure the shapes themselves
> are the 'particles' being transported, the identity of the particle changes as it is refracted
> throughout mediums, akin to how we say the speed of light 'slows' in different mediums."*

And the highway analogy, compressed: a car on a highway is one continuing occurrence whose soul is
never equivalent across time; macroscopically it is indistinguishable from the surrounding
vehicles; it is picked out only by **lineage** — having been observed before the merge — or by
**resonance at the offramp it specifically resonates with**; lane position and relative speed carry
deducible **tension** about intended continuation; and prediction above the individual needs
**population statistics for the higher-level partition**. And: *"irreducibility and caustics
signify landmarks relative to the receiver."*

Also governing, from 2026-08-04: spectral placement is one rough half of intelligence; the other
is *"lifting the observable invariant back to a geometric source … and the perturbance due to the
diffusion of information between distinct topologies, which is Hodge."* **This route is the lifting
half.** The Riemann route searches for the realizer that pays a placement; this route asks when a
receiver-visible invariant lifts back to a supported geometric source, and what prices the failure.

---

## 1. The target, complete

**The classical statement (the Millennium form is the rational one):** for a smooth projective
complex variety `X`, every class in `H^{2p}(X, ℚ) ∩ H^{p,p}(X)` is a `ℚ`-linear combination of
classes of algebraic subvarieties.

The proved and refuted perimeter, imported with citations:

- **Degree 2 is proved, integrally** — the Lefschetz theorem on `(1,1)`-classes: a `ℤ`-linear
  combination of divisor classes. Degrees `0`, `2`, `2n` are the only integrally true cases.
- **The integral statement fails in two independent ways**, and the uniform object is the
  **cokernel of the cycle class map**: torsion-habitat failures (Atiyah–Hirzebruch 1962, Totaro
  1997, Soulé–Voisin 2005 — the obstruction being odd stable cohomology operations, torsion only
  the habitat) and non-torsion failures (Kollár 1990/92 — `pα` algebraic, `α` not, in torsion-free
  cohomology, cokernel `ℤ/p`).
- **Dropping the ample realizer destroys the conclusion** — Voisin (IMRN 2002): compact tori carry
  Hodge classes in the `ℚ`-span of no coherent sheaf's Chern classes. Projective = Kähler + an
  integral **positive** class, and the theorem lives exactly in that gap. *Realization pays* has a
  named counterexample proving it.

---

## 2. Station: the index equivalence — proved, and the positivity can fail

**Standing, Lean, kernel-checked.**
`soma/formal/elementary-holonics/ElementaryHolonics/Millennium/LorentzianPerp.lean`:

- `theReverseCauchySchwarzIsNonpositivityOnThePerp` — the reverse inequality against a class of
  positive self-pairing **is** non-positivity on that class's perp, an equivalence; the
  denominator-cleared ordered-ring version retains the integral residue that field division hides.
- The ample witness: `theAmpleClassPays` (`q(ω,ω) = 24` on the Lorentzian lattice) and
  `theAmplePerpIsNonpositive`, proved by ordinary Cauchy–Schwarz on the spacelike block — **a
  positivity that can fail**, which the operating contract's missing-organ section names as the
  one demanded property the standing engine form (`supported_realizers::positive_form`, a Gram
  square) cannot exhibit.
- `Shadows.lean`'s `theStretchIsPlacedWhereTheSelfPairingSurvives` — the placement's operative
  hypothesis is the **nonzero self-pairing on the ray**, with the control that an honest isometry
  of an indefinite form (`!![2,1;1,1]` preserving `!![-2,1;1,2]`) stretches a null ray past 2 and
  places nothing. Positivity is supplied by the positive form, never by invariance.

**Imported:** the Hodge index theorem — signature `(1, ρ−1)` on the Néron–Severi lattice — is the
coupling as a theorem: the ample direction cannot exist without its negative complement. The hand
of the Hodge–Riemann relations is `i^{p−q}`, alternating across the pieces — the fork, not a
convention.

**Carrier change to the next station:** from a form on one lattice to the integral/rational span
question inside it.

---

## 3. Station: the cokernel priced exactly — the obstruction is a cokernel, not torsion

**Standing, Lean and engine, and the two agree.** `Shadows.lean` proves on one integral carrier:

- `theClassIsNotInTheIntegralSpan` and `theFourfoldIsInTheIntegralSpan` — the class reachable only
  at multiple 4, with `theFactorDividesTheSelfPairing` (`4 | 24`);
- sign failure and factor failure witnessed **independent** — a definite perp failing by the
  factor, an indefinite one splitting everything — which is the precise sense in which the
  obstruction is a **cokernel and not torsion**.

The engine owner is `crates/holonic-engine/src/supported_realizers.rs`, whose own module doc
states `ObstructionSpecies::ReachableOnlyInMultiple { factor }` as the faithful finite model of
Kollár's shape, with the standing bound: the Millennium statement is rational, so this models the
**integral** failure and may never be reported as a Millennium-Hodge obstruction after tensoring
with `ℚ`.

**The rung this station owes is the denominator bridge:** a period-theoretic statement about
denominators that would let the integral cokernel model speak to the rational statement — named in
the operating contract since 2026-08-08 and still unbuilt.
**Falsifier:** a class whose denominator behaviour the bridge predicts and a computed period
lattice that disagrees.

---

## 4. Station: the combinatorial proved instance — the ample chain runs on shapes already

**Standing, engine, driven.** `crates/holonic-engine/src/matroid_chow.rs` carries the
matroid Hodge–Riemann mechanism (Adiprasito–Huh–Katz, imported): `hodge_riemann_holds` for the
ample class, and the test named
`the_supermodular_class_breaks_hodge_riemann_wherever_the_top_grade_has_room` — outside-the-cone
classes are **required** to break the positivity, and do. Its driver prints the primitive part as
`P^k = ω^⊥`, which is this route's compression-onto-a-perp in a purely combinatorial chart.

This station matters because it is a **theorem-complete instance of the whole route** — ample
realizer → Lefschetz → Hodge–Riemann positivity → placement — on material with no variety at all:
the shapes carry the entire chain. That fact is the bridge to the next station.

---

## 5. Station: the particles are shapes, and the landing is exact

`interpretation` for the identification; `proved-standard` for every mathematical statement named;
and this is the station Brandon's protein and navigation notes were pointing at.

**The polygon→polynomial coupling is already standing terrain.**
`crates/holonic-engine/src/winding_inertia.rs` names circulant passages by winding through star
polygons and Dickson/Chebyshev polynomials; the nested-radical family's moduli are genus-zero
point counts ([`2026-08-20_LANDMARKS_AND_MODULI.md`](2026-08-20_LANDMARKS_AND_MODULI.md)). The
polygon *is* a polynomial's spectrum there.

**The integration ladder he describes — polygon into hull into polyhedron into polytope — is the
Newton-polytope dictionary, exactly:**

- **A polynomial's Newton polytope** is the convex hull of its exponent vectors — the shape *of*
  the algebra, with no chart chosen. This is the algebra↔geometry coupling posed.
- **Bernstein–Kushnirenko:** the generic number of solutions of a polynomial system is the **mixed
  volume** of its Newton polytopes — "integrating shapes into a hull that describes the potential
  of a volume" is literally how solution counts are computed.
- **The toric dictionary:** a lattice polytope presents a projective toric variety; its Hodge
  theory is lattice-point combinatorics (Danilov). Ampleness, the Lefschetz operator, and the
  Hodge–Riemann relations all have polytope presentations, and the AHK proof that
  `matroid_chow.rs` implements runs the ample chain on precisely this dictionary's abstraction.

So on this route the transported particle **is** a shape: a polytope with its lattice, carried
through chart transitions (refractions) that change its presentation — triangulation, projection,
mixed subdivision, fan refinement — while its lineage persists. *The identity of the particle
changes as it is refracted* is typed by the standing sameness family
([`2026-08-21_EQUALITY_IS_OCCURRENCE_IDENTITY_THE_SOUL_MAPS_KINSHIP_AND_THE_LEADER_RETURNS_THROUGH_THE_ACTIVE_CODEC.md`](2026-08-21_EQUALITY_IS_OCCURRENCE_IDENTITY_THE_SOUL_MAPS_KINSHIP_AND_THE_LEADER_RETURNS_THROUGH_THE_ACTIVE_CODEC.md)),
and the highway analogy lands on it clause by clause:

| the highway | the typed relation |
|---|---|
| the same car the whole trip, soul never equivalent | occurrence identity along lineage; soul isomorphism refused across states |
| indistinguishable among the traffic | receiver/history equivalence at the macroscopic family |
| picked out only if seen before the merge | lineage is the identity; a path plus its history, never a digest |
| the offramp it resonates with | the separating receiver — the distinguishing word of the collapsed pair |
| lane tension, relative speed | local covectors — pressure as a receiver-indexed reaction, never a global scalar |
| commute statistics of the district | the declared quotient `Q` — probability as an observer's quotient over what it does not carry |

**And the landmarks clause closes the loop with the Riemann route:** irreducibility and caustics
are landmarks relative to the receiver. An irreducible polynomial is a landmark in the shape
chart exactly as a prime is in the arithmetic chart — indecomposable under the declared product,
which for Newton polytopes is Minkowski sum: **a polytope is "prime" when it is not a Minkowski
sum of smaller ones, and polynomial factorization projects onto Minkowski decomposition of its
Newton polytope** (Ostrowski, imported). The two routes share their landmark law.

**What this station feeds without scheduling it:** the mathematics codec's particle deed. The
fold-and-catalysis audit already requires M1 particles to carry configuration, constraints,
Jacobian, energy sections and phase seams; this station adds the candidate carrier for the *purely
mathematical* particle — a shape with lattice, lineage, and typed sameness — and the protein
constraint ecology and the Newton polytope are the same demand at two physical grains.

---

## 6. Station: the far population — where the route meets the one missing organ

**Open, and it is the same organ the Riemann route needs at the archimedean place.** The operating
contract's missing-organ section holds three of four parts built (certified remainder; reopening
rule; supported realizer population with `positive_form` live) and one open: **a positive form
whose positivity can fail, computed on a far population where condensation is required rather than
incidental.** The Lean ample witness and `matroid_chow.rs` both have the can-fail property; both
run on small carriers. The named route to scale is spanning-tree interval labelling, where the
forced non-tree population is the certified remainder.

**Falsifier:** a run on a declared far population returning a condensed realizer whose certified
remainder fails to reopen under the declared receiver family.

---

## 7. What is owed on this route, consolidated

**None is scheduled; the roadmap alone schedules.**

| owed | station | falsifier |
|---|---|---|
| the denominator bridge, integral model → rational statement | the cokernel | as stated at its station |
| the far-population condensation run | the far population | as stated at its station |
| ~~the composed engine driver~~ — **WITHDRAWN 2026-08-21 by Brandon's ruling**: the Lean line does not couple to the engine — *"the Lean documents do not require the engine whatsoever."* The mathematics is theorized outside the engine and adapted within the mathematics first; any later engine composition is the roadmap's decision, not this route's. | the index equivalence | — |
| `Shadows.lean`'s own limits: the quotient `L/(ℤω ⊕ ω^⊥)` as a group with proved exponent; the complex spectral statement `\|λ\| = √q` | the cokernel | as recorded in its source |
| a first shape-particle witness: one polynomial family, its Newton polytopes, one Minkowski-irreducibility reading, cross-checked against `winding_inertia`'s isolation on the circulant case | the particles | a factorization whose Minkowski projection the reading misses, or an irreducible whose polytope decomposes |
| the rigidity join — self-stress as supported realizer, stress-form radical as the gauge, prestress stability as positivity on the flex subspace — deposited and then instanced over `ℚ` with the algebraic radical quotient | the index equivalence | a framework whose stress form is positive semidefinite of maximal rank and which is not globally rigid under the imported theorem's hypotheses |

## 8. Boundaries

No claim of movement on the Hodge conjecture is made anywhere above. The proved content cited is:
the index equivalence and its witnesses, the integral-span pair with the independence of sign and
factor failure, the fixed-locus and placement theorems, and the engine's matroid Hodge–Riemann
mechanism — each on its declared carrier. Lefschetz `(1,1)`, Atiyah–Hirzebruch, Totaro,
Soulé–Voisin, Kollár, Voisin, Adiprasito–Huh–Katz, Bernstein–Kushnirenko, Danilov and Ostrowski
are imported and cited, never reproved. The shapes-as-particles identification is
`interpretation`: it names a candidate carrier and its typed sameness; it does not assert that
every mathematical particle is a polytope, and it grades nothing.
