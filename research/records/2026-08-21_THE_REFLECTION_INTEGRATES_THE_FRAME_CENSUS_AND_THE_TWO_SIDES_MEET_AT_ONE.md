# The reflection integrates the frame census, and the two sides meet at one

**Date:** 2026-08-21
**Kind:** the analytic-side deed — Brandon: *"Let's proceed with B1 and what follows … as
much as you can, not only one step."*  Solo orchestrator work, two Lean files, no agents;
controls computed in exact arithmetic before encoding.  **It schedules nothing.**
[`blueprint/THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction
authorities.
**Position under the active plan.** Exterior mathematical material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../archive/plans/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
The Lean line does not couple to the engine, per Brandon's standing ruling.
**Truth grades:** `proved-derived` with `formal-checked` evidence for the fourteen Lean
theorems (`#print axioms` → `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`);
`proved-standard` for the cited bridges, named; `measured` where a command is stated.

---

## 0. The greater plan this sits in

The Birch–Swinnerton-Dyer question compares two readings of one curve, and the route builds
each exactly:

```text
REALIZED SIDE (closed for the two route curves)          ANALYTIC SIDE (opened by this deed)
rank zero on y² = x³ − x        (Fermat's descent)       the atoms: frame counts a_p
torsion = Klein on y² = x³−25x  (kernel depth descent)   = phase readings of the quarter-turn
infinite chain at (−4, 6)       (census + separation)    assembled by heat-damped winding sums
                                                          into L(E, s); reflection-symmetric;
              BOTH SIDES MEET AT n = 1 ────────────────► the value at the reflection's fixed
              (this deed: the theta census agrees          point is what BSD interrogates
               with the descent)
```

What follows this deed, in order of reach: the per-`n` Tunnell instrument (the theta
censuses are finite and decidable for every odd squarefree `n` — a both-sides laboratory);
the sign law of the sighted frames (Gauss's quartic residue condition) as a proved rather
than cited statement; the face-homomorphism proposition; the Selmer/Ш landing joined
through torsor classes.  None is scheduled here.

## 1. What was proved

Owners: `ElementaryHolonics/Millennium/ReflectionCensus.lean` and
`ElementaryHolonics/Millennium/ThetaCensus.lean` — **14 theorems, zero `sorry`, all
audited**.  Measured after the merge: `Millennium/` is **63 files, 20,700 lines, 990
top-level `theorem` declarations** (`grep -h "^theorem " ElementaryHolonics/Millennium/*.lean | wc -l`,
2026-08-21; three files are Sol's in the shared tree); the library builds at **3,388
jobs**.

**B1 — the reflection integrates the census** (`theReflectionIntegratesTheCensus`):
over every half-turn prime (`p ≡ 3 mod 4`), the affine census of **every** odd cubic
`y² = x³ + ax` is exactly `p` — the trace vanishes for the whole twist family at once, the
tree's first infinite-family fact about the analytic side's atoms.  The proof is one
reflection: the ordinate fiber counts `1 + χ(x³ + ax)`; the cubic is odd; the quarter-turn
is invisible to the frame (`theQuarterTurnIsInvisible`: no square root of minus one when
`p ≡ 3 mod 4`), so `χ(−1) = −1` and the summand is an odd function whose sum over the
closed frame vanishes.  **A blind frame is an intensity receiver: the count deviation
`a_p` is the phase the frame cannot read** — the phase-object theorem of the contract,
arriving as arithmetic.  Instances for both route curves
(`theBlindFrameIsBalancedOnBothCurves`) and brute-enumeration controls at 7, 11, 19
(`theBlindFrameControls`) agree with the general theorem.

**B2 — the sighted frames read the Gaussian winding**: a prime `p ≡ 1 mod 4` splits in the
Gaussian lattice (`theSightedPrimeSplitsInTheGaussianLattice`, `p = a² + b²`, mathlib's
two-squares theorem), and the count deviation is the winding readout `a_p = ±2a` —
verified as exact kernel enumerations at 13, 17, 29 (`theSightedFrameReadsTheWinding`,
`theWindingAgreesAtTheControls`: `a_p² = 4a²` with `a` the odd leg), with the quadratic
twist by five flipping the sign exactly where five is a non-residue
(`theTwistFlipsTheSign`, at 13: censuses 7 against 19, traces `+6` against `−6`).  The
sign law itself (which of `±2a`, Gauss's quartic residue condition) is cited, not proved.

**B3 — the two sides meet at one** (`ThetaCensus.lean`): Tunnell's theorem converts the
analytic side of the congruent-number problem into finite lattice censuses.  At `n = 1`
both are enumerated whole and kernel-checked (`theThickCensusIsComplete`,
`theThinCensusIsComplete`: each population is exactly `(0, ±1, 0)`), the vanishing
condition fails (`theTunnellComparisonRefusesEquality`: two is not half of two), and the
agreement theorem (`theAnalyticAndRealizedSidesAgreeAtOne`) places the count inequality
beside the kernel-checked `RankZero.theOneIsNotACongruentNumber`: the cited chain — count
inequality ⟹ nonvanishing central value (Tunnell 1983 via Waldspurger) ⟹ rank zero
(Coates–Wiles 1977, complex multiplication) — lands on exactly the statement Fermat's
descent proved.  **The first Birch–Swinnerton-Dyer instance in this tree with both sides
exact: the realized side by descent, the analytic side by a lattice census, agreeing.**

## 2. The framing enacted

[The trapezoid-and-Poisson record](2026-08-21_THE_TRAPEZOID_IS_THE_INTERACTION_PROFILE_AND_POISSON_SUMMATION_OWNS_INTEGRATION_BY_REFLECTION.md)
carries the derivation this deed enacts: integration by reflection is the closed-loop form
of the equal-spacing census — reflection deletes the boundary, Poisson summation is the
exact law, reduction at a prime is its arithmetic instance — and the theta census of B3 is
the same object on the lattice side.  The proof of B1 *is* the slogan made kernel-checkable:
**the census over a closed frame is integrated exactly by the reflection that the material
carries** — here the curve's own oddness, which is its half-turn structure, met by the
frame's inability to represent the quarter-turn.

## 3. What is owed, with falsifiers

**None scheduled; the roadmap alone schedules.**

| owed | falsifier |
|---|---|
| the per-`n` Tunnell instrument — **ADVANCED 2026-08-21, same day, to three and five**: `theCensusesDifferAtThree` (four ways each, four is not half of four — rank zero read, three not congruent, consistent with the classical record) and `theVanishingCensusMeetsTheInfiniteChainAtFive` (**neither form represents five at all**, so the vanishing condition *holds* — the signature of positive rank — and the tree's realized side answers with the kernel-checked infinite-order point: **across one and five the two sides move together, in opposite directions, both exact**) | an `n` whose census enumeration the box bound fails to close |
| the sighted-frame sign law (Gauss) proved rather than cited: `a_p = 2a` with the normalized split | a sighted prime whose normalized split disagrees with the enumerated trace |
| the count census lifted from the affine equation to `E(𝔽_p)` as mathlib's point type, joining B1 to the group structure the torsion census uses | a frame where the affine count plus one differs from the point count |
| the reflection law stated once at the Poisson grain: the finite aliasing identity `Σ_j ζ^{jk} = n·[n ∣ k]` as the common owner of B1's mechanism and the frame census | a winding the identity misreads |

## 4. Boundaries

The censuses are exact statements about equations over frames and lattices; nothing here
constructs an L-function, proves modularity, or claims the conjecture.  The two bridges in
B3 are imported literature, cited with their sources, and the agreement theorem asserts
only the conjunction of two facts proved in this tree — the reading that they are two sides
of one conjecture is the cited chain's, carried as provenance.  At the bad prime five the
affine census of the twisted curve still counts `p`, but the reading is not a supersingular
trace; the boundary is stated in the file.
