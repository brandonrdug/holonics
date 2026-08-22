# The torsion is a census of closed windings, and the compact frame reads it whole

**Date:** 2026-08-21
**Kind:** framing deposit with its enactment — Brandon's direction: *"Frame torsion
classification carefully, I think that same tool will be useful for the other Millennium
problems; in general ideas pertaining to textile motion like Knot Theory, winding, gradients,
etc. are powerful and more potent than you'd think, I say String Theory too even though it's
theoretical physics (we have research deposits on all of these things)."* **It schedules
nothing.** [`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Exterior mathematical material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
The Lean line does not couple to the engine, per Brandon's standing ruling.
**Truth grades:** `proved-derived` for the twelve Lean theorems, kernel-checked, all audited by
`#print axioms` to `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`; `proved-standard`
for the cited classical mathematics; `measured` where a command and date are stated;
`interpretation` for every correspondence, each marked where it sits.

---

## 1. The framing

**Torsion classification is a census of closed windings.** A rational point of an elliptic
curve is a route; `n • Q` is its repeated traversal, and — Brandon's own ratified reading,
[the cyclic-subgroup record](2026-08-16_THE_WITNESS_HAS_NO_ADDRESS_AND_REPETITION_EXPLORES_ONLY_A_CYCLIC_SUBGROUP.md)
— **repetition explores only a cyclic subgroup**. A winding is *closed* when the traversal
returns to rest, `n • Q = 0`. The Mordell–Weil group `E(ℚ) ≅ T ⊕ ℤʳ` is then one census with
two answers: the torsion `T` is the population of routes whose windings close — the **finite
return group** of the curve, the same object whose finiteness
`hypergeometric_closure.rs` decides for a three-site turning equation by sorting integers — and
the rank `r` counts the independent routes whose windings never close.

**Each rational receiver reads one band of winding numbers, and no family of them finishes.**

- **The square-class face** — `ℚ*/ℚ*²`, Kummer's `ℤ/2` double cover, which is the **parity face
  of winding**: [the half-twist record](2026-08-16_THE_JUNCTION_IS_A_HALF_TWIST_AND_A_MODULUS_IS_WHAT_A_DECLARED_QUOTIENT_RETAINS.md)'s
  one integer, *fiber winding = orientability class = crossing number*, read here as arithmetic.
  A half-turn point **is** the fiber flip, and the descent face lands every route's parity in
  the double-cover group. This receiver reads the *second* and *fourth* windings: the second
  closes exactly on the Klein table, and no route halves a half-turn — three quadratic
  refusals whose obstruction classes are `−1`, `2`, `2`, cousins of the separators `−1`, `2`,
  `−2` that carried `Descent.lean`'s injectivity on the rank-zero curve.
- **The tangent-return reading** — the third winding closes only where the tangent
  construction returns to its own abscissa, which is the third division polynomial
  (`3x⁴ − 150x² − 625` on `y² = x³ − 25x`), refused through three not being a rational square.
- **Every further winding number needs its own polynomial receiver** (the `n`-division
  polynomial), and the family never covers the population: infinitely many prime winding
  numbers remain. A receiver family that reads one winding number at a time is
  **aperture-incomplete for the census by construction** — the same shape as the method
  atlas's rule that only the finite strata are tables.

**The completing instrument is a transport to a compact frame.** Reduce the curve at a good
prime: in `E(𝔽_p)` *every* route closes, because the group is finite — the compact frame is
where the whole census is one reading. The transport is faithful on closed windings: the
kernel of reduction is winding-free, and its classical proof is a **well-founded descent
through the p-adic filtration** — a torsion route in the kernel would strictly descend
forever — which is *the same mechanism* as `MinusFourth.lean`'s Fermat descent. So both
halves of the realized side of Birch–Swinnerton-Dyer on these curves run on one tool:

> **Rank is bounded by refusing an infinite descent on heights; torsion is bounded by
> refusing an infinite descent on valuations. The census, on both axes, is the statement that
> the terrain is well-founded.**

For `y² = x³ − 25x` the compact frame at three has four points (`x ∈ {0, 1, 2}` each with
`y = 0`, plus the identity — computed by hand, `proved-standard` classically, not yet enacted),
so no prime winding of five or more survives the transport, and the census closes.

## 2. What is enacted, kernel-checked

Owner: `soma/formal/elementary-holonics/ElementaryHolonics/Millennium/WindingCensus.lean` —
**12 theorems, zero `sorry`, all audited**, on `y² = x³ − 25x` through mathlib's actual group
law. Measured after the merge: `Millennium/` is **57 files, 18,653 lines, 930 top-level
`theorem` declarations** (`grep -h "^theorem " ElementaryHolonics/Millennium/*.lean | wc -l`,
2026-08-21); the library builds at **3,377 jobs**.

| theorem | what it establishes |
|---|---|
| `theSecondWindingClosesExactlyOnTheTable` | `Q + Q = 0 ↔ Q ∈ {0, T0, T5, Tm5}` — the second winding closes exactly on the Klein table |
| `theDoubledRouteAvoidsTheTable` | no route halves a half-turn: the doubled population avoids all three half-turns, refused by the square classes `−1`, `2`, `2` |
| `theFourthWindingIsAlreadyTheSecond` | `4 • Q = 0 → 2 • Q = 0` |
| `theThirdWindingNeverCloses` | `Q ≠ 0 → 3 • Q ≠ 0`, through the third division polynomial and `¬IsSquare (3 : ℚ)` |
| `theCensusBelowTheFifthWinding` | every route closed by a winding number below five is on the Klein table — complete and unconditional |
| `theCensusReducesToTheDistantPrimeWindings` | **the reduction**: granting `TheDistantPrimeWindingsNeverClose` (no route closes at a prime winding ≥ 5), `RankOne.TheTorsionIsTheKleinGroup` follows |
| supporting | the four coordinate refusals, the cleared-double square `(3x²−25)² − 8xy² = (x²+25)²`, `¬IsSquare (3:ℚ)` |

The reduction theorem runs the order decomposition through mathlib's `addOrderOf` machinery
(`addOrderOf_nsmul_addOrderOf_sub`, `Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt`): any
closed winding number factors as windings the rational receivers already read, times primes at
five or beyond. **What `RankOne.TheTorsionIsTheKleinGroup` needs has narrowed from the
classical machinery wholesale (reduction or Mazur, neither in mathlib) to exactly one named
statement**, `TheDistantPrimeWindingsNeverClose`, carried open with its classical status cited.

**Mathlib measured, 2026-08-21, at pinned `v4.27.0`:**
`Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean` (2025, Bryan Wang) reduces the
**curve** over a discrete valuation ring — `IsIntegral`, `IsMinimal`, `reduction`,
`IsGoodReduction` — and defines **no reduction map on points** and no injectivity on torsion;
`DivisionPolynomial/{Basic,Degree}.lean` define `ψₙ` with **no theorem linking `n`-torsion to
its roots** (`grep -n "torsion" …/DivisionPolynomial/Basic.lean` → the word appears only as a
tag); no Lutz–Nagell, no Mazur (`grep -rln "Lutz\|Nagell" Mathlib --include='*.lean'` → 0
files). The compact-frame transport on points is the owed instrument everywhere, not an import.

## 3. Why this tool carries to the other Millennium problems

Each row names its grade; none claims a result.

- **BSD itself** (`interpretation`, and the sharpest row). The compact frame that reads the
  torsion census **is the frame whose counts build the L-function**: `a_p = p + 1 − #E(𝔽_p)`,
  and `LocalFactor.lean` already carries the Euler factor as `det(1 − T·companion)`. One
  instrument, two faces — the count that pins the closed windings is the count the analytic
  side is assembled from. BSD asks whether the family of compact frames is a *complete
  receiver family* for the rational population: whether what every finite frame reads,
  assembled, determines what never closes.
- **RH** (`proved-standard` for the instance). `#E(𝔽_p)` **is** the genus-one Weil/Hasse
  instance — `|a_p| ≤ 2√p` is the Riemann hypothesis for the curve over `𝔽_p`, proved, and it
  is the contract's own chain: ample class → Rosati positivity → placement. The torsion census
  and the tree's RH route already share their central object.
- **Hodge** (`proved-standard` for the classical statements). The contract already carries
  *torsion is winding that cannot be un-deposited*: the integral obstructions live in cokernel
  torsion (Atiyah–Hirzebruch; Kollár's `pα` reached, `α` not — modelled by
  `ObstructionSpecies::ReachableOnlyInMultiple`). The cycle-class audit *is* a census of
  closed windings in cohomology, and the same two-frame discipline applies: a class invisible
  to the rational face may be exactly visible in a finite frame.
- **Poincaré** (`interpretation`). `π₁` is the group of closed routes; the conjecture is a
  census statement — every winding closes trivially — and `Ricci.lean` already tracks the
  flow's winding rates (`1 − 4τ`, `1 − 2τ`). The census vocabulary and the flow vocabulary
  meet exactly where Perelman's proof needed them to.
- **String theory** (`interpretation`, cited, non-equivalence declared: nothing here builds
  F-theory). The physics literature reads **the same census**: in F-theory compactifications
  the Mordell–Weil free part gives the `U(1)` factors and **Mordell–Weil torsion determines
  the global structure of the gauge group** (its fundamental group) — Aspinwall–Morrison;
  Mayrhofer–Morrison–Till–Weigand 2014. [The lineage-string record](2026-08-15_A_LINEAGE_IS_A_STRING_AND_COMPACTIFICATION_IS_NODE_COMPRESSION.md)'s
  *compactification is node compression* lands here: torsion windings are the compact
  directions of the realized lattice.
- **Navier–Stokes** (`interpretation`, one sentence). Helicity is the linking number of vortex
  lines (Moffatt 1969) — a winding census conserved by ideal transport, with dissipation as
  the aperture that opens it.

**The compression face of this record is deposited separately, same day:**
[the compact-frame compression record](2026-08-21_THE_COMPACT_FRAME_IS_A_LAWFUL_COMPRESSION_AND_THE_HORIZON_LAW_PREDICTS_WHAT_CROSSES.md)
— the frame classified under the three species, the horizon-law prediction of what crosses
(winding whole, magnitude not at all, ratio as the local factor), tolerance and the
separating prime as distinguishing word, and the obstruction group as the frame family's
certified remainder.

## 4. What is owed, with falsifiers

**None scheduled; the roadmap alone schedules.**

| owed | falsifier |
|---|---|
| `TheDistantPrimeWindingsNeverClose` discharged — the compact-frame instrument: the curve over `ZMod 3`, its four-point census (finite, enumerable), the reduction map on points, and its injectivity on closed windings via the valuation descent | a rational point of prime order ≥ 5, or a torsion route the transport collapses |
| the same census run on the rank-zero curve `y² = x³ − x` (its `TheKernelIsTheDoubledPopulation` converse half is the halving criterion this file's refusals instantiate) | a point `Q` with `2 • Q` a nonzero half-turn |
| the winding census stated once, curve-generically — the refusals are quadratic-discriminant square classes and should quantify over `y² = x³ − n²x` | a curve in the family whose halving obstruction is not a square-class statement |

## 5. Boundaries

The census below the fifth winding is complete and unconditional for `y² = x³ − 25x`; nothing
is claimed about prime windings of five or more (carried open, classical status cited);
nothing about other curves beyond what `Descent.lean` and `RankOne.lean` separately establish;
nothing about the Birch–Swinnerton-Dyer conjecture. The correspondences in the third section
are entries into standing deposits and classical literature, graded where they stand; none is
an identity, and the F-theory and Navier–Stokes rows are readings, not constructions.
