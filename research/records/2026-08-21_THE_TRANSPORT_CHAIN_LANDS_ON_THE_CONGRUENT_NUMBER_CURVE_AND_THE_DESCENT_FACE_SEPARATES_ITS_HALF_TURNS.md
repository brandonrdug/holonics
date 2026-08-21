# The transport chain lands on the congruent-number curve, and the descent face separates its half-turns

**Date:** 2026-08-21
**Kind:** derivation deposit — the first Birch–Swinnerton-Dyer-facing deed, taken on Brandon's
encouragement to spend the BSD momentum the strategy review surfaced. **It schedules nothing.**
[`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Exterior mathematical material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
Per Brandon's standing ruling, the Lean line does not couple to the engine; the only trees written
are `soma/formal/` and `research/records/`.
**Truth grades:** `proved-derived` for the fourteen Lean theorems, kernel-checked, all fourteen
audited by `#print axioms`, depending only on `propext`, `Classical.choice`, `Quot.sound`;
`proved-standard` for the imported classical descent facts, cited; `measured` for the mathlib
sweeps, with one correction recorded below; `interpretation` where marked; `open` for the three
named propositions.

---

## 0. The occasion

The strategy review found that the transport-chain vocabulary formalized on 2026-08-20 — realized
population, locally admissible population, obstruction group as their quotient, descent placed at
the chain's target `G/2G` — **is the two-descent diagram of an elliptic curve**: Realized is the
image of the rational points, LocallyAdmissible is the Selmer group, and the obstruction group is
Tate–Shafarevich at two. The chain was built before it was aimed. Brandon: *"If we have momentum
on BSD I would definitely encourage you to take a moment to see what you can do with it."* This
deed brings the chain onto the curve where descent began — `y² = x³ − x`, the congruent-number
curve for one, whose rank-zero statement is Fermat's own infinite descent.

## 1. What is proved

Owner: `soma/formal/elementary-holonics/ElementaryHolonics/Millennium/Descent.lean` — **14
theorems, zero `sorry`**, all audited clean, built through **mathlib's actual affine group law**
(`WeierstrassCurve.Affine.Point`), not a restatement of it.
**Measured after the merge: `Millennium/` is 28 files, 6,080 lines, 318 theorems**; the library
builds at 3,334 jobs.

| theorem | what it establishes |
|---|---|
| `nonsingular00`, `nonsingular10`, `nonsingularNeg10` | the three affine two-torsion points are nonsingular points of the curve |
| `theThreePointsAreHalfTurns` | each is a half-turn, `P + P = 0`, through the group law's own vertical-chord case |
| `theChordThroughTwoLandsOnTheThird` | all three chord sums computed through mathlib's secant slope and addition formulas — **the complete Klein four-group inside `E(ℚ)`, computed rather than declared** |
| `theFourFaceValues` | the descent face `P ↦ (x, x−1)` mod squares, with the classical convention at vanishing coordinates: `0 ↦ (1,1)`, `(0,0) ↦ (−1,−1)`, `(1,0) ↦ (1,2)`, `(−1,0) ↦ (−1,−2)` |
| `theFaceSeparatesTheFourPoints` | the four image pairs are **pairwise inequivalent** under componentwise square-class equality — injectivity carried entirely by `−1`, `2`, `−2` not being rational squares |
| `theFaceIsMultiplicativeOnTheComputedPopulation` | every product identity in the Klein group exhibited with its square witness — five literal, and one (`2 · (−2) = (1/2)⁻²·(−1)` read as `−1 = (1/2)²·(−4)`) where the square class genuinely works |

The three arithmetic separators (`theNegativeUnitClassIsNotTheTrivialClass`,
`theTwoClassIsNotTheTrivialClass`, `theNegativeTwoClassIsNotTheNegativeUnitClass`) are the whole
cost of injectivity: **the arithmetic pays for the geometry**, which is the realization law at its
smallest.

## 2. The open half, named and never claimed

Three real propositions about this curve, carried open with their classical status:

- **`TheFaceIsAHomomorphismEverywhere`** — the face is a homomorphism on the whole point group
  (the multiplicativity half of `E(ℚ)/2E(ℚ) ↪ (ℚ*/ℚ*²)²`). Classical; open here.
- **`TheKernelIsTheDoubledPopulation`** — trivial slots exactly on `2E(ℚ)` (the exactness half).
  Classical; open here.
- **`TheFourHalfTurnsAreTheWholePopulation`** — the rank is zero and the computed Klein group is
  everything. **Equivalent to one not being a congruent number**; classically Fermat's infinite
  descent, the first descent argument in mathematics — the FOUND stroke of navigation with the
  well-foundedness of the terrain as its termination. Open here.

The Tate–Shafarevich correspondence is carried in prose only: declaring the Selmer group by hand
would author the partition the grading rules forbid. Classically, for this curve, Selmer equals
the computed image and `Ш(E/ℚ)[2] = 0` — imported, cited, not proved.

## 3. A measurement corrected in the making, and what it found

The file's first draft claimed `grep -rli "selmer\|shafarevich\|mordell" Mathlib
--include='*.lean'` → 0 files. **Re-measured before committing the sentence: 2 files**, and one
is load-bearing: `Mathlib/RingTheory/DedekindDomain/SelmerGroup.lean` carries the `K(S, n)`
Selmer group of a Dedekind domain — **the target group of the descent map**, with its finiteness
route through the exact sequence against the unit and class groups. The Mordell–Weil theorem, the
Selmer group *of an elliptic curve*, and Tate–Shafarevich remain without owner. So the open
homomorphism proposition has a mathlib-native landing structure (`K({2}, 2)` over `ℚ` is exactly
where the four computed classes live), which raises the value of discharging it. The corrected
measurement is in the file header; a false zero from an unverified sweep is the convicted defect
and it was caught by re-running the command, not by luck.

## 4. The exactness question, and its standing anchor

`interpretation`, deposited because Brandon posed it directly: *"When and why do we lose
exactness, what are the characteristic constraints, when is something 'exact' as a solution?"* —
and noted its BSD flavour, rational against irrational.

The route reading: **exactness is closure of the return under the declared chart family, and the
loss sites are completed limits whose remainder was quotiented.** The first kernel-checked anchor
already exists in mathlib: `GenContFract.terminates_iff_rat` — a continued-fraction route
**terminates exactly when its value is rational**. The route's closure *is* rationality; a
quadratic irrational is a route that never closes but repeats (the periodicity half is Lagrange's
theorem, whose mathlib status is not measured here); and a rational point on the curve is a route
that closes on the curve, which is why the exactness question and BSD feel like one question.
This paragraph grades nothing and is the seed of its own future deposit.

## 5. What is owed, with falsifiers

**None is scheduled; the roadmap alone schedules.**

| owed | falsifier |
|---|---|
| the homomorphism proposition discharged against mathlib's `K(S, n)` Selmer group as the codomain — **ADVANCED 2026-08-21**: `ElementaryHolonics/Millennium/FaithfulFace.lean` (36 theorems) proves the face's law on the families a 2-descent uses, as general field identities over free `x, y` with the curve equation as hypothesis: **every doubled point reads trivial on both curves** (the three doubling numerators as exhibited squares over `4y²`, bridged to mathlib's own `addX`/tangent slope), and the three torsion translations carry their predicted classes with the closure products literal squares. The general square roots evaluate at `(−4, 6)` to exactly `RankOne`'s witnesses `41/12, 31/12`. The full `∀ P Q` proposition and the `K(S,n)` landing remain open. | a pair of points whose sum's slots leave the square class of the product |
| the kernel proposition on the computed population first — **the `2E(ℚ) ⊆ ker` half is now general** (the doubling-reads-trivial theorems above); the converse half remains open | a point `Q` with `2 • Q` a nonzero half-turn |
| ~~a second curve with **nonzero rank**~~ — **RETURNED 2026-08-21, same day**: `ElementaryHolonics/Millennium/RankOne.lean`, 12 theorems, zero `sorry`, first-pass clean compile. On `y² = x³ − 25x`: the three half-turns proved; the new point `P = (−4, 6)` doubled **through the tangent case of the group law** to `2P = (1681/144, −62279/1728)`; `P` and `2P` proved distinct from the identity and every half-turn; the descent face separating `P` from all four torsion images (the separations carried by `−1` and `5` failing to be squares — and the first-slot agreement with `(0,0)`, `−4 = (2/5)²·(−25)`, is the square class genuinely working before the second slot separates); and **both slots of `2P` proved literal squares** — `x(2P) = (41/12)²`, `x(2P) − 5 = (31/12)²` — the descent homomorphism's prediction returned as computation. Infinite order, the Klein torsion classification, and the homomorphism remain named open `Prop`s. | a generator whose slots the face cannot separate from the torsion images |
| **the rank-N investigation, planned at Brandon's direction 2026-08-21.** The record rank moved to **≥ 30 this month**: thirty linearly independent rational points exhibited unconditionally, attributed by [MathWorld's elliptic-curve-rank page](https://mathworld.wolfram.com/EllipticCurveRank.html) to *Claude working with L. Alpöge and A. Howell*, superseding Elkies 2006 (≥ 28) and Elkies–Klagsbrun 2024 (≥ 29); the largest unconditionally *exact* rank remains 20. The holonic question is not the leaderboard: it is what the realized population of a high-rank chain looks like as terrain — how thirty independent generators are *found* (navigation through which chart family), what the descent face's image population does as rank grows, and whether the boundedness-of-rank question is a receiver aperture statement. `open`; feeds the route, schedules nothing. | a high-rank curve whose generator population the chain vocabulary cannot state without collapsing independent generators |
| the exactness deposit: route closure as the definition of exact, with the terminating/periodic/aperiodic trichotomy against the algebraic degree | a rational value with a non-terminating canonical route, or a closed route off the declared chart family |
| the Perelman reading — the Poincaré proof posed in pure holonics (diffusion with retention contract, monotone receiver, condensation exhibiting its cut) — queued next per Brandon | — |

## 6. Boundaries

Nothing here claims movement on the Birch–Swinnerton-Dyer conjecture: no L-function, height
pairing, analytic rank, or Heegner point appears, and the three open propositions are carried as
propositions, never as results. The classical descent convention at vanishing coordinates is
cited (the product of differences against the other two roots); the four-point addition table and
the face values on it are computed, not declared, and the one authored object — the convention
itself — is named as authored. The curve has full rational two-torsion, which is the easiest
descent situation; nothing about general number fields, general torsion, or rank bounds follows.
