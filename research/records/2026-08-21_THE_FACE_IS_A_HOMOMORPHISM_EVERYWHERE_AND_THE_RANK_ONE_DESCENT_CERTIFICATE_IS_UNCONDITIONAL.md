# The face is a homomorphism everywhere, and the rank-one descent certificate is unconditional

**Date:** 2026-08-21
**Kind:** the first rung of the wall ladder — Brandon: *"I would like to proceed with the
attack ladder."*  Solo orchestrator work, one Lean file; the two landing identities
verified in exact rational arithmetic (688 random samples plus the factored cofactor
forms) before encoding.  **It schedules nothing.**
[`blueprint/THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction
authorities.
**Position under the active plan.** Exterior mathematical material for the mathematics
codec arm of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../archive/plans/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
Its Deed M6 poses the machine-side question over exactly this material — the theorem name
`Descent.TheFaceIsAHomomorphismEverywhere`, the case complex, the exceptional
conventions — and admits its source as a content-addressed snapshot, so which occurrence
M6 admits (before or after this file) is that deed's own declaration to make.  The Lean
line does not couple to the engine, per Brandon's standing ruling.
**Truth grades:** `proved-derived` with `formal-checked` evidence for the twelve Lean
theorems (`#print axioms` → `[propext, Classical.choice, Quot.sound]` on all twelve,
zero `sorryAx`).

---

## 1. What was proved

Owner: `ElementaryHolonics/Millennium/FaceHomomorphism.lean` (911 lines).  Measured after
the merge: `Millennium/` is **68 files, 22,952 lines, 1,033 top-level `theorem`
declarations** (`grep -h "^theorem " ElementaryHolonics/Millennium/*.lean | wc -l`,
2026-08-21; six files are Sol's); the library builds at **3,393 jobs**.

**Three named-open propositions are discharged**, each open since the file that posed it:

| proposition | posed in | discharged by |
|---|---|---|
| `Descent.TheFaceIsAHomomorphismEverywhere` — the face `P ↦ (x, x−1)` mod squares is multiplicative on the whole point group of `y² = x³ − x` | `Descent.lean` | `theDescentFaceIsAHomomorphismEverywhereHolds` |
| `RankOne.TheFaceIsAHomomorphismEverywhere` — the same on `y² = x³ − 25x` | `RankOne.lean` | `theRankOneFaceIsAHomomorphismEverywhereHolds` |
| `FaithfulFace.TheGeneralChordClosesTheFace` — the guarded coordinate form, checked over 198 pairs before this file | `FaithfulFace.lean` | `theGeneralChordClosesTheFaceHolds` |

The proof runs through mathlib's actual group law on
`WeierstrassCurve.Affine.Point` — every branch of the addition (identity, vertical
inverse, tangent doubling, half-turn chord, general secant) enters through its own
mathlib case lemma, with no hidden default branch.

## 2. The conventions are derived, not declared

The two landing laws are the load-bearing new mathematics, and they are **family-wise**
— every twist `y² = x³ − n²x` at once:

```text
theChordLandsOnTheZeroHalfTurn:    X₃ = 0  ⟹  x₁·x₂ = −n²        exactly
theChordLandsOnTheSecondHalfTurn:  X₃ = n  ⟹  (x₁−n)(x₂−n) = 2n²  exactly
```

The classical descent convention at a vanishing slot — `−n²` at `(0,0)`, `2n²` at
`(n,0)` — is exactly what the constraint algebra returns when the chord lands there: the
convention values are theorems.  The mechanism: the landing forces the line through the
half-turn, the vanishing line-value collapses one chord identity, and eliminating the
slope against the curve equation leaves the product of the surviving slots pinned to the
convention constant.  Both identities were verified over 688 exact random samples before
encoding; the kernel certificates are two `linear_combination` calls with hand-derived
cofactors.

`theDoublesLandInTheKernel` (both curves) is the forward half of the kernel law: every
`Q + Q` reads trivially on both slots, at point level, through the tangent case.

## 3. The rank-one descent certificate is unconditional

**`theNewPointEscapesEveryTorsionTranslateOfADouble`**: for every point `T` of finite
order and every point `Q` of `y² = x³ − 25x`, the realized point `P = (−4, 6)` is not
`T + 2Q`.  So `P` is nonzero in `E₅(ℚ)/(torsion + 2·E₅(ℚ))` — the two-descent's
certificate that the realized population strictly exceeds the torsion — and every
ingredient is now a theorem in this tree:

- the face homomorphism (this file);
- the doubles-in-kernel law (this file);
- the face separations (`RankOne.theFaceSeparatesTheNewPoint`, by `−1` and `5` failing
  to be squares);
- the torsion classification (`DistantWindings.theTorsionIsTheKleinGroupHolds`, the
  3-adic depth descent).

With `DistantWindings.thePointHasInfiniteOrderHolds` this closes the rank-one curve's
descent story as far as the lower bound goes: the five-curve's realized population
carries a direction no torsion supplies, kernel-checked end to end with no imported
classification and no counting receiver.

## 4. What is owed, with falsifiers

**None scheduled; the roadmap alone schedules.**

| owed | falsifier |
|---|---|
| the kernel's converse (`Descent.TheKernelIsTheDoubledPopulation`): a point with trivial face is a double — the surjectivity half of the descent exact sequence | a point with square slots that no `Q` doubles to |
| the same assembly at thirty-four: slot definitions on the `E₃₄` point type, its Klein sums, and its torsion classification (the depth-descent machinery re-aimed) — turning `ChordFace.theSevenClassesAreSeparated` into the unconditional independence certificate | a relation `aP₁ + bP₂ ∈ torsion` the face fails to refuse |
| the Selmer enumeration at thirty-four bounding the rank above — rank exactly two | a fifth Selmer class the local frames admit |
| the four-half-turns population on `y² = x³ − x` (Fermat's own descent, the rank-zero side at one) — now reachable because the face homomorphism it needed is proved | a fifth rational point off the two-torsion |

## 5. Boundaries

The homomorphism is proved for the two route curves, not yet instanced at thirty-four
(the landing laws are family-wise; the point-level slots and torsion classification
there are owed).  The kernel law has only its forward half.  Nothing about the
Birch–Swinnerton-Dyer conjecture.
