# The descent is climbed, the rank is zero, and one is not a congruent number

**Date:** 2026-08-21
**Kind:** the sharpening deed — Brandon's direction after the waves: *no wave, sharpen and
focus, hone in on BSD.* Solo orchestrator work, two Lean files, no agents. **It schedules
nothing.** [`blueprint/THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Exterior mathematical material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../archive/plans/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
The Lean line does not couple to the engine, per Brandon's standing ruling.
**Truth grades:** `proved-derived` for every theorem named, kernel-checked, audited by
`#print axioms` free of `sorryAx`; `proved-standard` for the imported classical machinery,
cited; `measured` where stated with commands.

---

## 1. What was proved

**The BSD route's oldest named-open proposition is discharged as a theorem.**
`Descent.TheFourHalfTurnsAreTheWholePopulation` — every rational point of the congruent-number
curve `y² = x³ − x` is the identity or one of the three half-turns — now holds by
`RankZero.theFourHalfTurnsAreTheWholePopulationHolds`. **The curve's Mordell–Weil group is
exactly the computed Klein four-group; the rank is zero; and
`theOneIsNotACongruentNumber` is a theorem** — no rational right triangle has area one. This is
the first complete rank computation in the tree, and it is Fermat's own theorem (c. 1640), by
Fermat's own method, kernel-checked.

Two owners:

- **`ElementaryHolonics/Millennium/MinusFourth.lean`** — the mountain: `x⁴ − y⁴ = z²` has no
  integer solution with `y, z ≠ 0` (`theMinusFourthHasNoSolution`). **Measured absent from
  mathlib** (`grep -rn "4 - b ^ 4" Mathlib --include='*.lean'` → 0; `not_fermat_42` covers only
  the plus form, and the minus form descends within itself). The proof is the first infinite
  descent in mathematics, transported onto mathlib's Pythagorean classification and
  `Int.sq_of_gcd_eq_one` in the idiom of mathlib's own plus-form file: the even lead fails by
  the odd-square residue `1 mod 8`; the odd branch descends in one classification
  (`(ab)² = m⁴ − n⁴`, `|m| < |a|`); the even branch descends through two nested classifications
  and the four-fold coprime factorization `(b/2)² = r·s·(r−s)·(r+s)`, whose bands and factors
  are forced to squares, returning `j⁴ − k⁴ = (uv)²` with `j⁴` strictly below the lead.
  **The descent preserves coprimality** — the classification hands `gcd = 1` down and coprime
  squares force coprime roots — so the strong induction carries coprimality and the
  gcd-reduction happens once, in the wrapper. Every branch identity was verified in exact
  rational arithmetic before encoding.
- **`ElementaryHolonics/Millennium/RankZero.lean`** — the bridge and the discharge: a point
  with `y ≠ 0` yields `X = (x²+1)/(2y)`, `Y = (x⁴−6x²+1)/(4y²)` with `X⁴ − 1 = Y²` (the
  identity's whole content is `(x²+1)⁴ − (x⁴−6x²+1)² = 16(x³−x)²`, verified on 292 exact
  points before encoding); `Y ≠ 0` because `x⁴−6x²+1 = 0` would make `(x²−3)² = 8` with eight
  not a rational square; clearing `X`'s denominator lands `num⁴ − den⁴ = (Y·den²)²` with the
  rational `Y·den²` forced integral because its square is — and the descent refuses it. The
  vanishing ordinate factors the abscissa into `{0, 1, −1}`, and the population is the four
  half-turns. The triangle face rides the same refusal through `x = c²/4, y = c(a²−b²)/8` and
  the exact identity `(a²−b²)² = c⁴ − 16` under `ab = 2, a²+b² = c²`.

**State after the merge: `Millennium/` is 56 files, 18,300 lines, 919 theorems**, library at
3,376 jobs; the four summit theorems audit to the three ordinary foundations, zero `sorryAx`.

## 2. What this closes, in the route's own terms

The BSD route's spine sentence is *placement is a faithful receiver of realization*. On this
curve, both sides are now theorems: the realized population is exactly the torsion table
(this deed), and the descent face separates it with both slots of every double reading trivial
(`Descent.lean`, `FaithfulFace.lean`). The realized side of the rank-zero BSD instance for this
curve is closed; the analytic side (`L(E,1) ≠ 0`) is untouched and unclaimed. And the proof is
the dialect's own mechanism made load-bearing: **a route that would realize a fifth point
cannot close, because closing it would found an infinite strictly-descending chain on
well-founded terrain** — navigation's FOUND stroke, with well-foundedness as termination,
exactly as the route records posed it before the deed existed.

## 3. What is owed next, with falsifiers

**None scheduled; the roadmap alone schedules.**

| owed | falsifier |
|---|---|
| the same discharge for the rank-one curve's torsion classification (`RankOne.TheTorsionIsTheKleinGroup`) — **ADVANCED 2026-08-21, same day**: `ElementaryHolonics/Millennium/WindingCensus.lean` reads the census receiver by receiver — the second winding closes exactly on the Klein table, no route halves a half-turn, the third winding never closes — and reduces the whole classification to one named statement, `TheDistantPrimeWindingsNeverClose` (no route closes at a prime winding of five or more), whose classical proof is the compact-frame transport; the framing is [the winding-census record](2026-08-21_THE_TORSION_IS_A_CENSUS_OF_CLOSED_WINDINGS_AND_THE_COMPACT_FRAME_READS_IT_WHOLE.md). **DISCHARGED IN FULL 2026-08-21, same day**: the kernel's depth descent closes the census — [the kernel-descent record](2026-08-21_THE_KERNEL_DESCENDS_ON_DEPTH_AND_THE_TORSION_CENSUS_IS_A_THEOREM.md) | a torsion point off the Klein group |
| `MinusFourth` offered upstream: mathlib has the plus form and lacks the minus form; the file is written in mathlib's own idiom | a mathlib declaration under another name already carrying it |
| the congruent-number statement for other small `n` (2, 3 non-congruent classically; 5, 6, 7 congruent — `RankOne` already carries five's point) | — |

## 4. Boundaries

Rank zero for this one curve; the non-congruence of one; nothing about other congruent numbers
beyond what `RankOne.lean` separately exhibits, nothing about ranks in general, and nothing
about the Birch–Swinnerton-Dyer conjecture — whose rank-zero prediction for this curve this
result is consistent with, not evidence for. The Pythagorean classification,
`Int.sq_of_gcd_eq_one`, and the plus-form idioms are mathlib's; Fermat's theorem and Koblitz's
correspondence are cited, and the minus-form descent and the bridge are proved here.
