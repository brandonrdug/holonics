# The obstruction is exhibited at seventeen, and the invisible cosets pass every frame

**Date:** 2026-08-22
**Kind:** the aggressive deed of the mod-two Birch–Swinnerton-Dyer goal — the
Tate–Shafarevich structure made exact at its classical first home.  Solo orchestrator
work, one Lean file; the full local structure computed and verified before encoding
(sixteen classes refused at two, twelve everywhere-locally-admissible, the
depth-universal witness families checked in exact arithmetic).  **It schedules
nothing.**
[`blueprint/THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction
authorities.
**Truth grades:** `proved-derived` with `formal-checked` evidence for the five headline
Lean theorems (`#print axioms` → `[propext, Classical.choice, Quot.sound]`, zero
`sorryAx`); `interpretation` for the Selmer/Ш readings, marked; one named-open
proposition carrying the second descent.

---

## 1. What was proved

Owner: `ElementaryHolonics/Millennium/SeventeenObstruction.lean` (1,231 lines).  The
library builds at **3,399 jobs**.

Seventeen is where the governance matrix goes **singular**: `17 ≡ 1 (mod 8)`, both
governing characters vanish, and the stratum machinery's `p`-adic refusals have
nothing to grip.  What replaces the clean corank law is the obstruction object, and
this file computes its entire local anatomy:

- **`theSeventeenFaceLiesInTheSelmerSixteen`** — every point's face lies among sixteen
  classes: the four realized torsion classes and **twelve locally invisible classes**
  in three cosets.  Thirty-two candidates die in the real frame; sixteen die at the
  frame of eight (four kernel `decide`s with the halving descent, the refused classes
  translated through the homomorphism);
- **`theInvisibleCosetsPassEveryTwoAdicFrame`** and
  **`theInvisibleCosetsPassEverySeventeenAdicFrame`** — for each of the three coset
  representatives `(1,2)`, `(1,17)`, `(1,34)`, **fixed integer witnesses solve the
  class system modulo `2^k` and modulo `17^k` for every `k`** — carried by two
  square-lifting lemmas (a unit `≡ 1 mod 8` is a square at every two-adic depth; a
  unit quadratic residue lifts at every seventeen-adic depth, Hensel's step through
  `ZMod 17`).  The instrument that killed twenty-eight classes **provably cannot kill
  these twelve, at any depth of either frame**;
- **`TheInvisibleCosetsAreGloballyRefused`** (named-open) — classically the three
  cosets contain no rational face: seventeen is not a congruent number, and the
  refusal is a Lind–Reichardt-type quartic-residue second descent, possible exactly
  because two is a square but not a fourth power mod seventeen.  Falsifier: a point
  with such a face;
- **`theObstructionIsExhibited`** — the conjunction: image in the Selmer sixteen,
  realized four, and the depth-universal invisibility.

## 2. The reading, in both vocabularies

Classically (through exterior Mordell–Weil and the cited second descent):
`dim Sel₂(E₁₇) = 4`, image dimension `2`, so **`Ш(E₁₇)[2] ≅ (ℤ/2)²`** — the
Birch–Swinnerton-Dyer obstruction group, with every local ingredient kernel-checked
in this tree and only the global second descent imported.

In the corpus's own vocabulary, unconditionally: **a population locally admissible at
every named frame and every depth, that the realized current never reaches** — the
phase-object of descent.  The twenty-eight refused classes were visible to magnitude
checks (signs, congruences); the twelve invisible ones are not, and no congruence ever
will see them — the obstruction lives precisely in the gap between every local frame
and the global body, which is what Ш *is*.

## 3. What is owed, with falsifiers

**None scheduled; the roadmap alone schedules.**

| owed | falsifier |
|---|---|
| the second descent: proving `TheInvisibleCosetsAreGloballyRefused` (the quartic-residue arguments — mathlib carries quadratic reciprocity and the Jacobi symbol, the needed instruments) | a rational point with an invisible face |
| **the five-mod-eight stratum, corrected**: the earlier record posed it as a corank-zero sibling — wrong: primes `p ≡ 5 (mod 8)` are classically *congruent* (rank one), so the family theorem there is a **Selmer bound of rank at most one** (image within torsion and one coset), not a completed descent; the realized side needs generators the family does not supply in closed form | a stratum prime with two independent directions |
| the `p ≡ 1 (mod 8)` governance reading: the singular-matrix corank against the completed local analysis, seventeen as first fixture | corank/image disagreement |
| the parity ledger extension to seventeen (root number `+1`, descent rank zero granted the second descent) | — |

## 4. Boundaries

The global refusal of the three invisible cosets is named-open, not claimed; "Selmer"
and "Ш" are classical readings carried as `interpretation`; the depth-universal
invisibility statements quantify over congruence frames, which is weaker than
constructing `ℚ₂`- and `ℚ₁₇`-points though it is exactly the invisibility the
completed descents' instruments can measure; nothing about the Birch–Swinnerton-Dyer
conjecture.
