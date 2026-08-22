# The two-descent at thirty-four is complete, and the image is exactly the realized sixteen

**Date:** 2026-08-22
**Kind:** the rank deed — Brandon: *"Rank exactly two and beyond, please stop being
conservative and push."*  Solo orchestrator work, one Lean file; every arithmetic input
verified exactly before encoding — the sixteen-element realized group and its four-coset
quotient computed over 𝔽₂, the local obstructions located by exhaustive 2-adic and
17-adic search with a positive control, the canonical refusal confirmed to die at the
frame of eight, and the realization/translation tables generated from the verified
computation.  **It schedules nothing.**
[`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction
authorities.
**Position under the active plan.** Exterior mathematical material for the mathematics
codec arm of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
The Lean line does not couple to the engine, per Brandon's standing ruling.
**Truth grades:** `proved-derived` with `formal-checked` evidence for the five headline
Lean theorems (`#print axioms` → `[propext, Classical.choice, Quot.sound]`, zero
`sorryAx`); `interpretation` for the classical translation through Mordell–Weil, marked
in the file.

---

## 1. What was proved

Owner: `ElementaryHolonics/Millennium/FaceImage.lean` (1,001 lines).  Measured after the
merge: the library builds at **3,395 jobs**.

**The image of the descent face on `E₃₄(ℚ)` is exactly the sixteen realized classes.**
Both bounds, kernel-checked:

- **`theFaceImageIsTheRealizedSixteen`** — every point's face pair lies in the sixteen
  classes spanned by the faces of the half-turns and the two directions;
- **`theRealizedSixteenAreInTheImage`** — every one of the sixteen is the face of an
  explicit point (sums over subsets of `{T₀, T₃₄, P₁, P₂}`, their classes read through
  the family homomorphism, no sum coordinate ever computed).

With the escape certificates of the previous deed, this is **rank exactly two in
descent form**: the face sees exactly two independent directions beyond the torsion,
and it can see no third.  The classical translation — image sixteen, torsion image
four, so Mordell–Weil rank exactly two — is carried as `interpretation` because
Mordell–Weil finiteness is exterior; every arithmetic ingredient of the descent itself
is a theorem in this tree.

## 2. The three walls of the upper bound, and how each fell

The sixty-four candidate classes (`±2^a·17^b` per slot) reduce to sixteen in three
strokes, each a named theorem:

- **The support law** (`theSlotClassesAreSupportedOnTheDiscriminant`): for a prime
  `ℓ ∉ {2, 17}`, the `ℓ`-adic valuation of each slot is even — `ℓ` divides at most one
  factor of `y² = x(x−34)(x+34)` — so nothing survives the square quotient beyond the
  discriminant.  Proved with the `padicValRat` depth calculus (the compact-frame
  machinery of `FrameDescent.lean` re-aimed at a quantified prime) and a
  squarefree-decomposition bridge through `Nat.sq_mul_squarefree`.
- **The sign law** (`theSignsAgreeAcrossTheFace`): the real curve with `y ≠ 0` lives on
  `x > 34` or `−34 < x < 0`, so the two slot classes carry one sign — thirty-two
  classes die in the real frame.
- **The canonical refusal** (`theCanonicalCosetIsRefused`): no point has face `(1, 2)`.
  The class equations clear to `C² − 34D² = 2E²` and `C² + 34D² = 2F²`, which have **no
  primitive solution mod eight** — a kernel `decide` over `ZMod 8`, the same weight as
  the congruum refusal — and the halving descent kills the imprimitive ones.  The
  remaining fifteen refused classes each **translate onto the canonical one**: add the
  realized point carrying the complementary class, apply the homomorphism, and the sum
  has face `(1, 2)`.  The group structure of the image did the work of fifteen
  descents.

The measured coset structure that made this finite: the realized group has exactly four
cosets in the sixty-four-class ambient group, with representatives `(1,−1)`, `(1,2)`,
`(1,−2)` — the first and third die by sign alone, and only `(1,2)` needed the 2-adic
argument.  Equivalently: **the 2-Selmer group of the thirty-four twist is the realized
group** — `Ш(E₃₄)[2]` sees nothing beyond the points — read as `interpretation` since
Selmer is not a type in this tree.

## 3. What this closes and what it opens

Closed, as theorems: the face homomorphism on every twist; the doubles in the kernel;
the two directions and their sum escaping torsion-translated doubles; the image exactly
sixteen.  The descent story of the thirty-four twist is complete except for the torsion
classification (that the four listed half-turns are all the torsion), which bounds
nothing here but upgrades the escape statements from list-quantified to
property-quantified.

| owed | falsifier |
|---|---|
| the torsion classification at thirty-four (depth-descent re-aim; good reduction at three with `34² ≡ 1 mod 3` puts the five-curve machinery directly on it) | a fifth torsion point |
| the same complete descent for the rank-one five-curve (its image should be eight: four torsion classes and one direction) — the machinery of this file instanced there | a ninth class in its image |
| the mod-2 Birch–Swinnerton-Dyer programme this deed instantiates: Selmer rank as 𝔽₂ matrix corank across the twist family (the Monsky/Rédei governance layer), realized image = Selmer per instance, parity against the theta census | a twist where the matrix corank disagrees with the completed descent |

## 4. Boundaries

The word "rank" enters only through the classical Mordell–Weil theorem, which is
imported interpretation; the theorems are the exact image computation.  The torsion
classification at thirty-four is owed.  Nothing about the Birch–Swinnerton-Dyer
conjecture is claimed; the mod-2 programme row above is a posed receiver question, not
a result.
