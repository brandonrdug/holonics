# The centre is isolated: a small square returns the analytic rank

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: owner cone across the RH and BSD trees; root module green, 9740 jobs)
**Provenance:** Assistant, under Brandon's direct-route directive of 2026-09-02, discharging the isolation hypothesis of the winding theorem by the identity theorem: a nonzero entire function has isolated zeros, so a small square about the centre carries no other zero. Assistant derivation for the proofs.
**Band:** NONZERO ENTIRE ⇒ ISOLATED ZEROS (IDENTITY THEOREM + PUNCTURED NEIGHBOURHOOD) / SQUARE OF HALF-SIDE ε/2 ABOUT 1 INSIDE THE CLOSED BALL OF RADIUS ε / ∮ L′/L = 2πi·analyticRank AROUND THE SQUARE, NO ISOLATION HYPOTHESIS / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[proved-derived] `exists_isolated`: a nonzero entire function has, about any point `a`, a
radius `ε > 0` on whose closed ball it vanishes at most at `a`. Mathlib's dichotomy for an
analytic germ (eventually zero, or eventually nonzero on the punctured neighbourhood) with the
identity theorem on the connected plane excludes the first branch.

[proved-derived] `re_corner`, `im_corner`, `re_corner'`, `im_corner'`: the coordinates of the
corners `1 ∓ δ(1 + i)`. `exists_square_winding` (**a small square returns the analytic rank**):
for an `LDatum W` with `analyticRank W = m`, there is `δ > 0` with
`∮_{square of half-side δ about 1} L′/L = 2πi · m`. The square of half-side `ε/2` lies in the
closed ball of radius `ε` (by `‖ζ − 1‖ ≤ |Re ζ − 1| + |Im ζ|`), so the previous owner's
isolation hypothesis holds there.

## Constants

[definition] `ε/2 = ε · (1/2)`: the half-side that keeps the square, whose corners are at
`ℓ¹`-distance `ε` from the centre, inside the ball of radius `ε`. `2πi` inherited.

## Holonic reading

[definition] The analytic rank is now returned by a contour with no hypothesis beyond the pose:
`L` nonzero (the rank finite) gives a square about the centre whose winding of `L′/L` is the
rank. The zero side of BSD is one comb multiplicity read by the same receiver as the zero comb
of `ξ`.

[established-bounded] The realizer side (the Mordell–Weil rank) remains the conjecture's other
half; the corpus's parity and finite-rank owners tie the sign to the parity of this count.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/Millennium/BirchSwinnertonDyerWindingIsolated.lean`
  compiles under `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains
  green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.Millennium.BirchSwinnertonDyerWinding`.
- Axiom audit for `exists_square_winding`, `exists_isolated`:
  `[propext, Classical.choice, Quot.sound]`.
