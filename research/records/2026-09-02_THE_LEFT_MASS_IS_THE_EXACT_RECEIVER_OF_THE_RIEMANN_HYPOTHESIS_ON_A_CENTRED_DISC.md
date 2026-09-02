# The left mass is the exact receiver of the Riemann Hypothesis on a centred disc

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`); `measured` (`lake` job count: 3778 jobs for the owner cone; root module green)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, articulating the exact receiver of RH on a centred disc on the RH line. Assistant derivation for the proofs.
**Band:** DIVISOR ≠ 0 ⇔ ZERO IN THE DISC, ANY RADIUS / DIVISOR ≥ 0 FOR ENTIRE ξ / LEFT MASS = 0 ⇔ RH ON THE DISC / DISC MASS = ON-LINE MASS ⇔ RH ON THE DISC / ON-LINE MASS ≤ DISC MASS / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[proved-derived] `centredDivisor_ne_zero_iff`: on `closedBall ½ R` for any real `R`, the divisor of
`ξ` is nonzero exactly at the zeros of `ξ` in the disc (the earlier owner had this for `|R|`).
`centredDivisor_nonneg` and `leftMass_nonneg` follow from the divisor of an entire function
being nonnegative.

[definition] `RiemannHypothesisOn R`: every zero of `ξ` in `closedBall ½ R` has real part `½`.

[proved-derived] `leftMass_eq_zero_iff`: `leftMass R = 0 ↔ RiemannHypothesisOn R`. A zero
strictly left of the line carries positive mass; a zero strictly right of the line reflects to a
zero strictly left with the same mass; conversely a positive left mass exhibits an off-line zero.

[proved-derived] `divisorMass_eq_onLineMass_iff`: `divisorMass R = onLineMass R ↔
RiemannHypothesisOn R`, by the reflection splitting `disc = 2 · left + on-line`; and
`onLineMass_le_divisorMass`.

## Holonic reading

[definition] The centred disc is the receiver of the zero comb at radius `R`; its zeros are read
with multiplicity by the divisor. The left mass is the population of receivers strictly left of
the reflection's fixed line, and by reflection it is half the off-line population. RH on the disc
is exactly the statement that the off-line population is empty, so the left mass is the exact
receiver of RH: not a bound, not a witness, but the quantity whose vanishing is RH itself.

[established-bounded] The argument-principle owners bound `divisorMass` by the Jensen receiver
unconditionally; RH would follow from showing the on-line mass saturates that bound. That is the
open seam of this line, and this owner names the two masses whose equality it asserts.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/LeftMassReceiver.lean` compiles under
  `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.ZeroCountParity`.

Next in the loop: Hodge line; on RH, the on-line mass against the argument-principle count.
