# The off-line population under the Jensen bound

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`); `measured` (`lake` job count: 3779 jobs for the owner cone; root module green)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, carrying the unconditional Jensen bound to the off-line population on the RH line. Assistant derivation for the proofs.
**Band:** log 2 · DISC MASS ≤ JENSEN RECEIVER / log 2 · ON-LINE MASS ≤ JENSEN / 2 log 2 · LEFT MASS ≤ JENSEN / OFF-LINE COUNT ≤ 2 · LEFT MASS / log 2 · OFF-LINE COUNT ≤ JENSEN / CONDITIONAL ON ξ(½) ≠ 0 / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[definition] `jensenReceiver C R` is the right-hand side of the unconditional inner-disc bound at
centre `½`: `C (‖½‖ + 2R + 2) log(‖½‖ + 2R + 2) − log ‖ξ(½)‖`.

[proved-derived] For `1 ≤ R` and `ξ(½) ≠ 0` there is `C > 0` with
`log 2 · divisorMass R ≤ jensenReceiver C R` (`logTwo_mul_divisorMass_le`), hence
`log 2 · onLineMass R ≤ jensenReceiver C R` and `2 log 2 · leftMass R ≤ jensenReceiver C R`
by the reflection splitting and the nonnegativity of the on-line mass.

[proved-derived] `sum_offLine_eq_two_mul_leftMass`: the divisor summed over the off-line support
is twice the left mass. `card_offLineZeros_le`: the number of off-line, off-axis zeros is at most
twice the left mass, since each carries mass at least one. Hence
`logTwo_mul_card_offLineZeros_le`: `log 2 · #offLineZeros R ≤ jensenReceiver C R`.

## Holonic reading

[definition] The Jensen receiver is the growth budget of `ξ` on the doubled disc. The disc mass
pays at least `log 2` per unit of multiplicity into it, so the whole zero population is bounded
by the budget. By reflection the off-line population pays twice, once on each side of the line,
so the off-line population is bounded by half the budget. This is the quantitative face of the
left-mass receiver: RH on the disc says the left mass is zero, and unconditionally it is at most
`jensenReceiver / (2 log 2)`.

[established-bounded] The hypothesis `ξ(½) ≠ 0` is inherited from the growth owners; it is true
(`ξ(½) ≈ 0.497`) but not yet certified in this line.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/OffLineJensen.lean` compiles under
  `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.LeftMassReceiver`.

Next in the loop: Hodge bigraded differential; on RH, certifying `ξ(½) ≠ 0`.
