# Zero-count parity: the multiplicity-weighted count in a centred disc has the parity of the on-line count

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below: 3777 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, articulating the reflection splitting of the multiplicity-weighted zero count on the RH line. Assistant derivation for the proofs.
**Band:** REFLECTION s ↦ 1 − s PRESERVES THE CENTRED DIVISOR / LEFT MASS + RIGHT MASS + ON-LINE MASS / RIGHT MASS = LEFT MASS BY THE INJECTIVE IMAGE / DISC MASS = 2 · LEFT + ON-LINE / DISC PARITY = ON-LINE PARITY / CAST BRIDGE TO innerRiemannXiZeroCount / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[proved-derived] On the centred disc `closedBall ½ R`, the divisor of `ξ` has finite support
`centredSupport R`, closed under the reflection `u ↦ 1 − u` because the reflection preserves the
divisor (`divisor_riemannXi_one_sub`). The multiplicity-weighted count `divisorMass R` is the sum
of the divisor over that support; `onLineMass R` and `leftMass R` restrict the sum to `re = ½` and
`re < ½`.

[proved-derived] `divisorMass_eq_two_mul_leftMass_add_onLineMass`: the support splits into the
on-line part and the off-line part; the off-line part splits into the left and right halves; the
right half is the injective image of the left half under the reflection, and the divisor agrees on
reflected points, so the two half-masses coincide. Hence
`divisorMass R = 2 · leftMass R + onLineMass R`, and `divisorMass_emod_two`:
`divisorMass R % 2 = onLineMass R % 2`.

[proved-derived] `innerRiemannXiZeroCount_eq_divisorMass_cast`: for `0 ≤ R` the real-valued inner
count of `RiemannXiZeroCounting` at centre `½` is the cast of `divisorMass R`, so the parity law
reads directly on the unconditional Jensen-bounded count.

## Holonic reading

[definition] The centred disc receives the zero comb with multiplicity. The reflection is the
functional-equation involution of the receiver; its fixed set is the critical line. The mass of a
free reflection orbit is `2 · m`, the orbit size times the shared multiplicity, so every off-line
receiver contributes an even mass and the parity of the total is carried entirely by the fixed
set. The disc count therefore reads the on-line count modulo two: an odd disc count certifies at
least one on-line zero of odd multiplicity, unconditionally.

[established-bounded] The multiplicity-free four-orbit count of the previous record and this
multiplicity-weighted parity are the two faces of the same exterior symmetry: the first uses both
involutions without multiplicity; the second uses one involution with multiplicity. The
multiplicity-weighted mod-four law needs the conjugation symmetry of the divisor, which remains
open pending analyticity of `conj ∘ ξ ∘ conj` in Mathlib.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/ZeroCountParity.lean` compiles under
  `lake env lean` and `lake build ElementaryHolonics.RH.ZeroCountParity`; axioms
  `[propext, Classical.choice, Quot.sound]`.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.ZeroOrbitCount`.

Next in the loop: NS frontier chain, BSD sign law; on RH, the argument-principle side of
`divisorMass` as a contour integral over the centred circle.
