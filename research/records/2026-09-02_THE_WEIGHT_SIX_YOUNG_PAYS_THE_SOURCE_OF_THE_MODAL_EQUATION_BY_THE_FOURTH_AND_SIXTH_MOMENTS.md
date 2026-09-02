# The weight-six Young pays the source of the modal equation by the fourth and sixth moments

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, toward the goal `weightedTail_energy_inequality`. Assistant derivation for the proofs.
**Band:** CUBE-WEIGHTED POPULATIONS PAID BY THE FOURTH MOMENT / ROOT-ENERGY MASS PAID BY THE FOURTH MOMENT THROUGH THE LATTICE WEIGHT / WEIGHT-SIX YOUNG ON THE ADVECTION / NO MOMENT ABOVE SIX / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `NavierStokesSixthYoung.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`l1CubePop p = |p|_∞³ ℓ¹(û(p))`, `rootCube q = |q|_∞³ √E_q`. `l1CubePop_sq_le`,
`tsum_l1CubePop_sq_le`: `Σ' |p|_∞⁶ ℓ¹(û(p))² ≤ (3/(2π)²) W₄`, Lagrange. `rootEnergy_zero`.
`sum_rootEnergy_le`, `summable_rootEnergy`, `tsum_rootEnergy_le`: `Σ' √E_q ≤ √52 √W₄`, the lattice
weight. `sup_cube_mul_norm_le`: the weight-three convolution bound at one receiver.
`sum_pow_six_norm_adv_sq_le`: for every finite family of receivers, with the eleventh moment
summable,

```text
Σ_{k∈F} |k|_∞⁶ ‖adv_k‖² ≤ 2⁵ · (3/(2π)²) · 52 · W₄² + 2⁵ · (Σ'_p ℓ¹(û(p)))² · W₆.
```

## What it says

[interpretation] The source of the modal equation is the curl of the advection, one power of the
frequency more, so the source's fourth moment is the advection's sixth. It is paid by `W₄²`, which
the interpolation reads as `W₂ W₆`, and by the velocity mass squared against `W₆`. The velocity
mass is `ℓ¹(û(0)) + √(52·3/(2π)²) √W₂`. So the drive of the fourth-moment Riccati is
`W₆ · (W₂ + ℓ¹(û(0))² + W₂)`-shaped and the dissipation is `ν(2π)² W₆`: the family Riccati with the
Young drive closes into `M₄' ≤ −ν' M₆ + (K/ν)(ℓ¹(û(0))² + W₂) M₄` after Cauchy--Schwarz on the
cross term and one arithmetic-geometric step, which is the next owner.

## What this does not establish

[open] The family Riccati with the Young drive is not yet written; nothing bounds a moment in
time.

## Owners

[definition] `ElementaryHolonics/Millennium/NavierStokesSixthYoung.lean` (new; registered).
