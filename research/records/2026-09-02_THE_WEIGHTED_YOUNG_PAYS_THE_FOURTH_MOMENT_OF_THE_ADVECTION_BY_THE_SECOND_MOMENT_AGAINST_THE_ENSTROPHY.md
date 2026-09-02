# The weighted Young pays the fourth moment of the advection by the second moment against the enstrophy

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, toward the goal `weightedTail_energy_inequality`. Assistant derivation for the proofs.
**Band:** WHOLE ADVECTION UNDER THE COMPLETE CONVOLUTION BOUND / SUP-NORM SQUARE SHARED BETWEEN LEGS / WEIGHTED YOUNG TWICE / PRODUCT ESTIMATE IN THE TREE'S FACES / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `NavierStokesWeightedYoung.lean` (registered; `lake build` `4078`
jobs; axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`). With `l1Pop p = ℓ¹(û(p))`,
`l1SecondPop p = |p|_∞² ℓ¹(û(p))`, `rootEnergy q = √E_q`, `rootSecond q = |q|_∞² √E_q`:

`modalEnergy_le_momentPop_one` (the zero mode has zero energy), `summable_rootEnergy_sq`,
`summable_rootSecond_sq`. `norm_openActualAdvectionMode_le_conv`: the advection coefficient at
`k` is at most `Σ'_p ℓ¹(û(p)) √E_{k−p}`. `frequencySup_sq_le`:
`|k|_∞² ≤ 2 (|p|_∞² + |k−p|_∞²)`. `sup_sq_mul_norm_le`: the weighted convolution bound at one
receiver. `sum_pow_four_norm_adv_sq_le`: for every finite family of receivers, with the eleventh
moment summable and the second-moment `ℓ¹` population summable,

```text
Σ_{k∈F} |k|_∞⁴ ‖adv_k‖² ≤ 2³ (Σ'_p |p|_∞² ℓ¹(û(p)))² · W₀ + 2³ (Σ'_p ℓ¹(û(p)))² · W₄.
```

## What it says

[interpretation] This is the product estimate in the tree's own faces: the receiver's fourth
moment is paid by the advecting population's second moment against the enstrophy `W₀`, plus the
advecting mass against the fourth moment `W₄`. The `2³` is one doubling for the shared weight,
squared, times the two-term split. The two advecting populations are paid by `W₆` and by
`ℓ¹(û(0)) + √(52·3/(2π)²) √W₂` through the lattice weight, which is the next owner, and then the
fourth-moment Riccati closes into `M₄' ≤ −ν(2π)² M₆ + (K/ν)(W₆ W₀ + (ℓ¹(û(0))² + W₂) W₄)`.

## What this does not establish

[open] The summability of the second-moment `ℓ¹` population is a hypothesis here; the two
advecting populations are not yet read in moments; the Riccati with the Young drive is not yet
written.

## Owners

[definition] `ElementaryHolonics/Millennium/NavierStokesWeightedYoung.lean` (new; registered).
