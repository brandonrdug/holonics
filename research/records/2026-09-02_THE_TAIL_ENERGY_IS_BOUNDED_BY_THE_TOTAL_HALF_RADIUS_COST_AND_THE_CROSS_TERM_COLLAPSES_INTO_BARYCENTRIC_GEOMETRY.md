# The tail energy is bounded by the total half-radius cost, and the cross term collapses into barycentric geometry

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job counts below)
**Provenance:** Brandon, 2026-09-02: *"Like collapsing into barycentric and affine geometry? Okay, so let's proceed, derive and formalize whatever you need."* Assistant derivation for the proofs.
**Band:** HALF-RADIUS REACH PROVED / EIGENVALUE LOWER BOUND BY THE SUP-NORM / SCALAR WEIGHTED MAXIMUM PRINCIPLE / FAMILY RICCATI SUMMED / TAIL ENERGY BOUNDED BY TOTAL COST / BARYCENTRIC COLLAPSE OF THE CROSS TERM / OBLIGATION TRANSFORMED TO A TOTAL SQUARED COST / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `NavierStokesHalfRadiusReach.lean` (registered; `4066` jobs;
axioms `[propext, Classical.choice, Quot.sound]`). `frequencySup k = max_c |k_c|`;
`mem_frequencyCube_iff_frequencySup_le`; `halfRadius k = ⌊(|k|_∞ − 1)/2⌋` with
`not_mem_frequencyCube_two_mul_halfRadius` for every nonzero mode;
`torusStokesEigenvalue_ge : (2π)² |k|_∞² ≤ λ_k`; `halfRadiusCost t k = feedBound t (halfRadius k)`;
`modalEnergy_riccati_halfRadius`: the modal Riccati inequality with the cost taken at the mode's
own half radius, so the drive of a mode decays with the mode by per-event irrelevance.

[proved-derived; formal-checked] `NavierStokesTailGronwall.lean` (registered; `4067` jobs; same
axioms). `le_max_of_hasDerivAt_le`: if `f' ≤ −a f + G` on `[s, τ]` with `a > 0` then
`f τ ≤ max (f s) (G/a)`, the scalar weighted maximum principle.
`familyEnergy_riccati`: for a finite family of modes with sup-norm at least `m ≥ 1`, the family
energy is differentiable with derivative at most `−ν (2π)² m² · familyEnergy + (3⁵/ν) · familyCost`.
`familyEnergy_le_of_familyCost_le`: the family Gronwall bound.
`tailEnergy_le_of_tailCost_le`: if the total squared half-radius cost of the tail beyond sup-norm
`m` is bounded by `M` on `[s, T)`, and the tail energy is summable at `s`, then on `[s, T)`

```text
tailEnergy_m(τ) ≤ max ( tailEnergy_m(s),  3⁵ M / (ν² (2π)² m²) ).
```

The passage from finite families to the tail is `Real.tsum_le_of_sum_le` on nonnegative modal
energies.

[proved-derived; formal-checked] `NavierStokesBandBarycenter.lean` (registered; job count in the
commit receipt; same axioms). On any finite family of complex numbers with barycenter `z̄`:
`sum_norm_sub_mean_sq` (the variance identity, spread = diagonal − n‖z̄‖²) and
`cross_eq_pairs_mul_mean_sq_sub_spread` (cross term = n(n−1)‖z̄‖² − spread). On the band feed:
`bandFeed_eq_count_mul_barycenter` (the feed is `(2N+1)³ · z̄`), `bandCrossTerm_eq`, and
`bandCrossTerm_nonpos_iff`: the half power holds exactly when
`(2N+1)³ · ((2N+1)³ − 1) · ‖z̄‖² ≤ spread`, the teeth surround the pin more than they cluster
away from it.

## The obligation, transformed

[open] The periodic finish line now reads: the total squared half-radius cost of the tail,
`Σ_{|k|_∞ ≥ m} feedBound(⌊(|k|_∞ − 1)/2⌋)²`, stays bounded up to `T`. The shell at sup-norm `m`
carries `(2m+1)³ − (2m−1)³` modes and each pays `((2r+1)³ · 3√(2E(0)) · tailJ(r) + velocityTail(r)
· totalJ)²` with `r = ⌊(m − 1)/2⌋`. At every interior time the sum converges by per-event
irrelevance; the uniformity in time is the obligation. The passage from the bounded tail energy
back to the interval-integrable Jacobian tail mass of `TailRelevanceControl` is not made; it needs
one half power of weight in `k`, which is the same half power the barycentric collapse names.

## What this does not establish

[open] Nothing discharges the total-cost bound; nothing decides the barycenter's distance from the
pin; `TailRelevanceControl` remains uninhabited.

## Owners

[definition] `ElementaryHolonics/Millennium/NavierStokesHalfRadiusReach.lean`,
`ElementaryHolonics/Millennium/NavierStokesTailGronwall.lean`,
`ElementaryHolonics/Millennium/NavierStokesBandBarycenter.lean` (all new; registered).
