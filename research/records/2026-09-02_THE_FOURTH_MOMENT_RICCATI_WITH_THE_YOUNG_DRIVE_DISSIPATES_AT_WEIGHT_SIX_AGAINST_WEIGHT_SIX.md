# The fourth-moment Riccati with the Young drive dissipates at weight six against weight six

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, toward the goal `weightedTail_energy_inequality`. Assistant derivation for the proofs.
**Band:** VELOCITY MASS IN MOMENTS / RAW MODAL RICCATI / SOURCE PAID BY THE SIXTH MOMENT OF THE ADVECTION / FAMILY RICCATI WITH THE YOUNG DRIVE / DRIVE AT WEIGHT SIX / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `NavierStokesYoungRiccati.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`tsum_l1Pop_le`: `Σ' ℓ¹(û(p)) ≤ ℓ¹(û(0)) + √(52·3/(2π)²) √W₂`. `frequencySquared_le_three_sup_sq`.
`modalEnergy_riccati_raw`: for every nonzero mode, `E_k' ≤ −2ν λ_k E_k + 2 ℓ¹(ω̂_k) ℓ¹(N_k)`.
`sup_pow_four_l1_nonlinear_sq_le`: `|k|⁴ ℓ¹(N_k)² ≤ 3³ (2π)² |k|⁶ Σ_o ‖adv_k(o)‖²`.
`sourceBound = 3³ (2π)² · 3 · [2⁵ (3/(2π)²) 52 W₄² + 2⁵ (Σ' ℓ¹(û))² W₆]`;
`sum_sup_pow_four_l1_nonlinear_sq_le`: the weighted source squared over a finite family is at most
`sourceBound`. `momentEnergy_riccati_young`: for every finite family of nonzero modes, with the
eleventh moment summable,

```text
M₄' ≤ −2 ν (2π)² M₆(F) + 2 √(3 M₄(F)) · √sourceBound.
```

## What it says

[interpretation] The drive is now at weight six: `sourceBound ≤ K(t) W₆` with
`K(t) = 3⁴ 2⁵ [(2π)² (Σ' ℓ¹(û))² + 3·52·W₂]` after the interpolation `W₄² ≤ W₂ W₆`, and
`Σ' ℓ¹(û)` is paid by the zero mode and `√W₂`. One arithmetic-geometric step gives
`M₄' ≤ −2ν(2π)² M₆(F) + ν(2π)² W₆ + (3K/(ν(2π)²)) M₄(F)`. The constants are product
expansions: `3³` the three coordinate comparisons in the source, `3` the outputs, `2⁵` the
doublings of the cube weight, `52 = 2·26` the lattice weight, `(2π)²` the circle constraint.
The remaining passage is from finite families to the tail, where `M₆(F) → W₆` and the two
weight-six terms combine into `−ν(2π)² W₆`; that is the integrated form with monotone
convergence, the next owner. The closure condition then reads: `W₂` bounded on a terminal tail,
with `ℓ¹(û(0)) ≤ 3√(2E(0))`, keeps `W₄` bounded, which is `WeightedTailEnergyControl`, hence
`StatementB`.

## What this does not establish

[open] The arithmetic-geometric corollary and the family-to-tail passage are not yet written;
nothing bounds `W₂` in time.

## Owners

[definition] `ElementaryHolonics/Millennium/NavierStokesYoungRiccati.lean` (new; registered).
