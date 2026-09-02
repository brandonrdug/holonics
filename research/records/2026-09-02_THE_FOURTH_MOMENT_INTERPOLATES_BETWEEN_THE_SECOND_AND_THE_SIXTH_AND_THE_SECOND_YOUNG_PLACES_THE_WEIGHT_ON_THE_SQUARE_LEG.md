# The fourth moment interpolates between the second and the sixth, and the second Young places the weight on the square leg

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, toward the goal `weightedTail_energy_inequality`. Assistant derivation for the proofs.
**Band:** MOMENT INTERPOLATION ON FAMILIES AND COMPLETE POPULATIONS / YOUNG L2 TIMES L1 INTO L2 / CUBE WEIGHT SHARED WITH DOUBLING TWO SQUARED / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `NavierStokesMomentInterpolation.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`sum_momentPop_four_sq_le`, `moment_four_sq_le`: `W₄² ≤ W₂ · W₆` on finite families and on the
complete populations, Cauchy--Schwarz between `|k| √E_k` and `|k|³ √E_k`.
`summable_sq_mul_shift`, `summable_shift`, `summable_shift_neg`, `conv_sq_le'`: Cauchy--Schwarz
on the complete convolution weighted by the mass leg. `young_l2_l1`: for nonnegative `A` square
summable and `b` summable, every finite family of receivers satisfies
`Σ_{k∈F} (Σ'_p A_p b_{k−p})² ≤ (Σ'_p A_p²) · (Σ'_q b_q)²`.
`frequencySup_cube_le`: `|k|_∞³ ≤ 2² (|p|_∞³ + |k−p|_∞³)`.

## What it says

[interpretation] The second Young lets the weight sit on the square-summable leg while the other
leg carries only its mass, which is what removes the higher moment from the drive: the weighted
velocity leg is paid by `W₂` or `W₄` through Lagrange, and the transported leg by the mass of
`√E`, itself paid by `√(52 · W₄)` through the lattice weight. The interpolation pays a term
quadratic in `W₄` by `W₂` against the dissipating `W₆`. The cube weight is what the curl symbol
needs: the source of the modal equation carries one more power of the frequency than the
advection coefficient.

## What this does not establish

[open] The weight-six Young on the advection and the family Riccati with the Young drive are not
yet written; nothing bounds a moment in time.

## Owners

[definition] `ElementaryHolonics/Millennium/NavierStokesMomentInterpolation.lean` (new;
registered).
