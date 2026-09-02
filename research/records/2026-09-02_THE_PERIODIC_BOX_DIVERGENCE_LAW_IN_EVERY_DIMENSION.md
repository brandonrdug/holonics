# The periodic box divergence law in every dimension

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audit below); `measured` (`lake` job count below: 3719 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, lifting the fluid line's three-dimensional cube law to the connection base so the gauge line can integrate. Assistant derivation on Mathlib's box divergence theorem.
**Band:** UNIT BOX OF Base (n+1) / ONE-PERIODIC FUNCTIONS ON THE BASE / FRONT FACE = BACK FACE + UNIT / ∫_box Σ_i ∂_i f_i = 0 FOR C¹ PERIODIC COMPONENTS / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `HolonicPeriodicBoxDivergence.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`unitBox n`; `IsOnePeriodicBase`; `insertNth_one_eq_insertNth_zero_add_single` (the front face of
the box is the back face translated by the unit direction); `integral_divergence_unitBox_eq_zero`:
for `C¹` one-periodic components `f i : Base (n+1) → ℝ`, `∫_box Σ_i ∂_i f_i = 0`.

## Reading

[definition] The current law on the box: what leaves through the front face of each direction
enters through the back face, so the total divergence integrates to zero. It is the cell current
law of the fluid line in every dimension, and it is the tool that integrates the local Yang--Mills
energy identity into the global one on the torus.

[established-bounded] Next: periodicity propagation through `∂`, brackets, curvature, and covariant
derivatives, then the integrated Yang--Mills energy identity
`∫_box Σ_{ij} B((D_A G)_ij, F_ij) = −2 Σ_j ∫_box B(G_j, G_j)`.

## Evidence

- `lake build ElementaryHolonics.Millennium.HolonicPeriodicBoxDivergence` green within the 180 s bound.
- Axiom audit: `integral_divergence_unitBox_eq_zero` depends on `[propext, Classical.choice, Quot.sound]`.
