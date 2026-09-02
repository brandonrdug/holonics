# Joint continuity and Lipschitz bound of the flow in t

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `soma/formal/elementary-holonics/ElementaryHolonics/RH/HeatFlowContinuity.lean`
**Provenance:** Assistant, under Brandon's direct instruction of 2026-09-02 to take the pair population under the de Bruijn–Newman flow at the entire face: the flow is bounded on boxes |t| ≤ T, ‖z‖ ≤ R by the summed majorant, Lipschitz in t there through the mean value inequality and ∂_t H = −H″, and jointly continuous in (t, z), as are its z-derivatives. Assistant derivation for the proofs.
**Band:** ‖heatE t f z‖ ≤ K(A,B,ρ,T,R) ON |t| ≤ T, ‖z‖ ≤ R / ‖heatE s f z − heatE t f z‖ ≤ L·|s − t| / (t,z) ↦ H_t(z) CONTINUOUS / (t,z) ↦ H_t′(z) CONTINUOUS / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Owner

[definition] `Soma.Holonics.RH.HeatFlowContinuity` in
`soma/formal/elementary-holonics/ElementaryHolonics/RH/HeatFlowContinuity.lean`, importing
`RH.ConjugationEntire`. Receiver: the map `(t, z) ↦ heatE t f z` on boxes.

## Theorems

[definition] `CT B ρ T = 4e·T·e^{B2^ρ}`, the majorant constant at `|t| ≤ T`;
`K A B ρ T R = A e^{B 2^ρ R^ρ} Σ_k majorant (CT B ρ T) δ k`; `L A B ρ T R` is `K` for the growth
constants of `f″`.

[proved-derived] `norm_heatE_le`: `‖heatE t f z‖ ≤ K A B ρ T R` for `|t| ≤ T`, `‖z‖ ≤ R`.

[proved-derived] `hasGrowth_deriv_deriv`, `norm_heatE_sub_le`:
`‖heatE s f z − heatE t f z‖ ≤ L A B ρ T R · |s − t|` on the box, by the mean value inequality
along `t` with derivative `−heatE u f″ z`.

[proved-derived] `continuous_heatE`, `continuous_deriv_heatE`: `(t, z) ↦ H_t(z)` and
`(t, z) ↦ H_t′(z)` are continuous on `ℝ × ℂ`.

## Position on the route

[established-bounded] With joint continuity of `H_t` and `H_t′`, the logarithmic derivative
`H_t′/H_t` is continuous in `(t, ζ)` wherever `H_t(ζ) ≠ 0`, and the argument-principle integral of
the corpus over a rectangle avoiding the zeros of `H_{t₀}` on its boundary is continuous in `t`
near `t₀`. That integral is `2πi` times the zero count inside, so the count is locally constant
in `t`: the next owner.

[established-bounded] Nothing here touches the face `t = 0`. Axioms:
`[propext, Classical.choice, Quot.sound]`; no `sorry`.

[established-bounded] Next: the rectangle zero count of `H_t` is locally constant in `t` when
`H_{t₀}` has no zero on the boundary.
