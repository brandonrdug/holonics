# Zero velocity of H_t along a curve of simple zeros

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `soma/formal/elementary-holonics/ElementaryHolonics/RH/ZeroDynamicsEntire.lean`
**Provenance:** Assistant, under Brandon's direct instruction of 2026-09-02 to take the pair population under the de Bruijn–Newman flow at the entire face: the chain rule for s ↦ H_s(z(s)) along a C¹ curve by termwise differentiation with a majorant uniform on a bounded interval and a bounded curve, and the velocity of a simple zero z′ = H″/H′ from the vanishing of the composite. Assistant derivation for the proofs.
**Band:** d/ds[(−s)^k/k!] = k(−s)^{k−1}(−1)/k! / curveDeriv = (∂_t TERM) + (TERM OF f′)·z′ / d/ds H_s(z(s)) = −H_s″(z(s)) + H_s′(z(s)) z′(s) / H_s(z(s)) = 0 ∀s, H_{t₀}′(z(t₀)) ≠ 0 ⇒ z′(t₀) = H″/H′ / SAME FOR Ξ / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Owner

[definition] `Soma.Holonics.RH.ZeroDynamicsEntire` in
`soma/formal/elementary-holonics/ElementaryHolonics/RH/ZeroDynamicsEntire.lean`, importing
`RH.HeatEquationEntire`. Receiver: the composite `s ↦ heatE s f (z s)` along a `C¹` curve and the
velocity of a simple zero of `H_t`.

## Theorems

[proved-derived] `hasDerivAt_coeff`, `coeff_deriv_succ`, `iteratedDeriv_two_mul_succ`,
`deriv_iteratedDeriv_two_mul`: the scalar and derivative bookkeeping of a term.

[proved-derived] `hasDerivAt_heatTerm_comp`, `curveDeriv_first_succ`: along the curve each term
differentiates to `(∂_t term) + (term of f′)·z′`, and the `∂_t` part of the `(k+1)`-st term is minus
the `k`-th term of `f″`.

[proved-derived] `hasDerivAt_heatE_comp`: for `f` entire of order below two and `z` a `C¹` curve,
`d/ds H_s(z(s)) = −H_s″(z(s)) + H_s′(z(s)) z′(s)`, by `hasDerivAt_tsum_of_isPreconnected` on the
interval `(t₀−1, t₀+1)`, where `|s|`, `‖z s‖`, `‖z′ s‖` are bounded by compactness.

[proved-derived] `zero_curve_velocity`, `zero_curve_velocity_riemannXi`: if `H_s(z(s)) = 0` for
all `s` and `H_{t₀}′(z(t₀)) ≠ 0`, then `z′(t₀) = H_{t₀}″(z(t₀)) / H_{t₀}′(z(t₀))`.

## Position on the route

[established-bounded] At the polynomial face `zero_curve_flux` continues from this point by
expanding `p″/p′` at a simple root as `2 Σ_{w ≠ z} 1/(z − w)`, which is the partial-fraction form
of the logarithmic derivative of a polynomial. The same continuation for `H_t` is the Hadamard
product of an entire function of order one, which Mathlib does not have and the corpus has not
built; it is the exact remaining passage between this owner and the entire-function forms of
`im_flux_le` and `highest_pair_dead`.

[established-bounded] Nothing here touches the face `t = 0`. Axioms:
`[propext, Classical.choice, Quot.sound]`; no `sorry`.

[established-bounded] Next: conjugation symmetry `H_t(conj s) = conj H_t(s)`, so the pair
population of `H_t` is closed under conjugation and reflection; then the Hadamard passage, which
is the open front.
