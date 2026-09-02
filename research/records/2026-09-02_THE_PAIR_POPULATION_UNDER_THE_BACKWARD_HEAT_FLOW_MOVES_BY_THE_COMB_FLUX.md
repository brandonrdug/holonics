# The pair population under the backward heat flow moves by the comb flux

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: 8730 jobs for the owner cone; root module green, 9749 jobs)
**Provenance:** Assistant, under Brandon's direct instruction of 2026-09-02 to take the pair population under the de Bruijn–Newman flow and go directly at RH: the polynomial face of the flow, e^{−tD²}p, is defined, satisfies the backward heat equation, and moves every C¹ curve of simple zeros by the comb flux ż = 2Σ_{w≠z} 1/(z − w), derived from the equation rather than postulated. Assistant derivation for the proofs.
**Band:** heat t p = Σ_k (−t)^k/k!·p^{(2k)} / heat 0 p = p / d/dt (heat t p)(z(t)) = −(heat t p)″(z) + (heat t p)′(z)·ż / p″(z)/p′(z) = 2Σ_{w ∈ roots∖{z}} 1/(z−w) AT A SIMPLE ROOT / ZERO CURVES OBEY ż = 2Σ_{w≠z} 1/(z−w) / THE POSTULATE RodgersTaoZeroDynamics IS SUPERSEDED AT THE POLYNOMIAL FACE / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[definition] `heat t p = Σ_{k ≤ deg p} (−t)^k/k! · p^{(2k)}`, the backward heat flow `e^{−tD²}` on
`ℂ[X]`, the finite-dimensional face of the de Bruijn–Newman flow `H_t` (`RH.0070`).

[proved-derived] `heat_zero`: `heat 0 p = p`. `derivative_heat`, `second_derivative_heat`: the
flow commutes with differentiation. `hasDerivAt_eval_heat_comp`: along any `C¹` curve `z(t)`,
`d/dt (heat t p)(z(t)) = −(heat t p)″(z(t)) + (heat t p)′(z(t)) · ż`; with `z` constant this is
the backward heat equation `∂_t = −∂_z²`.

[proved-derived] `derivative_multiset_prod_div`: the log derivative of `∏(X − w)` at a non-root
is `Σ 1/(z − w)`. `second_div_first_eq` (**the flux at a simple root**): for a simple root `z`
of `p`, `p″(z)/p′(z) = 2 Σ_{w ∈ roots(p) ∖ {z}} 1/(z − w)`, the sum over the other roots with
multiplicity, through `p = (X − z) q` with `q(z) = p′(z) ≠ 0`.

[proved-derived] `zero_curve_flux` (**the pair population moves by the comb flux**): a `C¹` curve
of simple zeros of `heat t p` satisfies `ż = 2 Σ_{w ≠ z} 1/(z − w)`. This is the law the
phase-flow ledger postulated as `RodgersTaoZeroDynamics`; at the polynomial face it is now a
theorem of the flow.

## Constants

[definition] `2 = 1 + 1`: the two surviving terms of `p″` at a simple root (`m = j` and
`l = j` in the double sum). `k!` is the exponential's Taylor denominator. No other constant.

## Holonic reading

[definition] Brandon's instruction: take the pair population under the de Bruijn–Newman flow
and go directly at RH. The pair population of a real polynomial is its set of non-real roots, in
conjugate pairs; this owner makes their motion a theorem: every pair moves by the comb flux of
the whole comb, the partner contributing `2/(z − z̄) = −i/Im z`, the real comb pulling downward,
and the other pairs pulling toward themselves. The ledger's collapse law
(`sq_add_two_mul_le`: a pair's height squared loses at least `2t`) applies to the highest pair of
any real polynomial under this flow, so the pair population of `heat t p` is empty for
`t ≥ (max height)²/2`; de Bruijn's bound at the polynomial face.

[established-bounded] Not returned here: the existence and `C¹` dependence of the root curves
(implicit function theorem at simple roots), the descent of the maximal height with only
Lipschitz regularity at collisions, the passage from polynomials to `H_t` (Hurwitz), and the `t = 0`
face itself. The last is RH: the flow shows pairs die forward and are born backward; nothing in
its monotone quantities decides whether any pair exists at `t = 0`. The next owner takes the
maximal-height descent for real polynomials.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/HeatFlowOfPolynomials.lean` compiles
  under `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.TrivialZeros`.
- Axiom audit for `zero_curve_flux`, `second_div_first_eq`, `hasDerivAt_eval_heat_comp`:
  `[propext, Classical.choice, Quot.sound]`.
