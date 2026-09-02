# The two vertical edges fold onto the prime comb

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: 8710 jobs for the owner cone; root module green, 9729 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, decomposing ξ′/ξ on the edges of the rectangle: the classical product right of Re s = 1, the reflection that folds the left edge onto the right, and the right edge as the prime comb minus the archimedean integral. Assistant derivation for the proofs.
**Band:** ξ = ½ s(s−1) Γℝ(s) ζ(s) FOR Re s > 1 / ξ′/ξ = ARCHIMEDEAN + ζ′/ζ / ξ′/ξ(1−s) = −ξ′/ξ(s) EVERYWHERE / LEFT EDGE = −RIGHT EDGE WITH WEIGHT h(1−s) / RIGHT EDGE: PRIME COMB SUMS TO ARCHIMEDEAN INTEGRAL MINUS ∫ h·ξ′/ξ / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[proved-derived] `differentiableAt_Gammaℝ_of_re_pos`: `Γ_ℝ` is differentiable on `Re s > 0`
(as the inverse of Mathlib's entire `Γ_ℝ⁻¹`). `riemannXi_eq_mul_zeta`: for `Re s > 1`,
`ξ(s) = ½ · s (s − 1) · Γ_ℝ(s) · ζ(s)`, from the corpus's classical-product identity and
Mathlib's `ζ = Λ / Γ_ℝ`.

[definition] `archimedean s = 1/s + 1/(s − 1) + Γ_ℝ′/Γ_ℝ (s)`.

[proved-derived] `logDeriv_riemannXi_eq`: for `Re s > 1`, `ξ′/ξ = archimedean + ζ′/ζ`, by the
product rule for log derivatives on a neighbourhood where the product identity holds.

[proved-derived] `hasDerivAt_riemannXi_one_sub`, `deriv_riemannXi_one_sub`,
`logDeriv_riemannXi_one_sub`: from `ξ(1 − s) = ξ(s)`, `ξ′(1 − s) = −ξ′(s)` and
`ξ′/ξ (1 − s) = −ξ′/ξ (s)` at every `s`, zeros included.

[proved-derived] `left_edge_eq`, `rectIntegral_riemannXi_fold`: for a rectangle with
`z.re + w.re = 1` and `z.im = −w.im`, the left edge of `h · ξ′/ξ` equals minus the right edge
with the reflected weight `h(1 − s)`, so the rectangle integral is the two horizontal edges plus
the right edge carrying `h(s)` and `h(1 − s)` separately.

[proved-derived] `continuousOn_logDeriv_riemannXi`, `continuousOn_archimedean`: both are
continuous on `Re s > 1`. `hasSum_right_edge`: for a continuous weight `g` and `σ > 1`, the prime
comb `n ↦ ∫ g(σ + it) Λ(n) (σ + it)^{−n}` sums to
`∫ g · archimedean − ∫ g · ξ′/ξ` along the edge, by the previous owner's dominated convergence
and the decomposition above.

## Constants

[definition] `½ = 1/2` from the classical normalisation `ξ = ½ s(s−1) Λ`; the archimedean part
carries `1/s + 1/(s−1)`, the two removed poles of the completed zeta, as explicit terms. No other
constant appears.

## Holonic reading

[definition] Both vertical edges are the prime comb, one with the weight `h(s)` and one with
`h(1 − s)`: the reflection is the statement that the comb is read twice, once from each side of
the critical line. The interior is the zero comb (previous owner). The explicit formula at
finite height is now one identity away: the argument principle equates the rectangle integral to
the interior comb, and this owner writes the same rectangle integral as horizontal edges plus two
prime-comb edges plus two archimedean integrals.

[established-bounded] Remaining: assemble the finite-height identity for a rectangle
`[−δ, 1 + δ] × [−T, T]` whose horizontal edges avoid the zeros of `ξ`, then bound the horizontal
edges by Landau for `ξ` along a good sequence of heights, and pass to the limit.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/XiEdgeDecomposition.lean` compiles under
  `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.RectangleArgumentPrinciple`.
- Axiom audit for `hasSum_right_edge`, `rectIntegral_riemannXi_fold`, `logDeriv_riemannXi_eq`:
  `[propext, Classical.choice, Quot.sound]`.
