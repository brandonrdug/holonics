# The interior zero count of H_t is locally constant in t

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `soma/formal/elementary-holonics/ElementaryHolonics/RH/RectangleCountStable.lean`
**Provenance:** Assistant, under Brandon's direct instruction of 2026-09-02 to take the pair population under the de Bruijn–Newman flow at the entire face: the corpus zero factorization about a corner and the rectangle argument principle write the winding integral of an entire function as 2πi times the divisor sum over the open rectangle, a natural number; continuity of the integral in t and the integer gap make the count locally constant while no zero is on the boundary. Assistant derivation for the proofs.
**Band:** z ∈ ∂R / closedRect ⊆ ball z (cornerRadius/2) / ZEROS OF A FACTORIZATION ARE ZEROS OF f / ∮_R f′/f = 2πi·n, n = Σᶠ divisor f (openRect) ∈ ℕ / ∃ n, ∀ᶠ t NEAR t₀: H_t ≠ 0 ON ∂R ∧ ∮_R H_t′/H_t = 2πi n ∧ Σᶠ divisor (H_t) (openRect) = n / SAME FOR Ξ / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Owner

[definition] `Soma.Holonics.RH.RectangleCountStable` in
`soma/formal/elementary-holonics/ElementaryHolonics/RH/RectangleCountStable.lean`, importing
`RH.RectangleWindingContinuity`, `RH.FactorizationMultiplicity`, `RH.ZeroFactorizationExists`,
`RH.HurwitzPolynomial`, and `RH.XiGrowth`. Receiver: the divisor sum of `H_t` over the open
rectangle, as a function of `t`.

## Theorems

[proved-derived] `corner_mem_boundaryRect`, `cornerRadius`, `closedRect_subset_ball_corner`: the
corner `z` is on the boundary and the closed rectangle lies in the half-ball about it.

[proved-derived] `eq_zero_of_mem_zeros`: the zeros of a corpus factorization are zeros of `f`.

[proved-derived] `exists_count`: for entire `f` nonvanishing on the boundary,
`∮ f′/f = 2πi · n` and `Σᶠ divisor f (openRect) = n` for a natural number `n`, by the corpus
argument principle and `finsum_divisor_eq` applied to the factorization about the corner.

[proved-derived] `eventually_count_eq`: for `H_t = heatE t f`, there is `n` such that for all `t`
near `t₀`, `H_t` is nonvanishing on the boundary, `∮ H_t′/H_t = 2πi n`, and the divisor sum of
`H_t` over the open rectangle is `n`. The integer gap `2π > 1` closes it.

[proved-derived] `eventually_count_eq_riemannXi`: the same for `H_t = e^{−tD²} Ξ`.

## Position on the route

[established-bounded] This is the entire-function local form of forward preservation: inside any
rectangle whose boundary carries no zero of `H_{t₀}`, the zero count with multiplicity of `H_t`
is constant for `t` near `t₀`. A pair of `H_t` can be created or destroyed only by crossing the
boundary of every such rectangle, that is, only on the critical line or at infinity. What is not
transported is the global count: that zeros cannot arrive from infinity. At the polynomial face
that is automatic; at the entire face it is where the Hadamard product enters.

[established-bounded] Nothing here touches the face `t = 0`. Axioms:
`[propext, Classical.choice, Quot.sound]`; no `sorry`.

[established-bounded] Next: the local implicit-function curve through a simple pair, making
`zero_curve_velocity` non-vacuous; then the Hadamard passage.
