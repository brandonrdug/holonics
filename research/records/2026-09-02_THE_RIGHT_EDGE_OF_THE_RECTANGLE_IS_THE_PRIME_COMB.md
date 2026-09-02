# The right edge of the rectangle is the prime comb

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: 8706 jobs for the owner cone; root module green)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, opening the rectangular explicit formula on its right edge, where the log-derivative of zeta is the von Mangoldt series integrated term by term. Assistant derivation for the proofs.
**Band:** EDGE σ + it WITH σ > 1 / −ζ′/ζ = L(Λ) ON THE EDGE (MATHLIB) / TERM NORM DEPENDS ON THE REAL PART ONLY / DOMINATED CONVERGENCE WITH BOUND C · Λ(n)/n^σ / ∫ h · (−ζ′/ζ) = Σ_n ∫ h · Λ(n) n^{−s} / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[definition] `edge σ t = σ + it` and `vonMangoldtC n = Λ(n)` as complex coefficients.

[proved-derived] `continuous_term`: each von Mangoldt term `Λ(n) n^{−s}` is continuous in `s`.
`norm_term_edge`: the term's norm on the edge depends only on `σ`. `summable_norm_term`: the
series converges absolutely at real part `σ > 1`.

[proved-derived] `hasSum_integral_term`: for a continuous weight `h`, real `σ > 1`, and any
segment `a ≤ t ≤ b`, the family `n ↦ ∫_a^b h(σ + it) Λ(n)(σ + it)^{−n}` sums to
`∫_a^b h(σ + it) · (−ζ′/ζ)(σ + it)`. The weight is bounded on the compact segment, the terms are
dominated by `C · Λ(n)/n^σ`, and Mathlib's dominated convergence for interval integrals swaps the
sum and the integral; Mathlib's identity `L(Λ) = −ζ′/ζ` on `re s > 1` identifies the limit.

## Holonic reading

[definition] The explicit formula is a rectangle whose left and right edges carry the two combs.
On the right edge, where the Euler product converges, the log-derivative is exactly the prime
comb `Σ Λ(n) n^{−s}`, and this owner integrates it term by term: the right edge is the prime
comb weighted by the test. The left edge returns to the right by the reflection of `ξ`; the
horizontal edges are the Landau remainder of the previous owners. The zero comb, by the argument
principle on the rectangle, is what the interior returns.

[established-bounded] The corpus's explicit-formula port is posed on a circle, which has no
edge in the region of absolute convergence; it should be re-posed on the rectangle. The
remaining pieces are the rectangle contour integral of `ĥ ξ′/ξ` (Mathlib's
`integral_boundary_rect` family), the reflection of the left edge, and the horizontal-edge
bounds from Landau, then the limit `b → ∞` along heights where the Landau bound holds.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/PrimeSideVertical.lean` compiles under
  `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.JensenCountsTheComb`.
