# The interior of the rectangle returns the zero comb

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: 8707 jobs for the owner cone; root module green, 9728 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, returning the argument principle on a rectangle for a zero factorization: the weighted contour integral of the log derivative is the interior zero comb, multiplicities and all. Assistant derivation for the proofs.
**Band:** LOG DERIVATIVE = LANDAU FLUX + UNIT LOG DERIVATIVE ON THE HALF DISC / RECTANGLE INSIDE THE HALF DISC, NO ZERO ON THE BOUNDARY / UNIT TERM INTEGRATES TO ZERO / EACH FLUX TERM IS CAUCHY'S FORMULA OR CAUCHY–GOURSAT / ∮ h·f′/f = 2πi Σ_{ρ inside} m_ρ h(ρ) / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[proved-derived] `logDeriv_eq_flux_add`: for a `ZeroFactorization Z` of `f` on the disc of
radius `r` about `z₀`, at every point `z` of the half disc with `f z ≠ 0`,
`f′/f (z) = Σ_{ρ ∈ Z.zeros} m_ρ/(z − ρ) + unit′/unit (z)`. This is the decomposition that the
Landau owner used inline, now returned as its own theorem.

[proved-derived] `rectIntegral_mul_logDeriv` (**the rectangle argument principle**): for a
rectangle with `z.re < w.re`, `z.im < w.im`, whose closure lies in the half disc, whose boundary
meets no zero of the factorization, and a weight `h` holomorphic on the closed rectangle,
`∮ h(ζ) · f′/f (ζ) dζ = 2πi · Σ_{ρ ∈ Z.zeros} [ρ ∈ openRect] · m_ρ · h(ρ)`.
On the boundary `f` does not vanish, so the log derivative splits as above; the unit's term is
`h · unit′/unit`, holomorphic on the closed rectangle (the unit is analytic on the open disc and
nonvanishing on the half disc), and Cauchy--Goursat kills it; each flux term is
`m_ρ · ∮ h/(ζ − ρ)`, which is `2πi · m_ρ · h(ρ)` by Cauchy's formula on the rectangle when `ρ`
is interior and zero by Cauchy--Goursat when `ρ` is outside the closed rectangle.

## Constants

[definition] `2πi = 2 · π · i`, inherited from the previous owner's residue; the multiplicities
`m_ρ` are the exponents of the factorization. No other constant appears.

## Holonic reading

[definition] The rectangle's interior returns the zero comb, weighted by the test and counted
with multiplicity, and nothing else: the unit carries no population. Combined with the previous
two owners, the right edge is the prime comb and the interior is the zero comb; the explicit
formula is the statement that the same rectangle integral is read both ways.

[established-bounded] For `ξ`, the factorization exists on any disc
(`exists_zeroFactorization_riemannXi`), so this theorem applies to every rectangle of the
critical strip whose horizontal edges avoid the zeros. Remaining: the reflection of the left edge
onto the right through `ξ(1 − s) = ξ(s)`, the log-derivative decomposition of `ξ` into `ζ` and
the archimedean factor on the right edge, and the horizontal-edge bounds from Landau in the
limit of height.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/RectangleArgumentPrinciple.lean`
  compiles under `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains
  green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.RectangleCauchy`; that
  owner's namespace was aligned to `Soma.Holonics.RH.RectangleCauchy`.
- Axiom audit for `rectIntegral_mul_logDeriv`, `logDeriv_eq_flux_add`:
  `[propext, Classical.choice, Quot.sound]`.
