# The archimedean term is bounded polynomially along a vertical line

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: 8730 jobs for the owner cone; root module green, 9745 jobs)
**Provenance:** Assistant, under Brandon's direct-route directive of 2026-09-02, bounding the archimedean part of ξ′/ξ on the line Re s = 1 + δ without digamma asymptotics: |Γ(s)| ≤ Γ(Re s) from the integral, the reflection lower bound, and Landau's lemma on Γℝ, whose disc carries no zero. Assistant derivation for the proofs.
**Band:** |Γ(s)| ≤ Γ(Re s) FOR Re s > 0 / |sin z| ≤ e^{|Im z|} / |Γ(a+iy)| ≥ π e^{−π|y|}/Γ(1−a) FOR 0 < a < 1 / Γℝ BOUNDED ON EVERY CLOSED STRIP Re ∈ [a, b], a > 0 / LANDAU ON Γℝ ABOUT σ + it (NO ZEROS): |Γℝ′/Γℝ| ≤ C(1+|t|) FOR 1 < σ < 2 / |archimedean(1+δ+it)| ≤ C(1+|t|) / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[proved-derived] `norm_Gamma_le_Gamma_re`: for `Re s > 0`, `|Γ(s)| ≤ Γ(Re s)`, from the integral
representation and `|x^{s−1}| = x^{Re s − 1}`. `norm_sin_le_exp`: `|sin z| ≤ e^{|Im z|}`.
`sin_pi_mul_ne_zero`: `sin(π(a + iy)) ≠ 0` for `0 < a < 1`. `norm_Gamma_ge`: the reflection
lower bound `|Γ(a + iy)| ≥ π e^{−π|y|}/Γ(1 − a)` for `0 < a < 1`.

[proved-derived] `exists_bound_Gammaℝ_strip`: `Γ_ℝ` is bounded on every closed strip
`a ≤ Re z ≤ b` with `a > 0`, by continuity of `π^{−u} Γ(u)` on `[a/2, b/2]`.
`exists_logDeriv_Gammaℝ_bound` (**Landau on the line**): for `1 < σ < 2` there is `C` with
`|Γ_ℝ′/Γ_ℝ(σ + it)| ≤ C (1 + |t|)`; the disc of radius `σ/2` about `σ + it` carries no zero of
`Γ_ℝ`, its supremum is the strip bound, and its centre is bounded below by the reflection bound,
so the Landau budget is `|log(G/L)| + 1 + π|t|/2` and the remainder is the whole log derivative.

[proved-derived] `exists_archimedean_bound` (**the archimedean term is bounded polynomially**):
for `0 < δ < 1` there is `C` with `‖archimedean(1 + δ + it)‖ ≤ C (1 + |t|)`, adding the bounds
`|1/s| ≤ 1` and `|1/(s − 1)| ≤ 1/δ`.

## Constants

[definition] `16/σ = 8/(σ/2)`: Landau's `8M/r` at radius `σ/2`; `π/2` is the slope of the
reflection bound at half the height (`|Γ(σ/2 + it/2)|`); `1 + 1/δ` collects the two pole terms.
All elementary product expansions with lineage in the proofs.

## Holonic reading

[definition] Landau's lemma is the corpus's one tool for log derivatives, and it applies to
`Γ_ℝ` as it did to `ξ`: with no zeros inside, the flux is empty and the remainder is everything.
The archimedean receiver of the explicit formula is thereby polynomially bounded along the
line where the prime comb converges, which is what the decaying weight needs for the prime side
to converge as the height grows.

[established-bounded] Next: the convergence of the prime side as `T → ∞`, with the improper
archimedean integrals and the von Mangoldt sum exchanged by dominated convergence.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/ArchimedeanPolynomialBound.lean`
  compiles under `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains
  green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.SpectralKernelDecay`.
- Axiom audit for `exists_archimedean_bound`, `norm_Gamma_ge`, `norm_Gamma_le_Gamma_re`:
  `[propext, Classical.choice, Quot.sound]`.
