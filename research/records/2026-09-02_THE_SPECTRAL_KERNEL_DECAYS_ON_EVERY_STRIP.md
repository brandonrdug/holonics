# The spectral kernel decays on every strip

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: 8730 jobs for the owner cone; root module green, 9744 jobs)
**Provenance:** Assistant, under Brandon's direct-route directive of 2026-09-02, supplying the decay hypothesis of the explicit formula in the limit for the corpus's own Weil test functions: the spectral kernel of a smooth compactly supported kernel decays faster than any power along every vertical strip, by k-fold integration by parts through Mathlib's Fourier-derivative identity and the Leibniz bound. Assistant derivation for the proofs.
**Band:** ĥ(σ + it) = 𝓕(e^{(σ−½)x} g)(−t/2π) / 𝓕(∂^k f)(w) = (2πiw)^k 𝓕 f(w) ⇒ |ĥ| ≤ ‖∂^k f‖₁/|t|^k / LEIBNIZ + COMPACT SUPPORT ⇒ ‖∂^k f_σ‖₁ ≤ e^{AR} Σ C(k,i) A^i ‖g^{(k−i)}‖₁ UNIFORMLY ON THE STRIP / ‖ĥ(x+it)‖ ≤ K/(1+|t|)^k / EXPLICIT FORMULA IN THE LIMIT FOR EVERY WEIL TEST FUNCTION / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[definition] `expWeight a x = e^{a x}` (complex-valued, real variable); `weighted T σ = expWeight (σ − ½) · g`
for the arithmetic kernel `g` of a Weil test function `T`; `stripConst T A R k = e^{AR} Σ_{i ≤ k} C(k,i) A^i ‖g^{(k−i)}‖_{L¹}`.

[proved-derived] `iteratedDeriv_expWeight`, `norm_iteratedDeriv_expWeight`: `∂^n e^{ax} = a^n e^{ax}`.
`hasCompactSupport_iteratedDeriv`, `integrable_iteratedDeriv_weighted`: every derivative of the
weighted kernel is integrable. `spectralKernel_eq_fourier`: on `Re s = σ`, `ĥ(σ + it)` is the
Fourier transform of the weighted kernel at `−t/2π`.

[proved-derived] `norm_spectralKernel_le_of_ne`: for `t ≠ 0`,
`‖ĥ(σ + it)‖ ≤ ‖∂^k(weighted T σ)‖_{L¹} / |t|^k` (Mathlib's `fourier_iteratedDeriv`).
`norm_spectralKernel_le`: `‖ĥ(σ + it)‖ ≤ ‖weighted T σ‖_{L¹}`.

[proved-derived] `norm_iteratedDeriv_weighted_le`, `integral_norm_iteratedDeriv_weighted_le`:
for `|σ − ½| ≤ A` and `supp g ⊆ [−R, R]`, `‖∂^k(weighted T σ)‖_{L¹} ≤ stripConst T A R k`, by the
Leibniz bound with the exponential absorbed into `e^{AR}` on the support (both sides vanish off
it).

[proved-derived] `exists_strip_decay` (**the spectral kernel decays on every strip**): for every
`k` and `δ > 0` there is `K ≥ 0` with `‖ĥ(x + it)‖ ≤ K/(1 + |t|)^k` for `−δ ≤ x ≤ 1 + δ` and all
`t`, with `K = 2^k (stripConst 0 + stripConst k)` at `A = ½ + δ`.

[proved-derived] `explicit_formula_limit_weil`: **for every Weil test function of the corpus, the
explicit formula in the limit holds** with its spectral kernel as the weight.

## Constants

[definition] `2^k`: from `(1 + |t|)^k ≤ 2^k max(1, |t|)^k`. `A = ½ + δ` is the largest
`|σ − ½|` on the strip. `2π` is Mathlib's Fourier normalisation, cancelled exactly by the
evaluation point `−t/2π`. All elementary product expansions with lineage in the proofs.

## Holonic reading

[definition] The corpus's Weil test charts (smooth compactly supported kernels on the
logarithmic line) are exactly the weights the explicit formula in the limit accepts; nothing is
assumed of them beyond the pose. The population ledger of `ξ` is therefore complete for the
charts the corpus declared: the zero comb read by any such chart is asymptotically the prime
comb read twice.

[established-bounded] The convergence of the prime side itself as `T → ∞` (the improper
archimedean and von Mangoldt integrals) remains the one classical step not returned; it needs a
logarithmic bound on `Γ_ℝ′/Γ_ℝ` along a vertical line.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/SpectralKernelDecay.lean` compiles
  under `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.ExplicitFormulaLimit`.
- Axiom audit for `explicit_formula_limit_weil`, `exists_strip_decay`:
  `[propext, Classical.choice, Quot.sound]`.
