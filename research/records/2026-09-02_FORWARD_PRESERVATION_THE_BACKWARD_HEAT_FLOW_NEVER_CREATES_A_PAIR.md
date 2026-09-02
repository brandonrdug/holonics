# Forward preservation: the backward heat flow never creates a pair

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: 8730 jobs for the owner cone; root module green, 9753 jobs)
**Provenance:** Assistant, under Brandon's direct instruction of 2026-09-02, closing forward preservation at the polynomial face: the Euler iterate (1 − tD²/N)^N p is a binomial sum of even derivatives whose coefficients C(N,k)(−t/N)^k converge to (−t)^k/k!, each Euler step never increases the non-real count (Hermite–Poulain), and the count is lower semicontinuous in the limit (Hurwitz), so nonreal (e^{−tD²} p) ≤ nonreal p for t ≥ 0. Assistant derivation for the proofs.
**Band:** heatStep λ = (−λ)•D² + 1 IN End(ℝ[X]) / (1 − λD²)^N p = Σ_k C(N,k)(−λ)^k p^{(2k)} / C(N,k)(−t/N)^k → (−t)^k/k! / ITERATE → e^{−tD²}p COEFFICIENTWISE, DEGREES BOUNDED / nonreal((1 − λD²)^N p) ≤ nonreal p / nonreal(e^{−tD²}p) ≤ nonreal p FOR t ≥ 0 / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[definition] `D` is the derivative as an endomorphism of `ℝ[X]`; the heat step is
`(−λ) • D² + 1`.

[proved-derived] `heatStep_iterate_eq_end`, `heatStep_iterate_eq_sum` (**the binomial
iterate**): `(1 − λD²)^N p = Σ_{k ≤ N} C(N,k)(−λ)^k p^{(2k)}`, by the commuting binomial theorem
in the endomorphism ring. `tendsto_sub_div`, `tendsto_choose_mul_pow` (**the scalar limit**):
`C(N,k)(−t/N)^k → (−t)^k/k!`, through `C(N,k) = N^{(k)}/k!` and `∏_{i<k}(N − i)/N → 1`.

[proved-derived] `coeff_heatStep_iterate`, `coeff_heatR`, `tendsto_coeff_iterate`: the Euler
iterate `(1 − (t/N)D²)^N p` converges to `e^{−tD²} p` coefficientwise; the higher derivatives
vanish beyond the degree, so both are sums over `k ≤ deg p`. `natDegree_heatStep_iterate_le`,
`natDegree_heatR_le`: degrees stay bounded by `deg p`.

[proved-derived] `nonreal_heatStep_iterate_le`: `N` Hermite–Poulain steps never increase the
non-real count. `nonreal_heatR_le` (**forward preservation**): for `t ≥ 0`,
`nonreal (e^{−tD²} p) ≤ nonreal p`, by Hurwitz on the convergent iterates.

## Constants

[definition] `k!` is the exponential's Taylor denominator, recovered as the limit of
`N^k/C(N,k) = k! · N^k/N^{(k)}`; `1 = ∏ 1` is the limit of the falling-factorial ratio. All
lineage in the proofs.

## Holonic reading

[definition] This is de Bruijn's forward theorem at the polynomial face, proved from the flow:
no pair is born forward. With the descent law of the highest pair, the polynomial face of the
route is complete in both directions: pairs only die, and the highest dies by half its height
squared. What is left for the actual `H_t` is the transcendental object itself; what is left
for RH is the `t = 0` face, on which this owner is silent by construction.

[established-bounded] Next: the semigroup `e^{−sD²} e^{−tD²} = e^{−(s+t)D²}` on polynomials,
hence monotonicity of the non-real count in `t`.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/ForwardPreservation.lean` compiles
  under `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.HurwitzPolynomial`.
- Axiom audit for `nonreal_heatR_le`, `tendsto_coeff_iterate`, `heatStep_iterate_eq_sum`:
  `[propext, Classical.choice, Quot.sound]`.
