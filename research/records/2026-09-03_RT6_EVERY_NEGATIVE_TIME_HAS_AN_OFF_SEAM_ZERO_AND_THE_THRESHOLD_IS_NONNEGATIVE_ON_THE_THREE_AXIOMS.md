# RT6: every negative time has an off-seam zero, and the threshold is nonnegative on the three axioms

**Date:** 2026-09-03  
**Truth status:** `proved-derived`  
**Evidence:** `formal-checked`, `source-inspected`  
**Campaign:** RT6 under
[`THE_DESCENT_SIDE_HAS_OFF_SEAM_ZEROS_AT_EVERY_NEGATIVE_TIME_AND_THE_THRESHOLD_IS_NONNEGATIVE.md`](../../blueprint/THE_DESCENT_SIDE_HAS_OFF_SEAM_ZEROS_AT_EVERY_NEGATIVE_TIME_AND_THE_THRESHOLD_IS_NONNEGATIVE.md).  
**Owners:** `RH/DescentZeros.lean` and `RH/ThresholdReturn.lean` (amended) under
`soma/formal/elementary-holonics/ElementaryHolonics/`, registered in the root umbrella.  
**Scope:** schedules nothing beyond the directed order; the engine frontier is unchanged.

## The return

[definition] Repository `t > 0` is standard `τ = −t < 0`; `seamTimes = {τ | ∀ z, heatE (−τ) ξ z = 0 → Re z = ½}`;
`Λ_DN = sInf seamTimes`; the shift `J_t(s) = s + t(Log(s/2) − log π)`; the disc data of RT5:
`s₀` a zero of `F_t`, `δ ≤ ‖F_t‖` on `|s − s₀| = r`, the strip `X = |Re s₀| + r`.

[proved-derived; formal-checked]

- `descent_approximation_height`: RT4 in height form — for `ε > 0` a height `y₁` beyond which,
  on the strip, `γ_t'(s) ≠ 0`, `heatE t ξ (J_t s) = γ_t'(s)(F_t(s) + R_t(s))`, and
  `‖R_t(s)‖ ≤ ε`, by `w = (Im s)^{1/12}`.
- `differentiableAt_J`, `differentiableAt_γt'`, `differentiable_heatE_xi`: `J_t` and `γ_t'` are
  differentiable on the upper half-plane (the principal logarithm off the slit), `heatE t ξ`
  is entire.
- `re_J_ge`: `Re J_t(s) ≥ Re s + t log(Im s /(2π))`, so **`Re J_t → ∞` with the height**.
- **`exists_offSeam_zero`: for every `t > 0`, `heatE t ξ` has a zero off the seam.** Take
  `τ ≥ y₂ + r − Im s₀` an almost period of size `δ/8` (RT5), with `y₂` above RT4's height and
  above `2π e^{(X+1)/t}`; on the translated disc `G(s) = heatE t ξ (J_t(s + iτ))/γ_t'(s + iτ)`
  equals `F_t(s + iτ) + R_t(s + iτ)`, is below `δ/2` at `s₀` and above `δ/2` on the circle;
  the minimum-modulus principle (`BohrZeros.exists_zero_of_norm_center_lt`) gives a zero `z₁`
  of `G`, so `heatE t ξ (J_t(z₁ + iτ)) = 0`, and `Re J_t(z₁ + iτ) ≥ 1 ≠ ½`.
- `not_mem_seamTimes_of_neg`, `seamTimes_subset_Ici`: **no negative standard time is a seam
  time.**
- **`Λ_DN_nonneg : 0 ≤ Λ_DN`**, by `le_csInf` on the nonempty case and `Real.sInf_empty` on the
  empty one.
- `ThresholdReturn.rodgersTaoNonneg : RodgersTaoNonneg` discharges the former port;
  **`riemannHypothesis_iff_Λ_DN_eq_of_deBruijn (h : DeBruijnBound) : RiemannHypothesis ↔ Λ_DN = 0`**
  carries the single port `DeBruijnBound`; `Λ_DN_mem_Icc : Λ_DN ∈ [0, ½]` given it.

`#print axioms` on `exists_offSeam_zero`, `Λ_DN_nonneg`, `rodgersTaoNonneg`,
`riemannHypothesis_iff_Λ_DN_eq_of_deBruijn`, and `Λ_DN_mem_Icc` returns `propext`,
`Classical.choice`, `Quot.sound`. `DescentZeros` builds alone (8,817 jobs), `ThresholdReturn`
(8,826 jobs), and the root umbrella (9,834 jobs, 4 s incremental), each under the 180 s limit.

## The scope, corrected in place

[definition] The contract named Rouché's transfer through the tree's rectangle argument
principle or Hurwitz owners. The transfer returned uses neither: the minimum-modulus principle
on a disc (Mathlib's maximum modulus applied to `1/G`) carries the zero of the translate of `F_t`
to a zero of `F_t + R_t`, which needs only `G` differentiable on the disc and continuous on its
closure. The rectangle owners require entire functions, which `heatE t ξ ∘ J_t / γ_t'` is not
(the logarithm's slit); the disc route avoids the generalization. The contract's RT6 text is
corrected to say so.

## Pass RT6

`0 ≤ Λ_DN` on the three axioms, `#print axioms` deposited, root umbrella green under 180 s per
owner, `ThresholdReturn` re-stated with the single port `DeBruijnBound`. **RT6 passes.** The
campaign's target `0 ≤ Λ_DN` is returned. Falsifier: a standard time `τ < 0` at which every zero
of `heatE (−τ) ξ` lies on the seam.

## Boundaries

- No claim on the Riemann Hypothesis: `Λ_DN ≤ 0` remains the first exact missing inequality,
  and de Bruijn's bound `½ ∈ seamTimes` remains a port.
- No zero statistics, no counts, no zero-free region, and no information about the zeros of `ζ`
  are claimed or used, as the contract's §0b records of Dobner's proof.

## Reproduction

```bash
cd soma/formal/elementary-holonics
timeout 180s lake build ElementaryHolonics.RH.DescentZeros
timeout 180s lake build ElementaryHolonics.RH.ThresholdReturn
timeout 180s lake build ElementaryHolonics
```
