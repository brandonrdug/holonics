# FT4 (i)–(ii): the Foster class holds every flowed `ξ`, the kernel is positive, and the port is a theorem

**Date:** 2026-09-03  
**Truth status:** `proved-derived`  
**Evidence:** `formal-checked`, `source-inspected`  
**Campaign:** FT4 (i)–(ii) under
[`THE_FLOW_CARRIES_THE_ZEROS_AS_FOSTER_TANKS_AND_THE_THRESHOLD_IS_THE_TARGET.md`](../../blueprint/THE_FLOW_CARRIES_THE_ZEROS_AS_FOSTER_TANKS_AND_THE_THRESHOLD_IS_THE_TARGET.md).  
**Owners:** `RH/FosterClassLandau.lean`, `RH/FosterClassCount.lean`, `RH/FosterClassProduct.lean`,
`RH/FosterClassSplit.lean`, `RH/FosterClassHadamard.lean`, `RH/FosterClassFlux.lean`,
`RH/FosterClassHeat.lean`, `RH/HeatKernelPhi.lean`, `RH/FosterClassHeatFlow.lean`, and the
docstring of `RH/ZeroDynamicsEntire.lean`, all under
`soma/formal/elementary-holonics/ElementaryHolonics/` and registered in the root umbrella.  
**Scope:** FT4 (i) and the kernel, centre-value, and port items of FT4 (ii) are returned; FT4's
forward preservation, real-zero times, `Λ_DN`, and the equivalence remain current. Schedules
nothing beyond the directed order; the engine frontier is unchanged.

## (i) The Foster class (`FosterClassLandau` … `FosterClassFlux`)

[definition] `class FosterClass (f : ℂ → ℂ) (A B σ : outParam ℝ) : Prop`: `f` entire,
`f(1 − s) = f(s)`, `f(½) ≠ 0`, `0 < A`, `0 ≤ B`, `0 < σ < 2`, and `‖f w‖ ≤ A exp(B ‖w‖^σ)`. The
constants are the class's own; nothing is existential.

[proved-derived; formal-checked] FT0–FT3 for every member, by instance resolution:

- `SymmetricZeroFactorizationOf f r` and `exists_symmetricZeroFactorizationOf_count`; the budget
  `budget f A B σ r = max 1 (log A + B(½ + r)^σ − log ‖f(½)‖)` and `norm_le_of_growth`; Jensen's
  count `finsum_divisor_le` by `AnalyticOnNhd.sum_divisor_le`; the paired finite Foster form with
  Landau's remainder `landau f A B σ r` (`exists_paired_foster_form`).
- `mult f`, `Zero f`, the count `N f R ≤ K₁ + K₂ (½ + 2R)^σ` with `K₁, K₂` exhibited
  (`count_le`), and `summable_inverse_square` by dyadic shells with ratio `2^{σ−2} < 1`.
- `Idx f`, `P f`, `tank`: `differentiable_P`, `P_symm`, `P_eq_zero`, `P_ne_zero`, `logDeriv_P`.
- The finite/tail split, `landau ≤ landauA + landauB R^τ` with `τ = max (σ − 1) 0 < 1`
  (`landau_le`), Cauchy's estimate vanishing by `tendsto_rpow_neg_atTop`, the connected nonzero
  set, oddness, hence `sq_eq_centre_mul_P : f² = f(½)² P f` and `foster_form`.
- **`FosterClassFlux.flux`: at every simple zero `z₀` of a member,
  `2 Σ_{u ∈ D(½,R), u ≠ z₀} m_u/(z₀ − u) → f″(z₀)/f′(z₀)`.**
- `FosterClassHeat.instFosterClassRiemannXi`: `ξ` is a member with `A = Cθ e^{74} + 1`, `B = 10`,
  `σ = 3/2` (`XiGrowth`); `hasGrowth_heatE`: the flow of a function of growth `A exp(B‖w‖^ρ)` has
  growth `A · flowSum · exp(B 2^ρ ‖w‖^ρ)`, `flowSum` the sum of the majorant of `HeatFlowEntire`.

## (ii) The kernel `Φ` (`HeatKernelPhi`)

[definition] `θ(x) = Σ_{n ∈ ℤ} e^{−π n² x}` is Mathlib's `evenKernel 0`;
`Ψ(x) := 2x² θ″(x) + 3x θ′(x)`; **`Φ(u) := e^{u/2} Ψ(e^{2u})`**, with
`Ψ(x) = Σ_{n ∈ ℤ} (2π² n⁴ x² − 3π n² x) e^{−π n² x}`.

[proved-derived; formal-checked]

- `hasDerivAt_tsum_gterm`: the theta-type series `Σ c n^k e^{−π n² x}` differentiate termwise on
  `(0, ∞)` (`hasDerivAt_tsum_of_isPreconnected`); `hasDerivAt_theta`, `hasDerivAt_theta'`.
- `theta_fe : θ(x) = x^{−1/2} θ(1/x)` (`evenKernel_functional_equation`), differentiated twice by
  uniqueness of derivatives (`theta'_eq`, `theta''_eq`), giving **`Ψ_inv : Ψ(1/x) = x^{1/2} Ψ(x)`**
  by the substitution `x = s²`.
- **`Φ_neg : Φ(−u) = Φ(u)`; `Φ_pos : 0 < Φ(u)`** (termwise for `x ≥ 1`, `2π n² x > 3`, then by
  evenness); `Φ_le : Φ(u) ≤ 2π² C₄ e^{9|u|/2} e^{−π e^{2|u|}}`; `exp_mul_Φ_le`: for `a, b ≥ 0`,
  `e^{a u² + b|u|} Φ(u) ≤ K e^{−u²}` (from `e^{2|u|} ≥ (2|u|)⁴/24`).
- `integral_comp_exp_two`: the substitution `x = e^{2u}` on the whole line
  (`integral_image_eq_integral_abs_deriv_smul`); the term integrals are Gamma integrals
  (`Complex.integral_cpow_mul_exp_neg_mul_Ioi`): `integral_lapTerm ε`; the majorant's values are
  `Cmaj σ · |n|^{−σ}` (`termValue_one_re_eq`), summable for `σ > 1`, so the sum and the integral
  exchange (`integral_tsum`, `hasSum_integral_lapTerm`); the term values sum to
  `ξ(s) = ½ s(s−1) Λ(s)` through `Γ(s/2 + 2) = (s/2 + 1)(s/2) Γ(s/2)`, `Gammaℝ`, and
  `completedRiemannZeta_eq` (`hasSum_termValue`); the transform is entire
  (`hasDerivAt_L`, by `hasDerivAt_integral_of_dominated_loc_of_deriv_le`); hence
  **`riemannXi_eq_L : ξ(s) = ∫_ℝ e^{(s − ½) u} Φ(u) du` for every `s`** by the identity theorem
  from `Re s > 1`.
- The moment transforms `LM m s = ∫ u^m e^{(s−½)u} Φ(u) du` form a derivative ladder
  (`hasDerivAt_LM`), so `iteratedDeriv m L = LM m`; the heat series exchanges with the integral
  (`integral_tsum` with the Gaussian domination), giving **the flow identity in the corrected
  coordinate, `heatE_riemannXi : heatE t ξ (z) = ∫_ℝ e^{−t u²} e^{(z − ½) u} Φ(u) du`** for every
  real `t` and complex `z`; at `z = ½` the integrand is `e^{−t u²} Φ(u) > 0`, so
  **`heatE_riemannXi_half_ne_zero : heatE t ξ (½) ≠ 0` at every `t`.**

## The port discharged (`FosterClassHeatFlow`)

[proved-derived; formal-checked] `instFosterClassHeatE t : FosterClass (heatE t ξ) …` with
`A_t = (Cθ e^{74} + 1) · flowSum 10 (3/2) t`, `B = 10 · 2^{3/2}`, `σ = 3/2`; and
**`rodgersTaoZeroDynamics_heatE : RodgersTaoZeroDynamics (fun t => heatE t riemannXi)`**: along
every `C¹` curve of zeros of the flow that is simple at time `t`, the velocity
`ż = H_t″/H_t′` of `ZeroDynamicsEntire` equals the principal-value comb flux about `½`. The
docstring of `ZeroDynamicsEntire` no longer names its second half open.

`#print axioms` on `FosterClassFlux.flux`, `FosterClassHadamard.sq_eq_centre_mul_P`,
`FosterClassHadamard.foster_form`, `FosterClassCount.summable_inverse_square`,
`HeatKernelPhi.riemannXi_eq_L`, `HeatKernelPhi.heatE_riemannXi`,
`HeatKernelPhi.heatE_riemannXi_half_ne_zero`, `HeatKernelPhi.Φ_pos`, `HeatKernelPhi.Φ_neg`,
`FosterClassHeatFlow.instFosterClassHeatE`, and
`FosterClassHeatFlow.rodgersTaoZeroDynamics_heatE` returns `propext`, `Classical.choice`,
`Quot.sound`. The owners build alone and inside the root umbrella (9,803 jobs).

## The coordinate

[definition] `heatE t f = Σ_k (−t)^k/k! · f^{(2k)} = e^{−t D²} f`. In the kernel representation
`D_z² e^{(z − ½)u} = u² e^{(z − ½)u}`, so `heatE t ξ` carries the weight `e^{−t u²}`: repository time
`t` multiplies `Φ` by `e^{−t u²}`, the standard de Bruijn weight `e^{t_std u²}` at `t_std = −t`,
with the factor `4` of the 2026-09-02 correction absorbed in the choice `x = e^{2u}` (the
standard `H_t(x) = ⅛ Ξ(x/2)` normalizes `u` differently). Forward preservation in FT4 (iii) is the
statement in this coordinate: real zeros of `heatE t ξ` on `Re z = ½` persist as `t` decreases.

## Boundaries

- No claim of movement on the Riemann Hypothesis. `Φ > 0` and the flow identity hold wherever the
  zeros are; nothing here places a zero.
- The class's constants for `heatE t ξ` are exhibited (`flowSum` is a convergent series with a
  positive first term), not computed.
- FT4 (iii)–(v) remain: forward preservation at the entire face, the real-zero times as a closed
  up-set, `Λ_DN`, de Bruijn's bound, and `RH ⟺ Λ_DN ≤ 0` against the anchor.

## Reproduction

```bash
cd soma/formal/elementary-holonics
timeout 180s lake build ElementaryHolonics.RH.FosterClassHeatFlow
timeout 180s lake build ElementaryHolonics
```
