import HolonicsResearch.Fluid.NavierStokesLaminarClass
import HolonicsResearch.Fluid.NavierStokesGalerkinInstance
import Mathlib

/-!
# Below Reynolds one the laminar class is stable: two solutions stay within a fixed multiple of their opening distance, the opening state decides the solution, and all of it relaxes at the rate of the lowest mode

This module reads the difference of two solutions of one comb. It joins
`Fluid/NavierStokesLaminarClass` (the laminar class of a comb system, `c * X 0 < ν`) and
`Fluid/NavierStokesGalerkinInstance` (the truncated fluid is a comb system with `c = 1`). The
readings are those files': `X = criticalNorm w a = ∑ k, ‖a k‖ / w k`,
`Y = dissipationNorm w a = ∑ k, w k * ‖a k‖` and `A = amplitudeSum a = ∑ k, ‖a k‖`, with
`A ^ 2 ≤ X * Y`.

## The setting: a bilinear comb

[definition] Finitely many modes `k : ι`, weights `w k > 0`, a viscosity `ν > 0`, a coherence
constant `c ≥ 0`, pairwise disjoint fibres `T k : Finset (ι × ι)` and amplitudes in a real inner
product space `E`. The feed is bilinear,

  `combFeed T b k a = ∑ pq ∈ T k, b k pq (a pq.1) (a pq.2)`,  `b k pq : E →ₗ[ℝ] E →ₗ[ℝ] E`,

and the bound `‖b k pq x y‖ ≤ c * w k * ‖x‖ * ‖y‖` is asked only of admissible amplitudes,
`x ∈ adm pq.1` and `y ∈ adm pq.2`, for subspaces `adm : ι → Submodule ℝ E` (`BilinearComb`). The
fluid's admissible amplitudes are those across the wave vector; `adm = ⊤` is a plain bilinear
comb. A `Solution` keeps `u t k ∈ adm k` and obeys
`d/dt u_k = -(ν * w_k ^ 2) • u_k + combFeed T b k u` on `[0, ∞)` (the derivative within
`Ici 0`). Below, `u` and `v` are two solutions of one bilinear comb and `δ = u - v`.

## Statements

[proved-derived; formal-checked]

* S1 `Solution.combSystem`: a solution of a bilinear comb is a `CombSystem w ν c T u` with the
  feed `fun t k => combFeed T b k (u t)` (`BilinearComb.norm_combFeed_le`), so every statement of
  the two files above holds for it.
* S2 `combFeed_sub`: `N_k(u) - N_k(v) = ∑ pq ∈ T k, (b k pq δ_p u_q + b k pq v_p δ_q)`;
  `BilinearComb.sum_combFeed_sub_le`: `∑ k, ‖N_k(u) - N_k(v)‖ / w k ≤ c * (A δ * (A u + A v))`
  (a pair of modes feeds at most one mode, `sum_fibres_le`);
  `BilinearComb.sum_combFeed_sub_le_half`: the same sum is at most
  `c / 2 * (Y δ * (X u + X v) + X δ * (Y u + Y v))`, from
  `amplitudeSum_mul_le : A δ * A u ≤ 1 / 2 * (Y δ * X u + X δ * Y u)`.
* S3 `Solution.hasDerivWithinAt_critical_sub`, `BilinearComb.differenceSlope_le`: `X δ` has the
  forward derivative `differenceSlope` at every `0 ≤ t`, and
  `differenceSlope ≤ -(ν - c / 2 * (X u + X v)) * Y δ + c / 2 * (Y u + Y v) * X δ`.
* S4 `BilinearComb.critical_sub_le_mul_exp`: if `c * X (u 0) < ν` and `c * X (v 0) < ν` then
  `X δ t ≤ X δ 0 * exp (c / 2 * ∫ s in 0..t, (Y (u s) + Y (v s)))` at every `0 ≤ t`;
  `BilinearComb.critical_sub_le`: `X δ t ≤ K * X δ 0` with
  `K = stabilityConstant w ν c (u 0) (v 0)
     = exp (c / 2 * (X (u 0) / (ν - c * X (u 0)) + X (v 0) / (ν - c * X (v 0))))`;
  `stabilityConstant_le`, `BilinearComb.critical_sub_le_of_le`: if both opening readings are at
  most `R` with `c * R < ν` then `K ≤ exp (c * R / (ν - c * R))`, a constant that names neither
  the modes nor their number.
* S5 `BilinearComb.sum_combFeed_sub_le_young`:
  `∑ k, ‖N_k(u) - N_k(v)‖ / w k ≤ ν * Y δ + c ^ 2 / (4 * ν) * (A u + A v) ^ 2 * X δ`;
  `BilinearComb.critical_sub_le_mul_exp_sq`: with no smallness,
  `X δ t ≤ X δ 0 * exp (c ^ 2 / (4 * ν) * ∫ s in 0..t, (A (u s) + A (v s)) ^ 2)`;
  `BilinearComb.eq_of_initial_eq`: two solutions with one opening state agree at every `0 ≤ t`,
  at every size of the data; `BilinearComb.eq_of_initial_eq_of_laminar` is the same read from S4
  inside the laminar class.
* S6 `sq_mul_criticalNorm_le_dissipationNorm`: `w₀ ^ 2 * X a ≤ Y a` when `0 < w₀ ≤ w k`;
  `CombSystem.critical_le_mul_exp_decay`: in the laminar class of any comb system
  `X (u t) ≤ X (u 0) * exp (-(ν - c * X (u 0)) * w₀ ^ 2 * t)`;
  `BilinearComb.critical_sub_le_mul_exp_decay`:
  `X δ t ≤ K * X δ 0 * exp (-(ν - c * max (X (u 0)) (X (v 0))) * w₀ ^ 2 * t)` with the `K` of S4
  (`BilinearComb.critical_sub_le_mul_exp_decay_of_le` for any `m` over both opening readings with
  `c * m < ν`).
* S7 the fluid's truncation is a bilinear comb. On `EuclideanSpace ℂ n` read over the reals:
  `transportForm κ P k pq x y = (-i) • P k ((κ q · x) • y)` (complex bilinear, restricted to real
  scalars), `across κ p = {x | wavePairing (κ p) x = 0}` (`mem_across`),
  `combFeed_transportForm : combFeed (triads κ) (transportForm κ P) k a = feed κ P a k`,
  `norm_transportForm_le` (the bound with `c = 1` for `x` across `κ p`),
  `bilinearComb_of_waves`, `Truncation.bilinearComb`, `Truncation.solution`. Hence, for two
  truncations `a`, `a'` of one law (the same `κ`, `ν`, `P`):
  `Truncation.critical_sub_le` and `Truncation.critical_sub_le_of_le` (S4, with
  `K ≤ exp (R / (ν - R))` for opening readings at most `R < ν`),
  `Truncation.eq_of_initial_eq` (S5, at every size of the data),
  `Truncation.critical_le_mul_exp_decay` and `Truncation.critical_sub_le_mul_exp_decay` (S6).
  None of the constants names `ι`: they are the same at every truncation.

The Grönwall step is `le_mul_exp_integral_of_slope_le`: a continuous `f` on `[0, ∞)` whose
forward derivative is at most `g * f`, `g` continuous, has `f t ≤ f 0 * exp (∫ s in 0..t, g s)`
(the argument of `CombSystem.critical_le_mul_exp` on `f * exp (-∫ g)`, with no sign asked of `f`
or `g`).

[proved-standard; from training] For the equation itself this is uniqueness and continuous
dependence in the class of Lei and Lin (2011), `∫ |ξ|⁻¹ |û(ξ)| dξ < (2π)³ ν`, with the decay at
the rate of the lowest mode on a torus; here it is stated on the comb and on the truncations
only.

Reading: below Reynolds one (`c * X 0 < ν`) the laminar class is a stable region of the comb.
Two solutions never part by more than `K` times their opening distance, `K` is fixed by the two
opening readings and the viscosity, and the distance itself relaxes at the rate
`(ν - c * max X) * w₀ ^ 2` of the lowest mode. The opening state decides the solution at every
size of the data; above the threshold what is not bounded is the constant, through
`∫ (A u + A v) ^ 2`.

## What this does not state

Nothing here is the Clay statement. The module constructs no solution: a `Solution`, like a
`Truncation`, is a hypothesis given on `[0, ∞)`, so existence is not stated for the comb, for a
truncation or for the fluid. It makes no limit of truncations and says nothing of infinitely many
modes; the constants not naming `ι` is what such a limit would use, and the limit is not made. At
or above the threshold (`c * X 0 ≥ ν`) it states only S5's uniqueness and its bound through
`∫ (A u + A v) ^ 2`, which is not bounded here; it gives no stability constant and no decay there.
S7 compares two truncations with the same modes and the same projections; two different
truncations are not compared.
-/

noncomputable section

namespace Holonics.Fluid.LaminarStability

open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
open Holonics.Fluid.LaminarClass Holonics.Fluid.GalerkinInstance

/-! ## Scalar lemmas -/

section Scalars

/-- A continuous function on `[0, ∞)` is interval integrable on `[0, t]`. -/
theorem intervalIntegrable_of_continuousOn_Ici {g : ℝ → ℝ} (hg : ContinuousOn g (Ici 0))
    {t : ℝ} (ht : 0 ≤ t) : IntervalIntegrable g volume 0 t := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le ht]
  exact hg.mono Icc_subset_Ici_self

/-- [proved-derived; formal-checked] **Grönwall's step on `[0, ∞)`.** A continuous `f` whose
forward derivative is at most `g * f`, with `g` continuous, has
`f t ≤ f 0 * exp (∫ s in 0..t, g s)`: the argument on `f * exp (-∫ g)`. No sign is asked of `f`
or of `g`. -/
theorem le_mul_exp_integral_of_slope_le {f f' g : ℝ → ℝ} (hf : ContinuousOn f (Ici 0))
    (hf' : ∀ x, 0 ≤ x → HasDerivWithinAt f (f' x) (Ici x) x) (hg : ContinuousOn g (Ici 0))
    (hle : ∀ x, 0 ≤ x → f' x ≤ g x * f x) {t : ℝ} (ht : 0 ≤ t) :
    f t ≤ f 0 * Real.exp (∫ s in (0 : ℝ)..t, g s) := by
  have hprim_cont : ContinuousOn (fun x => ∫ s in (0 : ℝ)..x, g s) (Icc 0 t) := by
    have hI : IntegrableOn g (uIcc 0 t) volume := by
      rw [uIcc_of_le ht]
      exact (hg.mono Icc_subset_Ici_self).integrableOn_Icc
    have := intervalIntegral.continuousOn_primitive_interval hI
    rwa [uIcc_of_le ht] at this
  have hprim_deriv : ∀ x, 0 ≤ x →
      HasDerivWithinAt (fun y => ∫ s in (0 : ℝ)..y, g s) (g x) (Ici x) x := by
    intro x hx
    have hgx : ContinuousOn g (Ici x) := hg.mono (Ici_subset_Ici.mpr hx)
    refine intervalIntegral.integral_hasDerivWithinAt_right
      (intervalIntegrable_of_continuousOn_Ici hg hx) (s := Ici x) (t := Ioi x) ?_ ?_
    · exact (hgx.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ici x).filter_mono
        (nhdsWithin_mono x Ioi_subset_Ici_self)
    · exact (hgx x (mem_Ici.mpr le_rfl)).mono Ioi_subset_Ici_self
  have key := image_le_of_deriv_right_le_deriv_boundary
    (f := fun s => f s * Real.exp (-∫ r in (0 : ℝ)..s, g r))
    (f' := fun x => f' x * Real.exp (-∫ r in (0 : ℝ)..x, g r)
      + f x * (Real.exp (-∫ r in (0 : ℝ)..x, g r) * (-g x)))
    (a := 0) (b := t)
    (B := fun _ => f 0) (B' := fun _ => 0)
    ((hf.mono Icc_subset_Ici_self).mul
      (Real.continuous_exp.comp_continuousOn hprim_cont.neg))
    (fun x hx => (hf' x hx.1).fun_mul ((hprim_deriv x hx.1).fun_neg.exp))
    (by simp)
    continuousOn_const
    (fun x _ => hasDerivWithinAt_const _ _ _)
    (by
      intro x hx
      have he := Real.exp_pos (-∫ r in (0 : ℝ)..x, g r)
      have h1 : f' x - g x * f x ≤ 0 := by linarith [hle x hx.1]
      show f' x * Real.exp (-∫ r in (0 : ℝ)..x, g r)
        + f x * (Real.exp (-∫ r in (0 : ℝ)..x, g r) * (-g x)) ≤ 0
      calc f' x * Real.exp (-∫ r in (0 : ℝ)..x, g r)
            + f x * (Real.exp (-∫ r in (0 : ℝ)..x, g r) * (-g x))
          = Real.exp (-∫ r in (0 : ℝ)..x, g r) * (f' x - g x * f x) := by ring
        _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos he.le h1)
  have hk : f t * Real.exp (-∫ r in (0 : ℝ)..t, g r) ≤ f 0 := key (right_mem_Icc.mpr ht)
  have hmul := mul_le_mul_of_nonneg_right hk (Real.exp_pos (∫ r in (0 : ℝ)..t, g r)).le
  rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at hmul
  exact hmul

/-- [proved-derived; formal-checked] The mean of two products over a product of two means:
`s ^ 2 ≤ x * y` and `t ^ 2 ≤ x' * y'` give `s * t ≤ (y * x' + x * y') / 2`. -/
theorem mul_le_half_of_sq_le {s t x y x' y' : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hx' : 0 ≤ x')
    (hy' : 0 ≤ y') (h1 : s ^ 2 ≤ x * y) (h2 : t ^ 2 ≤ x' * y') :
    s * t ≤ 1 / 2 * (y * x' + x * y') := by
  have h5 : 0 ≤ 1 / 2 * (y * x' + x * y') := by positivity
  have h4 : (s * t) ^ 2 ≤ x * y * (x' * y') := by
    rw [mul_pow]
    exact mul_le_mul h1 h2 (sq_nonneg _) (mul_nonneg hx hy)
  have h6 : (1 / 2 * (y * x' + x * y')) ^ 2
      = x * y * (x' * y') + 1 / 4 * (y * x' - x * y') ^ 2 := by ring
  have h3 : (s * t) ^ 2 ≤ (1 / 2 * (y * x' + x * y')) ^ 2 := by
    rw [h6]
    have h7 := sq_nonneg (y * x' - x * y')
    linarith
  exact (abs_le_of_sq_le_sq' h3 h5).2

/-- [proved-derived; formal-checked] The split that asks no smallness: `A ^ 2 ≤ X * Y` gives
`c * A * S ≤ ν * Y + c ^ 2 / (4 * ν) * S ^ 2 * X`. -/
theorem mul_mul_le_split {ν c A S X Y : ℝ} (hν : 0 < ν) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h : A ^ 2 ≤ X * Y) : c * A * S ≤ ν * Y + c ^ 2 / (4 * ν) * S ^ 2 * X := by
  have hν' : ν ≠ 0 := hν.ne'
  have hR : 0 ≤ ν * Y + c ^ 2 / (4 * ν) * S ^ 2 * X := by positivity
  have h2 : (c * A * S) ^ 2 ≤ c ^ 2 * S ^ 2 * (X * Y) := by
    have h3 : (c * A * S) ^ 2 = c ^ 2 * S ^ 2 * A ^ 2 := by ring
    rw [h3]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  have hq : 4 * ν * (c ^ 2 / (4 * ν)) = c ^ 2 := by field_simp
  have h4 : (ν * Y + c ^ 2 / (4 * ν) * S ^ 2 * X) ^ 2
      = 4 * ν * (c ^ 2 / (4 * ν)) * S ^ 2 * (X * Y)
        + (ν * Y - c ^ 2 / (4 * ν) * S ^ 2 * X) ^ 2 := by ring
  rw [hq] at h4
  have h1 : (c * A * S) ^ 2 ≤ (ν * Y + c ^ 2 / (4 * ν) * S ^ 2 * X) ^ 2 := by
    rw [h4]
    have h5 := sq_nonneg (ν * Y - c ^ 2 / (4 * ν) * S ^ 2 * X)
    linarith
  exact (abs_le_of_sq_le_sq' h1 hR).2

/-- [proved-derived; formal-checked] A pair of modes feeds at most one mode: over pairwise
disjoint fibres, `∑ k, ∑ pq ∈ T k, f p * g q ≤ (∑ p, f p) * ∑ q, g q` for nonnegative `f`, `g`. -/
theorem sum_fibres_le {ι : Type*} [Fintype ι] {T : ι → Finset (ι × ι)}
    (hT : ∀ k k', k ≠ k' → Disjoint (T k) (T k')) {f g : ι → ℝ} (hf : ∀ p, 0 ≤ f p)
    (hg : ∀ q, 0 ≤ g q) :
    ∑ k, ∑ pq ∈ T k, f pq.1 * g pq.2 ≤ (∑ p, f p) * ∑ q, g q := by
  classical
  calc ∑ k, ∑ pq ∈ T k, f pq.1 * g pq.2
      = ∑ pq ∈ Finset.univ.biUnion T, f pq.1 * g pq.2 := by
        rw [Finset.sum_biUnion]
        intro k _ k' _ hkk'
        exact hT k k' hkk'
    _ ≤ ∑ pq : ι × ι, f pq.1 * g pq.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun pq _ _ => mul_nonneg (hf _) (hg _))
    _ = (∑ p, f p) * ∑ q, g q := by
        rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

end Scalars

/-! ## The three readings -/

section Norms

variable {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E]

/-- [proved-derived; formal-checked] `A d * A a ≤ (Y d * X a + X d * Y a) / 2`, from
`A ^ 2 ≤ X * Y` for each family. -/
theorem amplitudeSum_mul_le {w : ι → ℝ} (hw : ∀ k, 0 < w k) (d a : ι → E) :
    amplitudeSum d * amplitudeSum a ≤ 1 / 2 *
      (dissipationNorm w d * criticalNorm w a + criticalNorm w d * dissipationNorm w a) :=
  mul_le_half_of_sq_le (criticalNorm_nonneg (fun k => (hw k).le) d)
    (dissipationNorm_nonneg (fun k => (hw k).le) d) (criticalNorm_nonneg (fun k => (hw k).le) a)
    (dissipationNorm_nonneg (fun k => (hw k).le) a) (amplitudeSum_sq_le hw d)
    (amplitudeSum_sq_le hw a)

/-- [proved-derived; formal-checked] With a lowest weight `w₀`, the dissipation reading is at
least `w₀ ^ 2` times the critical reading. -/
theorem sq_mul_criticalNorm_le_dissipationNorm {w : ι → ℝ} {w₀ : ℝ} (hw₀ : 0 < w₀)
    (hle : ∀ k, w₀ ≤ w k) (a : ι → E) :
    w₀ ^ 2 * criticalNorm w a ≤ dissipationNorm w a := by
  unfold criticalNorm dissipationNorm
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have hwk : 0 < w k := hw₀.trans_le (hle k)
  rw [← mul_div_assoc, div_le_iff₀ hwk]
  have hsq : w₀ ^ 2 ≤ w k ^ 2 := pow_le_pow_left₀ hw₀.le (hle k) 2
  calc w₀ ^ 2 * ‖a k‖ ≤ w k ^ 2 * ‖a k‖ := mul_le_mul_of_nonneg_right hsq (norm_nonneg _)
    _ = w k * ‖a k‖ * w k := by ring

/-- A family whose critical reading is not positive is zero. -/
theorem eq_zero_of_criticalNorm_le_zero {w : ι → ℝ} (hw : ∀ k, 0 < w k) {d : ι → E}
    (h : criticalNorm w d ≤ 0) : d = 0 := by
  funext k
  have h3 : ‖d k‖ / w k ≤ criticalNorm w d :=
    Finset.single_le_sum (f := fun k => ‖d k‖ / w k)
      (fun j _ => div_nonneg (norm_nonneg _) (hw j).le) (Finset.mem_univ k)
  have h4 : ‖d k‖ ≤ 0 := by
    have h5 := h3.trans h
    rwa [div_le_iff₀ (hw k), zero_mul] at h5
  exact norm_le_zero_iff.mp h4

theorem continuousOn_amplitudeSum {d : ℝ → ι → E}
    (hd : ∀ k, ContinuousOn (fun s => d s k) (Ici 0)) :
    ContinuousOn (fun s => amplitudeSum (d s)) (Ici 0) := by
  unfold amplitudeSum
  exact continuousOn_finsetSum _ fun k _ => (hd k).norm

theorem continuousOn_criticalNorm (w : ι → ℝ) {d : ℝ → ι → E}
    (hd : ∀ k, ContinuousOn (fun s => d s k) (Ici 0)) :
    ContinuousOn (fun s => criticalNorm w (d s)) (Ici 0) := by
  unfold criticalNorm
  exact continuousOn_finsetSum _ fun k _ => (hd k).norm.div_const _

/-- [definition] The stability constant of two opening states in the laminar class:
`exp (c / 2 * (X a / (ν - c * X a) + X a' / (ν - c * X a')))`. -/
def stabilityConstant (w : ι → ℝ) (ν c : ℝ) (a a' : ι → E) : ℝ :=
  Real.exp (c / 2 * (criticalNorm w a / (ν - c * criticalNorm w a)
    + criticalNorm w a' / (ν - c * criticalNorm w a')))

theorem stabilityConstant_pos (w : ι → ℝ) (ν c : ℝ) (a a' : ι → E) :
    0 < stabilityConstant w ν c a a' :=
  Real.exp_pos _

/-- [proved-derived; formal-checked] The stability constant under a common bound on the two
opening readings: `K ≤ exp (c * R / (ν - c * R))`, which names neither the modes nor their
number. -/
theorem stabilityConstant_le {w : ι → ℝ} (hw : ∀ k, 0 < w k) {ν c R : ℝ} (hc : 0 ≤ c)
    (hR : c * R < ν) {a a' : ι → E} (ha : criticalNorm w a ≤ R) (ha' : criticalNorm w a' ≤ R) :
    stabilityConstant w ν c a a' ≤ Real.exp (c * R / (ν - c * R)) := by
  have hdR : 0 < ν - c * R := sub_pos.mpr hR
  have hone : ∀ {x : ℝ}, 0 ≤ x → x ≤ R → x / (ν - c * x) ≤ R / (ν - c * R) := by
    intro x hx0 hx
    have hcx : c * x ≤ c * R := mul_le_mul_of_nonneg_left hx hc
    have hdx : 0 < ν - c * x := by linarith
    have hν : 0 ≤ ν := by nlinarith [mul_nonneg hc hx0]
    rw [div_le_div_iff₀ hdx hdR]
    have h1 := mul_le_mul_of_nonneg_right hx hν
    linarith
  have h1 := hone (criticalNorm_nonneg (fun k => (hw k).le) a) ha
  have h2 := hone (criticalNorm_nonneg (fun k => (hw k).le) a') ha'
  unfold stabilityConstant
  refine Real.exp_le_exp.mpr ?_
  have h3 : c * R / (ν - c * R) = c / 2 * (R / (ν - c * R) + R / (ν - c * R)) := by ring
  rw [h3]
  exact mul_le_mul_of_nonneg_left (add_le_add h1 h2) (div_nonneg hc zero_le_two)

end Norms

/-! ## S1, S2. The bilinear comb and the feed of a difference -/

section Form

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- [definition] The feed of a bilinear comb into the mode `k`: its fibre's pairs, each through
its own bilinear form. -/
def combFeed (T : ι → Finset (ι × ι)) (b : ι → ι × ι → E →ₗ[ℝ] E →ₗ[ℝ] E) (k : ι)
    (a : ι → E) : E :=
  ∑ pq ∈ T k, b k pq (a pq.1) (a pq.2)

/-- [definition] A bilinear comb: positive weights, a positive viscosity, a coherence constant,
pairwise disjoint fibres, and the bound `‖b k pq x y‖ ≤ c * w k * ‖x‖ * ‖y‖` on the admissible
amplitudes of the pair. -/
structure BilinearComb (w : ι → ℝ) (ν c : ℝ) (T : ι → Finset (ι × ι))
    (b : ι → ι × ι → E →ₗ[ℝ] E →ₗ[ℝ] E) (adm : ι → Submodule ℝ E) : Prop where
  weight_pos : ∀ k, 0 < w k
  viscosity_pos : 0 < ν
  coherence_nonneg : 0 ≤ c
  fibres_disjoint : ∀ k k', k ≠ k' → Disjoint (T k) (T k')
  form_le : ∀ k, ∀ pq ∈ T k, ∀ x ∈ adm pq.1, ∀ y ∈ adm pq.2,
    ‖b k pq x y‖ ≤ c * w k * ‖x‖ * ‖y‖

/-- [definition] A solution of a bilinear comb on `[0, ∞)`: admissible amplitudes and the law
`d/dt u_k = -(ν * w_k ^ 2) • u_k + combFeed T b k u`. -/
structure Solution (w : ι → ℝ) (ν : ℝ) (T : ι → Finset (ι × ι))
    (b : ι → ι × ι → E →ₗ[ℝ] E →ₗ[ℝ] E) (adm : ι → Submodule ℝ E) (u : ℝ → ι → E) : Prop where
  admissible : ∀ t, 0 ≤ t → ∀ k, u t k ∈ adm k
  evolves : ∀ k t, 0 ≤ t →
    HasDerivWithinAt (fun s => u s k) (-(ν * w k ^ 2) • u t k + combFeed T b k (u t)) (Ici 0) t

variable {w : ι → ℝ} {ν c : ℝ} {T : ι → Finset (ι × ι)} {b : ι → ι × ι → E →ₗ[ℝ] E →ₗ[ℝ] E}
  {adm : ι → Submodule ℝ E} {u : ℝ → ι → E}

/-- [proved-derived; formal-checked] **S2, the feed of a difference.**
`N_k(a) - N_k(a') = ∑ pq ∈ T k, (b k pq (a_p - a'_p) a_q + b k pq a'_p (a_q - a'_q))`. -/
theorem combFeed_sub (T : ι → Finset (ι × ι)) (b : ι → ι × ι → E →ₗ[ℝ] E →ₗ[ℝ] E) (k : ι)
    (a a' : ι → E) :
    combFeed T b k a - combFeed T b k a' =
      ∑ pq ∈ T k, (b k pq (a pq.1 - a' pq.1) (a pq.2) + b k pq (a' pq.1) (a pq.2 - a' pq.2)) := by
  unfold combFeed
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun pq _ => ?_
  simp only [map_sub, LinearMap.sub_apply]
  abel

/-- [proved-derived; formal-checked] The comb's feed bound for admissible amplitudes. -/
theorem BilinearComb.norm_combFeed_le (hb : BilinearComb w ν c T b adm) {a : ι → E}
    (ha : ∀ k, a k ∈ adm k) (k : ι) :
    ‖combFeed T b k a‖ ≤ c * w k * ∑ pq ∈ T k, ‖a pq.1‖ * ‖a pq.2‖ := by
  unfold combFeed
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun pq hpq => ?_
  calc ‖b k pq (a pq.1) (a pq.2)‖ ≤ c * w k * ‖a pq.1‖ * ‖a pq.2‖ :=
        hb.form_le k pq hpq (a pq.1) (ha _) (a pq.2) (ha _)
    _ = c * w k * (‖a pq.1‖ * ‖a pq.2‖) := by ring

/-- [proved-derived; formal-checked] **S1.** A solution of a bilinear comb is a comb system. -/
theorem Solution.combSystem (hu : Solution w ν T b adm u) (hb : BilinearComb w ν c T b adm) :
    CombSystem w ν c T u (fun t k => combFeed T b k (u t)) where
  weight_pos := hb.weight_pos
  viscosity_pos := hb.viscosity_pos
  coherence_nonneg := hb.coherence_nonneg
  fibres_disjoint := hb.fibres_disjoint
  evolves := hu.evolves
  feed_le t ht k := hb.norm_combFeed_le (hu.admissible t ht) k

/-- [proved-derived; formal-checked] The feed of a difference in one mode. -/
theorem BilinearComb.norm_combFeed_sub_le (hb : BilinearComb w ν c T b adm) {a a' : ι → E}
    (ha : ∀ k, a k ∈ adm k) (ha' : ∀ k, a' k ∈ adm k) (k : ι) :
    ‖combFeed T b k a - combFeed T b k a'‖ ≤ c * w k *
      ∑ pq ∈ T k, (‖a pq.1 - a' pq.1‖ * ‖a pq.2‖ + ‖a' pq.1‖ * ‖a pq.2 - a' pq.2‖) := by
  rw [combFeed_sub]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun pq hpq => ?_
  have h1 := hb.form_le k pq hpq (a pq.1 - a' pq.1) (sub_mem (ha _) (ha' _)) (a pq.2) (ha _)
  have h2 := hb.form_le k pq hpq (a' pq.1) (ha' _) (a pq.2 - a' pq.2) (sub_mem (ha _) (ha' _))
  calc ‖b k pq (a pq.1 - a' pq.1) (a pq.2) + b k pq (a' pq.1) (a pq.2 - a' pq.2)‖
      ≤ ‖b k pq (a pq.1 - a' pq.1) (a pq.2)‖ + ‖b k pq (a' pq.1) (a pq.2 - a' pq.2)‖ :=
        norm_add_le _ _
    _ ≤ c * w k * ‖a pq.1 - a' pq.1‖ * ‖a pq.2‖ + c * w k * ‖a' pq.1‖ * ‖a pq.2 - a' pq.2‖ :=
        add_le_add h1 h2
    _ = c * w k * (‖a pq.1 - a' pq.1‖ * ‖a pq.2‖ + ‖a' pq.1‖ * ‖a pq.2 - a' pq.2‖) := by ring

variable [Fintype ι]

/-- [proved-derived; formal-checked] **S2.** The feed of a difference read in the critical norm:
`∑ k, ‖N_k(a) - N_k(a')‖ / w k ≤ c * (A (a - a') * (A a + A a'))`. -/
theorem BilinearComb.sum_combFeed_sub_le (hb : BilinearComb w ν c T b adm) {a a' : ι → E}
    (ha : ∀ k, a k ∈ adm k) (ha' : ∀ k, a' k ∈ adm k) :
    ∑ k, ‖combFeed T b k a - combFeed T b k a'‖ / w k
      ≤ c * (amplitudeSum (a - a') * (amplitudeSum a + amplitudeSum a')) := by
  have hw := hb.weight_pos
  have hc := hb.coherence_nonneg
  calc ∑ k, ‖combFeed T b k a - combFeed T b k a'‖ / w k
      ≤ ∑ k, c * ∑ pq ∈ T k,
          (‖a pq.1 - a' pq.1‖ * ‖a pq.2‖ + ‖a' pq.1‖ * ‖a pq.2 - a' pq.2‖) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [div_le_iff₀ (hw k)]
        calc ‖combFeed T b k a - combFeed T b k a'‖
            ≤ c * w k * ∑ pq ∈ T k,
                (‖a pq.1 - a' pq.1‖ * ‖a pq.2‖ + ‖a' pq.1‖ * ‖a pq.2 - a' pq.2‖) :=
              hb.norm_combFeed_sub_le ha ha' k
          _ = c * (∑ pq ∈ T k,
                (‖a pq.1 - a' pq.1‖ * ‖a pq.2‖ + ‖a' pq.1‖ * ‖a pq.2 - a' pq.2‖)) * w k := by
              ring
    _ = c * (∑ k, ∑ pq ∈ T k, ‖a pq.1 - a' pq.1‖ * ‖a pq.2‖
          + ∑ k, ∑ pq ∈ T k, ‖a' pq.1‖ * ‖a pq.2 - a' pq.2‖) := by
        rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
        congr 1
        exact Finset.sum_congr rfl fun k _ => Finset.sum_add_distrib
    _ ≤ c * ((∑ p, ‖a p - a' p‖) * (∑ q, ‖a q‖) + (∑ p, ‖a' p‖) * ∑ q, ‖a q - a' q‖) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hc
        · exact sum_fibres_le hb.fibres_disjoint (f := fun p => ‖a p - a' p‖)
            (g := fun q => ‖a q‖) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
        · exact sum_fibres_le hb.fibres_disjoint (f := fun p => ‖a' p‖)
            (g := fun q => ‖a q - a' q‖) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    _ = c * (amplitudeSum (a - a') * (amplitudeSum a + amplitudeSum a')) := by
        unfold amplitudeSum
        simp only [Pi.sub_apply]
        ring

/-- [proved-derived; formal-checked] **S2, in the two readings.**
`∑ k, ‖N_k(a) - N_k(a')‖ / w k ≤ c / 2 * (Y δ * (X a + X a') + X δ * (Y a + Y a'))`, `δ = a - a'`. -/
theorem BilinearComb.sum_combFeed_sub_le_half (hb : BilinearComb w ν c T b adm) {a a' : ι → E}
    (ha : ∀ k, a k ∈ adm k) (ha' : ∀ k, a' k ∈ adm k) :
    ∑ k, ‖combFeed T b k a - combFeed T b k a'‖ / w k
      ≤ c / 2 * (dissipationNorm w (a - a') * (criticalNorm w a + criticalNorm w a')
          + criticalNorm w (a - a') * (dissipationNorm w a + dissipationNorm w a')) := by
  have hw := hb.weight_pos
  have hc := hb.coherence_nonneg
  have h1 := mul_le_mul_of_nonneg_left (amplitudeSum_mul_le hw (a - a') a) hc
  have h2 := mul_le_mul_of_nonneg_left (amplitudeSum_mul_le hw (a - a') a') hc
  calc ∑ k, ‖combFeed T b k a - combFeed T b k a'‖ / w k
      ≤ c * (amplitudeSum (a - a') * (amplitudeSum a + amplitudeSum a')) :=
        hb.sum_combFeed_sub_le ha ha'
    _ = c * (amplitudeSum (a - a') * amplitudeSum a)
          + c * (amplitudeSum (a - a') * amplitudeSum a') := by ring
    _ ≤ c * (1 / 2 * (dissipationNorm w (a - a') * criticalNorm w a
            + criticalNorm w (a - a') * dissipationNorm w a))
          + c * (1 / 2 * (dissipationNorm w (a - a') * criticalNorm w a'
            + criticalNorm w (a - a') * dissipationNorm w a')) := add_le_add h1 h2
    _ = c / 2 * (dissipationNorm w (a - a') * (criticalNorm w a + criticalNorm w a')
          + criticalNorm w (a - a') * (dissipationNorm w a + dissipationNorm w a')) := by ring

/-- [proved-derived; formal-checked] **S5, the split with no smallness.**
`∑ k, ‖N_k(a) - N_k(a')‖ / w k ≤ ν * Y δ + c ^ 2 / (4 * ν) * (A a + A a') ^ 2 * X δ`. -/
theorem BilinearComb.sum_combFeed_sub_le_young (hb : BilinearComb w ν c T b adm) {a a' : ι → E}
    (ha : ∀ k, a k ∈ adm k) (ha' : ∀ k, a' k ∈ adm k) :
    ∑ k, ‖combFeed T b k a - combFeed T b k a'‖ / w k
      ≤ ν * dissipationNorm w (a - a')
        + c ^ 2 / (4 * ν) * (amplitudeSum a + amplitudeSum a') ^ 2 * criticalNorm w (a - a') := by
  have hw := hb.weight_pos
  calc ∑ k, ‖combFeed T b k a - combFeed T b k a'‖ / w k
      ≤ c * (amplitudeSum (a - a') * (amplitudeSum a + amplitudeSum a')) :=
        hb.sum_combFeed_sub_le ha ha'
    _ = c * amplitudeSum (a - a') * (amplitudeSum a + amplitudeSum a') := by ring
    _ ≤ ν * dissipationNorm w (a - a')
        + c ^ 2 / (4 * ν) * (amplitudeSum a + amplitudeSum a') ^ 2 * criticalNorm w (a - a') :=
        mul_mul_le_split hb.viscosity_pos (criticalNorm_nonneg (fun k => (hw k).le) _)
          (dissipationNorm_nonneg (fun k => (hw k).le) _) (amplitudeSum_sq_le hw (a - a'))

end Form

/-! ## S3 to S6. The difference of two solutions -/

section Stability

variable {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {w : ι → ℝ} {ν c : ℝ} {T : ι → Finset (ι × ι)} {b : ι → ι × ι → E →ₗ[ℝ] E →ₗ[ℝ] E}
  {adm : ι → Submodule ℝ E} {u v : ℝ → ι → E}

/-- [proved-derived; formal-checked] The critical norm of a damped and fed family has the forward
derivative `criticalSlope` at every `0 ≤ t`; no bound is asked of the feed. -/
theorem hasDerivWithinAt_critical_of_evolves {d M : ℝ → ι → E} (hd : Evolves w ν d M) {t : ℝ}
    (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => criticalNorm w (d s)) (criticalSlope w ν d M t) (Ici t) t := by
  unfold criticalNorm criticalSlope
  refine HasDerivWithinAt.fun_sum fun k _ => ?_
  exact (hasDerivWithinAt_norm_Ici ((hd k t ht).mono (Ici_subset_Ici.mpr ht))).div_const _

/-- [proved-derived; formal-checked] The slope of the critical norm is at most the damping's
payment plus the feed read in the critical norm. -/
theorem criticalSlope_le_feed (hw : ∀ k, 0 < w k) (ν : ℝ) (d M : ℝ → ι → E) (t : ℝ) :
    criticalSlope w ν d M t ≤ -(ν * dissipationNorm w (d t)) + ∑ k, ‖M t k‖ / w k := by
  have h1 : criticalSlope w ν d M t ≤ ∑ k, (-(ν * (w k * ‖d t k‖)) + ‖M t k‖ / w k) := by
    unfold criticalSlope
    refine Finset.sum_le_sum fun k _ => ?_
    rw [div_le_iff₀ (hw k)]
    calc normSlope (d t k) (-(ν * w k ^ 2) • d t k + M t k)
        ≤ -(ν * w k ^ 2) * ‖d t k‖ + ‖M t k‖ := normSlope_damped_le _ _ _
      _ = (-(ν * (w k * ‖d t k‖)) + ‖M t k‖ / w k) * w k := by
          rw [add_mul, div_mul_cancel₀ _ (hw k).ne']
          ring
  have h2 : ∑ k, (-(ν * (w k * ‖d t k‖)) + ‖M t k‖ / w k)
      = -(ν * dissipationNorm w (d t)) + ∑ k, ‖M t k‖ / w k := by
    unfold dissipationNorm
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.mul_sum]
  rw [h2] at h1
  exact h1

/-- [definition] The forward derivative of the critical norm of the difference of two
solutions. -/
def differenceSlope (w : ι → ℝ) (ν : ℝ) (T : ι → Finset (ι × ι))
    (b : ι → ι × ι → E →ₗ[ℝ] E →ₗ[ℝ] E) (u v : ℝ → ι → E) (t : ℝ) : ℝ :=
  criticalSlope w ν (fun s => u s - v s)
    (fun s k => combFeed T b k (u s) - combFeed T b k (v s)) t

omit [Fintype ι] in
/-- [proved-derived; formal-checked] The difference of two solutions is damped by the same law
and fed by the difference of the feeds. -/
theorem Solution.sub_evolves (hu : Solution w ν T b adm u) (hv : Solution w ν T b adm v) :
    Evolves w ν (fun s => u s - v s)
      (fun s k => combFeed T b k (u s) - combFeed T b k (v s)) := by
  intro k t ht
  have h : HasDerivWithinAt (fun s => u s k - v s k)
      ((-(ν * w k ^ 2) • u t k + combFeed T b k (u t))
        - (-(ν * w k ^ 2) • v t k + combFeed T b k (v t))) (Ici 0) t :=
    (hu.evolves k t ht).fun_sub (hv.evolves k t ht)
  refine h.congr_deriv ?_
  simp only [Pi.sub_apply, smul_sub]
  abel

omit [Fintype ι] in
theorem Solution.continuousOn_mode (hu : Solution w ν T b adm u) (k : ι) :
    ContinuousOn (fun s => u s k) (Ici 0) :=
  fun t ht => (hu.evolves k t ht).continuousWithinAt

theorem Solution.continuousOn_critical_sub (hu : Solution w ν T b adm u)
    (hv : Solution w ν T b adm v) :
    ContinuousOn (fun s => criticalNorm w (u s - v s)) (Ici 0) :=
  continuousOn_criticalNorm w fun k => (hu.sub_evolves hv).continuousOn_mode k

/-- [proved-derived; formal-checked] **S3.** The critical norm of the difference has the forward
derivative `differenceSlope` at every `0 ≤ t`. -/
theorem Solution.hasDerivWithinAt_critical_sub (hu : Solution w ν T b adm u)
    (hv : Solution w ν T b adm v) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => criticalNorm w (u s - v s)) (differenceSlope w ν T b u v t)
      (Ici t) t :=
  hasDerivWithinAt_critical_of_evolves (hu.sub_evolves hv) ht

/-- The slope of the difference against the feed of the difference. -/
theorem differenceSlope_le_feed (hw : ∀ k, 0 < w k) (ν : ℝ) (T : ι → Finset (ι × ι))
    (b : ι → ι × ι → E →ₗ[ℝ] E →ₗ[ℝ] E) (u v : ℝ → ι → E) (t : ℝ) :
    differenceSlope w ν T b u v t ≤ -(ν * dissipationNorm w (u t - v t))
      + ∑ k, ‖combFeed T b k (u t) - combFeed T b k (v t)‖ / w k :=
  criticalSlope_le_feed hw ν _ _ t

/-- [proved-derived; formal-checked] **S3, the slope of the difference.**
`D⁺ X δ ≤ -(ν - c / 2 * (X u + X v)) * Y δ + c / 2 * (Y u + Y v) * X δ`. -/
theorem BilinearComb.differenceSlope_le (hb : BilinearComb w ν c T b adm)
    (hu : Solution w ν T b adm u) (hv : Solution w ν T b adm v) {t : ℝ} (ht : 0 ≤ t) :
    differenceSlope w ν T b u v t ≤
      -(ν - c / 2 * (criticalNorm w (u t) + criticalNorm w (v t)))
          * dissipationNorm w (u t - v t)
        + c / 2 * (dissipationNorm w (u t) + dissipationNorm w (v t))
          * criticalNorm w (u t - v t) := by
  have h1 := differenceSlope_le_feed hb.weight_pos ν T b u v t
  have h2 := hb.sum_combFeed_sub_le_half (hu.admissible t ht) (hv.admissible t ht)
  have h3 : -(ν - c / 2 * (criticalNorm w (u t) + criticalNorm w (v t)))
          * dissipationNorm w (u t - v t)
        + c / 2 * (dissipationNorm w (u t) + dissipationNorm w (v t))
          * criticalNorm w (u t - v t)
      = -(ν * dissipationNorm w (u t - v t))
        + c / 2 * (dissipationNorm w (u t - v t) * (criticalNorm w (u t) + criticalNorm w (v t))
          + criticalNorm w (u t - v t) * (dissipationNorm w (u t) + dissipationNorm w (v t))) := by
    ring
  rw [h3]
  linarith

/-- [proved-derived; formal-checked] **S4.** In the laminar class of both solutions,
`X δ t ≤ X δ 0 * exp (c / 2 * ∫ s in 0..t, (Y (u s) + Y (v s)))`. -/
theorem BilinearComb.critical_sub_le_mul_exp (hb : BilinearComb w ν c T b adm)
    (hu : Solution w ν T b adm u) (hv : Solution w ν T b adm v)
    (hu0 : c * criticalNorm w (u 0) < ν) (hv0 : c * criticalNorm w (v 0) < ν) {t : ℝ}
    (ht : 0 ≤ t) :
    criticalNorm w (u t - v t) ≤ criticalNorm w (u 0 - v 0) *
      Real.exp (c / 2 * ∫ s in (0 : ℝ)..t, (dissipationNorm w (u s) + dissipationNorm w (v s))) := by
  have hw := hb.weight_pos
  have hc := hb.coherence_nonneg
  have hU := hu.combSystem hb
  have hV := hv.combSystem hb
  have hg : ContinuousOn
      (fun s => c / 2 * (dissipationNorm w (u s) + dissipationNorm w (v s))) (Ici 0) :=
    continuousOn_const.mul (hU.continuousOn_dissipation.add hV.continuousOn_dissipation)
  have key : criticalNorm w (u t - v t) ≤ criticalNorm w (u 0 - v 0) *
      Real.exp (∫ s in (0 : ℝ)..t,
        c / 2 * (dissipationNorm w (u s) + dissipationNorm w (v s))) :=
    le_mul_exp_integral_of_slope_le
      (f := fun s => criticalNorm w (u s - v s)) (f' := differenceSlope w ν T b u v)
      (g := fun s => c / 2 * (dissipationNorm w (u s) + dissipationNorm w (v s)))
      (hu.continuousOn_critical_sub hv)
      (fun x hx => hu.hasDerivWithinAt_critical_sub hv hx) hg
      (fun x hx => by
        have hs := hb.differenceSlope_le hu hv hx
        have hXu := mul_le_mul_of_nonneg_left (hU.critical_le_initial hu0 hx) hc
        have hXv := mul_le_mul_of_nonneg_left (hV.critical_le_initial hv0 hx) hc
        have hY : 0 ≤ dissipationNorm w (u x - v x) :=
          dissipationNorm_nonneg (fun k => (hw k).le) _
        have h1 : 0 ≤ ν - c / 2 * (criticalNorm w (u x) + criticalNorm w (v x)) := by linarith
        have h2 := mul_nonneg h1 hY
        show differenceSlope w ν T b u v x ≤
          c / 2 * (dissipationNorm w (u x) + dissipationNorm w (v x))
            * criticalNorm w (u x - v x)
        linarith) ht
  rw [intervalIntegral.integral_const_mul] at key
  exact key

/-- The dissipation integrals of two solutions in the laminar class. -/
theorem BilinearComb.half_integral_dissipation_le (hb : BilinearComb w ν c T b adm)
    (hu : Solution w ν T b adm u) (hv : Solution w ν T b adm v)
    (hu0 : c * criticalNorm w (u 0) < ν) (hv0 : c * criticalNorm w (v 0) < ν) {t : ℝ}
    (ht : 0 ≤ t) :
    c / 2 * ∫ s in (0 : ℝ)..t, (dissipationNorm w (u s) + dissipationNorm w (v s))
      ≤ c / 2 * (criticalNorm w (u 0) / (ν - c * criticalNorm w (u 0))
        + criticalNorm w (v 0) / (ν - c * criticalNorm w (v 0))) := by
  have hU := hu.combSystem hb
  have hV := hv.combSystem hb
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hb.coherence_nonneg zero_le_two)
  rw [intervalIntegral.integral_add
    (intervalIntegrable_of_continuousOn_Ici hU.continuousOn_dissipation ht)
    (intervalIntegrable_of_continuousOn_Ici hV.continuousOn_dissipation ht)]
  exact add_le_add (hU.integral_dissipation_le hu0 ht) (hV.integral_dissipation_le hv0 ht)

/-- [proved-derived; formal-checked] **S4, stability of the laminar class.** If
`c * X (u 0) < ν` and `c * X (v 0) < ν`, two solutions stay within the fixed multiple
`K = stabilityConstant w ν c (u 0) (v 0)` of their opening distance at every `0 ≤ t`. -/
theorem BilinearComb.critical_sub_le (hb : BilinearComb w ν c T b adm)
    (hu : Solution w ν T b adm u) (hv : Solution w ν T b adm v)
    (hu0 : c * criticalNorm w (u 0) < ν) (hv0 : c * criticalNorm w (v 0) < ν) {t : ℝ}
    (ht : 0 ≤ t) :
    criticalNorm w (u t - v t) ≤
      stabilityConstant w ν c (u 0) (v 0) * criticalNorm w (u 0 - v 0) := by
  have h1 := hb.critical_sub_le_mul_exp hu hv hu0 hv0 ht
  have h2 := Real.exp_le_exp.mpr (hb.half_integral_dissipation_le hu hv hu0 hv0 ht)
  have h3 : 0 ≤ criticalNorm w (u 0 - v 0) :=
    criticalNorm_nonneg (fun k => (hb.weight_pos k).le) _
  calc criticalNorm w (u t - v t)
      ≤ criticalNorm w (u 0 - v 0) * Real.exp (c / 2 *
          ∫ s in (0 : ℝ)..t, (dissipationNorm w (u s) + dissipationNorm w (v s))) := h1
    _ ≤ criticalNorm w (u 0 - v 0) * stabilityConstant w ν c (u 0) (v 0) :=
        mul_le_mul_of_nonneg_left h2 h3
    _ = stabilityConstant w ν c (u 0) (v 0) * criticalNorm w (u 0 - v 0) := mul_comm _ _

/-- [proved-derived; formal-checked] **S4, with a constant that names no mode.** If both opening
readings are at most `R` and `c * R < ν`, then `X δ t ≤ exp (c * R / (ν - c * R)) * X δ 0`. -/
theorem BilinearComb.critical_sub_le_of_le (hb : BilinearComb w ν c T b adm)
    (hu : Solution w ν T b adm u) (hv : Solution w ν T b adm v) {R : ℝ} (hR : c * R < ν)
    (huR : criticalNorm w (u 0) ≤ R) (hvR : criticalNorm w (v 0) ≤ R) {t : ℝ} (ht : 0 ≤ t) :
    criticalNorm w (u t - v t) ≤
      Real.exp (c * R / (ν - c * R)) * criticalNorm w (u 0 - v 0) := by
  have hc := hb.coherence_nonneg
  have hu0 : c * criticalNorm w (u 0) < ν :=
    (mul_le_mul_of_nonneg_left huR hc).trans_lt hR
  have hv0 : c * criticalNorm w (v 0) < ν :=
    (mul_le_mul_of_nonneg_left hvR hc).trans_lt hR
  refine (hb.critical_sub_le hu hv hu0 hv0 ht).trans ?_
  exact mul_le_mul_of_nonneg_right (stabilityConstant_le hb.weight_pos hc hR huR hvR)
    (criticalNorm_nonneg (fun k => (hb.weight_pos k).le) _)

/-- [proved-derived; formal-checked] **S5, continuous dependence with no smallness.** For any two
solutions, `X δ t ≤ X δ 0 * exp (c ^ 2 / (4 * ν) * ∫ s in 0..t, (A (u s) + A (v s)) ^ 2)`. -/
theorem BilinearComb.critical_sub_le_mul_exp_sq (hb : BilinearComb w ν c T b adm)
    (hu : Solution w ν T b adm u) (hv : Solution w ν T b adm v) {t : ℝ} (ht : 0 ≤ t) :
    criticalNorm w (u t - v t) ≤ criticalNorm w (u 0 - v 0) *
      Real.exp (c ^ 2 / (4 * ν) *
        ∫ s in (0 : ℝ)..t, (amplitudeSum (u s) + amplitudeSum (v s)) ^ 2) := by
  have hw := hb.weight_pos
  have hg : ContinuousOn
      (fun s => c ^ 2 / (4 * ν) * (amplitudeSum (u s) + amplitudeSum (v s)) ^ 2) (Ici 0) :=
    continuousOn_const.mul (((continuousOn_amplitudeSum hu.continuousOn_mode).add
      (continuousOn_amplitudeSum hv.continuousOn_mode)).pow 2)
  have key : criticalNorm w (u t - v t) ≤ criticalNorm w (u 0 - v 0) *
      Real.exp (∫ s in (0 : ℝ)..t,
        c ^ 2 / (4 * ν) * (amplitudeSum (u s) + amplitudeSum (v s)) ^ 2) :=
    le_mul_exp_integral_of_slope_le
      (f := fun s => criticalNorm w (u s - v s)) (f' := differenceSlope w ν T b u v)
      (g := fun s => c ^ 2 / (4 * ν) * (amplitudeSum (u s) + amplitudeSum (v s)) ^ 2)
      (hu.continuousOn_critical_sub hv)
      (fun x hx => hu.hasDerivWithinAt_critical_sub hv hx) hg
      (fun x hx => by
        have h1 := differenceSlope_le_feed hw ν T b u v x
        have h2 := hb.sum_combFeed_sub_le_young (hu.admissible x hx) (hv.admissible x hx)
        show differenceSlope w ν T b u v x ≤
          c ^ 2 / (4 * ν) * (amplitudeSum (u x) + amplitudeSum (v x)) ^ 2
            * criticalNorm w (u x - v x)
        linarith) ht
  rw [intervalIntegral.integral_const_mul] at key
  exact key

/-- [proved-derived; formal-checked] **S5, the opening state decides the solution.** Two
solutions of a bilinear comb with one opening state agree at every `0 ≤ t`, at every size of the
data. -/
theorem BilinearComb.eq_of_initial_eq (hb : BilinearComb w ν c T b adm)
    (hu : Solution w ν T b adm u) (hv : Solution w ν T b adm v) (h0 : u 0 = v 0) {t : ℝ}
    (ht : 0 ≤ t) : u t = v t := by
  have h1 := hb.critical_sub_le_mul_exp_sq hu hv ht
  have h2 : criticalNorm w (u 0 - v 0) = 0 := by
    rw [h0, sub_self]
    simp [criticalNorm]
  rw [h2, zero_mul] at h1
  exact sub_eq_zero.mp (eq_zero_of_criticalNorm_le_zero hb.weight_pos h1)

/-- [proved-derived; formal-checked] **S5 inside the laminar class**, read from S4's bound. -/
theorem BilinearComb.eq_of_initial_eq_of_laminar (hb : BilinearComb w ν c T b adm)
    (hu : Solution w ν T b adm u) (hv : Solution w ν T b adm v)
    (hu0 : c * criticalNorm w (u 0) < ν) (h0 : u 0 = v 0) {t : ℝ} (ht : 0 ≤ t) :
    u t = v t := by
  have hv0 : c * criticalNorm w (v 0) < ν := by rwa [← h0]
  have h1 := hb.critical_sub_le hu hv hu0 hv0 ht
  have h2 : criticalNorm w (u 0 - v 0) = 0 := by
    rw [h0, sub_self]
    simp [criticalNorm]
  rw [h2, mul_zero] at h1
  exact sub_eq_zero.mp (eq_zero_of_criticalNorm_le_zero hb.weight_pos h1)

/-- [proved-derived; formal-checked] **S6, relaxation at the rate of the lowest mode.** In the
laminar class of a comb system whose weights are at least `w₀ > 0`,
`X (u t) ≤ X (u 0) * exp (-(ν - c * X (u 0)) * w₀ ^ 2 * t)`. -/
theorem _root_.Holonics.Fluid.LaminarClass.CombSystem.critical_le_mul_exp_decay
    {N : ℝ → ι → E} (h : CombSystem w ν c T u N) (h0 : c * criticalNorm w (u 0) < ν) {w₀ : ℝ}
    (hw₀ : 0 < w₀) (hle : ∀ k, w₀ ≤ w k) {t : ℝ} (ht : 0 ≤ t) :
    criticalNorm w (u t) ≤ criticalNorm w (u 0) *
      Real.exp (-(ν - c * criticalNorm w (u 0)) * w₀ ^ 2 * t) := by
  have hw := h.weight_pos
  have key : criticalNorm w (u t) ≤ criticalNorm w (u 0) *
      Real.exp (∫ _ in (0 : ℝ)..t, -(ν - c * criticalNorm w (u 0)) * w₀ ^ 2) :=
    le_mul_exp_integral_of_slope_le
      (f := fun s => criticalNorm w (u s)) (f' := criticalSlope w ν u N)
      (g := fun _ => -(ν - c * criticalNorm w (u 0)) * w₀ ^ 2)
      h.continuousOn_critical (fun x hx => h.hasDerivWithinAt_critical hx) continuousOn_const
      (fun x hx => by
        have hs := h.criticalSlope_le hx
        have hX := mul_le_mul_of_nonneg_left (h.critical_le_initial h0 hx) h.coherence_nonneg
        have hY := sq_mul_criticalNorm_le_dissipationNorm hw₀ hle (u x)
        have hY0 : 0 ≤ dissipationNorm w (u x) := dissipationNorm_nonneg (fun k => (hw k).le) _
        have hμ : 0 ≤ ν - c * criticalNorm w (u 0) := by linarith
        have h1 := mul_nonneg (sub_nonneg.mpr hX) hY0
        have h2 := mul_nonneg hμ (sub_nonneg.mpr hY)
        show criticalSlope w ν u N x ≤
          -(ν - c * criticalNorm w (u 0)) * w₀ ^ 2 * criticalNorm w (u x)
        linarith) ht
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at key
  have he : t * (-(ν - c * criticalNorm w (u 0)) * w₀ ^ 2)
      = -(ν - c * criticalNorm w (u 0)) * w₀ ^ 2 * t := by ring
  rwa [he] at key

/-- [proved-derived; formal-checked] **S6, the difference relaxes.** For any `m` over both
opening readings with `c * m < ν`, and weights at least `w₀ > 0`,
`X δ t ≤ K * X δ 0 * exp (-(ν - c * m) * w₀ ^ 2 * t)` with `K` the stability constant. -/
theorem BilinearComb.critical_sub_le_mul_exp_decay_of_le (hb : BilinearComb w ν c T b adm)
    (hu : Solution w ν T b adm u) (hv : Solution w ν T b adm v) {m : ℝ}
    (hmu : criticalNorm w (u 0) ≤ m) (hmv : criticalNorm w (v 0) ≤ m) (hm : c * m < ν)
    {w₀ : ℝ} (hw₀ : 0 < w₀) (hle : ∀ k, w₀ ≤ w k) {t : ℝ} (ht : 0 ≤ t) :
    criticalNorm w (u t - v t) ≤
      stabilityConstant w ν c (u 0) (v 0) * criticalNorm w (u 0 - v 0) *
        Real.exp (-(ν - c * m) * w₀ ^ 2 * t) := by
  have hw := hb.weight_pos
  have hc := hb.coherence_nonneg
  have hU := hu.combSystem hb
  have hV := hv.combSystem hb
  have hu0 : c * criticalNorm w (u 0) < ν := (mul_le_mul_of_nonneg_left hmu hc).trans_lt hm
  have hv0 : c * criticalNorm w (v 0) < ν := (mul_le_mul_of_nonneg_left hmv hc).trans_lt hm
  have hμ : 0 ≤ ν - c * m := by linarith
  have hYc : ContinuousOn
      (fun s => dissipationNorm w (u s) + dissipationNorm w (v s)) (Ici 0) :=
    hU.continuousOn_dissipation.add hV.continuousOn_dissipation
  have hg : ContinuousOn (fun s => -((ν - c * m) * w₀ ^ 2)
      + c / 2 * (dissipationNorm w (u s) + dissipationNorm w (v s))) (Ici 0) :=
    continuousOn_const.add (continuousOn_const.mul hYc)
  have key : criticalNorm w (u t - v t) ≤ criticalNorm w (u 0 - v 0) *
      Real.exp (∫ s in (0 : ℝ)..t, (-((ν - c * m) * w₀ ^ 2)
        + c / 2 * (dissipationNorm w (u s) + dissipationNorm w (v s)))) :=
    le_mul_exp_integral_of_slope_le
      (f := fun s => criticalNorm w (u s - v s)) (f' := differenceSlope w ν T b u v)
      (g := fun s => -((ν - c * m) * w₀ ^ 2)
        + c / 2 * (dissipationNorm w (u s) + dissipationNorm w (v s)))
      (hu.continuousOn_critical_sub hv)
      (fun x hx => hu.hasDerivWithinAt_critical_sub hv hx) hg
      (fun x hx => by
        have hs := hb.differenceSlope_le hu hv hx
        have hXu := mul_le_mul_of_nonneg_left ((hU.critical_le_initial hu0 hx).trans hmu) hc
        have hXv := mul_le_mul_of_nonneg_left ((hV.critical_le_initial hv0 hx).trans hmv) hc
        have hY := sq_mul_criticalNorm_le_dissipationNorm hw₀ hle (u x - v x)
        have hY0 : 0 ≤ dissipationNorm w (u x - v x) :=
          dissipationNorm_nonneg (fun k => (hw k).le) _
        have h1 : 0 ≤ c * m - c / 2 * (criticalNorm w (u x) + criticalNorm w (v x)) := by
          linarith
        have h2 := mul_nonneg h1 hY0
        have h3 := mul_nonneg hμ (sub_nonneg.mpr hY)
        show differenceSlope w ν T b u v x ≤
          (-((ν - c * m) * w₀ ^ 2)
            + c / 2 * (dissipationNorm w (u x) + dissipationNorm w (v x)))
            * criticalNorm w (u x - v x)
        linarith) ht
  have hI : ∫ s in (0 : ℝ)..t, (-((ν - c * m) * w₀ ^ 2)
        + c / 2 * (dissipationNorm w (u s) + dissipationNorm w (v s)))
      = -(ν - c * m) * w₀ ^ 2 * t
        + c / 2 * ∫ s in (0 : ℝ)..t, (dissipationNorm w (u s) + dissipationNorm w (v s)) := by
    rw [intervalIntegral.integral_add intervalIntegrable_const
      ((intervalIntegrable_of_continuousOn_Ici hYc ht).const_mul _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul,
      sub_zero]
    ring
  rw [hI, Real.exp_add] at key
  have h2 := Real.exp_le_exp.mpr (hb.half_integral_dissipation_le hu hv hu0 hv0 ht)
  have h3 : 0 ≤ criticalNorm w (u 0 - v 0) := criticalNorm_nonneg (fun k => (hw k).le) _
  have h4 := (Real.exp_pos (-(ν - c * m) * w₀ ^ 2 * t)).le
  calc criticalNorm w (u t - v t)
      ≤ criticalNorm w (u 0 - v 0) * (Real.exp (-(ν - c * m) * w₀ ^ 2 * t) *
          Real.exp (c / 2 *
            ∫ s in (0 : ℝ)..t, (dissipationNorm w (u s) + dissipationNorm w (v s)))) := key
    _ ≤ criticalNorm w (u 0 - v 0) * (Real.exp (-(ν - c * m) * w₀ ^ 2 * t) *
          stabilityConstant w ν c (u 0) (v 0)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 h4) h3
    _ = stabilityConstant w ν c (u 0) (v 0) * criticalNorm w (u 0 - v 0) *
          Real.exp (-(ν - c * m) * w₀ ^ 2 * t) := by ring

/-- [proved-derived; formal-checked] **S6.** In the laminar class of both solutions the
difference relaxes at the rate of the lowest mode:
`X δ t ≤ K * X δ 0 * exp (-(ν - c * max (X (u 0)) (X (v 0))) * w₀ ^ 2 * t)`. -/
theorem BilinearComb.critical_sub_le_mul_exp_decay (hb : BilinearComb w ν c T b adm)
    (hu : Solution w ν T b adm u) (hv : Solution w ν T b adm v)
    (hu0 : c * criticalNorm w (u 0) < ν) (hv0 : c * criticalNorm w (v 0) < ν) {w₀ : ℝ}
    (hw₀ : 0 < w₀) (hle : ∀ k, w₀ ≤ w k) {t : ℝ} (ht : 0 ≤ t) :
    criticalNorm w (u t - v t) ≤
      stabilityConstant w ν c (u 0) (v 0) * criticalNorm w (u 0 - v 0) *
        Real.exp (-(ν - c * max (criticalNorm w (u 0)) (criticalNorm w (v 0))) * w₀ ^ 2 * t) := by
  have hm : c * max (criticalNorm w (u 0)) (criticalNorm w (v 0)) < ν := by
    rcases max_choice (criticalNorm w (u 0)) (criticalNorm w (v 0)) with h | h <;> rw [h] <;>
      assumption
  exact hb.critical_sub_le_mul_exp_decay_of_le hu hv (le_max_left _ _) (le_max_right _ _) hm
    hw₀ hle ht

end Stability

/-! ## S7. The truncated fluid is a bilinear comb -/

section Fluid

variable {ι : Type*} [Fintype ι] {n : Type*} [Fintype n]

/-- The wave pairing is additive in the amplitude. -/
theorem wavePairing_add_right (q : EuclideanSpace ℝ n) (x y : EuclideanSpace ℂ n) :
    wavePairing q (x + y) = wavePairing q x + wavePairing q y := by
  simp only [wavePairing_eq_inner, inner_add_right]

/-- The wave pairing is complex homogeneous in the amplitude. -/
theorem wavePairing_smul_right (q : EuclideanSpace ℝ n) (z : ℂ) (x : EuclideanSpace ℂ n) :
    wavePairing q (z • x) = z * wavePairing q x := by
  simp only [wavePairing_eq_inner, inner_smul_right]

/-- [definition] The transport form of the truncated fluid for the triad `pq` of the mode `k`:
`(x, y) ↦ (-i) • P k ((κ q · x) • y)`, complex bilinear, read over the reals. -/
def transportForm (κ : ι → EuclideanSpace ℝ n)
    (P : ι → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (k : ι) (pq : ι × ι) :
    EuclideanSpace ℂ n →ₗ[ℝ] EuclideanSpace ℂ n →ₗ[ℝ] EuclideanSpace ℂ n :=
  LinearMap.restrictScalars₁₂ ℝ ℝ
    (LinearMap.mk₂ ℂ (fun x y => (-Complex.I) • P k (wavePairing (κ pq.2) x • y))
      (fun x x' y => by rw [wavePairing_add_right, add_smul, map_add, smul_add])
      (fun z x y => by rw [wavePairing_smul_right, mul_smul, map_smul, smul_comm])
      (fun x y y' => by rw [smul_add, map_add, smul_add])
      (fun z x y => by
        rw [smul_comm (wavePairing (κ pq.2) x) z y, map_smul, smul_comm]))

omit [Fintype ι] in
theorem transportForm_apply (κ : ι → EuclideanSpace ℝ n)
    (P : ι → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (k : ι) (pq : ι × ι)
    (x y : EuclideanSpace ℂ n) :
    transportForm κ P k pq x y = (-Complex.I) • P k (wavePairing (κ pq.2) x • y) :=
  rfl

/-- [definition] The admissible amplitudes of the mode `p`: those across its wave vector, a real
subspace of the complex amplitude space. -/
def across (κ : ι → EuclideanSpace ℝ n) (p : ι) : Submodule ℝ (EuclideanSpace ℂ n) :=
  ((ℂ ∙ complexify (κ p))ᗮ).restrictScalars ℝ

omit [Fintype ι] in
theorem mem_across {κ : ι → EuclideanSpace ℝ n} {p : ι} {x : EuclideanSpace ℂ n} :
    x ∈ across κ p ↔ wavePairing (κ p) x = 0 := by
  unfold across
  rw [Submodule.restrictScalars_mem, Submodule.mem_orthogonal_singleton_iff_inner_right,
    wavePairing_eq_inner]

variable {κ : ι → EuclideanSpace ℝ n} {ν : ℝ}
  {P : ι → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n} {a a' : ℝ → ι → EuclideanSpace ℂ n}

/-- [proved-derived; formal-checked] The fluid's feed is the feed of the bilinear comb of its
transport forms over its triads. -/
theorem combFeed_transportForm (κ : ι → EuclideanSpace ℝ n)
    (P : ι → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (x : ι → EuclideanSpace ℂ n) (k : ι) :
    combFeed (triads κ) (transportForm κ P) k x = feed κ P x k := by
  unfold combFeed feed
  simp only [transportForm_apply]
  rw [map_sum, Finset.smul_sum]

/-- [proved-derived; formal-checked] The transport form meets the comb's bound with weight
`‖κ k‖` and coherence constant one, on amplitudes across the first wave vector of the triad. -/
theorem norm_transportForm_le (hP : ∀ k, ‖P k‖ ≤ 1) {k : ι} {pq : ι × ι}
    (hpq : pq ∈ triads κ k) {x : EuclideanSpace ℂ n} (hx : wavePairing (κ pq.1) x = 0)
    (y : EuclideanSpace ℂ n) :
    ‖transportForm κ P k pq x y‖ ≤ 1 * ‖κ k‖ * ‖x‖ * ‖y‖ := by
  rw [transportForm_apply, norm_smul, norm_neg, Complex.norm_I, one_mul, one_mul]
  exact norm_projected_transport_le (mem_triads.mp hpq).symm hx y (P k) (hP k)

/-- [proved-derived; formal-checked] **S7.** Distinct nonzero wave vectors, a positive viscosity
and projections of norm at most one make a bilinear comb with weights `‖κ k‖`, coherence
constant one, the comb of the triads, the transport forms and the amplitudes across the wave
vectors. -/
theorem bilinearComb_of_waves (hκ : Function.Injective κ) (hκ0 : ∀ k, κ k ≠ 0) (hν : 0 < ν)
    (hP : ∀ k, ‖P k‖ ≤ 1) :
    BilinearComb (fun k => ‖κ k‖) ν 1 (triads κ) (transportForm κ P) (across κ) where
  weight_pos k := norm_pos_iff.mpr (hκ0 k)
  viscosity_pos := hν
  coherence_nonneg := zero_le_one
  fibres_disjoint := triads_disjoint hκ
  form_le _ _ hpq _ hx y _ := norm_transportForm_le hP hpq (mem_across.mp hx) y

/-- [proved-derived; formal-checked] A truncation's law is a bilinear comb. -/
theorem _root_.Holonics.Fluid.GalerkinInstance.Truncation.bilinearComb
    (h : Truncation κ ν P a) :
    BilinearComb (fun k => ‖κ k‖) ν 1 (triads κ) (transportForm κ P) (across κ) :=
  bilinearComb_of_waves h.wave_injective h.wave_ne_zero h.viscosity_pos h.projection_le

/-- [proved-derived; formal-checked] A truncation is a solution of its bilinear comb. -/
theorem _root_.Holonics.Fluid.GalerkinInstance.Truncation.solution (h : Truncation κ ν P a) :
    Solution (fun k => ‖κ k‖) ν (triads κ) (transportForm κ P) (across κ) a where
  admissible t ht k := mem_across.mpr (h.incompressible t ht k)
  evolves k t ht := by
    rw [combFeed_transportForm]
    exact h.evolves k t ht

/-- [proved-derived; formal-checked] **Stability of the truncated fluid's laminar class.** Two
truncations of one law with `X (a 0) < ν` and `X (a' 0) < ν` stay within the fixed multiple
`stabilityConstant` of their opening distance, the same at every truncation. -/
theorem _root_.Holonics.Fluid.GalerkinInstance.Truncation.critical_sub_le
    (h : Truncation κ ν P a) (h' : Truncation κ ν P a')
    (h0 : criticalNorm (fun k => ‖κ k‖) (a 0) < ν)
    (h0' : criticalNorm (fun k => ‖κ k‖) (a' 0) < ν) {t : ℝ} (ht : 0 ≤ t) :
    criticalNorm (fun k => ‖κ k‖) (a t - a' t) ≤
      stabilityConstant (fun k => ‖κ k‖) ν 1 (a 0) (a' 0)
        * criticalNorm (fun k => ‖κ k‖) (a 0 - a' 0) := by
  let _ : InnerProductSpace ℝ (EuclideanSpace ℂ n) := InnerProductSpace.complexToReal
  exact BilinearComb.critical_sub_le h.bilinearComb h.solution h'.solution (by rwa [one_mul])
    (by rwa [one_mul]) ht

/-- [proved-derived; formal-checked] **One constant for every truncation.** If both opening
readings are at most `R < ν` then `X δ t ≤ exp (R / (ν - R)) * X δ 0`, whatever the set of
modes. -/
theorem _root_.Holonics.Fluid.GalerkinInstance.Truncation.critical_sub_le_of_le
    (h : Truncation κ ν P a) (h' : Truncation κ ν P a') {R : ℝ} (hR : R < ν)
    (haR : criticalNorm (fun k => ‖κ k‖) (a 0) ≤ R)
    (haR' : criticalNorm (fun k => ‖κ k‖) (a' 0) ≤ R) {t : ℝ} (ht : 0 ≤ t) :
    criticalNorm (fun k => ‖κ k‖) (a t - a' t) ≤
      Real.exp (R / (ν - R)) * criticalNorm (fun k => ‖κ k‖) (a 0 - a' 0) := by
  let _ : InnerProductSpace ℝ (EuclideanSpace ℂ n) := InnerProductSpace.complexToReal
  have key := BilinearComb.critical_sub_le_of_le h.bilinearComb h.solution h'.solution
    (R := R) (by rwa [one_mul]) haR haR' ht
  rwa [one_mul] at key

/-- [proved-derived; formal-checked] **The opening state decides the truncation's solution**, at
every size of the data and at every truncation. -/
theorem _root_.Holonics.Fluid.GalerkinInstance.Truncation.eq_of_initial_eq
    (h : Truncation κ ν P a) (h' : Truncation κ ν P a') (h0 : a 0 = a' 0) {t : ℝ}
    (ht : 0 ≤ t) : a t = a' t := by
  let _ : InnerProductSpace ℝ (EuclideanSpace ℂ n) := InnerProductSpace.complexToReal
  exact BilinearComb.eq_of_initial_eq h.bilinearComb h.solution h'.solution h0 ht

/-- [proved-derived; formal-checked] **The truncated fluid's laminar class relaxes at the rate of
its lowest mode**: with `w₀ ≤ ‖κ k‖`, `X (a t) ≤ X (a 0) * exp (-(ν - X (a 0)) * w₀ ^ 2 * t)`. -/
theorem _root_.Holonics.Fluid.GalerkinInstance.Truncation.critical_le_mul_exp_decay
    (h : Truncation κ ν P a) (h0 : criticalNorm (fun k => ‖κ k‖) (a 0) < ν) {w₀ : ℝ}
    (hw₀ : 0 < w₀) (hle : ∀ k, w₀ ≤ ‖κ k‖) {t : ℝ} (ht : 0 ≤ t) :
    criticalNorm (fun k => ‖κ k‖) (a t) ≤ criticalNorm (fun k => ‖κ k‖) (a 0) *
      Real.exp (-(ν - criticalNorm (fun k => ‖κ k‖) (a 0)) * w₀ ^ 2 * t) := by
  let _ : InnerProductSpace ℝ (EuclideanSpace ℂ n) := InnerProductSpace.complexToReal
  have key := CombSystem.critical_le_mul_exp_decay h.combSystem (by rwa [one_mul]) hw₀ hle ht
  rwa [one_mul] at key

/-- [proved-derived; formal-checked] **The difference of two truncations relaxes** at the rate of
the lowest mode, with the stability constant of their opening states. -/
theorem _root_.Holonics.Fluid.GalerkinInstance.Truncation.critical_sub_le_mul_exp_decay
    (h : Truncation κ ν P a) (h' : Truncation κ ν P a')
    (h0 : criticalNorm (fun k => ‖κ k‖) (a 0) < ν)
    (h0' : criticalNorm (fun k => ‖κ k‖) (a' 0) < ν) {w₀ : ℝ} (hw₀ : 0 < w₀)
    (hle : ∀ k, w₀ ≤ ‖κ k‖) {t : ℝ} (ht : 0 ≤ t) :
    criticalNorm (fun k => ‖κ k‖) (a t - a' t) ≤
      stabilityConstant (fun k => ‖κ k‖) ν 1 (a 0) (a' 0)
        * criticalNorm (fun k => ‖κ k‖) (a 0 - a' 0)
        * Real.exp (-(ν - max (criticalNorm (fun k => ‖κ k‖) (a 0))
            (criticalNorm (fun k => ‖κ k‖) (a' 0))) * w₀ ^ 2 * t) := by
  let _ : InnerProductSpace ℝ (EuclideanSpace ℂ n) := InnerProductSpace.complexToReal
  have key := BilinearComb.critical_sub_le_mul_exp_decay h.bilinearComb h.solution h'.solution
    (by rwa [one_mul]) (by rwa [one_mul]) hw₀ hle ht
  rwa [one_mul] at key

end Fluid

section Audit

#print axioms le_mul_exp_integral_of_slope_le
#print axioms Solution.combSystem
#print axioms combFeed_sub
#print axioms BilinearComb.sum_combFeed_sub_le
#print axioms BilinearComb.sum_combFeed_sub_le_half
#print axioms BilinearComb.sum_combFeed_sub_le_young
#print axioms Solution.hasDerivWithinAt_critical_sub
#print axioms BilinearComb.differenceSlope_le
#print axioms BilinearComb.critical_sub_le_mul_exp
#print axioms BilinearComb.critical_sub_le
#print axioms BilinearComb.critical_sub_le_of_le
#print axioms BilinearComb.critical_sub_le_mul_exp_sq
#print axioms BilinearComb.eq_of_initial_eq
#print axioms BilinearComb.eq_of_initial_eq_of_laminar
#print axioms sq_mul_criticalNorm_le_dissipationNorm
#print axioms CombSystem.critical_le_mul_exp_decay
#print axioms BilinearComb.critical_sub_le_mul_exp_decay_of_le
#print axioms BilinearComb.critical_sub_le_mul_exp_decay
#print axioms combFeed_transportForm
#print axioms bilinearComb_of_waves
#print axioms Truncation.solution
#print axioms Truncation.critical_sub_le
#print axioms Truncation.critical_sub_le_of_le
#print axioms Truncation.eq_of_initial_eq
#print axioms Truncation.critical_le_mul_exp_decay
#print axioms Truncation.critical_sub_le_mul_exp_decay

end Audit

end Holonics.Fluid.LaminarStability
