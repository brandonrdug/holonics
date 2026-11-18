import Mathlib

/-!
# The laminar class of a comb system: a count that decides at every truncation alike

This module states and proves the a priori estimate of Lei and Lin (2011) for finite mode systems
of Navier-Stokes type, in the comb vocabulary. It imports Mathlib alone.

[definition] A **comb system** is a finite family of modes `u t k` in a real normed space, each
with a positive weight `w k` (its wave number), damped at the rate `ν * w k ^ 2` and fed by
`N t k`:

  `d/dt u_k = -(ν * w_k ^ 2) • u_k + N_k`,
  `‖N_k‖ ≤ c * w_k * ∑_{(p, q) ∈ T k} ‖u_p‖ * ‖u_q‖`.

The comb `T` sends each mode to a finite set of pairs (its triads), and the fibres `T k` are
pairwise disjoint: a pair of modes feeds at most one mode (`k = p + q`). The constant `c ≥ 0` is
the coherence constant of the feed: the count's own bound is `c = 1`, and a feed whose phases
cancel has a smaller one. The derivative is taken on `[0, ∞)`, that is as
`HasDerivWithinAt … (Ici 0) t` for every `0 ≤ t`; `CombSystem.of_hasDerivAt` builds a comb system
from derivatives on the whole line.

[definition] Two readings of a configuration `a : ι → E`:

* `criticalNorm w a = ∑ k, ‖a k‖ / w k`, the scale-critical norm (`X`);
* `dissipationNorm w a = ∑ k, w k * ‖a k‖`, the norm the damping pays in (`Y`);

with `amplitudeSum a = ∑ k, ‖a k‖` between them, and `reynolds w ν a = criticalNorm w a / ν`
the dimensionless reading.

[proved-derived; formal-checked] The algebra, in any normed group:

* `amplitudeSum_sq_le`: `amplitudeSum a ^ 2 ≤ criticalNorm w a * dissipationNorm w a`
  (Cauchy-Schwarz);
* `feed_sum_le`: `∑ k, ‖n k‖ / w k ≤ c * amplitudeSum a ^ 2`, by the fibres' disjointness;
* `feed_sum_le_critical_mul_dissipation`: hence `≤ c * (criticalNorm w a * dissipationNorm w a)`.

[proved-derived; formal-checked] The right derivative of a norm, in a real inner product space:

* `hasDerivWithinAt_norm_Ici`: if `f` has the right derivative `f'` at `t` then `s ↦ ‖f s‖` has
  the right derivative `normSlope (f t) f'` at `t`, where `normSlope x v = ⟪x, v⟫ / ‖x‖` for
  `x ≠ 0` and `normSlope 0 v = ‖v‖`;
* `normSlope_damped_le`: `normSlope x (-c • x + n) ≤ -c * ‖x‖ + ‖n‖`.

[proved-derived; formal-checked] The laminar class. For a comb system with
`c * criticalNorm w (u 0) < ν`, and every `0 ≤ t`:

* `CombSystem.criticalSlope_le`: the right derivative of `X` is at most `-(ν - c * X) * Y`;
* `CombSystem.critical_le_initial`: `X t ≤ X 0`;
* `CombSystem.dissipation_integral_le_drop`: `(ν - c * X 0) * ∫ s in 0..t, Y s ≤ X 0 - X t`;
* `CombSystem.integral_dissipation_le`: `∫ s in 0..t, Y s ≤ X 0 / (ν - c * X 0)`;
* `CombSystem.reynolds_le_initial`: `c * Re 0 < 1` gives `Re t ≤ Re 0`;
* `CombSystem.critical_le_initial_of_lt_div`: for `0 < c` the class is `X 0 < ν / c`, so it
  widens as `1 / c`.

The case `c = 1` (the count's bound) is restated as `CombSystem.count_critical_le_initial`,
`CombSystem.count_dissipation_integral_le_drop` and `CombSystem.count_reynolds_le_initial`.
None of these statements names the number of modes: the class is the same at every truncation.

[proved-derived; formal-checked] The Fourier instance's feed bound, on complex amplitudes over
any finite set of coordinates (`Fin 3` for the fluid):

* `norm_transport_le`: for `k = p + q` and `p · a = 0`, `‖(q · a) • b‖ ≤ ‖k‖ * ‖a‖ * ‖b‖`;
* `norm_projected_transport_le`: a continuous linear map of norm at most one does not raise it;
* `norm_feed_le`: summed over a set of pairs with `κ k = κ p + κ q`, the projected feed is at
  most `‖κ k‖ * ∑ ‖a p‖ * ‖a q‖`, which is the comb's feed bound with `w k = ‖κ k‖` and `c = 1`.

A complex amplitude space meets the theorems above through `CombSystem.critical_le_initial_complex`
and `CombSystem.dissipation_integral_le_drop_complex`, which read its norm through the real inner
product `InnerProductSpace.complexToReal`.

## What this does not state

Nothing here is the Clay statement. This is a class of data, the same at every truncation, on
which the count decides. The module does not construct a solution: a comb system is a hypothesis,
given on `[0, ∞)`. It says nothing of a system with infinitely many modes, of a limit of
truncations, or of uniqueness. It says nothing of data with `c * criticalNorm w (u 0) ≥ ν`, where
the count's bound does not decide and the triads' phases do. The feed bound of the last section
is the bound of one transport term and of a finite sum of them; that the Galerkin truncation of
the fluid's equation is a comb system (its modes, its projection, the factor `-i`) is read from
these statements and is not assembled here.
-/

noncomputable section

namespace Holonics.Fluid.LaminarClass

open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace

/-! ## The two norms and the algebra between them -/

section Algebra

variable {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E]

/-- [definition] The scale-critical norm `X = ∑ k, ‖a k‖ / w k`. -/
def criticalNorm (w : ι → ℝ) (a : ι → E) : ℝ := ∑ k, ‖a k‖ / w k

/-- [definition] The norm the damping pays in, `Y = ∑ k, w k * ‖a k‖`. -/
def dissipationNorm (w : ι → ℝ) (a : ι → E) : ℝ := ∑ k, w k * ‖a k‖

/-- [definition] The sum of the amplitudes, `∑ k, ‖a k‖`. -/
def amplitudeSum (a : ι → E) : ℝ := ∑ k, ‖a k‖

/-- [definition] The dimensionless reading `Re = X / ν`. -/
def reynolds (w : ι → ℝ) (ν : ℝ) (a : ι → E) : ℝ := criticalNorm w a / ν

theorem criticalNorm_nonneg {w : ι → ℝ} (hw : ∀ k, 0 ≤ w k) (a : ι → E) :
    0 ≤ criticalNorm w a :=
  Finset.sum_nonneg fun k _ => div_nonneg (norm_nonneg _) (hw k)

theorem dissipationNorm_nonneg {w : ι → ℝ} (hw : ∀ k, 0 ≤ w k) (a : ι → E) :
    0 ≤ dissipationNorm w a :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (norm_nonneg _)

theorem amplitudeSum_nonneg (a : ι → E) : 0 ≤ amplitudeSum a :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- [proved-derived; formal-checked] Cauchy-Schwarz between the two norms:
`(∑ ‖a k‖) ^ 2 ≤ X * Y`. -/
theorem amplitudeSum_sq_le {w : ι → ℝ} (hw : ∀ k, 0 < w k) (a : ι → E) :
    amplitudeSum a ^ 2 ≤ criticalNorm w a * dissipationNorm w a := by
  unfold amplitudeSum criticalNorm dissipationNorm
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun k _ => div_nonneg (norm_nonneg _) (hw k).le)
    (fun k _ => mul_nonneg (hw k).le (norm_nonneg _)) (fun k _ => le_of_eq ?_)
  rw [← mul_assoc, div_mul_cancel₀ _ (hw k).ne', sq]

/-- [proved-derived; formal-checked] The feed read in the critical norm is at most `c` times the
square of the amplitude sum: a pair of modes feeds at most one mode. -/
theorem feed_sum_le {w : ι → ℝ} (hw : ∀ k, 0 < w k) {c : ℝ} (hc : 0 ≤ c)
    {T : ι → Finset (ι × ι)} (hT : ∀ k k', k ≠ k' → Disjoint (T k) (T k'))
    (a n : ι → E)
    (hn : ∀ k, ‖n k‖ ≤ c * w k * ∑ pq ∈ T k, ‖a pq.1‖ * ‖a pq.2‖) :
    ∑ k, ‖n k‖ / w k ≤ c * amplitudeSum a ^ 2 := by
  classical
  calc ∑ k, ‖n k‖ / w k ≤ ∑ k, c * ∑ pq ∈ T k, ‖a pq.1‖ * ‖a pq.2‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [div_le_iff₀ (hw k)]
        calc ‖n k‖ ≤ c * w k * ∑ pq ∈ T k, ‖a pq.1‖ * ‖a pq.2‖ := hn k
          _ = c * (∑ pq ∈ T k, ‖a pq.1‖ * ‖a pq.2‖) * w k := by ring
    _ = c * ∑ pq ∈ Finset.univ.biUnion T, ‖a pq.1‖ * ‖a pq.2‖ := by
        rw [← Finset.mul_sum, Finset.sum_biUnion]
        intro k _ k' _ hkk'
        exact hT k k' hkk'
    _ ≤ c * ∑ pq : ι × ι, ‖a pq.1‖ * ‖a pq.2‖ := by
        refine mul_le_mul_of_nonneg_left ?_ hc
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun pq _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = c * amplitudeSum a ^ 2 := by
        unfold amplitudeSum
        rw [Fintype.sum_prod_type, sq, Finset.sum_mul_sum]

/-- [proved-derived; formal-checked] The feed read in the critical norm is at most `c * X * Y`. -/
theorem feed_sum_le_critical_mul_dissipation {w : ι → ℝ} (hw : ∀ k, 0 < w k) {c : ℝ}
    (hc : 0 ≤ c) {T : ι → Finset (ι × ι)} (hT : ∀ k k', k ≠ k' → Disjoint (T k) (T k'))
    (a n : ι → E)
    (hn : ∀ k, ‖n k‖ ≤ c * w k * ∑ pq ∈ T k, ‖a pq.1‖ * ‖a pq.2‖) :
    ∑ k, ‖n k‖ / w k ≤ c * (criticalNorm w a * dissipationNorm w a) :=
  (feed_sum_le hw hc hT a n hn).trans
    (mul_le_mul_of_nonneg_left (amplitudeSum_sq_le hw a) hc)

end Algebra

/-! ## The right derivative of a norm -/

section NormSlope

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open Classical in
/-- [definition] The right derivative of `s ↦ ‖f s‖` at a point where `f` is `x` and its right
derivative is `v`: the radial part `⟪x, v⟫ / ‖x‖` away from zero, and `‖v‖` at zero. -/
def normSlope (x v : E) : ℝ := if x = 0 then ‖v‖ else ⟪x, v⟫ / ‖x‖

theorem normSlope_zero_left (v : E) : normSlope (0 : E) v = ‖v‖ := by
  simp [normSlope]

theorem normSlope_of_ne_zero {x : E} (hx : x ≠ 0) (v : E) :
    normSlope x v = ⟪x, v⟫ / ‖x‖ := by
  simp [normSlope, hx]

/-- [proved-derived; formal-checked] The norm of a curve with a right derivative has a right
derivative, the `normSlope`. At a zero of the curve the norm leaves at the speed `‖f'‖`. -/
theorem hasDerivWithinAt_norm_Ici {f : ℝ → E} {f' : E} {t : ℝ}
    (hf : HasDerivWithinAt f f' (Ici t) t) :
    HasDerivWithinAt (fun s => ‖f s‖) (normSlope (f t) f') (Ici t) t := by
  unfold normSlope
  split_ifs with h0
  · rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left] at hf ⊢
    refine Tendsto.congr' ?_ hf.norm
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hst : 0 < s - t := sub_pos.mpr hs
    simp [slope, h0, norm_smul, abs_of_pos hst]
  · have hpos : 0 < ‖f t‖ := norm_pos_iff.mpr h0
    have h3 : HasDerivWithinAt (fun y => √(‖f y‖ ^ 2))
        (2 * ⟪f t, f'⟫ / (2 * √(‖f t‖ ^ 2))) (Ici t) t :=
      (hf.norm_sq).sqrt (pow_ne_zero 2 hpos.ne')
    have hfun : (fun y => √(‖f y‖ ^ 2)) = fun y => ‖f y‖ := by
      funext y
      exact Real.sqrt_sq (norm_nonneg _)
    rw [hfun, Real.sqrt_sq (norm_nonneg _)] at h3
    convert h3 using 1
    exact (mul_div_mul_left _ _ two_ne_zero).symm

/-- [proved-derived; formal-checked] Under a damping `-c • x` and a feed `n`, the norm's right
derivative is at most `-c * ‖x‖ + ‖n‖`. No sign is asked of `c`. -/
theorem normSlope_damped_le (x n : E) (c : ℝ) :
    normSlope x (-c • x + n) ≤ -c * ‖x‖ + ‖n‖ := by
  unfold normSlope
  split_ifs with h0
  · subst h0
    simp
  · have hx : 0 < ‖x‖ := norm_pos_iff.mpr h0
    rw [div_le_iff₀ hx, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
    nlinarith [real_inner_le_norm x n]

end NormSlope

/-! ## The comb system -/

section System

variable {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- [definition] A comb system on `[0, ∞)`: positive weights, a positive viscosity, a coherence
constant `c ≥ 0`, a comb with pairwise disjoint fibres, modes damped at `ν * w k ^ 2` and fed by
`N`, and the feed bounded through the comb. -/
structure CombSystem (w : ι → ℝ) (ν c : ℝ) (T : ι → Finset (ι × ι)) (u N : ℝ → ι → E) :
    Prop where
  weight_pos : ∀ k, 0 < w k
  viscosity_pos : 0 < ν
  coherence_nonneg : 0 ≤ c
  fibres_disjoint : ∀ k k', k ≠ k' → Disjoint (T k) (T k')
  evolves : ∀ k t, 0 ≤ t →
    HasDerivWithinAt (fun s => u s k) (-(ν * w k ^ 2) • u t k + N t k) (Ici 0) t
  feed_le : ∀ t, 0 ≤ t → ∀ k, ‖N t k‖ ≤ c * w k * ∑ pq ∈ T k, ‖u t pq.1‖ * ‖u t pq.2‖

variable {w : ι → ℝ} {ν c : ℝ} {T : ι → Finset (ι × ι)} {u N : ℝ → ι → E}

omit [Fintype ι] in
/-- A comb system from derivatives and feed bounds on the whole line. -/
theorem CombSystem.of_hasDerivAt (hw : ∀ k, 0 < w k) (hν : 0 < ν) (hc : 0 ≤ c)
    (hT : ∀ k k', k ≠ k' → Disjoint (T k) (T k'))
    (hu : ∀ k t, HasDerivAt (fun s => u s k) (-(ν * w k ^ 2) • u t k + N t k) t)
    (hN : ∀ t k, ‖N t k‖ ≤ c * w k * ∑ pq ∈ T k, ‖u t pq.1‖ * ‖u t pq.2‖) :
    CombSystem w ν c T u N :=
  ⟨hw, hν, hc, hT, fun k t _ => (hu k t).hasDerivWithinAt, fun t _ k => hN t k⟩

omit [Fintype ι] in
theorem CombSystem.continuousOn_mode (h : CombSystem w ν c T u N) (k : ι) :
    ContinuousOn (fun s => u s k) (Ici 0) :=
  fun t ht => (h.evolves k t ht).continuousWithinAt

theorem CombSystem.continuousOn_critical (h : CombSystem w ν c T u N) :
    ContinuousOn (fun s => criticalNorm w (u s)) (Ici 0) := by
  unfold criticalNorm
  exact continuousOn_finsetSum _ fun k _ => (h.continuousOn_mode k).norm.div_const _

theorem CombSystem.continuousOn_dissipation (h : CombSystem w ν c T u N) :
    ContinuousOn (fun s => dissipationNorm w (u s)) (Ici 0) := by
  unfold dissipationNorm
  exact continuousOn_finsetSum _ fun k _ => continuousOn_const.mul (h.continuousOn_mode k).norm

end System

/-! ## The laminar class -/

section Main

variable {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {w : ι → ℝ} {ν c : ℝ} {T : ι → Finset (ι × ι)} {u N : ℝ → ι → E}

/-- [definition] The right derivative of the critical norm along a comb system. -/
def criticalSlope (w : ι → ℝ) (ν : ℝ) (u N : ℝ → ι → E) (t : ℝ) : ℝ :=
  ∑ k, normSlope (u t k) (-(ν * w k ^ 2) • u t k + N t k) / w k

/-- [proved-derived; formal-checked] The critical norm has the right derivative `criticalSlope`
at every `0 ≤ t`. -/
theorem CombSystem.hasDerivWithinAt_critical (h : CombSystem w ν c T u N) {t : ℝ}
    (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => criticalNorm w (u s)) (criticalSlope w ν u N t) (Ici t) t := by
  unfold criticalNorm criticalSlope
  refine HasDerivWithinAt.fun_sum fun k _ => ?_
  exact (hasDerivWithinAt_norm_Ici
    ((h.evolves k t ht).mono (Ici_subset_Ici.mpr ht))).div_const _

/-- [proved-derived; formal-checked] The inequality of Lei and Lin in the comb vocabulary:
the right derivative of `X` is at most `-(ν - c * X) * Y`. -/
theorem CombSystem.criticalSlope_le (h : CombSystem w ν c T u N) {t : ℝ} (ht : 0 ≤ t) :
    criticalSlope w ν u N t ≤
      -(ν - c * criticalNorm w (u t)) * dissipationNorm w (u t) := by
  have hw := h.weight_pos
  have h1 : criticalSlope w ν u N t ≤
      ∑ k, (-(ν * (w k * ‖u t k‖)) + ‖N t k‖ / w k) := by
    unfold criticalSlope
    refine Finset.sum_le_sum fun k _ => ?_
    rw [div_le_iff₀ (hw k)]
    calc normSlope (u t k) (-(ν * w k ^ 2) • u t k + N t k)
        ≤ -(ν * w k ^ 2) * ‖u t k‖ + ‖N t k‖ := normSlope_damped_le _ _ _
      _ = (-(ν * (w k * ‖u t k‖)) + ‖N t k‖ / w k) * w k := by
          rw [add_mul, div_mul_cancel₀ _ (hw k).ne']
          ring
  have h2 : ∑ k, (-(ν * (w k * ‖u t k‖)) + ‖N t k‖ / w k)
      = -(ν * dissipationNorm w (u t)) + ∑ k, ‖N t k‖ / w k := by
    unfold dissipationNorm
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.mul_sum]
  have h3 := feed_sum_le_critical_mul_dissipation hw h.coherence_nonneg h.fibres_disjoint
    (u t) (N t) (h.feed_le t ht)
  rw [h2] at h1
  have h4 : -(ν - c * criticalNorm w (u t)) * dissipationNorm w (u t)
      = -(ν * dissipationNorm w (u t))
        + c * (criticalNorm w (u t) * dissipationNorm w (u t)) := by ring
  rw [h4]
  linarith

/-- [proved-derived; formal-checked] **The laminar class.** If `c * X 0 < ν` then the critical
norm never passes its opening value. -/
theorem CombSystem.critical_le_initial (h : CombSystem w ν c T u N)
    (h0 : c * criticalNorm w (u 0) < ν) {t : ℝ} (ht : 0 ≤ t) :
    criticalNorm w (u t) ≤ criticalNorm w (u 0) := by
  have hc := h.coherence_nonneg
  have hd : 0 < ν - c * criticalNorm w (u 0) := sub_pos.mpr h0
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  -- a fence of slope `ε`, low enough to stay inside the class up to the time `t`
  obtain ⟨ε, hε, hεδ, hεd⟩ : ∃ ε : ℝ, 0 < ε ∧ ε * t ≤ δ ∧
      c * (ε * t) ≤ ν - c * criticalNorm w (u 0) := by
    have hc1 : 0 < c + 1 := by linarith
    have ht1 : 0 < t + 1 := by linarith
    have hm_pos : 0 < min δ ((ν - c * criticalNorm w (u 0)) / (c + 1)) :=
      lt_min hδ (div_pos hd hc1)
    have hmδ : min δ ((ν - c * criticalNorm w (u 0)) / (c + 1)) ≤ δ := min_le_left _ _
    have hmd : min δ ((ν - c * criticalNorm w (u 0)) / (c + 1))
        ≤ (ν - c * criticalNorm w (u 0)) / (c + 1) := min_le_right _ _
    generalize min δ ((ν - c * criticalNorm w (u 0)) / (c + 1)) = m at hm_pos hmδ hmd
    have hmt : m / (t + 1) * t ≤ m := by
      rw [div_mul_eq_mul_div, div_le_iff₀ ht1]
      nlinarith
    have hcd : c * ((ν - c * criticalNorm w (u 0)) / (c + 1))
        ≤ ν - c * criticalNorm w (u 0) := by
      rw [mul_div_assoc', div_le_iff₀ hc1]
      nlinarith
    refine ⟨m / (t + 1), div_pos hm_pos ht1, hmt.trans hmδ, ?_⟩
    calc c * (m / (t + 1) * t) ≤ c * m := mul_le_mul_of_nonneg_left hmt hc
      _ ≤ c * ((ν - c * criticalNorm w (u 0)) / (c + 1)) := mul_le_mul_of_nonneg_left hmd hc
      _ ≤ ν - c * criticalNorm w (u 0) := hcd
  have hB' : ∀ x : ℝ,
      HasDerivWithinAt (fun s => criticalNorm w (u 0) + ε * s) ε (Ici x) x := by
    intro x
    have := ((hasDerivAt_id' x).const_mul ε).const_add (criticalNorm w (u 0))
    simpa using this.hasDerivWithinAt
  have key := image_le_of_deriv_right_lt_deriv_boundary'
    (f := fun s => criticalNorm w (u s)) (f' := criticalSlope w ν u N) (a := 0) (b := t)
    (B := fun s => criticalNorm w (u 0) + ε * s) (B' := fun _ => ε)
    (h.continuousOn_critical.mono Icc_subset_Ici_self)
    (fun x hx => h.hasDerivWithinAt_critical hx.1)
    (by simp)
    (by fun_prop)
    (fun x _ => hB' x)
    (by
      intro x hx hxe
      have hxe' : criticalNorm w (u x) = criticalNorm w (u 0) + ε * x := hxe
      have hslope := h.criticalSlope_le hx.1
      have hY : 0 ≤ dissipationNorm w (u x) :=
        dissipationNorm_nonneg (fun k => (h.weight_pos k).le) _
      have hxt : c * (ε * x) ≤ c * (ε * t) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx.2.le hε.le) hc
      have hcX : 0 ≤ ν - c * criticalNorm w (u x) := by
        rw [hxe', mul_add]
        linarith
      have hle : -(ν - c * criticalNorm w (u x)) * dissipationNorm w (u x) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcX) hY
      show criticalSlope w ν u N x < ε
      linarith)
  have hkey : criticalNorm w (u t) ≤ criticalNorm w (u 0) + ε * t :=
    key (right_mem_Icc.mpr ht)
  linarith

/-- [proved-derived; formal-checked] **The laminar class pays its dissipation.** If
`c * X 0 < ν` then `X t + (ν - c * X 0) * ∫ s in 0..t, Y s ≤ X 0`. -/
theorem CombSystem.critical_add_dissipation_le (h : CombSystem w ν c T u N)
    (h0 : c * criticalNorm w (u 0) < ν) {t : ℝ} (ht : 0 ≤ t) :
    criticalNorm w (u t) + (ν - c * criticalNorm w (u 0)) *
      ∫ s in (0 : ℝ)..t, dissipationNorm w (u s) ≤ criticalNorm w (u 0) := by
  have hc := h.coherence_nonneg
  have hYc := h.continuousOn_dissipation
  have hYint : ∀ x, 0 ≤ x →
      IntervalIntegrable (fun s => dissipationNorm w (u s)) volume 0 x := by
    intro x hx
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hx]
    exact hYc.mono Icc_subset_Ici_self
  have hprim_cont :
      ContinuousOn (fun x => ∫ s in (0 : ℝ)..x, dissipationNorm w (u s)) (Icc 0 t) := by
    have hI : IntegrableOn (fun s => dissipationNorm w (u s)) (uIcc 0 t) volume := by
      rw [uIcc_of_le ht]
      exact (hYc.mono Icc_subset_Ici_self).integrableOn_Icc
    have := intervalIntegral.continuousOn_primitive_interval hI
    rwa [uIcc_of_le ht] at this
  have hprim_deriv : ∀ x, 0 ≤ x →
      HasDerivWithinAt (fun y => ∫ s in (0 : ℝ)..y, dissipationNorm w (u s))
        (dissipationNorm w (u x)) (Ici x) x := by
    intro x hx
    have hYx : ContinuousOn (fun s => dissipationNorm w (u s)) (Ici x) :=
      hYc.mono (Ici_subset_Ici.mpr hx)
    refine intervalIntegral.integral_hasDerivWithinAt_right (hYint x hx)
      (s := Ici x) (t := Ioi x) ?_ ?_
    · exact (hYx.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ici x).filter_mono
        (nhdsWithin_mono x Ioi_subset_Ici_self)
    · exact (hYx x (mem_Ici.mpr le_rfl)).mono Ioi_subset_Ici_self
  have key := image_le_of_deriv_right_le_deriv_boundary
    (f := fun s => criticalNorm w (u s) + (ν - c * criticalNorm w (u 0)) *
      ∫ r in (0 : ℝ)..s, dissipationNorm w (u r))
    (f' := fun x => criticalSlope w ν u N x +
      (ν - c * criticalNorm w (u 0)) * dissipationNorm w (u x))
    (a := 0) (b := t)
    (B := fun _ => criticalNorm w (u 0)) (B' := fun _ => 0)
    ((h.continuousOn_critical.mono Icc_subset_Ici_self).add
      (continuousOn_const.mul hprim_cont))
    (fun x hx => (h.hasDerivWithinAt_critical hx.1).add ((hprim_deriv x hx.1).const_mul _))
    (by simp)
    continuousOn_const
    (fun x _ => hasDerivWithinAt_const _ _ _)
    (by
      intro x hx
      have hslope := h.criticalSlope_le hx.1
      have hY : 0 ≤ dissipationNorm w (u x) :=
        dissipationNorm_nonneg (fun k => (h.weight_pos k).le) _
      have hXx := h.critical_le_initial h0 hx.1
      have hle : c * (criticalNorm w (u x) - criticalNorm w (u 0)) *
          dissipationNorm w (u x) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos hc (sub_nonpos.mpr hXx)) hY
      show criticalSlope w ν u N x +
        (ν - c * criticalNorm w (u 0)) * dissipationNorm w (u x) ≤ 0
      nlinarith)
  exact key (right_mem_Icc.mpr ht)

/-- [proved-derived; formal-checked] The dissipation paid up to `t` is at most the drop of the
critical norm: `(ν - c * X 0) * ∫ s in 0..t, Y s ≤ X 0 - X t`. -/
theorem CombSystem.dissipation_integral_le_drop (h : CombSystem w ν c T u N)
    (h0 : c * criticalNorm w (u 0) < ν) {t : ℝ} (ht : 0 ≤ t) :
    (ν - c * criticalNorm w (u 0)) * ∫ s in (0 : ℝ)..t, dissipationNorm w (u s)
      ≤ criticalNorm w (u 0) - criticalNorm w (u t) := by
  linarith [h.critical_add_dissipation_le h0 ht]

/-- [proved-derived; formal-checked] The dissipation is integrable over all time, with the bound
`∫ s in 0..t, Y s ≤ X 0 / (ν - c * X 0)` for every `t`. -/
theorem CombSystem.integral_dissipation_le (h : CombSystem w ν c T u N)
    (h0 : c * criticalNorm w (u 0) < ν) {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in (0 : ℝ)..t, dissipationNorm w (u s)
      ≤ criticalNorm w (u 0) / (ν - c * criticalNorm w (u 0)) := by
  have hd : 0 < ν - c * criticalNorm w (u 0) := sub_pos.mpr h0
  have h1 := h.dissipation_integral_le_drop h0 ht
  have h2 : 0 ≤ criticalNorm w (u t) :=
    criticalNorm_nonneg (fun k => (h.weight_pos k).le) _
  rw [le_div_iff₀ hd]
  linarith

/-- [proved-derived; formal-checked] For `0 < c` the class is `X 0 < ν / c`: it widens as
`1 / c`. -/
theorem CombSystem.critical_le_initial_of_lt_div (h : CombSystem w ν c T u N) (hc : 0 < c)
    (h0 : criticalNorm w (u 0) < ν / c) {t : ℝ} (ht : 0 ≤ t) :
    criticalNorm w (u t) ≤ criticalNorm w (u 0) := by
  refine h.critical_le_initial ?_ ht
  rw [lt_div_iff₀ hc] at h0
  linarith

/-- [proved-derived; formal-checked] The dimensionless form: `c * Re 0 < 1` gives
`Re t ≤ Re 0`. -/
theorem CombSystem.reynolds_le_initial (h : CombSystem w ν c T u N)
    (h0 : c * reynolds w ν (u 0) < 1) {t : ℝ} (ht : 0 ≤ t) :
    reynolds w ν (u t) ≤ reynolds w ν (u 0) := by
  have hν := h.viscosity_pos
  unfold reynolds at h0 ⊢
  have h0' : c * criticalNorm w (u 0) < ν := by
    rwa [← mul_div_assoc, div_lt_one hν] at h0
  exact div_le_div_of_nonneg_right (h.critical_le_initial h0' ht) hν.le

/-! ### The count's own bound, `c = 1` -/

/-- [proved-derived; formal-checked] The count's class: `X 0 < ν` gives `X t ≤ X 0`. -/
theorem CombSystem.count_critical_le_initial (h : CombSystem w ν 1 T u N)
    (h0 : criticalNorm w (u 0) < ν) {t : ℝ} (ht : 0 ≤ t) :
    criticalNorm w (u t) ≤ criticalNorm w (u 0) :=
  h.critical_le_initial (by rwa [one_mul]) ht

/-- [proved-derived; formal-checked] The count's class pays
`(ν - X 0) * ∫ s in 0..t, Y s ≤ X 0 - X t`. -/
theorem CombSystem.count_dissipation_integral_le_drop (h : CombSystem w ν 1 T u N)
    (h0 : criticalNorm w (u 0) < ν) {t : ℝ} (ht : 0 ≤ t) :
    (ν - criticalNorm w (u 0)) * ∫ s in (0 : ℝ)..t, dissipationNorm w (u s)
      ≤ criticalNorm w (u 0) - criticalNorm w (u t) := by
  have := h.dissipation_integral_le_drop (by rwa [one_mul]) ht
  rwa [one_mul] at this

/-- [proved-derived; formal-checked] The count's class, dimensionless: `Re 0 < 1` gives
`Re t ≤ Re 0`. -/
theorem CombSystem.count_reynolds_le_initial (h : CombSystem w ν 1 T u N)
    (h0 : reynolds w ν (u 0) < 1) {t : ℝ} (ht : 0 ≤ t) :
    reynolds w ν (u t) ≤ reynolds w ν (u 0) :=
  h.reynolds_le_initial (by rwa [one_mul]) ht

end Main

/-! ## Complex amplitudes -/

section ComplexAmplitudes

variable {ι : Type*} [Fintype ι] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {w : ι → ℝ} {ν c : ℝ} {T : ι → Finset (ι × ι)} {u N : ℝ → ι → F}

/-- [proved-derived; formal-checked] The laminar class on a complex amplitude space, whose norm
is read through the real inner product `Re ⟪x, y⟫`. -/
theorem CombSystem.critical_le_initial_complex (h : CombSystem w ν c T u N)
    (h0 : c * criticalNorm w (u 0) < ν) {t : ℝ} (ht : 0 ≤ t) :
    criticalNorm w (u t) ≤ criticalNorm w (u 0) := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  exact CombSystem.critical_le_initial h h0 ht

/-- [proved-derived; formal-checked] The dissipation paid on a complex amplitude space. -/
theorem CombSystem.dissipation_integral_le_drop_complex (h : CombSystem w ν c T u N)
    (h0 : c * criticalNorm w (u 0) < ν) {t : ℝ} (ht : 0 ≤ t) :
    (ν - c * criticalNorm w (u 0)) * ∫ s in (0 : ℝ)..t, dissipationNorm w (u s)
      ≤ criticalNorm w (u 0) - criticalNorm w (u t) := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  exact CombSystem.dissipation_integral_le_drop h h0 ht

end ComplexAmplitudes

/-! ## The Fourier instance's feed bound -/

section Triad

variable {n : Type*} [Fintype n]

/-- [definition] The pairing of a real wave vector with a complex amplitude,
`q · a = ∑ j, q j * a j`. -/
def wavePairing (q : EuclideanSpace ℝ n) (a : EuclideanSpace ℂ n) : ℂ :=
  ∑ j, (q j : ℂ) * a j

theorem norm_wavePairing_le (q : EuclideanSpace ℝ n) (a : EuclideanSpace ℂ n) :
    ‖wavePairing q a‖ ≤ ‖q‖ * ‖a‖ := by
  unfold wavePairing
  calc ‖∑ j, (q j : ℂ) * a j‖ ≤ ∑ j, ‖(q j : ℂ) * a j‖ := norm_sum_le _ _
    _ = ∑ j, |q j| * ‖a j‖ := by simp [Complex.norm_real]
    _ ≤ √(∑ j, |q j| ^ 2) * √(∑ j, ‖a j‖ ^ 2) := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = ‖q‖ * ‖a‖ := by
        rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
        simp

theorem wavePairing_add (p q : EuclideanSpace ℝ n) (a : EuclideanSpace ℂ n) :
    wavePairing (p + q) a = wavePairing p a + wavePairing q a := by
  unfold wavePairing
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [add_mul]

/-- [proved-derived; formal-checked] One transport term of a triad `k = p + q`, with the carrying
amplitude incompressible (`p · a = 0`): `‖(q · a) • b‖ ≤ ‖k‖ * ‖a‖ * ‖b‖`. -/
theorem norm_transport_le {k p q : EuclideanSpace ℝ n} (hk : k = p + q)
    {a : EuclideanSpace ℂ n} (ha : wavePairing p a = 0) (b : EuclideanSpace ℂ n) :
    ‖wavePairing q a • b‖ ≤ ‖k‖ * ‖a‖ * ‖b‖ := by
  have h1 : wavePairing q a = wavePairing k a := by
    rw [hk, wavePairing_add, ha, zero_add]
  rw [norm_smul, h1]
  exact mul_le_mul_of_nonneg_right (norm_wavePairing_le k a) (norm_nonneg _)

/-- [proved-derived; formal-checked] A continuous linear map of norm at most one (the projection
onto the plane across `k`) does not raise the transport term's bound. -/
theorem norm_projected_transport_le {k p q : EuclideanSpace ℝ n} (hk : k = p + q)
    {a : EuclideanSpace ℂ n} (ha : wavePairing p a = 0) (b : EuclideanSpace ℂ n)
    (P : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (hP : ‖P‖ ≤ 1) :
    ‖P (wavePairing q a • b)‖ ≤ ‖k‖ * ‖a‖ * ‖b‖ :=
  calc ‖P (wavePairing q a • b)‖ ≤ 1 * ‖wavePairing q a • b‖ := P.le_of_opNorm_le hP _
    _ = ‖wavePairing q a • b‖ := one_mul _
    _ ≤ ‖k‖ * ‖a‖ * ‖b‖ := norm_transport_le hk ha b

/-- [proved-derived; formal-checked] The comb's feed bound for the Fourier instance: over a set
`S` of pairs with `κ k = κ p + κ q` and incompressible amplitudes, the projected feed into `k` is
at most `‖κ k‖ * ∑ ‖a p‖ * ‖a q‖`. -/
theorem norm_feed_le {ι : Type*} (κ : ι → EuclideanSpace ℝ n) (a : ι → EuclideanSpace ℂ n)
    (hdiv : ∀ p, wavePairing (κ p) (a p) = 0) (k : ι) (S : Finset (ι × ι))
    (hS : ∀ pq ∈ S, κ k = κ pq.1 + κ pq.2)
    (P : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (hP : ‖P‖ ≤ 1) :
    ‖P (∑ pq ∈ S, wavePairing (κ pq.2) (a pq.1) • a pq.2)‖
      ≤ ‖κ k‖ * ∑ pq ∈ S, ‖a pq.1‖ * ‖a pq.2‖ :=
  calc ‖P (∑ pq ∈ S, wavePairing (κ pq.2) (a pq.1) • a pq.2)‖
      ≤ 1 * ‖∑ pq ∈ S, wavePairing (κ pq.2) (a pq.1) • a pq.2‖ := P.le_of_opNorm_le hP _
    _ = ‖∑ pq ∈ S, wavePairing (κ pq.2) (a pq.1) • a pq.2‖ := one_mul _
    _ ≤ ∑ pq ∈ S, ‖wavePairing (κ pq.2) (a pq.1) • a pq.2‖ := norm_sum_le _ _
    _ ≤ ∑ pq ∈ S, ‖κ k‖ * (‖a pq.1‖ * ‖a pq.2‖) := by
        refine Finset.sum_le_sum fun pq hpq => ?_
        have := norm_transport_le (hS pq hpq) (hdiv pq.1) (a pq.2)
        linarith
    _ = ‖κ k‖ * ∑ pq ∈ S, ‖a pq.1‖ * ‖a pq.2‖ := by rw [Finset.mul_sum]

end Triad

section Audit

#print axioms amplitudeSum_sq_le
#print axioms feed_sum_le_critical_mul_dissipation
#print axioms hasDerivWithinAt_norm_Ici
#print axioms normSlope_damped_le
#print axioms CombSystem.criticalSlope_le
#print axioms CombSystem.critical_le_initial
#print axioms CombSystem.dissipation_integral_le_drop
#print axioms CombSystem.integral_dissipation_le
#print axioms CombSystem.critical_le_initial_of_lt_div
#print axioms CombSystem.reynolds_le_initial
#print axioms CombSystem.count_critical_le_initial
#print axioms CombSystem.count_dissipation_integral_le_drop
#print axioms CombSystem.count_reynolds_le_initial
#print axioms CombSystem.critical_le_initial_complex
#print axioms CombSystem.dissipation_integral_le_drop_complex
#print axioms norm_feed_le

end Audit

end Holonics.Fluid.LaminarClass
