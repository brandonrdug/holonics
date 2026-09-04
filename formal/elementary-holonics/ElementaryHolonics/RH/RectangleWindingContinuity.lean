import ElementaryHolonics.RH.HeatFlowContinuity
import ElementaryHolonics.RH.RectangleArgumentPrinciple

/-!
# Continuity in `t` of the rectangle winding integral of `H_t`

If `H_{t₀}` has no zero on the boundary of a rectangle, then for `t` near `t₀` neither does `H_t`,
with a uniform lower bound, and the argument-principle integral `∮ H_t′/H_t` over the rectangle
is continuous in `t` at `t₀`, by dominated convergence on each edge with the joint continuity of
`H_t` and `H_t′`.
-/

open Complex Metric Filter Topology Set
open scoped Interval
open Soma.Holonics.RH.EntireDerivativeGrowth
open Soma.Holonics.RH.HeatFlowEntire
open Soma.Holonics.RH.HeatEquationEntire
open Soma.Holonics.RH.HeatFlowContinuity
open Soma.Holonics.RH.RectangleCauchy

namespace Soma.Holonics.RH.RectangleWindingContinuity

variable {f : ℂ → ℂ} {A B ρ : ℝ}

theorem norm_le_of_mem_closedRect {z w ζ : ℂ} (hζ : ζ ∈ closedRect z w) :
    ‖ζ‖ ≤ 2 * (‖z‖ + ‖w‖) := by
  rw [closedRect, Complex.mem_reProdIm] at hζ
  obtain ⟨hre, him⟩ := hζ
  have h1 : |ζ.re| ≤ ‖z‖ + ‖w‖ := by
    rw [Set.mem_uIcc] at hre
    have hz := Complex.abs_re_le_norm z
    have hw := Complex.abs_re_le_norm w
    rw [abs_le] at hz hw ⊢
    rcases hre with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
  have h2 : |ζ.im| ≤ ‖z‖ + ‖w‖ := by
    rw [Set.mem_uIcc] at him
    have hz := Complex.abs_im_le_norm z
    have hw := Complex.abs_im_le_norm w
    rw [abs_le] at hz hw ⊢
    rcases him with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
  calc ‖ζ‖ ≤ |ζ.re| + |ζ.im| := Complex.norm_le_abs_re_add_abs_im ζ
    _ ≤ 2 * (‖z‖ + ‖w‖) := by linarith

theorem isClosed_closedRect (z w : ℂ) : IsClosed (closedRect z w) :=
  IsClosed.reProdIm isClosed_Icc isClosed_Icc

theorem isCompact_closedRect (z w : ℂ) : IsCompact (closedRect z w) :=
  (isCompact_closedBall (0 : ℂ) (2 * (‖z‖ + ‖w‖))).of_isClosed_subset (isClosed_closedRect z w)
    (fun ζ hζ => by
      rw [mem_closedBall_zero_iff]
      exact norm_le_of_mem_closedRect hζ)

theorem isCompact_boundaryRect (z w : ℂ) : IsCompact (boundaryRect z w) :=
  (isCompact_closedRect z w).diff (isOpen_openRect z w)

/-- Nonvanishing of `H_{t₀}` on the boundary persists near `t₀` with a uniform lower bound. -/
theorem eventually_boundary_ge (hf : Differentiable ℂ f) (hg : HasGrowth f A B ρ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hρ0 : 0 < ρ) (hρ2 : ρ < 2) {z w : ℂ} {t₀ : ℝ}
    (hne : ∀ ζ ∈ boundaryRect z w, heatE t₀ f ζ ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ᶠ t in 𝓝 t₀, ∀ ζ ∈ boundaryRect z w, m ≤ ‖heatE t f ζ‖ := by
  have hcont : Continuous (fun p : ℝ × ℂ => ‖heatE p.1 f p.2‖) :=
    continuous_norm.comp (continuous_heatE hf hg hA hB hρ0 hρ2)
  rcases (boundaryRect z w).eq_empty_or_nonempty with hemp | hnon
  · refine ⟨1, one_pos, Filter.Eventually.of_forall fun t ζ hζ => ?_⟩
    rw [hemp] at hζ
    exact absurd hζ (Set.notMem_empty ζ)
  · obtain ⟨ζ₀, hζ₀, hmin⟩ := (isCompact_boundaryRect z w).exists_isMinOn hnon
      ((continuous_norm.comp (differentiable_heatE hf hg hA hB hρ0 hρ2 t₀).continuous).continuousOn)
    set m : ℝ := ‖heatE t₀ f ζ₀‖ / 2 with hm
    have hm0 : 0 < m := by
      have := norm_pos_iff.mpr (hne ζ₀ hζ₀)
      positivity
    refine ⟨m, hm0, ?_⟩
    have := (isCompact_boundaryRect z w).eventually_forall_of_forall_eventually (x₀ := t₀)
      (P := fun t ζ => m < ‖heatE t f ζ‖) (fun ζ hζ => ?_)
    · exact this.mono fun t ht ζ hζ => (ht ζ hζ).le
    · have hlt : m < ‖heatE t₀ f ζ‖ := by
        have h2 : ‖heatE t₀ f ζ₀‖ ≤ ‖heatE t₀ f ζ‖ := hmin hζ
        have hpos := norm_pos_iff.mpr (hne ζ₀ hζ₀)
        linarith
      exact (hcont.continuousAt (x := (t₀, ζ))).eventually (lt_mem_nhds hlt)

/-- Continuity in `t` of an edge integral of `H_t′/H_t` along an edge in the boundary. -/
theorem continuousAt_edge (hf : Differentiable ℂ f) (hg : HasGrowth f A B ρ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hρ0 : 0 < ρ) (hρ2 : ρ < 2) {z w : ℂ} {t₀ : ℝ}
    (hne : ∀ ζ ∈ boundaryRect z w, heatE t₀ f ζ ≠ 0) {e : ℝ → ℂ} (he : Continuous e) {a b : ℝ}
    (hedge : ∀ x ∈ [[a, b]], e x ∈ boundaryRect z w) :
    ContinuousAt (fun t => ∫ x in a..b, logDeriv (heatE t f) (e x)) t₀ := by
  obtain ⟨m, hm0, hev⟩ := eventually_boundary_ge hf hg hA hB hρ0 hρ2 hne
  have hf' : Differentiable ℂ (deriv f) := hf.deriv
  have hg' := hasGrowth_deriv hf hg hA hB hρ0.le
  set T : ℝ := |t₀| + 1 with hT
  set R : ℝ := 2 * (‖z‖ + ‖w‖) with hR
  have hT0 : 0 ≤ T := by positivity
  have hR0 : 0 ≤ R := by positivity
  set Kd : ℝ := K (A * Real.exp (B * 2 ^ ρ)) (B * 2 ^ ρ) ρ T R with hKd
  have hcont_e : ∀ t, ∀ x ∈ [[a, b]], heatE t f (e x) ≠ 0 → True := fun _ _ _ _ => trivial
  have hderiv_cont : ∀ t, Continuous (deriv (heatE t f)) :=
    fun t => (differentiable_heatE hf hg hA hB hρ0 hρ2 t).deriv.continuous
  have hH_cont : ∀ t, Continuous (heatE t f) :=
    fun t => (differentiable_heatE hf hg hA hB hρ0 hρ2 t).continuous
  have hev1 : ∀ᶠ t in 𝓝 t₀, |t - t₀| < 1 := by
    have : Ioo (t₀ - 1) (t₀ + 1) ∈ 𝓝 t₀ := Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [this] with t ht
    rw [mem_Ioo] at ht
    rw [abs_lt]
    constructor <;> linarith
  refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => Kd / m) ?_ ?_ ?_ ?_
  · filter_upwards [hev] with t ht
    have hc : ContinuousOn (fun x => logDeriv (heatE t f) (e x)) [[a, b]] := by
      have h1 : ContinuousOn (fun x => deriv (heatE t f) (e x)) [[a, b]] :=
        ((hderiv_cont t).comp he).continuousOn
      have h2 : ContinuousOn (fun x => heatE t f (e x)) [[a, b]] :=
        ((hH_cont t).comp he).continuousOn
      have h3 : ∀ x ∈ [[a, b]], heatE t f (e x) ≠ 0 := by
        intro x hx
        have := ht (e x) (hedge x hx)
        exact norm_pos_iff.mp (lt_of_lt_of_le hm0 this)
      exact (h1.div h2 h3).congr fun x _ => by simp [logDeriv_apply]
    exact (hc.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [hev, hev1] with t ht ht1
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hx' : x ∈ [[a, b]] := Set.uIoc_subset_uIcc hx
    have hζ := hedge x hx'
    have hlow := ht (e x) hζ
    have hne0 : heatE t f (e x) ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hm0 hlow)
    rw [logDeriv_apply, norm_div]
    have htT : |t| ≤ T := by
      rw [hT]
      calc |t| = |(t - t₀) + t₀| := by ring_nf
        _ ≤ |t - t₀| + |t₀| := abs_add_le _ _
        _ ≤ |t₀| + 1 := by linarith
    have hzR : ‖e x‖ ≤ R := norm_le_of_mem_closedRect (boundaryRect_subset_closedRect z w hζ)
    have hup : ‖deriv (heatE t f) (e x)‖ ≤ Kd := by
      rw [deriv_heatE hf hg hA hB hρ0 hρ2]
      exact norm_heatE_le hf' hg' (by positivity) (by positivity) hρ0 hρ2 hT0 hR0 htT hzR
    calc ‖deriv (heatE t f) (e x)‖ / ‖heatE t f (e x)‖ ≤ Kd / ‖heatE t f (e x)‖ :=
          div_le_div_of_nonneg_right hup (norm_nonneg _)
      _ ≤ Kd / m := by
          apply div_le_div_of_nonneg_left (K_nonneg (by positivity) hT0) hm0 hlow
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun x hx => ?_
    have hx' : x ∈ [[a, b]] := Set.uIoc_subset_uIcc hx
    have hζ := hedge x hx'
    have hne0 : heatE t₀ f (e x) ≠ 0 := hne (e x) hζ
    have h1 : ContinuousAt (fun t => deriv (heatE t f) (e x)) t₀ :=
      ((continuous_deriv_heatE hf hg hA hB hρ0 hρ2).comp
        (continuous_id.prodMk continuous_const)).continuousAt
    have h2 : ContinuousAt (fun t => heatE t f (e x)) t₀ :=
      ((continuous_heatE hf hg hA hB hρ0 hρ2).comp
        (continuous_id.prodMk continuous_const)).continuousAt
    have := h1.div h2 hne0
    simp only [logDeriv_apply]
    exact this

/-- The rectangle winding integral of `H_t` is continuous in `t` at `t₀`. -/
theorem continuousAt_rectIntegral_logDeriv (hf : Differentiable ℂ f) (hg : HasGrowth f A B ρ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hρ0 : 0 < ρ) (hρ2 : ρ < 2) {z w : ℂ} {t₀ : ℝ}
    (hne : ∀ ζ ∈ boundaryRect z w, heatE t₀ f ζ ≠ 0) :
    ContinuousAt (fun t => rectIntegral (logDeriv (heatE t f)) z w) t₀ := by
  unfold rectIntegral
  have hb := continuousAt_edge hf hg hA hB hρ0 hρ2 hne (e := fun x : ℝ => (x : ℂ) + z.im * I)
    (by fun_prop) (a := z.re) (b := w.re) (fun x hx => bottom_mem hx)
  have ht := continuousAt_edge hf hg hA hB hρ0 hρ2 hne (e := fun x : ℝ => (x : ℂ) + w.im * I)
    (by fun_prop) (a := z.re) (b := w.re) (fun x hx => top_mem hx)
  have hr := continuousAt_edge hf hg hA hB hρ0 hρ2 hne (e := fun y : ℝ => (w.re : ℂ) + y * I)
    (by fun_prop) (a := z.im) (b := w.im) (fun y hy => right_mem hy)
  have hl := continuousAt_edge hf hg hA hB hρ0 hρ2 hne (e := fun y : ℝ => (z.re : ℂ) + y * I)
    (by fun_prop) (a := z.im) (b := w.im) (fun y hy => left_mem hy)
  exact ((hb.sub ht).add (hr.const_smul I)).sub (hl.const_smul I)

end Soma.Holonics.RH.RectangleWindingContinuity
