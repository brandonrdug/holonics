import ElementaryHolonics.RH.ExplicitFormulaLimit
import ElementaryHolonics.RH.ArchimedeanPolynomialBound
import ElementaryHolonics.RH.SpectralKernelDecay

/-!
# The prime side converges, and the explicit formula is classical

With the archimedean term bounded by `C (1 + |t|)` and the weight by `K / (1 + |t|)^5` on the
line `Re s = 1 + δ`, the archimedean integrals converge absolutely, each von Mangoldt integral
converges, and Tannery's theorem exchanges the limit in the height with the sum over `n`.
Hence `primeSide δ h T` converges as `T → ∞` to `primeSideLimit δ h`, the prime side with
improper integrals over the whole line, and the explicit formula reads
`2πi · zeroSide δ h (T_n) → primeSideLimit δ h` along the selected heights: the zero comb of `ξ`
converges to the prime comb.  For the corpus's Weil test functions this holds with no further
hypothesis.
-/

open Complex MeasureTheory Set Filter Topology
open Soma.Holonics.RH.XiEdgeDecomposition
open Soma.Holonics.RH.PrimeSideVertical
open Soma.Holonics.RH.ExplicitFormulaLimit
open Soma.Holonics.RH.ArchimedeanPolynomialBound
open Soma.Holonics.RH.ExplicitFormulaReceiver
open Soma.Holonics.RH.SpectralKernelDecay

namespace Soma.Holonics.RH.PrimeSideConverges

/-- The prime side at infinite height: improper integrals over the whole line `Re s = 1 + δ`. -/
noncomputable def primeSideLimit (δ : ℝ) (h : ℂ → ℂ) : ℂ :=
  I • ((∫ t : ℝ, h (((1 + δ : ℝ) : ℂ) + t * I) * archimedean (((1 + δ : ℝ) : ℂ) + t * I)) -
      ∑' n, ∫ t : ℝ, h (((1 + δ : ℝ) : ℂ) + t * I) *
        LSeries.term vonMangoldtC (((1 + δ : ℝ) : ℂ) + t * I) n) +
    I • ((∫ t : ℝ, h (1 - (((1 + δ : ℝ) : ℂ) + t * I)) * archimedean (((1 + δ : ℝ) : ℂ) + t * I)) -
      ∑' n, ∫ t : ℝ, h (1 - (((1 + δ : ℝ) : ℂ) + t * I)) *
        LSeries.term vonMangoldtC (((1 + δ : ℝ) : ℂ) + t * I) n)

/-- The decay majorant `(1 + |t|)^{-k}` is integrable on the line for `k ≥ 2`. -/
theorem integrable_decay (k : ℕ) (hk : 2 ≤ k) : Integrable fun t : ℝ => 1 / (1 + |t|) ^ k := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := k)
    (by rw [Module.finrank_self]; exact_mod_cast (by omega : 1 < k))
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only [Real.norm_eq_abs]
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, one_div]

theorem integrable_mul_archimedean {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {g : ℂ → ℂ}
    (hg : Continuous g) {K : ℝ} (hK : 0 ≤ K)
    (hgd : ∀ t : ℝ, ‖g (((1 + δ : ℝ) : ℂ) + t * I)‖ ≤ K / (1 + |t|) ^ 5) :
    Integrable fun t : ℝ =>
      g (((1 + δ : ℝ) : ℂ) + t * I) * archimedean (((1 + δ : ℝ) : ℂ) + t * I) := by
  obtain ⟨C, hC0, hC⟩ := exists_archimedean_bound hδ hδ1
  have hcont : Continuous fun t : ℝ =>
      g (((1 + δ : ℝ) : ℂ) + t * I) * archimedean (((1 + δ : ℝ) : ℂ) + t * I) := by
    apply Continuous.mul
    · exact hg.comp (continuous_edge (1 + δ))
    · exact continuousOn_archimedean.comp_continuous (continuous_edge (1 + δ))
        fun t => edge_mem (by linarith) t
  refine ((integrable_decay 4 (by norm_num)).const_mul (K * C)).mono'
    hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [norm_mul]
  have hpos : 0 < 1 + |t| := by positivity
  calc ‖g (((1 + δ : ℝ) : ℂ) + t * I)‖ * ‖archimedean (((1 + δ : ℝ) : ℂ) + t * I)‖
      ≤ K / (1 + |t|) ^ 5 * (C * (1 + |t|)) :=
        mul_le_mul (hgd t) (hC t) (norm_nonneg _) (by positivity)
    _ = K * C * (1 / (1 + |t|) ^ 4) := by
        field_simp

theorem integrable_mul_term {δ : ℝ} (hδ : 0 < δ) {g : ℂ → ℂ} (hg : Continuous g) {K : ℝ}
    (hK : 0 ≤ K) (hgd : ∀ t : ℝ, ‖g (((1 + δ : ℝ) : ℂ) + t * I)‖ ≤ K / (1 + |t|) ^ 5) (n : ℕ) :
    Integrable fun t : ℝ =>
      g (((1 + δ : ℝ) : ℂ) + t * I) * LSeries.term vonMangoldtC (((1 + δ : ℝ) : ℂ) + t * I) n := by
  have hcont : Continuous fun t : ℝ =>
      g (((1 + δ : ℝ) : ℂ) + t * I) * LSeries.term vonMangoldtC (((1 + δ : ℝ) : ℂ) + t * I) n :=
    (hg.comp (continuous_edge (1 + δ))).mul ((continuous_term n).comp (continuous_edge (1 + δ)))
  refine ((integrable_decay 5 (by norm_num)).const_mul
    (K * ‖LSeries.term vonMangoldtC ((1 + δ : ℝ) : ℂ) n‖)).mono'
    hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [norm_mul, show (((1 + δ : ℝ) : ℂ) + t * I) = edge (1 + δ) t from rfl, norm_term_edge]
  calc ‖g (edge (1 + δ) t)‖ * ‖LSeries.term vonMangoldtC ((1 + δ : ℝ) : ℂ) n‖
      ≤ K / (1 + |t|) ^ 5 * ‖LSeries.term vonMangoldtC ((1 + δ : ℝ) : ℂ) n‖ := by
        gcongr
        exact hgd t
    _ = K * ‖LSeries.term vonMangoldtC ((1 + δ : ℝ) : ℂ) n‖ * (1 / (1 + |t|) ^ 5) := by ring

theorem tendsto_intervalIntegral {f : ℝ → ℂ} (hf : Integrable f) :
    Tendsto (fun T : ℝ => ∫ t in (-T)..T, f t) atTop (𝓝 (∫ t, f t)) :=
  intervalIntegral_tendsto_integral hf tendsto_neg_atTop_atBot tendsto_id

/-- Tannery's theorem exchanges the height limit with the von Mangoldt sum. -/
theorem tendsto_tsum_intervalIntegral {δ : ℝ} (hδ : 0 < δ) {g : ℂ → ℂ} (hg : Continuous g)
    {K : ℝ} (hK : 0 ≤ K)
    (hgd : ∀ t : ℝ, ‖g (((1 + δ : ℝ) : ℂ) + t * I)‖ ≤ K / (1 + |t|) ^ 5) :
    Tendsto (fun T : ℝ => ∑' n, ∫ t in (-T)..T,
        g (((1 + δ : ℝ) : ℂ) + t * I) * LSeries.term vonMangoldtC (((1 + δ : ℝ) : ℂ) + t * I) n)
      atTop (𝓝 (∑' n, ∫ t : ℝ,
        g (((1 + δ : ℝ) : ℂ) + t * I) * LSeries.term vonMangoldtC (((1 + δ : ℝ) : ℂ) + t * I) n)) := by
  have hdec := integrable_decay 5 (by norm_num)
  apply tendsto_tsum_of_dominated_convergence
    (bound := fun n => K * ‖LSeries.term vonMangoldtC ((1 + δ : ℝ) : ℂ) n‖ * ∫ t : ℝ, 1 / (1 + |t|) ^ 5)
  · exact ((summable_norm_term (by linarith)).mul_left K).mul_right _
  · intro n
    exact tendsto_intervalIntegral (integrable_mul_term hδ hg hK hgd n)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    intro n
    have hint := integrable_mul_term hδ hg hK hgd n
    calc ‖∫ t in (-T)..T, g (((1 + δ : ℝ) : ℂ) + t * I) *
            LSeries.term vonMangoldtC (((1 + δ : ℝ) : ℂ) + t * I) n‖
        ≤ ∫ t in (-T)..T, ‖g (((1 + δ : ℝ) : ℂ) + t * I) *
            LSeries.term vonMangoldtC (((1 + δ : ℝ) : ℂ) + t * I) n‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ = ∫ t in Ioc (-T) T, ‖g (((1 + δ : ℝ) : ℂ) + t * I) *
            LSeries.term vonMangoldtC (((1 + δ : ℝ) : ℂ) + t * I) n‖ :=
          intervalIntegral.integral_of_le (by linarith)
      _ ≤ ∫ t : ℝ, ‖g (((1 + δ : ℝ) : ℂ) + t * I) *
            LSeries.term vonMangoldtC (((1 + δ : ℝ) : ℂ) + t * I) n‖ :=
          setIntegral_le_integral hint.norm (Eventually.of_forall fun t => norm_nonneg _)
      _ ≤ ∫ t : ℝ, K * ‖LSeries.term vonMangoldtC ((1 + δ : ℝ) : ℂ) n‖ * (1 / (1 + |t|) ^ 5) := by
          apply integral_mono hint.norm (hdec.const_mul _)
          intro t
          beta_reduce
          rw [norm_mul, show (((1 + δ : ℝ) : ℂ) + t * I) = edge (1 + δ) t from rfl, norm_term_edge]
          calc ‖g (edge (1 + δ) t)‖ * ‖LSeries.term vonMangoldtC ((1 + δ : ℝ) : ℂ) n‖
              ≤ K / (1 + |t|) ^ 5 * ‖LSeries.term vonMangoldtC ((1 + δ : ℝ) : ℂ) n‖ := by
                gcongr
                exact hgd t
            _ = K * ‖LSeries.term vonMangoldtC ((1 + δ : ℝ) : ℂ) n‖ * (1 / (1 + |t|) ^ 5) := by ring
      _ = K * ‖LSeries.term vonMangoldtC ((1 + δ : ℝ) : ℂ) n‖ * ∫ t : ℝ, 1 / (1 + |t|) ^ 5 :=
          integral_const_mul _ _

/-- **The prime side converges.** -/
theorem tendsto_primeSide {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {h : ℂ → ℂ}
    (hh : Differentiable ℂ h) {K : ℝ} (hK : 0 ≤ K)
    (hdecay : ∀ x ∈ Icc (-δ) (1 + δ), ∀ t : ℝ, ‖h (x + t * I)‖ ≤ K / (1 + |t|) ^ 5) :
    Tendsto (fun T => primeSide δ h T) atTop (𝓝 (primeSideLimit δ h)) := by
  have hc : Continuous h := hh.continuous
  have hc' : Continuous fun s => h (1 - s) := hc.comp (continuous_const.sub continuous_id)
  have hgd1 : ∀ t : ℝ, ‖h (((1 + δ : ℝ) : ℂ) + t * I)‖ ≤ K / (1 + |t|) ^ 5 := fun t =>
    hdecay (1 + δ) ⟨by linarith, le_rfl⟩ t
  have hgd2 : ∀ t : ℝ, ‖(fun s => h (1 - s)) (((1 + δ : ℝ) : ℂ) + t * I)‖ ≤ K / (1 + |t|) ^ 5 := by
    intro t
    show ‖h (1 - (((1 + δ : ℝ) : ℂ) + t * I))‖ ≤ _
    have e : (1 : ℂ) - (((1 + δ : ℝ) : ℂ) + t * I) = ((-δ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [e]
    have := hdecay (-δ) ⟨le_rfl, by linarith⟩ (-t)
    rwa [abs_neg] at this
  simp only [primeSide, primeSideLimit]
  refine Tendsto.add (Tendsto.const_smul (Tendsto.sub ?_ ?_) I)
    (Tendsto.const_smul (Tendsto.sub ?_ ?_) I)
  · exact tendsto_intervalIntegral (integrable_mul_archimedean hδ hδ1 hc hK hgd1)
  · exact tendsto_tsum_intervalIntegral hδ hc hK hgd1
  · exact tendsto_intervalIntegral (integrable_mul_archimedean hδ hδ1 hc' hK hgd2)
  · exact tendsto_tsum_intervalIntegral hδ hc' hK hgd2

/-- **The explicit formula, classical form.**  Along the selected heights the weighted zero comb
of `ξ` converges to the prime side at infinite height. -/
theorem explicit_formula_classical {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {h : ℂ → ℂ}
    (hh : Differentiable ℂ h) {K : ℝ} (hK : 0 ≤ K)
    (hdecay : ∀ x ∈ Icc (-δ) (1 + δ), ∀ t : ℝ, ‖h (x + t * I)‖ ≤ K / (1 + |t|) ^ 5) :
    ∃ T : ℕ → ℝ, (∀ n : ℕ, T n ∈ Icc ((n : ℝ) + 2) ((n : ℝ) + 3)) ∧
      Tendsto (fun n => 2 * Real.pi * I * zeroSide δ h (T n)) atTop (𝓝 (primeSideLimit δ h)) := by
  obtain ⟨T, hT, htend⟩ := explicit_formula_limit hδ hh hK hdecay
  refine ⟨T, hT, ?_⟩
  have hTinf : Tendsto T atTop atTop :=
    tendsto_atTop_mono (fun n => (hT n).1)
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hp := (tendsto_primeSide hδ hδ1 hh hK hdecay).comp hTinf
  have := htend.add hp
  simpa using this

/-- **The explicit formula, classical form, for every Weil test function of the corpus.** -/
theorem explicit_formula_classical_weil (W : WeilTestFunction) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    ∃ T : ℕ → ℝ, (∀ n : ℕ, T n ∈ Icc ((n : ℝ) + 2) ((n : ℝ) + 3)) ∧
      Tendsto (fun n => 2 * Real.pi * I * zeroSide δ W.spectralKernel (T n)) atTop
        (𝓝 (primeSideLimit δ W.spectralKernel)) := by
  obtain ⟨K, hK, hdecay⟩ := exists_strip_decay W 5 hδ
  exact explicit_formula_classical hδ hδ1 W.spectralAnalytic hK hdecay

end Soma.Holonics.RH.PrimeSideConverges
