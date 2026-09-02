import ElementaryHolonics.RH.HorizontalEdgeBound

/-!
# The horizontal-edge integrals vanish under polynomial decay

The edge bound is at most `edgeConst C δ · (T₀ + 1)⁴` for `T₀ ≥ 2`, and the edges have length
`1 + 2δ`.  A weight bounded by `K / (1 + |t|)⁵` on the strip therefore makes both horizontal-edge
integrals at the selected height `T ∈ [T₀, T₀ + 1]` at most `K · edgeConst · (1 + 2δ) / (1 + T₀)`,
which tends to zero with the height.
-/

open Complex Metric Set Finset
open scoped Interval
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.LandauAtHeight
open Soma.Holonics.RH.HorizontalEdgeBound

namespace Soma.Holonics.RH.EdgeIntegralVanishes

/-- The polynomial constant of the budget. -/
noncomputable def budgetConst (C r : ℝ) : ℝ := C * (5 + r) ^ 2 + 3

/-- The polynomial constant of the count. -/
noncomputable def countConst (C r : ℝ) : ℝ := (budgetConst C r + 2) / Real.log (3 / 2)

/-- The polynomial constant of the edge bound. -/
noncomputable def edgeConst (C δ : ℝ) : ℝ :=
  16 * (budgetConst C (8 * (3 + δ)) + countConst C (8 * (3 + δ)) * Real.log 2) /
      (8 * (3 + δ)) +
    2 * countConst C (8 * (3 + δ)) * (2 * countConst C (8 * (3 + δ)) + 1)

theorem budgetConst_nonneg {C r : ℝ} (hC : 0 < C) (hr : 0 < r) : 0 ≤ budgetConst C r := by
  unfold budgetConst
  positivity

theorem countConst_nonneg {C r : ℝ} (hC : 0 < C) (hr : 0 < r) : 0 ≤ countConst C r := by
  unfold countConst
  apply div_nonneg
  · linarith [budgetConst_nonneg hC hr]
  · exact (Real.log_pos (by norm_num)).le

theorem heightBudget_le {C r τ : ℝ} (hC : 0 < C) (hr : 0 < r) (hτ : 2 ≤ |τ|) :
    heightBudget C r τ ≤ budgetConst C r * (|τ| + 1) ^ 2 := by
  unfold heightBudget budgetConst
  have hu1 : 1 ≤ |τ| + 1 := by linarith [abs_nonneg τ]
  have hu2 : 1 ≤ (|τ| + 1) ^ 2 := one_le_pow₀ hu1
  apply max_le
  · nlinarith [mul_nonneg hC.le (sq_nonneg (5 + r))]
  · have hv : 0 ≤ 2 + |τ| + r + 3 := by positivity
    have hlog : Real.log (2 + |τ| + r + 3) ≤ 2 + |τ| + r + 3 := Real.log_le_self hv
    have h1 : 2 + |τ| + r + 3 ≤ (5 + r) * (|τ| + 1) := by
      have : 4 + r ≤ (4 + r) * (|τ| + 1) := le_mul_of_one_le_right (by linarith) hu1
      nlinarith
    have h2 : C * (2 + |τ| + r + 3) * Real.log (2 + |τ| + r + 3) ≤
        C * ((5 + r) * (|τ| + 1)) * ((5 + r) * (|τ| + 1)) := by
      calc C * (2 + |τ| + r + 3) * Real.log (2 + |τ| + r + 3)
          ≤ C * (2 + |τ| + r + 3) * (2 + |τ| + r + 3) :=
            mul_le_mul_of_nonneg_left hlog (by positivity)
        _ ≤ C * ((5 + r) * (|τ| + 1)) * ((5 + r) * (|τ| + 1)) := by gcongr
    have h3 : |τ| + 2 ≤ 3 * (|τ| + 1) ^ 2 := by nlinarith
    nlinarith [h2, h3]

theorem heightCount_le {C r τ : ℝ} (hC : 0 < C) (hr : 0 < r) (hτ : 2 ≤ |τ|) :
    heightCount C r τ ≤ countConst C r * (|τ| + 1) ^ 2 := by
  unfold heightCount countConst
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 3 / 2)).le
  have hB := heightBudget_le hC hr hτ
  have hu1 : 1 ≤ |τ| + 1 := by linarith [abs_nonneg τ]
  have hu2 : |τ| + 2 ≤ 2 * (|τ| + 1) ^ 2 := by nlinarith
  nlinarith

theorem edgeBound_le {C δ T₀ : ℝ} (hC : 0 < C) (hδ : 0 < δ) (hT₀ : 2 ≤ T₀) :
    edgeBound C δ T₀ ≤ edgeConst C δ * (T₀ + 1) ^ 4 := by
  have hr : 0 < 8 * (3 + δ) := by linarith
  have hτ : 2 ≤ |T₀| := by rw [abs_of_pos (by linarith)]; exact hT₀
  have hB := heightBudget_le hC hr hτ
  have hK := heightCount_le hC hr hτ
  rw [abs_of_pos (by linarith : 0 < T₀)] at hB hK
  have hK0 := heightCount_nonneg C (8 * (3 + δ)) T₀
  have hb0 := budgetConst_nonneg hC hr
  have hc0 := countConst_nonneg hC hr
  have hu1 : 1 ≤ T₀ + 1 := by linarith
  have hu24 : (T₀ + 1) ^ 2 ≤ (T₀ + 1) ^ 4 := pow_le_pow_right₀ hu1 (by norm_num)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold edgeBound edgeConst
  set B := heightBudget C (8 * (3 + δ)) T₀
  set K := heightCount C (8 * (3 + δ)) T₀
  set b := budgetConst C (8 * (3 + δ))
  set c := countConst C (8 * (3 + δ))
  set u := T₀ + 1
  have t1 : 16 * (B + K * Real.log 2) / (8 * (3 + δ)) ≤
      16 * (b + c * Real.log 2) / (8 * (3 + δ)) * u ^ 4 := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hr.le
    have : B + K * Real.log 2 ≤ (b + c * Real.log 2) * u ^ 2 := by nlinarith
    have h0 : 0 ≤ b + c * Real.log 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hu24 h0]
  have t2 : 2 * K * (2 * K + 1) ≤ 2 * c * (2 * c + 1) * u ^ 4 := by
    have hK2 : K * K ≤ (c * u ^ 2) * (c * u ^ 2) := mul_le_mul hK hK hK0 (by positivity)
    have hKu : K ≤ c * u ^ 4 := hK.trans (mul_le_mul_of_nonneg_left hu24 hc0)
    nlinarith [hK2, hKu]
  linarith

/-- A bounded weight times a bounded log derivative gives a bounded edge integral. -/
theorem norm_edge_integral_le {h : ℂ → ℂ} {δ T K B : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (hh : ∀ x ∈ Icc (-δ) (1 + δ), ‖h (x + T * I)‖ ≤ K)
    (hξ : ∀ x ∈ Icc (-δ) (1 + δ), ‖logDeriv riemannXi (x + T * I)‖ ≤ B) :
    ‖∫ x in (-δ)..(1 + δ), h (x + T * I) * logDeriv riemannXi (x + T * I)‖ ≤
      K * B * (1 + 2 * δ) := by
  have hle : (-δ : ℝ) ≤ 1 + δ := by linarith
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -δ) (b := 1 + δ) (C := K * B)
    (f := fun x : ℝ => h (x + T * I) * logDeriv riemannXi (x + T * I)) (fun x hx => by
      rw [Set.uIoc_of_le hle] at hx
      have hx' : x ∈ Icc (-δ) (1 + δ) := Ioc_subset_Icc_self hx
      rw [norm_mul]
      exact mul_le_mul (hh x hx') (hξ x hx') (norm_nonneg _) hK)
  rw [show |(1 + δ) - -δ| = 1 + 2 * δ by rw [abs_of_pos (by linarith)]; ring] at this
  exact this

/-- **The horizontal edges vanish.**  Under decay `‖h(x + it)‖ ≤ K / (1 + |t|)⁵` on the strip,
there is a height `T ∈ [T₀, T₀ + 1]` on whose two horizontal edges `ξ` does not vanish and both
edge integrals are at most `K · edgeConst · (1 + 2δ) / (1 + T₀)`. -/
theorem exists_height_edges_small {C : ℝ} (hC : 0 < C)
    (hgrowth : ∀ z : ℂ, Real.log ‖riemannXi z‖ ≤ C * (‖z‖ + 3) * Real.log (‖z‖ + 3))
    {δ : ℝ} (hδ : 0 < δ) {h : ℂ → ℂ} {K : ℝ} (hK : 0 ≤ K)
    (hdecay : ∀ x ∈ Icc (-δ) (1 + δ), ∀ t : ℝ, ‖h (x + t * I)‖ ≤ K / (1 + |t|) ^ 5)
    {T₀ : ℝ} (hT₀ : 2 ≤ T₀) :
    ∃ T ∈ Icc T₀ (T₀ + 1),
      (∀ x ∈ Icc (-δ) (1 + δ),
        riemannXi (x + T * I) ≠ 0 ∧ riemannXi (x + ((-T : ℝ) : ℂ) * I) ≠ 0) ∧
      ‖∫ x in (-δ)..(1 + δ), h (x + T * I) * logDeriv riemannXi (x + T * I)‖ ≤
        K * edgeConst C δ * (1 + 2 * δ) / (1 + T₀) ∧
      ‖∫ x in (-δ)..(1 + δ),
          h (x + ((-T : ℝ) : ℂ) * I) * logDeriv riemannXi (x + ((-T : ℝ) : ℂ) * I)‖ ≤
        K * edgeConst C δ * (1 + 2 * δ) / (1 + T₀) := by
  obtain ⟨T, hT, hedge⟩ := exists_good_height hC hgrowth hδ hT₀
  have hTpos : 0 < T := by linarith [hT.1]
  have hE := edgeBound_le hC hδ hT₀
  have hE0 : 0 ≤ edgeConst C δ * (T₀ + 1) ^ 4 :=
    le_trans (by
      obtain ⟨x, hx⟩ : ∃ x, x ∈ Icc (-δ) (1 + δ) := ⟨0, by constructor <;> linarith⟩
      exact (norm_nonneg _).trans (hedge x hx).1.2) hE
  have hK' : 0 ≤ K / (1 + T) ^ 5 := by positivity
  have key : (T₀ + 1) ^ 4 / (1 + T) ^ 5 ≤ 1 / (1 + T₀) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h5 : (T₀ + 1) ^ 5 ≤ (1 + T) ^ 5 := pow_le_pow_left₀ (by linarith) (by linarith [hT.1]) 5
    nlinarith [h5]
  have hfinal : K / (1 + T) ^ 5 * (edgeConst C δ * (T₀ + 1) ^ 4) * (1 + 2 * δ) ≤
      K * edgeConst C δ * (1 + 2 * δ) / (1 + T₀) := by
    have hEc : 0 ≤ edgeConst C δ := by
      have := hE0
      have hp : 0 < (T₀ + 1) ^ 4 := by positivity
      exact nonneg_of_mul_nonneg_left this hp
    calc K / (1 + T) ^ 5 * (edgeConst C δ * (T₀ + 1) ^ 4) * (1 + 2 * δ)
        = K * edgeConst C δ * (1 + 2 * δ) * ((T₀ + 1) ^ 4 / (1 + T) ^ 5) := by ring
      _ ≤ K * edgeConst C δ * (1 + 2 * δ) * (1 / (1 + T₀)) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = K * edgeConst C δ * (1 + 2 * δ) / (1 + T₀) := by ring
  refine ⟨T, hT, fun x hx => ⟨(hedge x hx).1.1, (hedge x hx).2.1⟩, ?_, ?_⟩
  · refine le_trans (norm_edge_integral_le hδ hK' (fun x hx => ?_)
      (fun x hx => (hedge x hx).1.2.trans hE)) hfinal
    have := hdecay x hx T
    rwa [abs_of_pos hTpos] at this
  · refine le_trans (norm_edge_integral_le hδ hK' (fun x hx => ?_)
      (fun x hx => (hedge x hx).2.2.trans hE)) hfinal
    have := hdecay x hx (-T)
    rwa [abs_neg, abs_of_pos hTpos] at this

end Soma.Holonics.RH.EdgeIntegralVanishes
