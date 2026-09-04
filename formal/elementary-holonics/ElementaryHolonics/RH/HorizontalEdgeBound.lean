import ElementaryHolonics.RH.LandauAtHeight
import ElementaryHolonics.RH.ZeroGap

/-!
# The horizontal edges are bounded polynomially in the height

Choose the height `T ∈ [T₀, T₀ + 1]` at distance `1 / (2 (N + 1))` from the imaginary parts of
the zeros of `ξ` in the two Landau half discs about `2 ± iT₀`, where `N` is at most twice the
Jensen count.  On the two horizontal edges `x ± iT`, `−δ ≤ x ≤ 1 + δ`, `ξ` does not vanish and
`|ξ′/ξ| ≤ edgeBound C δ T₀ = 16 (heightBudget + heightCount log 2) / r + 2 heightCount (2 heightCount + 1)`
with `r = 8 (3 + δ)`: the Landau remainder plus the flux of at most `heightCount` zeros, each at
distance at least the gap.  The bound is polynomial in `T₀` (through `T₀ log T₀`).
-/

open Complex Metric Set Finset
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.LandauLemma
open Soma.Holonics.RH.LandauAtHeight
open Soma.Holonics.RH.ZeroGap

namespace Soma.Holonics.RH.HorizontalEdgeBound

theorem card_zeros_le_count {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (Z : ZeroFactorization f z₀ r) :
    (Z.zeros.card : ℝ) ≤ Z.count := by
  have h : Z.zeros.card ≤ Z.count := by
    unfold ZeroFactorization.count
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun ρ hρ => Z.mult_pos ρ hρ
  exact_mod_cast h

/-- At a point of the eighth disc whose imaginary part is at distance at least `ε` from every
zero of the factorization, `ξ` does not vanish and `|ξ′/ξ|` is the remainder plus `count / ε`. -/
theorem edge_bound_of_gap {z₀ : ℂ} {r : ℝ} (Z : ZeroFactorization riemannXi z₀ r) (hr : 0 < r)
    {R : ℝ} (hflux : ∀ z ∈ closedBall z₀ (r / 8), riemannXi z ≠ 0 →
      ‖logDeriv riemannXi z - ∑ ρ ∈ Z.zeros, (Z.mult ρ : ℂ) / (z - ρ)‖ ≤ R)
    {z : ℂ} (hz : z ∈ closedBall z₀ (r / 8)) {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ ρ ∈ Z.zeros, ε ≤ |z.im - ρ.im|) :
    riemannXi z ≠ 0 ∧ ‖logDeriv riemannXi z‖ ≤ R + Z.count / ε := by
  have hdist : ∀ ρ ∈ Z.zeros, ε ≤ ‖z - ρ‖ := fun ρ hρ =>
    (hgap ρ hρ).trans (by simpa using Complex.abs_im_le_norm (z - ρ))
  have hne : ∀ ρ ∈ Z.zeros, z - ρ ≠ 0 := fun ρ hρ h => by
    have := hdist ρ hρ
    rw [h, norm_zero] at this
    linarith
  have hz' : z ∈ ball z₀ r := by
    rw [mem_closedBall_iff_norm] at hz
    rw [mem_ball_iff_norm]
    linarith
  have hz2 : z ∈ ball z₀ (r / 2) := by
    rw [mem_closedBall_iff_norm] at hz
    rw [mem_ball_iff_norm]
    linarith
  have hξ : riemannXi z ≠ 0 := by
    rw [Z.factor z hz']
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (hne ρ hρ))
      (Z.unit_ne z hz2)
  refine ⟨hξ, ?_⟩
  have hfluxnorm : ‖∑ ρ ∈ Z.zeros, (Z.mult ρ : ℂ) / (z - ρ)‖ ≤ Z.count / ε := by
    calc ‖∑ ρ ∈ Z.zeros, (Z.mult ρ : ℂ) / (z - ρ)‖
        ≤ ∑ ρ ∈ Z.zeros, ‖(Z.mult ρ : ℂ) / (z - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z.zeros, (Z.mult ρ : ℝ) / ε := by
          apply Finset.sum_le_sum
          intro ρ hρ
          rw [norm_div, Complex.norm_natCast]
          exact div_le_div_of_nonneg_left (by positivity) hε (hdist ρ hρ)
      _ = Z.count / ε := by
          rw [← Finset.sum_div]
          unfold ZeroFactorization.count
          push_cast
          rfl
  calc ‖logDeriv riemannXi z‖
      = ‖(logDeriv riemannXi z - ∑ ρ ∈ Z.zeros, (Z.mult ρ : ℂ) / (z - ρ)) +
          ∑ ρ ∈ Z.zeros, (Z.mult ρ : ℂ) / (z - ρ)‖ := by rw [sub_add_cancel]
    _ ≤ ‖logDeriv riemannXi z - ∑ ρ ∈ Z.zeros, (Z.mult ρ : ℂ) / (z - ρ)‖ +
          ‖∑ ρ ∈ Z.zeros, (Z.mult ρ : ℂ) / (z - ρ)‖ := norm_add_le _ _
    _ ≤ R + Z.count / ε := add_le_add (hflux z hz hξ) hfluxnorm

/-- The explicit bound on `|ξ′/ξ|` along the selected horizontal edges. -/
noncomputable def edgeBound (C δ T₀ : ℝ) : ℝ :=
  16 * (heightBudget C (8 * (3 + δ)) T₀ + heightCount C (8 * (3 + δ)) T₀ * Real.log 2) /
      (8 * (3 + δ)) +
    2 * heightCount C (8 * (3 + δ)) T₀ * (2 * heightCount C (8 * (3 + δ)) T₀ + 1)

theorem heightCount_neg (C r τ : ℝ) : heightCount C r (-τ) = heightCount C r τ := by
  simp [heightCount, heightBudget, abs_neg]

theorem heightBudget_neg (C r τ : ℝ) : heightBudget C r (-τ) = heightBudget C r τ := by
  simp [heightBudget, abs_neg]

theorem norm_edge_sub_le {x T τ δ : ℝ} (hx : x ∈ Icc (-δ) (1 + δ)) (hT : |T - τ| ≤ 1) :
    ‖((x : ℂ) + T * I) - (2 + τ * I)‖ ≤ 3 + δ := by
  have e : ((x : ℂ) + T * I) - (2 + τ * I) = ((x - 2 : ℝ) : ℂ) + ((T - τ : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [e]
  calc ‖((x - 2 : ℝ) : ℂ) + ((T - τ : ℝ) : ℂ) * I‖
      ≤ ‖((x - 2 : ℝ) : ℂ)‖ + ‖((T - τ : ℝ) : ℂ) * I‖ := norm_add_le _ _
    _ = |x - 2| + |T - τ| := by
        simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (2 + δ) + 1 := by
        gcongr
        rw [abs_le]
        constructor <;> linarith [hx.1, hx.2]
    _ = 3 + δ := by ring

/-- **The horizontal-edge bound.**  For `T₀ ≥ 2` there is a height `T ∈ [T₀, T₀ + 1]` such
that on both horizontal edges `x ± iT`, `−δ ≤ x ≤ 1 + δ`, `ξ` does not vanish and
`|ξ′/ξ| ≤ edgeBound C δ T₀`. -/
theorem exists_good_height {C : ℝ} (hC : 0 < C)
    (hgrowth : ∀ z : ℂ, Real.log ‖riemannXi z‖ ≤ C * (‖z‖ + 3) * Real.log (‖z‖ + 3))
    {δ : ℝ} (hδ : 0 < δ) {T₀ : ℝ} (hT₀ : 2 ≤ T₀) :
    ∃ T ∈ Icc T₀ (T₀ + 1), ∀ x ∈ Icc (-δ) (1 + δ),
      (riemannXi (x + T * I) ≠ 0 ∧ ‖logDeriv riemannXi (x + T * I)‖ ≤ edgeBound C δ T₀) ∧
      (riemannXi (x + ((-T : ℝ) : ℂ) * I) ≠ 0 ∧
        ‖logDeriv riemannXi (x + ((-T : ℝ) : ℂ) * I)‖ ≤ edgeBound C δ T₀) := by
  classical
  set r : ℝ := 8 * (3 + δ) with hr_def
  have hr : 0 < r := by rw [hr_def]; linarith
  have hr8 : r / 8 = 3 + δ := by rw [hr_def]; ring
  have hτ : 2 ≤ |T₀| := by rw [abs_of_pos (by linarith)]; exact hT₀
  have hτ' : 2 ≤ |-T₀| := by rw [abs_neg]; exact hτ
  obtain ⟨Zp, hKp, hfluxp⟩ := exists_zeroFactorization_at_height hC hgrowth hr hτ
  obtain ⟨Zm, hKm, hfluxm⟩ := exists_zeroFactorization_at_height hC hgrowth hr hτ'
  rw [heightCount_neg] at hKm
  rw [heightCount_neg, heightBudget_neg] at hfluxm
  set K := heightCount C r T₀ with hK_def
  set B := heightBudget C r T₀ with hB_def
  have hK0 : 0 ≤ K := heightCount_nonneg C r T₀
  set S : Finset ℝ := Zp.zeros.image (fun ρ => ρ.im) ∪ Zm.zeros.image (fun ρ => -ρ.im) with hS_def
  have hScard : (S.card : ℝ) ≤ 2 * K := by
    have h1 : S.card ≤ Zp.zeros.card + Zm.zeros.card :=
      (Finset.card_union_le _ _).trans (add_le_add Finset.card_image_le Finset.card_image_le)
    have h2 := card_zeros_le_count Zp
    have h3 := card_zeros_le_count Zm
    have h1' : (S.card : ℝ) ≤ Zp.zeros.card + Zm.zeros.card := by exact_mod_cast h1
    linarith
  obtain ⟨T, hT, hgapS⟩ := exists_gap S T₀
  set ε : ℝ := 1 / (2 * (S.card + 1 : ℝ)) with hε_def
  have hε : 0 < ε := by positivity
  have hinv : Zp.count / ε ≤ 2 * K * (2 * K + 1) ∧ Zm.count / ε ≤ 2 * K * (2 * K + 1) := by
    have hinv_eq : ∀ c : ℝ, c / ε = c * (2 * (S.card + 1)) := by
      intro c
      rw [hε_def, div_div_eq_mul_div, div_one]
    constructor
    · rw [hinv_eq]
      calc (Zp.count : ℝ) * (2 * (S.card + 1)) ≤ K * (2 * (2 * K + 1)) := by gcongr
        _ = 2 * K * (2 * K + 1) := by ring
    · rw [hinv_eq]
      calc (Zm.count : ℝ) * (2 * (S.card + 1)) ≤ K * (2 * (2 * K + 1)) := by gcongr
        _ = 2 * K * (2 * K + 1) := by ring
  refine ⟨T, hT, fun x hx => ⟨?_, ?_⟩⟩
  · -- the top edge
    have hz : (x : ℂ) + T * I ∈ closedBall (2 + T₀ * I) (r / 8) := by
      rw [mem_closedBall_iff_norm, hr8]
      exact norm_edge_sub_le hx (by rw [abs_le]; constructor <;> linarith [hT.1, hT.2])
    have hgap : ∀ ρ ∈ Zp.zeros, ε ≤ |((x : ℂ) + T * I).im - ρ.im| := by
      intro ρ hρ
      have hmem : ρ.im ∈ S := Finset.mem_union_left _ (Finset.mem_image_of_mem _ hρ)
      have := hgapS ρ.im hmem
      simpa using this
    obtain ⟨hne, hbd⟩ := edge_bound_of_gap Zp hr hfluxp hz hε hgap
    refine ⟨hne, hbd.trans ?_⟩
    unfold edgeBound
    rw [← hr_def, ← hB_def, ← hK_def]
    linarith [hinv.1]
  · -- the bottom edge
    have hz : (x : ℂ) + ((-T : ℝ) : ℂ) * I ∈ closedBall (2 + ((-T₀ : ℝ) : ℂ) * I) (r / 8) := by
      rw [mem_closedBall_iff_norm, hr8]
      exact norm_edge_sub_le hx (by rw [abs_le]; constructor <;> linarith [hT.1, hT.2])
    have hgap : ∀ ρ ∈ Zm.zeros, ε ≤ |((x : ℂ) + ((-T : ℝ) : ℂ) * I).im - ρ.im| := by
      intro ρ hρ
      have hmem : -ρ.im ∈ S := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hρ)
      have := hgapS (-ρ.im) hmem
      have e : ((x : ℂ) + ((-T : ℝ) : ℂ) * I).im - ρ.im = -(T - -ρ.im) := by simp; ring
      rw [e, abs_neg]
      exact this
    obtain ⟨hne, hbd⟩ := edge_bound_of_gap Zm hr hfluxm hz hε hgap
    refine ⟨hne, hbd.trans ?_⟩
    unfold edgeBound
    rw [← hr_def, ← hB_def, ← hK_def]
    linarith [hinv.2]

end Soma.Holonics.RH.HorizontalEdgeBound
