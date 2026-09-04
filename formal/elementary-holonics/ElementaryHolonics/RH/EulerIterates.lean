import Mathlib
import ElementaryHolonics.RH.PolyaLine
import ElementaryHolonics.RH.HeatFlowEntire
import ElementaryHolonics.RH.ConjugationEntire
import ElementaryHolonics.RH.ZeroDynamicsEntire
import ElementaryHolonics.RH.HeatEquationEntire

/-!
# FT4 (iii): the Euler iterates converge to the flow

For an entire `f` of growth `A exp(B‖w‖^ρ)`, `ρ < 2`, and `λ ≥ 0`, the Euler iterates
`(1 + (λ/N) D²)^N f = Σ_k C(N,k) (λ/N)^k f^{(2k)}` converge to `heatE (−λ) f = Σ_k λ^k/k! f^{(2k)}`
locally uniformly as `N → ∞`, by Tannery's argument with the majorant of `HeatFlowEntire`. Every
theorem is discharged with no `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.RH.EulerIterates

open Complex Metric Set Filter Topology Finset
open Soma.Holonics.RH.EntireDerivativeGrowth
open Soma.Holonics.RH.HeatFlowEntire
open Soma.Holonics.RH.PolyaLine
open Soma.Holonics.RH.ForwardPreservation

variable {f : ℂ → ℂ} {A B ρ : ℝ}

/-- The coefficient of the Euler iterate. -/
def coeff (lam : ℝ) (N k : ℕ) : ℝ := (N.choose k : ℝ) * (lam / N) ^ k

theorem coeff_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (N k : ℕ) : 0 ≤ coeff lam N k := by
  unfold coeff
  positivity

theorem coeff_le {lam : ℝ} (hlam : 0 ≤ lam) (N k : ℕ) : coeff lam N k ≤ lam ^ k / k.factorial := by
  unfold coeff
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp
    · rw [Nat.choose_eq_zero_of_lt hk]
      simp only [Nat.cast_zero, zero_mul]
      positivity
  · have h := Nat.choose_le_pow_div (α := ℝ) k N
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_pow]
    have hN0 : (N : ℝ) ^ k ≠ 0 := pow_ne_zero _ hN'.ne'
    calc (N.choose k : ℝ) * (lam ^ k / (N : ℝ) ^ k)
        ≤ ((N : ℝ) ^ k / k.factorial) * (lam ^ k / (N : ℝ) ^ k) := by gcongr
      _ = lam ^ k / k.factorial := by
          field_simp

theorem tendsto_coeff (lam : ℝ) (k : ℕ) :
    Tendsto (fun N : ℕ => coeff lam N k) atTop (𝓝 (lam ^ k / k.factorial)) := by
  have := tendsto_choose_mul_pow (-lam) k
  simp only [neg_neg] at this
  exact this

theorem eulerIter_eq (lam : ℝ) (N : ℕ) (f : ℂ → ℂ) (z : ℂ) :
    eulerIter lam N f z = ∑ k ∈ range (N + 1), (coeff lam N k : ℂ) * iteratedDeriv (2 * k) f z := by
  unfold eulerIter coeff
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  ring

theorem heatE_neg_eq (lam : ℝ) (f : ℂ → ℂ) (z : ℂ) :
    heatE (-lam) f z = ∑' k : ℕ, ((lam ^ k / k.factorial : ℝ) : ℂ) * iteratedDeriv (2 * k) f z := by
  unfold heatE heatTerm
  apply tsum_congr
  intro k
  push_cast
  ring

theorem norm_term_eq (lam : ℝ) (hlam : 0 ≤ lam) (f : ℂ → ℂ) (z : ℂ) (k : ℕ) :
    ‖heatTerm (-lam) f z k‖ = lam ^ k / k.factorial * ‖iteratedDeriv (2 * k) f z‖ := by
  rw [norm_heatTerm, abs_neg, abs_of_nonneg hlam]

/-- **The Euler iterates converge to the flow locally uniformly.** -/
theorem tendsto_eulerIter (hf : Differentiable ℂ f) (hg : HasGrowth f A B ρ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hρ0 : 0 < ρ) (hρ2 : ρ < 2) {lam : ℝ} (hlam : 0 ≤ lam) :
    TendstoLocallyUniformly (fun N => eulerIter lam N f) (heatE (-lam) f) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  set r' : ℝ := max r 0 with hr'
  have hr'0 : 0 ≤ r' := le_max_right _ _
  have hKr : ∀ z ∈ K, ‖z‖ ≤ r' := fun z hz => by
    have := hr hz
    rw [mem_closedBall_zero_iff] at this
    exact this.trans (le_max_left _ _)
  -- the majorant
  set δ : ℝ := 2 / ρ - 1 with hδ
  have hδ0 : 0 < δ := by
    rw [hδ, sub_pos, lt_div_iff₀ hρ0]
    linarith
  set Cm : ℝ := 4 * Real.exp 1 * |(-lam)| * Real.exp (B * 2 ^ ρ) with hCm
  have hCm0 : 0 ≤ Cm := by positivity
  set maj : ℕ → ℝ := fun k => (A * Real.exp (B * 2 ^ ρ * r' ^ ρ)) * majorant Cm δ k with hmajdef
  have hmaj : Summable maj := (summable_majorant hCm0 hδ0).mul_left _
  have hmaj_nn : ∀ k, 0 ≤ maj k := fun k => by
    rw [hmajdef]
    simp only
    apply mul_nonneg (by positivity)
    unfold majorant
    split_ifs
    · exact zero_le_one
    · positivity
  have hbound : ∀ k, ∀ z ∈ K, ‖heatTerm (-lam) f z k‖ ≤ maj k := fun k z hz =>
    norm_heatTerm_le_majorant hf hg hA hB hρ0 (-lam) hr'0 (hKr z hz) k
  have hsumm : ∀ z, Summable (fun k => ‖heatTerm (-lam) f z k‖) :=
    fun z => summable_heatTerm hf hg hA hB hρ0 hρ2 (-lam) z
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- the tail of the majorant
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℕ, ∑' k, maj (k + K₀) < ε / 3 := by
    have := (tendsto_sum_nat_add maj).eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 3))
    exact this.exists
  -- bounds on the first `K₀` derivatives on `K`
  have hbdd : ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ K, ‖iteratedDeriv (2 * k) f z‖ ≤ M := by
    intro k
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
      (HeatEquationEntire.differentiable_iteratedDeriv hf (2 * k)).continuous.continuousOn
    refine ⟨max M 0, le_max_right _ _, fun z hz => (hM z hz).trans (le_max_left _ _)⟩
  choose M hM0 hM using hbdd
  -- coefficient convergence
  have hcoef : ∀ᶠ N in atTop, ∀ k ∈ range K₀,
      |lam ^ k / k.factorial - coeff lam N k| < ε / (3 * (K₀ + 1) * (M k + 1)) := by
    rw [Filter.eventually_all_finset]
    intro k _
    have hpos : (0 : ℝ) < ε / (3 * (K₀ + 1) * (M k + 1)) :=
      div_pos hε (mul_pos (by positivity) (by linarith [hM0 k]))
    have h := (tendsto_coeff lam k).eventually (Metric.ball_mem_nhds (lam ^ k / k.factorial) hpos)
    filter_upwards [h] with N hN
    rw [Real.dist_eq] at hN
    rwa [abs_sub_comm]
  filter_upwards [hcoef, eventually_ge_atTop K₀] with N hN hNK z hz
  -- split the two sums
  have hheat : heatE (-lam) f z = (∑ k ∈ range K₀, heatTerm (-lam) f z k) +
      ∑' k, heatTerm (-lam) f z (k + K₀) := by
    unfold heatE
    exact ((hsumm z).of_norm.sum_add_tsum_nat_add K₀).symm
  have heuler : eulerIter lam N f z = (∑ k ∈ range K₀, (coeff lam N k : ℂ) * iteratedDeriv (2 * k) f z) +
      ∑ k ∈ Ico K₀ (N + 1), (coeff lam N k : ℂ) * iteratedDeriv (2 * k) f z := by
    rw [eulerIter_eq]
    exact (Finset.sum_range_add_sum_Ico _ (by omega)).symm
  rw [dist_eq_norm, hheat, heuler]
  have hterm : ∀ k, heatTerm (-lam) f z k = ((lam ^ k / k.factorial : ℝ) : ℂ) * iteratedDeriv (2 * k) f z := by
    intro k
    unfold heatTerm
    push_cast
    ring
  -- the three pieces
  have hhead : ‖∑ k ∈ range K₀, (heatTerm (-lam) f z k - (coeff lam N k : ℂ) * iteratedDeriv (2 * k) f z)‖ ≤ ε / 3 := by
    calc ‖∑ k ∈ range K₀, (heatTerm (-lam) f z k - (coeff lam N k : ℂ) * iteratedDeriv (2 * k) f z)‖
        ≤ ∑ k ∈ range K₀, ‖heatTerm (-lam) f z k - (coeff lam N k : ℂ) * iteratedDeriv (2 * k) f z‖ :=
          norm_sum_le _ _
      _ ≤ ∑ k ∈ range K₀, ε / (3 * (K₀ + 1)) := by
          apply Finset.sum_le_sum
          intro k hk
          rw [hterm k, ← sub_mul, norm_mul]
          have h1 : ‖(((lam ^ k / k.factorial : ℝ) : ℂ) - (coeff lam N k : ℂ))‖ =
              |lam ^ k / k.factorial - coeff lam N k| := by
            rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          rw [h1]
          have h2 := hN k hk
          have h3 := hM k z hz
          have hpos : 0 < M k + 1 := by linarith [hM0 k]
          calc |lam ^ k / k.factorial - coeff lam N k| * ‖iteratedDeriv (2 * k) f z‖
              ≤ (ε / (3 * (K₀ + 1) * (M k + 1))) * (M k + 1) := by
                apply mul_le_mul h2.le (by linarith) (norm_nonneg _) (by positivity)
            _ = ε / (3 * (K₀ + 1)) := by field_simp
      _ = (K₀ : ℝ) * (ε / (3 * (K₀ + 1))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ε / 3 := by
          have hK1 : (0 : ℝ) < K₀ + 1 := by positivity
          rw [show (K₀ : ℝ) * (ε / (3 * (K₀ + 1))) = ε / 3 * (K₀ / (K₀ + 1)) by field_simp]
          apply mul_le_of_le_one_right (by positivity)
          rw [div_le_one hK1]
          linarith
  have htail1 : ‖∑' k, heatTerm (-lam) f z (k + K₀)‖ < ε / 3 := by
    have hs : Summable (fun k => ‖heatTerm (-lam) f z (k + K₀)‖) := (summable_nat_add_iff K₀).mpr (hsumm z)
    calc ‖∑' k, heatTerm (-lam) f z (k + K₀)‖ ≤ ∑' k, ‖heatTerm (-lam) f z (k + K₀)‖ :=
          norm_tsum_le_tsum_norm hs
      _ ≤ ∑' k, maj (k + K₀) :=
          Summable.tsum_le_tsum (fun k => hbound _ z hz) hs ((summable_nat_add_iff K₀).mpr hmaj)
      _ < ε / 3 := hK₀
  have htail2 : ‖∑ k ∈ Ico K₀ (N + 1), (coeff lam N k : ℂ) * iteratedDeriv (2 * k) f z‖ ≤ ε / 3 := by
    calc ‖∑ k ∈ Ico K₀ (N + 1), (coeff lam N k : ℂ) * iteratedDeriv (2 * k) f z‖
        ≤ ∑ k ∈ Ico K₀ (N + 1), ‖(coeff lam N k : ℂ) * iteratedDeriv (2 * k) f z‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Ico K₀ (N + 1), maj k := by
          apply Finset.sum_le_sum
          intro k _
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (coeff_nonneg hlam N k)]
          calc coeff lam N k * ‖iteratedDeriv (2 * k) f z‖
              ≤ lam ^ k / k.factorial * ‖iteratedDeriv (2 * k) f z‖ :=
                mul_le_mul_of_nonneg_right (coeff_le hlam N k) (norm_nonneg _)
            _ = ‖heatTerm (-lam) f z k‖ := (norm_term_eq lam hlam f z k).symm
            _ ≤ maj k := hbound k z hz
      _ = ∑ k ∈ range (N + 1 - K₀), maj (K₀ + k) := Finset.sum_Ico_eq_sum_range _ _ _
      _ ≤ ∑' k, maj (k + K₀) := by
          have hs : Summable (fun k => maj (k + K₀)) := (summable_nat_add_iff K₀).mpr hmaj
          have := hs.sum_le_tsum (range (N + 1 - K₀)) (fun k _ => hmaj_nn (k + K₀))
          refine le_trans (le_of_eq ?_) this
          apply Finset.sum_congr rfl
          intro k _
          rw [add_comm]
      _ ≤ ε / 3 := hK₀.le
  calc ‖(∑ k ∈ range K₀, heatTerm (-lam) f z k + ∑' k, heatTerm (-lam) f z (k + K₀)) -
        (∑ k ∈ range K₀, (coeff lam N k : ℂ) * iteratedDeriv (2 * k) f z +
          ∑ k ∈ Ico K₀ (N + 1), (coeff lam N k : ℂ) * iteratedDeriv (2 * k) f z)‖
      = ‖∑ k ∈ range K₀, (heatTerm (-lam) f z k - (coeff lam N k : ℂ) * iteratedDeriv (2 * k) f z) +
          ∑' k, heatTerm (-lam) f z (k + K₀) -
          ∑ k ∈ Ico K₀ (N + 1), (coeff lam N k : ℂ) * iteratedDeriv (2 * k) f z‖ := by
        congr 1
        rw [Finset.sum_sub_distrib]
        ring
    _ ≤ ‖∑ k ∈ range K₀, (heatTerm (-lam) f z k - (coeff lam N k : ℂ) * iteratedDeriv (2 * k) f z)‖ +
          ‖∑' k, heatTerm (-lam) f z (k + K₀)‖ +
          ‖∑ k ∈ Ico K₀ (N + 1), (coeff lam N k : ℂ) * iteratedDeriv (2 * k) f z‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ < ε := by linarith

end Soma.Holonics.RH.EulerIterates
