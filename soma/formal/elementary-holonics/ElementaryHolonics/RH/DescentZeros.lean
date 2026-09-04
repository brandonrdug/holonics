import Mathlib
import ElementaryHolonics.RH.BohrZeros
import ElementaryHolonics.RH.RealZeroTimes

/-!
# RT6: the transfer and the seal

Every zero of `F_t` at large height in the strip becomes, by the minimum-modulus principle on a
disc where the approximation theorem holds, a zero of `heatE t ξ ∘ J_t`; `Re J_t → ∞` with the
height, so the zero of `heatE t ξ` is off the seam. Hence no negative standard time is a seam
time, and `0 ≤ Λ_DN`.
-/

noncomputable section

namespace Soma.Holonics.RH.DescentZeros

open Real Set Filter Topology
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.HeatFlowEntire
open Soma.Holonics.RH.XiGrowth
open Soma.Holonics.RH.EntireDerivativeGrowth
open Soma.Holonics.RH.RealZeroTimes
open Soma.Holonics.RH.GammaPhase
open Soma.Holonics.RH.EventMain
open Soma.Holonics.RH.DescentApproximation
open Soma.Holonics.RH.BohrZeros

/-! ## RT4 in height form -/

theorem descent_approximation_height {t X : ℝ} (ht : 0 < t) (hX0 : 0 ≤ X) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ y₁ : ℝ, ∀ s : ℂ, |s.re| ≤ X → y₁ ≤ s.im →
      γt' t s ≠ 0 ∧ heatE t riemannXi (J t s) = γt' t s * (Ft t s + Rt t s) ∧ ‖Rt t s‖ ≤ ε := by
  have h1 := descent_approximation ht hX0
  have h2 := (tendsto_order.1 (tendsto_ρ ht hX0)).2 ε hε
  obtain ⟨w₁, hw₁⟩ := Filter.eventually_atTop.mp (h1.and h2)
  refine ⟨(max w₁ 0) ^ 12, fun s hX hy => ?_⟩
  set w : ℝ := s.im ^ ((12 : ℕ) : ℝ)⁻¹ with hw
  have hy0 : 0 ≤ s.im := le_trans (by positivity) hy
  have hw12 : w ^ 12 = s.im := Real.rpow_inv_natCast_pow hy0 (by norm_num)
  have hww₁ : w₁ ≤ w := by
    have : max w₁ 0 ≤ w := by
      rw [hw]
      calc max w₁ 0 = ((max w₁ 0) ^ 12) ^ ((12 : ℕ) : ℝ)⁻¹ :=
            (Real.pow_rpow_inv_natCast (le_max_right _ _) (by norm_num)).symm
        _ ≤ s.im ^ ((12 : ℕ) : ℝ)⁻¹ := Real.rpow_le_rpow (by positivity) hy (by positivity)
    exact le_trans (le_max_left _ _) this
  obtain ⟨hP, hρ⟩ := hw₁ w hww₁
  obtain ⟨hγ, heq, hR⟩ := hP s hX hw12.symm
  exact ⟨hγ, heq, hR.trans hρ.le⟩

/-! ## Differentiability on the upper half-plane -/

theorem half_mem_slitPlane {s : ℂ} (hs : 0 < s.im) : s / 2 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  simp only [Complex.div_ofNat_im]
  positivity

theorem differentiableAt_log_half {s : ℂ} (hs : 0 < s.im) :
    DifferentiableAt ℂ (fun z : ℂ => Complex.log (z / 2)) s :=
  (differentiableAt_id.div_const (2 : ℂ)).clog (half_mem_slitPlane hs)

theorem differentiableAt_Λs {s : ℂ} (hs : 0 < s.im) : DifferentiableAt ℂ Λs s := by
  unfold Λs
  exact (differentiableAt_log_half hs).sub_const _

theorem differentiableAt_J (t : ℝ) {s : ℂ} (hs : 0 < s.im) : DifferentiableAt ℂ (J t) s := by
  unfold J
  exact differentiableAt_id.add ((differentiableAt_Λs hs).const_mul _)

theorem differentiableAt_g {s : ℂ} (hs : 0 < s.im) : DifferentiableAt ℂ g s := by
  have hlog := differentiableAt_log_half hs
  have h1 : DifferentiableAt ℂ (fun s : ℂ => (1 / 4 : ℂ) * (s * (s - 1)) *
      Complex.exp (s * (-(Real.log π : ℂ) / 2))) s := by fun_prop
  have h2 : DifferentiableAt ℂ
      (fun s : ℂ => Complex.exp ((s / 2 - 1 / 2) * Complex.log (s / 2) - s / 2)) s := by
    apply DifferentiableAt.cexp
    apply DifferentiableAt.sub _ (differentiableAt_id.div_const (2 : ℂ))
    exact ((differentiableAt_id.div_const (2 : ℂ)).sub_const _).mul hlog
  unfold g
  exact (h1.mul (differentiableAt_const _)).mul h2

theorem differentiableAt_γt' (t : ℝ) {s : ℂ} (hs : 0 < s.im) : DifferentiableAt ℂ (γt' t) s := by
  unfold γt'
  exact (differentiableAt_g hs).mul
    ((((differentiableAt_Λs hs).pow 2).const_mul _).div_const _).cexp

theorem differentiable_heatE_xi (t : ℝ) : Differentiable ℂ (heatE t riemannXi) :=
  differentiable_heatE differentiable_riemannXi hasGrowth_riemannXi A_nonneg (by norm_num)
    (by norm_num) (by norm_num) t

/-! ## `Re J_t` grows with the height -/

theorem re_J_ge {t : ℝ} (ht : 0 < t) {s : ℂ} (hs : 0 < s.im) :
    s.re + t * Real.log (s.im / (2 * π)) ≤ (J t s).re := by
  unfold J Λs
  rw [Complex.add_re, Complex.re_ofReal_mul, Complex.sub_re, Complex.log_re, Complex.ofReal_re]
  have h1 : s.im / 2 ≤ ‖s / 2‖ := by
    rw [norm_div, Complex.norm_ofNat]
    have := Complex.im_le_norm s
    linarith
  have hs0 : ‖s / 2‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have h2 : Real.log (s.im / (2 * π)) ≤ Real.log ‖s / 2‖ - Real.log π := by
    rw [← Real.log_div hs0 Real.pi_pos.ne']
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ (by positivity) Real.pi_pos]
    nlinarith [Real.pi_pos]
  nlinarith [mul_le_mul_of_nonneg_left h2 ht.le]

/-! ## The transfer -/

/-- **RT6: for every repository `t > 0`, `heatE t ξ` has a zero off the seam.** -/
theorem exists_offSeam_zero {t : ℝ} (ht : 0 < t) :
    ∃ z : ℂ, heatE t riemannXi z = 0 ∧ z.re ≠ 1 / 2 := by
  obtain ⟨s₀, r, δ, hr, hδ, hs₀, hsph⟩ := exists_zero_margin ht
  set X : ℝ := |s₀.re| + r with hX
  have hX0 : 0 ≤ X := by positivity
  obtain ⟨y₁, hy₁⟩ := descent_approximation_height ht hX0 (by positivity : 0 < δ / 8)
  set y₂ : ℝ := max (max y₁ (2 * π * Real.exp ((X + 1) / t))) 1 with hy₂
  have hy₂1 : 1 ≤ y₂ := le_max_right _ _
  have hy₂y₁ : y₁ ≤ y₂ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hy₂e : 2 * π * Real.exp ((X + 1) / t) ≤ y₂ := le_trans (le_max_right _ _) (le_max_left _ _)
  obtain ⟨τ, hτ, hclose⟩ := exists_almost_period ht hX0 (by positivity : 0 < δ / 8)
    (y₂ + r - s₀.im)
  have hstrip : ∀ s ∈ Metric.closedBall s₀ r, |s.re| ≤ X := by
    intro s hs
    have h1 : ‖s - s₀‖ ≤ r := by rwa [Metric.mem_closedBall, dist_eq_norm] at hs
    have h2 : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
      have := Complex.abs_re_le_norm (s - s₀)
      rwa [Complex.sub_re] at this
    calc |s.re| = |(s.re - s₀.re) + s₀.re| := by ring_nf
      _ ≤ |s.re - s₀.re| + |s₀.re| := abs_add_le _ _
      _ ≤ |s₀.re| + r := by linarith
  have hheight : ∀ s ∈ Metric.closedBall s₀ r, y₂ ≤ (s + Complex.I * τ).im := by
    intro s hs
    have h1 : ‖s - s₀‖ ≤ r := by rwa [Metric.mem_closedBall, dist_eq_norm] at hs
    have h2 : |s.im - s₀.im| ≤ ‖s - s₀‖ := by
      have := Complex.abs_im_le_norm (s - s₀)
      rwa [Complex.sub_im] at this
    have h3 : (s + Complex.I * τ).im = s.im + τ := by simp
    rw [h3]
    have := abs_le.mp h2
    linarith
  have hre' : ∀ s : ℂ, (s + Complex.I * τ).re = s.re := by intro s; simp
  have hdata : ∀ s ∈ Metric.closedBall s₀ r,
      γt' t (s + Complex.I * τ) ≠ 0 ∧
      heatE t riemannXi (J t (s + Complex.I * τ)) =
        γt' t (s + Complex.I * τ) * (Ft t (s + Complex.I * τ) + Rt t (s + Complex.I * τ)) ∧
      ‖Rt t (s + Complex.I * τ)‖ ≤ δ / 8 := by
    intro s hs
    apply hy₁
    · rw [hre']; exact hstrip s hs
    · exact le_trans hy₂y₁ (hheight s hs)
  set G : ℂ → ℂ := fun s => heatE t riemannXi (J t (s + Complex.I * τ)) /
    γt' t (s + Complex.I * τ) with hG
  have hGeq : ∀ s ∈ Metric.closedBall s₀ r,
      G s = Ft t (s + Complex.I * τ) + Rt t (s + Complex.I * τ) := by
    intro s hs
    obtain ⟨hγ, heq, _⟩ := hdata s hs
    simp only [hG]
    rw [heq]
    field_simp
  have hGd : DiffContOnCl ℂ G (Metric.ball s₀ r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball s₀ hr.ne']
    intro s hs
    apply DifferentiableAt.differentiableWithinAt
    have hpos : 0 < (s + Complex.I * τ).im := by linarith [hheight s hs, hy₂1]
    have hγ := (hdata s hs).1
    simp only [hG]
    have h1 : DifferentiableAt ℂ (fun s : ℂ => heatE t riemannXi (J t (s + Complex.I * τ))) s :=
      ((differentiable_heatE_xi t).differentiableAt).comp s
        ((differentiableAt_J t hpos).comp s (differentiableAt_id.add_const _))
    have h2 : DifferentiableAt ℂ (fun s : ℂ => γt' t (s + Complex.I * τ)) s :=
      (differentiableAt_γt' t hpos).comp s (differentiableAt_id.add_const _)
    exact h1.div h2 hγ
  have hcenter : ‖G s₀‖ < δ / 2 := by
    rw [hGeq s₀ (Metric.mem_closedBall_self hr.le)]
    have h1 := hclose s₀ (hstrip s₀ (Metric.mem_closedBall_self hr.le))
    rw [hs₀, sub_zero] at h1
    have h2 := (hdata s₀ (Metric.mem_closedBall_self hr.le)).2.2
    calc ‖Ft t (s₀ + Complex.I * τ) + Rt t (s₀ + Complex.I * τ)‖
        ≤ ‖Ft t (s₀ + Complex.I * τ)‖ + ‖Rt t (s₀ + Complex.I * τ)‖ := norm_add_le _ _
      _ ≤ δ / 8 + δ / 8 := add_le_add h1 h2
      _ < δ / 2 := by linarith
  have hsphere : ∀ z ∈ Metric.sphere s₀ r, δ / 2 ≤ ‖G z‖ := by
    intro z hz
    have hzc := Metric.sphere_subset_closedBall hz
    rw [hGeq z hzc]
    have h1 := hsph z hz
    have h2 := hclose z (hstrip z hzc)
    have h3 := (hdata z hzc).2.2
    have h4 : ‖Ft t z‖ ≤ ‖Ft t (z + Complex.I * τ) + Rt t (z + Complex.I * τ)‖ +
        ‖Ft t (z + Complex.I * τ) - Ft t z‖ + ‖Rt t (z + Complex.I * τ)‖ := by
      have e : Ft t z = (Ft t (z + Complex.I * τ) + Rt t (z + Complex.I * τ)) -
          (Ft t (z + Complex.I * τ) - Ft t z) - Rt t (z + Complex.I * τ) := by ring
      calc ‖Ft t z‖ = ‖(Ft t (z + Complex.I * τ) + Rt t (z + Complex.I * τ)) -
            (Ft t (z + Complex.I * τ) - Ft t z) - Rt t (z + Complex.I * τ)‖ := by rw [← e]
        _ ≤ ‖(Ft t (z + Complex.I * τ) + Rt t (z + Complex.I * τ)) -
            (Ft t (z + Complex.I * τ) - Ft t z)‖ + ‖Rt t (z + Complex.I * τ)‖ := norm_sub_le _ _
        _ ≤ ‖Ft t (z + Complex.I * τ) + Rt t (z + Complex.I * τ)‖ +
            ‖Ft t (z + Complex.I * τ) - Ft t z‖ + ‖Rt t (z + Complex.I * τ)‖ := by
            linarith [norm_sub_le (Ft t (z + Complex.I * τ) + Rt t (z + Complex.I * τ))
              (Ft t (z + Complex.I * τ) - Ft t z)]
    linarith
  obtain ⟨z₁, hz₁, hz₁0⟩ := exists_zero_of_norm_center_lt hr hGd hcenter hsphere
  obtain ⟨hγ, heq, _⟩ := hdata z₁ hz₁
  refine ⟨J t (z₁ + Complex.I * τ), ?_, ?_⟩
  · have h0 : G z₁ = 0 := hz₁0
    simp only [hG] at h0
    rcases div_eq_zero_iff.mp h0 with h | h
    · exact h
    · exact absurd h hγ
  · have hpos : 0 < (z₁ + Complex.I * τ).im := by linarith [hheight z₁ hz₁, hy₂1]
    have hre := re_J_ge ht hpos
    have hX' : -X ≤ (z₁ + Complex.I * τ).re := by
      rw [hre']
      have := hstrip z₁ hz₁
      linarith [neg_abs_le z₁.re]
    have hlog : (X + 1) / t ≤ Real.log ((z₁ + Complex.I * τ).im / (2 * π)) := by
      have h1 : Real.exp ((X + 1) / t) ≤ (z₁ + Complex.I * τ).im / (2 * π) := by
        rw [le_div_iff₀ (by positivity)]
        have := hheight z₁ hz₁
        nlinarith [hy₂e]
      calc (X + 1) / t = Real.log (Real.exp ((X + 1) / t)) := (Real.log_exp _).symm
        _ ≤ Real.log ((z₁ + Complex.I * τ).im / (2 * π)) :=
            Real.log_le_log (Real.exp_pos _) h1
    have ht' : t * ((X + 1) / t) = X + 1 := by field_simp
    intro h
    have : 1 ≤ (J t (z₁ + Complex.I * τ)).re := by
      have := mul_le_mul_of_nonneg_left hlog ht.le
      linarith
    linarith

/-! ## The seal -/

/-- No negative standard time is a seam time. -/
theorem not_mem_seamTimes_of_neg {τ : ℝ} (hτ : τ < 0) : τ ∉ seamTimes := by
  intro h
  obtain ⟨z, hz, hre⟩ := exists_offSeam_zero (t := -τ) (by linarith)
  exact hre (h z hz)

theorem seamTimes_subset_Ici : seamTimes ⊆ Set.Ici 0 := by
  intro τ hτ
  by_contra h
  exact not_mem_seamTimes_of_neg (by simpa using h) hτ

/-- **`0 ≤ Λ_DN`: the de Bruijn–Newman threshold is nonnegative.** -/
theorem Λ_DN_nonneg : 0 ≤ Λ_DN := by
  unfold Λ_DN
  by_cases hne : seamTimes.Nonempty
  · exact le_csInf hne (fun τ hτ => seamTimes_subset_Ici hτ)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sInf_empty]

end Soma.Holonics.RH.DescentZeros
