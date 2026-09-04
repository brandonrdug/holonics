import Mathlib
import ElementaryHolonics.RH.DeBruijnIterate
import ElementaryHolonics.RH.RealZeroTimes

/-!
# DB4: the Gaussian limit — `cosh(u/(2N))^{N²} → e^{u²/8}`, and `1/8` is a seam time

The `N²`-fold average of `ξ` with `μ = 1/(2N)` is the transform of `cosh(u/(2N))^{N²} Φ`, which
converges to `e^{u²/8} Φ` pointwise under the domination `cosh y ≤ e^{y²/2}`; the transforms then
converge locally uniformly to `heatE (−1/8) ξ`, and Hurwitz on the seam passes the seam zeros of
the iterates to the limit.
-/

noncomputable section

namespace Soma.Holonics.RH.DeBruijnLimit

open Real Set Filter Topology MeasureTheory Complex
open Soma.Holonics.RH.KernelFlow
open Soma.Holonics.RH.KernelAverage
open Soma.Holonics.RH.DeBruijnIterate
open Soma.Holonics.RH.HeatKernelPhi
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.HeatFlowEntire
open Soma.Holonics.RH.RealZeroTimes
open Soma.Holonics.RH.HurwitzLine
open Soma.Holonics.RH.LineApproximation

/-! ## The pointwise limit -/

theorem one_add_sq_div_two_le_cosh (y : ℝ) : 1 + y ^ 2 / 2 ≤ Real.cosh y := by
  have h1 : Real.cosh y = 1 + 2 * Real.sinh (y / 2) ^ 2 := by
    have := Real.cosh_two_mul (y / 2)
    rw [show 2 * (y / 2) = y by ring, Real.cosh_sq'] at this
    linarith
  have h2 : (y / 2) ^ 2 ≤ Real.sinh (y / 2) ^ 2 := by
    rcases le_or_gt 0 (y / 2) with h | h
    · have := Real.self_le_sinh_iff.mpr h
      exact pow_le_pow_left₀ h this 2
    · have hs : Real.sinh (y / 2) < y / 2 := Real.sinh_lt_self_iff.mpr h
      have : (-(y / 2)) ^ 2 ≤ (-Real.sinh (y / 2)) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
      simpa using this
  nlinarith

theorem tendsto_coshPow (u : ℝ) :
    Tendsto (fun N : ℕ => Real.cosh (1 / (2 * N) * u) ^ (N ^ 2)) atTop
      (𝓝 (Real.exp (u ^ 2 / 8))) := by
  have hlower : Tendsto (fun N : ℕ => (1 + (u ^ 2 / 8) / ((N ^ 2 : ℕ) : ℝ)) ^ (N ^ 2)) atTop
      (𝓝 (Real.exp (u ^ 2 / 8))) :=
    (Real.tendsto_one_add_div_pow_exp (u ^ 2 / 8)).comp (tendsto_pow_atTop (by norm_num))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hbase : 1 + (u ^ 2 / 8) / ((N ^ 2 : ℕ) : ℝ) ≤ Real.cosh (1 / (2 * N) * u) := by
      have := one_add_sq_div_two_le_cosh (1 / (2 * N) * u)
      have e : (1 / (2 * N) * u) ^ 2 / 2 = (u ^ 2 / 8) / ((N ^ 2 : ℕ) : ℝ) := by
        push_cast
        field_simp
        ring
      linarith
    exact pow_le_pow_left₀ (by positivity) hbase _
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    calc Real.cosh (1 / (2 * N) * u) ^ (N ^ 2)
        ≤ Real.exp ((1 / (2 * N) * u) ^ 2 / 2) ^ (N ^ 2) :=
          pow_le_pow_left₀ (Real.cosh_pos _).le (Real.cosh_le_exp_half_sq _) _
      _ = Real.exp (u ^ 2 / 8) := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          field_simp
          ring

/-! ## Locally uniform convergence of transforms -/

theorem norm_lap_sub (κ κ' : Kernel) (s : ℂ) (u : ℝ) :
    ‖κ.lap s u - κ'.lap s u‖ = Real.exp ((s.re - 1 / 2) * u) * |κ.K u - κ'.K u| := by
  simp only [Kernel.lap]
  rw [← mul_sub, norm_mul, Complex.norm_exp, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]
  congr 2
  simp [Complex.mul_re, Complex.sub_re]

/-- **Transforms converge locally uniformly under a pointwise limit of the kernels with a
common admissible domination.** -/
theorem tendstoLocallyUniformly_T {K : ℕ → Kernel} {L M : Kernel}
    (hpt : ∀ u, Tendsto (fun N => (K N).K u) atTop (𝓝 (L.K u)))
    (hdom : ∀ N u, |(K N).K u| ≤ M.K u) (hLM : ∀ u, |L.K u| ≤ M.K u) :
    TendstoLocallyUniformly (fun N => (K N).T) L.T atTop := by
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε x
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, ?_⟩
  set b : ℝ := ‖x‖ + 2 with hb
  -- the integral majorant
  obtain ⟨C, hC0, hC⟩ := M.dom 0 b (le_refl 0) (by positivity)
  set g : ℝ → ℝ := fun u => Real.exp (b * |u|) * (2 * M.K u) with hg
  have hM0 : ∀ u, 0 ≤ M.K u := fun u => le_trans (abs_nonneg _) (hLM u)
  have hg_int : Integrable g := by
    have hbound : ∀ u, ‖g u‖ ≤ 2 * C * Real.exp (-u ^ 2) := by
      intro u
      have := hC u
      rw [zero_mul, zero_add, abs_of_nonneg (hM0 u)] at this
      rw [Real.norm_eq_abs, abs_of_nonneg (by have := hM0 u; positivity)]
      simp only [hg]
      nlinarith
    exact (Kernel.integrable_gauss (2 * C)).mono' ((Real.continuous_exp.comp
      (continuous_const.mul continuous_abs)).mul (continuous_const.mul M.cont)).aestronglyMeasurable
      (Eventually.of_forall hbound)
  set I : ℕ → ℝ := fun N => ∫ u, Real.exp (b * |u|) * |(K N).K u - L.K u| with hI
  have hI0 : Tendsto I atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence g
      (F := fun N u => Real.exp (b * |u|) * |(K N).K u - L.K u|) (f := fun _ => (0 : ℝ))
      (fun N => ((Real.continuous_exp.comp (continuous_const.mul continuous_abs)).mul
        (continuous_abs.comp ((K N).cont.sub L.cont))).aestronglyMeasurable) hg_int
      (fun N => Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        simp only [hg]
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        calc |(K N).K u - L.K u| ≤ |(K N).K u| + |L.K u| := abs_sub _ _
          _ ≤ M.K u + M.K u := add_le_add (hdom N u) (hLM u)
          _ = 2 * M.K u := by ring)
      (Eventually.of_forall fun u => by
        have h1 : Tendsto (fun N => (K N).K u - L.K u) atTop (𝓝 0) := by
          have := (hpt u).sub_const (L.K u)
          rwa [sub_self] at this
        have h2 : Tendsto (fun N => |(K N).K u - L.K u|) atTop (𝓝 0) := by
          have := h1.abs
          rwa [abs_zero] at this
        have := h2.const_mul (Real.exp (b * |u|))
        rwa [mul_zero] at this)
    simpa [hI] using this
  have hev : ∀ᶠ N in atTop, I N < ε := (tendsto_order.1 hI0).2 ε hε
  filter_upwards [hev] with N hN y hy
  have hyx : ‖y‖ < ‖x‖ + 1 := by
    have := Metric.mem_ball.mp hy
    rw [dist_eq_norm] at this
    calc ‖y‖ = ‖(y - x) + x‖ := by ring_nf
      _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
      _ < 1 + ‖x‖ := by linarith
      _ = ‖x‖ + 1 := by ring
  have hre : |y.re - 1 / 2| ≤ b := by
    have := Complex.abs_re_le_norm y
    rw [hb]
    calc |y.re - 1 / 2| ≤ |y.re| + 1 / 2 := by
          have := abs_sub y.re (1 / 2 : ℝ)
          rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
          linarith
      _ ≤ ‖x‖ + 2 := by linarith
  rw [dist_eq_norm]
  have hdiff : L.T y - (K N).T y = ∫ u, (L.lap y u - (K N).lap y u) := by
    unfold Kernel.T
    rw [integral_sub (L.integrable_lap y) ((K N).integrable_lap y)]
  rw [hdiff]
  calc ‖∫ u, (L.lap y u - (K N).lap y u)‖ ≤ ∫ u, ‖L.lap y u - (K N).lap y u‖ :=
        norm_integral_le_integral_norm _
    _ ≤ I N := by
        apply integral_mono_of_nonneg (Eventually.of_forall fun u => norm_nonneg _)
          (by
            have : Integrable (fun u => Real.exp (b * |u|) * |(K N).K u - L.K u|) :=
              hg_int.mono' (((Real.continuous_exp.comp (continuous_const.mul continuous_abs)).mul
                (continuous_abs.comp ((K N).cont.sub L.cont))).aestronglyMeasurable)
                (Eventually.of_forall fun u => by
                  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
                  simp only [hg]
                  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
                  calc |(K N).K u - L.K u| ≤ |(K N).K u| + |L.K u| := abs_sub _ _
                    _ ≤ M.K u + M.K u := add_le_add (hdom N u) (hLM u)
                    _ = 2 * M.K u := by ring)
            exact this)
          (Eventually.of_forall fun u => ?_)
        show ‖L.lap y u - (K N).lap y u‖ ≤ Real.exp (b * |u|) * |(K N).K u - L.K u|
        rw [norm_lap_sub, abs_sub_comm]
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        apply Real.exp_le_exp.mpr
        calc (y.re - 1 / 2) * u ≤ |(y.re - 1 / 2) * u| := le_abs_self _
          _ = |y.re - 1 / 2| * |u| := abs_mul _ _
          _ ≤ b * |u| := mul_le_mul_of_nonneg_right hre (abs_nonneg _)
    _ < ε := hN

/-! ## The seam time `1/8` -/

/-- The kernel of the `N`-th iterate. -/
def KN (N : ℕ) : Kernel := coshPow ΦK (1 / (2 * (N : ℝ))) (N ^ 2 : ℕ)

theorem KN_K (N : ℕ) (u : ℝ) : (KN N).K u = Real.cosh (1 / (2 * (N : ℝ)) * u) ^ (N ^ 2 : ℕ) * Φ u :=
  coshPow_K _ _ _ _

theorem xiIter_eq_KN (N : ℕ) : xiIter (1 / (2 * (N : ℝ))) (N ^ 2 : ℕ) = (KN N).T :=
  xiIter_eq_T _ _

theorem flow_eighth_K (u : ℝ) : (ΦK.flow (-(1 / 8))).K u = Real.exp (u ^ 2 / 8) * Φ u := by
  show Real.exp (-(-(1 / 8)) * u ^ 2) * Φ u = _
  congr 2
  ring

/-- **The iterates converge locally uniformly to `heatE (−1/8) ξ`.** -/
theorem tendsto_xiIter :
    TendstoLocallyUniformly (fun N : ℕ => xiIter (1 / (2 * (N : ℝ))) (N ^ 2 : ℕ))
      (heatE (-(1 / 8)) riemannXi) atTop := by
  rw [heatE_riemannXi_eq_T]
  simp_rw [xiIter_eq_KN]
  apply tendstoLocallyUniformly_T (M := ΦK.flow (-(1 / 8)))
  · intro u
    rw [flow_eighth_K]
    simp_rw [KN_K]
    exact (tendsto_coshPow u).mul_const _
  · intro N u
    rw [KN_K, flow_eighth_K, abs_of_nonneg (mul_pos (pow_pos (Real.cosh_pos _) _) (Φ_pos u)).le]
    apply mul_le_mul_of_nonneg_right _ (Φ_pos u).le
    by_cases hN : N = 0
    · subst hN
      have h0 : (0 : ℝ) ≤ u ^ 2 / 8 := by positivity
      simp
      first | positivity | exact Real.one_le_exp h0 | (rw [Real.one_le_exp_iff]; exact h0)
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    calc Real.cosh (1 / (2 * N) * u) ^ (N ^ 2)
        ≤ Real.exp ((1 / (2 * N) * u) ^ 2 / 2) ^ (N ^ 2) :=
          pow_le_pow_left₀ (Real.cosh_pos _).le (Real.cosh_le_exp_half_sq _) _
      _ = Real.exp (u ^ 2 / 8) := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          field_simp
          ring
  · intro u
    rw [flow_eighth_K, abs_of_nonneg (mul_pos (Real.exp_pos _) (Φ_pos u)).le]

/-- **DB4: `1/8` is a seam time.** -/
theorem eighth_mem_seamTimes : (1 / 8 : ℝ) ∈ seamTimes := by
  have hF : ∀ᶠ N : ℕ in atTop,
      Differentiable ℂ ((fun N : ℕ => xiIter (1 / (2 * (N : ℝ))) (N ^ 2 : ℕ)) N) :=
    Eventually.of_forall fun N => by
      show Differentiable ℂ (xiIter (1 / (2 * (N : ℝ))) (N ^ 2 : ℕ))
      rw [xiIter_eq_KN]
      exact (KN N).differentiable_T
  have hG : Differentiable ℂ (heatE (-(1 / 8)) riemannXi) := by
    rw [heatE_riemannXi_eq_T]
    exact (ΦK.flow _).differentiable_T
  have hG0 : ∃ x, heatE (-(1 / 8)) riemannXi x ≠ 0 := ⟨1 / 2, heatE_riemannXi_half_ne_zero _⟩
  have hseam : ∀ᶠ N : ℕ in atTop,
      ∀ ζ, (fun N : ℕ => xiIter (1 / (2 * (N : ℝ))) (N ^ 2 : ℕ)) N ζ = 0 → ζ.re = 1 / 2 := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact onSeam_xiIter hN
  have h := zeros_on_seam (l := atTop) (F := fun N : ℕ => xiIter (1 / (2 * (N : ℝ))) (N ^ 2 : ℕ))
    (G := heatE (-(1 / 8)) riemannXi) hF hG tendsto_xiIter hG0 hseam
  intro z hz
  exact h z hz

end Soma.Holonics.RH.DeBruijnLimit
