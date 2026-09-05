import ElementaryHolonics.Millennium.NavierStokesDilationResonance
import ElementaryHolonics.Millennium.NavierStokesSwirlDilationTransport
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# A radius-preserving inverse for the critical swirl transport

The critical coefficient is m/7. Every nonzero Taylor divisor has magnitude at least 1/7.
The actual convergent series obtained by coefficient division is holomorphic on the source
ball and solves the dilation equation with the resonant source coefficient retained as a
residual. A compatible source admits the full resonant monomial fibre. No radial nonlinear
source bound or convergence of the two-variable fluid expansion is assumed to have returned.
-/

noncomputable section

open Complex Metric Set

namespace Soma.Holonics.Millennium.NavierStokesAnalyticDilationInverse

open Soma.Holonics.Millennium.NavierStokesAxialPrimitive
open Soma.Holonics.Millennium.NavierStokesSwirlDilationTransport
open Soma.Holonics.Millennium.NavierStokesDilationResonance

theorem critical_divisor_gap (m n : ℕ) (hne : 7 * n ≠ m) :
    1 / 7 ≤ |(n : ℝ) - (m : ℝ) / 7| := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hnat : 7 * n + 1 ≤ m := hlt
    have hreal : 7 * (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hnat
    rw [abs_of_neg (by linarith : (n : ℝ) - (m : ℝ) / 7 < 0)]
    linarith
  · have hnat : m + 1 ≤ 7 * n := hgt
    have hreal : (m : ℝ) + 1 ≤ 7 * (n : ℝ) := by exact_mod_cast hnat
    rw [abs_of_pos (by linarith : 0 < (n : ℝ) - (m : ℝ) / 7)]
    linarith

theorem complex_critical_divisor_gap (m n : ℕ) (hne : 7 * n ≠ m) :
    1 / 7 ≤ ‖(n : ℂ) - (m : ℂ) / 7‖ := by
  have hcast : (n : ℂ) - (m : ℂ) / 7 = (((n : ℝ) - (m : ℝ) / 7 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  exact critical_divisor_gap m n hne

def resonantCoefficient (m : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if 7 * n = m then a n else 0

def inverseCoefficient (m : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if 7 * n = m then 0 else a n / ((n : ℂ) - (m : ℂ) / 7)

theorem inverseCoefficient_bound (m : ℕ) (a : ℕ → ℂ) (n : ℕ) :
    ‖inverseCoefficient m a n‖ ≤ 7 * ‖a n‖ := by
  unfold inverseCoefficient
  split_ifs with h
  · simp
  · rw [norm_div]
    have hg := complex_critical_divisor_gap m n h
    have hd : 0 < ‖(n : ℂ) - (m : ℂ) / 7‖ := lt_of_lt_of_le (by norm_num) hg
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg (norm_nonneg (a n)) (sub_nonneg.mpr hg)]

theorem inverseCoefficient_source (m : ℕ) (a : ℕ → ℂ) (n : ℕ) :
    ((n : ℂ) - (m : ℂ) / 7) * inverseCoefficient m a n =
      a n - resonantCoefficient m a n := by
  unfold inverseCoefficient resonantCoefficient
  split_ifs with h
  · simp
  · have hg := complex_critical_divisor_gap m n h
    have hd : (n : ℂ) - (m : ℂ) / 7 ≠ 0 := by
      intro heq
      rw [heq, norm_zero] at hg
      norm_num at hg
    simp only [sub_zero]
    exact mul_div_cancel₀ (a n) hd

def powerSeries (a : ℕ → ℂ) (z : ℂ) : ℂ := ∑' n, a n * z ^ n

def inverseSeries (m : ℕ) (a : ℕ → ℂ) : ℂ → ℂ := powerSeries (inverseCoefficient m a)

def complexDilation (gamma : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * deriv f z - gamma * f z

theorem term_bound (a : ℕ → ℂ) (R : ℝ) (z : ℂ) (hz : ‖z‖ ≤ R) (n : ℕ) :
    ‖a n * z ^ n‖ ≤ ‖a n‖ * R ^ n := by
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz n) (norm_nonneg _)

theorem powerSeries_summable {a : ℕ → ℂ} {R : ℝ}
    (ha : Summable (fun n ↦ ‖a n‖ * R ^ n)) {z : ℂ} (hz : ‖z‖ ≤ R) :
    Summable (fun n ↦ a n * z ^ n) :=
  ha.of_norm_bounded (term_bound a R z hz)

theorem inverse_term_bound (m : ℕ) (a : ℕ → ℂ) (R : ℝ) (z : ℂ)
    (hz : ‖z‖ ≤ R) (n : ℕ) :
    ‖inverseCoefficient m a n * z ^ n‖ ≤ 7 * (‖a n‖ * R ^ n) := by
  have hR : 0 ≤ R := (norm_nonneg z).trans hz
  calc
    ‖inverseCoefficient m a n * z ^ n‖ ≤ ‖inverseCoefficient m a n‖ * R ^ n :=
      term_bound _ R z hz n
    _ ≤ (7 * ‖a n‖) * R ^ n :=
      mul_le_mul_of_nonneg_right (inverseCoefficient_bound m a n) (pow_nonneg hR n)
    _ = 7 * (‖a n‖ * R ^ n) := by ring

theorem inverseSeries_differentiableOn (m : ℕ) {a : ℕ → ℂ} {R : ℝ}
    (ha : Summable (fun n ↦ ‖a n‖ * R ^ n)) :
    DifferentiableOn ℂ (inverseSeries m a) (ball 0 R) := by
  apply Complex.differentiableOn_tsum_of_summable_norm (ha.mul_left 7)
    (fun n ↦ by fun_prop) isOpen_ball
  intro n w hw
  exact inverse_term_bound m a R w (mem_ball_zero_iff.mp hw).le n

theorem monomial_dilation (gamma c : ℂ) (n : ℕ) (z : ℂ) :
    complexDilation gamma (fun w ↦ c * w ^ n) z = ((n : ℂ) - gamma) * c * z ^ n := by
  have hd : HasDerivAt (fun w : ℂ ↦ c * w ^ n) (c * ((n : ℂ) * z ^ (n - 1))) z := by
    convert (((hasDerivAt_id z).pow n).const_mul c) using 1 <;>
      first | rfl | (simp only [id_eq] <;> ring)
  rw [complexDilation, hd.deriv]
  cases n with
  | zero => simp
  | succ n => simp [pow_succ]; ring

/-- The actual analytic inverse returns the resonant source projection as its complete scalar
residual. The projection is not silently divided by zero. -/
theorem inverseSeries_returns_residual (m : ℕ) {a : ℕ → ℂ} {R : ℝ}
    (ha : Summable (fun n ↦ ‖a n‖ * R ^ n)) {z : ℂ} (hz : ‖z‖ < R) :
    complexDilation ((m : ℂ) / 7) (inverseSeries m a) z =
      powerSeries (fun n ↦ a n - resonantCoefficient m a n) z := by
  have hder := Complex.hasSum_deriv_of_summable_norm (ha.mul_left 7)
    (F := fun n w ↦ inverseCoefficient m a n * w ^ n)
    (U := ball 0 R) (fun n ↦ by fun_prop) isOpen_ball
    (fun n w hw ↦ inverse_term_bound m a R w (mem_ball_zero_iff.mp hw).le n)
    (mem_ball_zero_iff.mpr hz)
  have hfun : HasSum (fun n ↦ inverseCoefficient m a n * z ^ n) (inverseSeries m a z) :=
    ((ha.mul_left 7).of_norm_bounded (inverse_term_bound m a R z hz.le)).hasSum
  have hsub := (hder.mul_left z).sub (hfun.mul_left ((m : ℂ) / 7))
  have htarget : HasSum (fun n ↦ (a n - resonantCoefficient m a n) * z ^ n)
      (complexDilation ((m : ℂ) / 7) (inverseSeries m a) z) := by
    apply hsub.congr_fun
    intro n
    symm
    change complexDilation ((m : ℂ) / 7) (fun w ↦ inverseCoefficient m a n * w ^ n) z = _
    rw [monomial_dilation, inverseCoefficient_source]
  exact htarget.tsum_eq.symm

theorem inverseSeries_solves_compatible_source (m : ℕ) {a : ℕ → ℂ} {R : ℝ}
    (ha : Summable (fun n ↦ ‖a n‖ * R ^ n))
    (hcompatible : ∀ n, 7 * n = m → a n = 0) {z : ℂ} (hz : ‖z‖ < R) :
    complexDilation ((m : ℂ) / 7) (inverseSeries m a) z = powerSeries a z := by
  rw [inverseSeries_returns_residual m ha hz]
  congr 1
  funext n
  unfold resonantCoefficient
  split_ifs with h
  · rw [hcompatible n h]
    simp
  · simp

theorem inverseSeries_norm_bound (m : ℕ) {a : ℕ → ℂ} {R : ℝ}
    (ha : Summable (fun n ↦ ‖a n‖ * R ^ n)) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖inverseSeries m a z‖ ≤ 7 * ∑' n, ‖a n‖ * R ^ n := by
  have hs : HasSum (fun n ↦ inverseCoefficient m a n * z ^ n) (inverseSeries m a z) :=
    ((ha.mul_left 7).of_norm_bounded (inverse_term_bound m a R z hz)).hasSum
  simpa only [tsum_mul_left] using hs.norm_le_of_bounded (ha.mul_left 7).hasSum
    (inverse_term_bound m a R z hz)

/-- The coefficient-zero representative is only one member of the analytic inverse fibre. -/
theorem inverseSeries_fibre_returns_same_residual (j : ℕ) (c : ℂ)
    {a : ℕ → ℂ} {R : ℝ} (ha : Summable (fun n ↦ ‖a n‖ * R ^ n))
    {z : ℂ} (hz : ‖z‖ < R) :
    complexDilation (((7 * j : ℕ) : ℂ) / 7)
      (fun w ↦ inverseSeries (7 * j) a w + c * w ^ j) z =
        powerSeries (fun n ↦ a n - resonantCoefficient (7 * j) a n) z := by
  have hf : DifferentiableAt ℂ (inverseSeries (7 * j) a) z :=
    (inverseSeries_differentiableOn (7 * j) ha).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz))
  have hmain := inverseSeries_returns_residual (7 * j) ha hz
  have hmono := monomial_dilation (((7 * j : ℕ) : ℂ) / 7) c j z
  have hgamma : (((7 * j : ℕ) : ℂ) / 7) = (j : ℂ) := by push_cast; ring
  rw [hgamma, sub_self, zero_mul, zero_mul] at hmono
  unfold complexDilation at *
  rw [deriv_fun_add hf (by fun_prop)]
  rw [hgamma] at hmain ⊢
  linear_combination hmain + hmono

def realPowerSeries (a : ℕ → ℝ) (q : ℝ) : ℝ := ∑' n, a n * q ^ n

def realInverseSeries (m : ℕ) (a : ℕ → ℝ) (q : ℝ) : ℝ :=
  (inverseSeries m (fun n ↦ (a n : ℂ)) q).re

theorem powerSeries_ofReal (a : ℕ → ℝ) (q : ℝ) :
    powerSeries (fun n ↦ (a n : ℂ)) q = (realPowerSeries a q : ℂ) := by
  simp only [powerSeries, realPowerSeries, Complex.ofReal_tsum, Complex.ofReal_mul,
    Complex.ofReal_pow]

theorem realInverseSeries_hasDerivAt (m : ℕ) {a : ℕ → ℝ} {R q : ℝ}
    (ha : Summable (fun n ↦ |a n| * R ^ n)) (hq : |q| < R) :
    HasDerivAt (realInverseSeries m a)
      (deriv (inverseSeries m (fun n ↦ (a n : ℂ))) (q : ℂ)).re q := by
  have hac : Summable (fun n ↦ ‖(a n : ℂ)‖ * R ^ n) := by simpa using ha
  have hqc : ‖(q : ℂ)‖ < R := by simpa using hq
  exact ((inverseSeries_differentiableOn m hac).differentiableAt
    (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hqc))).hasDerivAt.real_of_complex

/-- Restriction of the constructed analytic inverse returns the real operator used by the
actual fluid axis. No derivative or real-valuedness port is assumed. -/
theorem realInverseSeries_solves (m : ℕ) {a : ℕ → ℝ} {R q : ℝ}
    (ha : Summable (fun n ↦ |a n| * R ^ n)) (hq : |q| < R)
    (hcompatible : ∀ n, 7 * n = m → a n = 0) :
    dilationTransport
      ((m : ℝ) / 7) (realInverseSeries m a) q = realPowerSeries a q := by
  have hac : Summable (fun n ↦ ‖(a n : ℂ)‖ * R ^ n) := by simpa using ha
  have hqc : ‖(q : ℂ)‖ < R := by simpa using hq
  have h := inverseSeries_solves_compatible_source m hac
    (fun n hn ↦ by simp [hcompatible n hn]) hqc
  rw [powerSeries_ofReal] at h
  have hr := congrArg Complex.re h
  unfold dilationTransport
  rw [(realInverseSeries_hasDerivAt m ha hq).deriv]
  simpa [complexDilation, realInverseSeries, Complex.mul_re] using hr

/-- The analytic inverse composes with the constructed reciprocal axis in the critical frame.
The admitted source coefficients still owe their own summability and resonant compatibility. -/
theorem critical_swirlCarrier_return (m : ℕ) (F : ℝ → ℝ)
    (hF : ContDiff ℝ 2 F) (hpositive : ∀ z, 0 < F z)
    {a : ℕ → ℝ} {R : ℝ} (ha : Summable (fun n ↦ |a n| * R ^ n))
    (hcompatible : ∀ n, 7 * n = m → a n = 0) (z : ℝ)
    (hz : |primitiveInv F z| < R) :
    let K := swirlCarrier
      m F (realInverseSeries m a)
    axialGamma (3 / 2) 1 F z * deriv K z +
      (3 / 2 + (2 * (m : ℝ) + 1) - ((m : ℝ) + 1) *
        deriv (axialW (3 / 2) 1 F) z) * K z =
      (7 / 2) * F z ^ (m + 1) * realPowerSeries a
        (primitiveInv F z) := by
  have h := swirl_linear_transport
    m (3 / 2) 1 F (realInverseSeries m a) hF hpositive (by norm_num) z
    (realInverseSeries_hasDerivAt m ha hz).differentiableAt
  have hg := swirlExponent_energyCritical
    m 1 (by norm_num)
  norm_num at hg
  rw [hg, realInverseSeries_solves m ha hz hcompatible] at h
  convert h using 1 <;> norm_num

#print axioms critical_divisor_gap
#print axioms inverseCoefficient_bound
#print axioms inverseCoefficient_source
#print axioms inverseSeries_differentiableOn
#print axioms inverseSeries_returns_residual
#print axioms inverseSeries_solves_compatible_source
#print axioms inverseSeries_norm_bound
#print axioms inverseSeries_fibre_returns_same_residual
#print axioms realInverseSeries_solves
#print axioms critical_swirlCarrier_return

end Soma.Holonics.Millennium.NavierStokesAnalyticDilationInverse
