import Mathlib
import ElementaryHolonics.RH.StripAverage
import ElementaryHolonics.RH.FosterClassHeat

/-!
# DB3 (v): the iteration — after `N²` averages with `μ = 1/(2N)` every zero of `ξ` is on the seam

The Foster class is closed under the translation average (the growth of translates), the
iterates of `ξ` are transforms of the positive even kernels `cosh(μu)^k Φ`, so they have no real
zero, a nonzero centre, and both symmetries; the strip theorem of `StripAverage` then contracts
`max(¼ − kμ², 0)` to `max(¼ − (k+1)μ², 0)` at each step, reaching `0` at `k = N²`.
-/

noncomputable section

namespace Soma.Holonics.RH.DeBruijnIterate

open Complex ComplexConjugate Set Filter Topology Real
open Soma.Holonics.RH.EntireDerivativeGrowth
open Soma.Holonics.RH.FosterClassLandau
open Soma.Holonics.RH.LineApproximation
open Soma.Holonics.RH.ConjIndex
open Soma.Holonics.RH.KernelAverage
open Soma.Holonics.RH.StripAverage
open Soma.Holonics.RH.KernelFlow
open Soma.Holonics.RH.HeatKernelPhi
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.XiStrip
open Soma.Holonics.RH.FosterClassHeat

/-! ## The class is closed under the average -/

theorem rpow_add_le {a b σ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hσ : 0 ≤ σ) :
    (a + b) ^ σ ≤ 2 ^ σ * (a ^ σ + b ^ σ) := by
  have hab : a + b ≤ 2 * max a b := by
    linarith [le_max_left a b, le_max_right a b]
  calc (a + b) ^ σ ≤ (2 * max a b) ^ σ := Real.rpow_le_rpow (by positivity) hab hσ
    _ = 2 ^ σ * (max a b) ^ σ := Real.mul_rpow (by norm_num) (by positivity)
    _ ≤ 2 ^ σ * (a ^ σ + b ^ σ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rcases le_total a b with h | h
        · rw [max_eq_right h]
          linarith [Real.rpow_nonneg ha σ]
        · rw [max_eq_left h]
          linarith [Real.rpow_nonneg hb σ]

theorem hasGrowth_avg {f : ℂ → ℂ} {A B σ μ : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hσ0 : 0 < σ)
    (hμ : 0 ≤ μ) (hg : HasGrowth f A B σ) :
    HasGrowth (avg μ f) (A * Real.exp (2 ^ σ * B * μ ^ σ)) (2 ^ σ * B) σ := by
  intro w
  have hn1 : ‖w + μ‖ ≤ ‖w‖ + μ := by
    calc ‖w + (μ : ℂ)‖ ≤ ‖w‖ + ‖(μ : ℂ)‖ := norm_add_le _ _
      _ = ‖w‖ + μ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hμ]
  have hn2 : ‖w - μ‖ ≤ ‖w‖ + μ := by
    calc ‖w - (μ : ℂ)‖ ≤ ‖w‖ + ‖(μ : ℂ)‖ := norm_sub_le _ _
      _ = ‖w‖ + μ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hμ]
  have key : (‖w‖ + μ) ^ σ ≤ 2 ^ σ * (‖w‖ ^ σ + μ ^ σ) := rpow_add_le (norm_nonneg _) hμ hσ0.le
  have hexp : ∀ v : ℂ, ‖v‖ ≤ ‖w‖ + μ →
      ‖f v‖ ≤ A * Real.exp (B * (2 ^ σ * (‖w‖ ^ σ + μ ^ σ))) := by
    intro v hv
    refine (hg v).trans ?_
    apply mul_le_mul_of_nonneg_left _ hA.le
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hB
    exact (Real.rpow_le_rpow (norm_nonneg _) hv hσ0.le).trans key
  have h1 := hexp _ hn1
  have h2 := hexp _ hn2
  unfold avg
  calc ‖(f (w + μ) + f (w - μ)) / 2‖ = ‖f (w + μ) + f (w - μ)‖ / 2 := by
        rw [norm_div, Complex.norm_two]
    _ ≤ (‖f (w + μ)‖ + ‖f (w - μ)‖) / 2 := by
        gcongr
        exact norm_add_le _ _
    _ ≤ A * Real.exp (B * (2 ^ σ * (‖w‖ ^ σ + μ ^ σ))) := by linarith
    _ = A * Real.exp (2 ^ σ * B * μ ^ σ) * Real.exp (2 ^ σ * B * ‖w‖ ^ σ) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-- **The Foster class is closed under the average**, given a nonzero centre. -/
theorem fosterClass_avg {f : ℂ → ℂ} {A B σ μ : ℝ} [hf : FosterClass f A B σ] (hμ : 0 ≤ μ)
    (hcentre : avg μ f (1 / 2) ≠ 0) :
    FosterClass (avg μ f) (A * Real.exp (2 ^ σ * B * μ ^ σ)) (2 ^ σ * B) σ where
  diff := avg_differentiable hf.diff
  symm := avg_one_sub hf.symm
  centre := hcentre
  A_pos := by have := hf.A_pos; positivity
  B_nonneg := by have := hf.B_nonneg; positivity
  σ_pos := hf.σ_pos
  σ_lt_two := hf.σ_lt_two
  growth := hasGrowth_avg hf.A_pos hf.B_nonneg hf.σ_pos hμ hf.growth

/-! ## The iterates of `ξ` -/

/-- The `k`-fold average of `ξ`. -/
def xiIter (μ : ℝ) (k : ℕ) : ℂ → ℂ := (avg μ)^[k] riemannXi

theorem xiIter_zero (μ : ℝ) : xiIter μ 0 = riemannXi := rfl

theorem xiIter_succ (μ : ℝ) (k : ℕ) : xiIter μ (k + 1) = avg μ (xiIter μ k) := by
  unfold xiIter
  rw [Function.iterate_succ_apply']

theorem xiIter_eq_T (μ : ℝ) (k : ℕ) : xiIter μ k = (coshPow ΦK μ k).T := by
  unfold xiIter
  rw [T_coshPow, ΦK_T]

theorem ΦK_pos (u : ℝ) : 0 < ΦK.K u := Φ_pos u

theorem ΦK_even (u : ℝ) : ΦK.K (-u) = ΦK.K u := Φ_neg u

theorem xiIter_conjSymm (μ : ℝ) (k : ℕ) : ConjSymm (xiIter μ k) := by
  intro z
  rw [xiIter_eq_T]
  exact T_conj _ z

theorem xiIter_noRealZero (μ : ℝ) (k : ℕ) : NoRealZero (xiIter μ k) := by
  intro z hz
  rw [xiIter_eq_T] at hz
  exact im_ne_zero_of_T_eq_zero _ (coshPow_pos ΦK ΦK_pos μ k) hz

theorem xiIter_centre_ne_zero (μ : ℝ) (k : ℕ) : xiIter μ k (1 / 2) ≠ 0 := by
  rw [xiIter_eq_T]
  have := T_ofReal_ne_zero (coshPow ΦK μ k) (coshPow_pos ΦK ΦK_pos μ k) (1 / 2)
  simpa using this

/-- The iterates are members of the class, with some constants. -/
theorem fosterClass_xiIter {μ : ℝ} (hμ : 0 ≤ μ) (k : ℕ) :
    ∃ A B : ℝ, FosterClass (xiIter μ k) A B (3 / 2) := by
  induction k with
  | zero => exact ⟨_, _, instFosterClassRiemannXi⟩
  | succ k ih =>
    obtain ⟨A, B, hk⟩ := ih
    refine ⟨A * Real.exp (2 ^ (3 / 2 : ℝ) * B * μ ^ (3 / 2 : ℝ)), 2 ^ (3 / 2 : ℝ) * B, ?_⟩
    rw [xiIter_succ]
    exact fosterClass_avg (hf := hk) hμ (by rw [← xiIter_succ]; exact xiIter_centre_ne_zero μ _)

/-! ## The strip shrinks -/

theorem max_sub_max {x y : ℝ} (hy : 0 ≤ y) : max (max x 0 - y) 0 = max (x - y) 0 := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h]
    have h1 : max (0 - y) 0 = 0 := max_eq_right (by linarith)
    have h2 : max (x - y) 0 = 0 := max_eq_right (by linarith)
    rw [h1, h2]
  · rw [max_eq_left h]

/-- **The strip of the iterates:** every zero of `xiIter μ k` has `(Re − ½)² ≤ max(¼ − kμ², 0)`. -/
theorem strip_xiIter {μ : ℝ} (hμ : 0 < μ) (k : ℕ) :
    ∀ z, xiIter μ k z = 0 → (z.re - 1 / 2) ^ 2 ≤ max (1 / 4 - k * μ ^ 2) 0 := by
  induction k with
  | zero =>
    intro z hz
    rw [xiIter_zero] at hz
    have := abs_re_sub_half_lt_of_riemannXi_eq_zero hz
    have h2 : (z.re - 1 / 2) ^ 2 < (1 / 2) ^ 2 := by
      rw [← sq_abs]
      exact pow_lt_pow_left₀ this (abs_nonneg _) (by norm_num)
    simp only [Nat.cast_zero, zero_mul, sub_zero]
    calc (z.re - 1 / 2) ^ 2 ≤ 1 / 4 := by linarith
      _ ≤ max (1 / 4) 0 := le_max_left _ _
  | succ k ih =>
    intro z hz
    rw [xiIter_succ] at hz
    obtain ⟨A, B, hk⟩ := fosterClass_xiIter hμ.le k
    set D : ℝ := max (1 / 4 - k * μ ^ 2) 0 with hD
    have hD0 : 0 ≤ D := le_max_right _ _
    have hΔ : ∀ w, xiIter μ k w = 0 → |w.re - 1 / 2| ≤ Real.sqrt D := by
      intro w hw
      exact Real.abs_le_sqrt (ih w hw)
    have := re_sq_le_of_avg_eq_zero (hf := hk) (xiIter_conjSymm μ k) (xiIter_noRealZero μ k)
      (Real.sqrt_nonneg D) hμ hΔ hz
    rw [Real.sq_sqrt hD0, hD, max_sub_max (sq_nonneg μ)] at this
    push_cast
    calc (z.re - 1 / 2) ^ 2 ≤ max (1 / 4 - k * μ ^ 2 - μ ^ 2) 0 := this
      _ = max (1 / 4 - (k + 1) * μ ^ 2) 0 := by ring_nf

/-- **After `N²` averages with `μ = 1/(2N)`, every zero of the iterate lies on the seam.** -/
theorem onSeam_xiIter {N : ℕ} (hN : 0 < N) : OnSeam (xiIter (1 / (2 * N)) (N ^ 2)) := by
  intro z hz
  have hμ : (0 : ℝ) < 1 / (2 * N) := by positivity
  have h := strip_xiIter hμ (N ^ 2) z hz
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hzero : (1 / 4 : ℝ) - (N ^ 2 : ℕ) * (1 / (2 * N)) ^ 2 = 0 := by
    push_cast
    field_simp
    ring
  rw [hzero, max_self] at h
  have : (z.re - 1 / 2) ^ 2 = 0 := le_antisymm h (sq_nonneg _)
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  linarith

end Soma.Holonics.RH.DeBruijnIterate
