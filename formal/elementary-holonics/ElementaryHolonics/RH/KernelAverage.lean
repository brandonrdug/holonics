import Mathlib
import ElementaryHolonics.RH.KernelFlow
import ElementaryHolonics.RH.XiStrip

/-!
# DB3 (i): the translation average is a cosh-weighted kernel

`avg μ f (s) = ½ (f(s + μ) + f(s − μ))`; for a kernel transform `T_K` this is `T_{cosh(μu) K}`.
The iterates multiply the kernel by `cosh(μu)^k`. A positive kernel gives a transform that is a
positive real on the real axis; a real kernel gives conjugation symmetry; an even kernel gives
the reflection `s ↦ 1 − s`.
-/

noncomputable section

namespace Soma.Holonics.RH.KernelAverage

open Real Set Filter Topology MeasureTheory Complex ComplexConjugate
open Soma.Holonics.RH.KernelFlow

/-! ## The average -/

/-- The translation average along the real direction. -/
def avg (μ : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ := (f (z + μ) + f (z - μ)) / 2

theorem avg_differentiable {μ : ℝ} {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (avg μ f) := by
  unfold avg
  exact ((hf.comp (differentiable_id.add_const _)).add
    (hf.comp (differentiable_id.sub_const _))).div_const _

theorem avg_one_sub {μ : ℝ} {f : ℂ → ℂ} (hs : ∀ s, f (1 - s) = f s) (s : ℂ) :
    avg μ f (1 - s) = avg μ f s := by
  unfold avg
  rw [show (1 : ℂ) - s + μ = 1 - (s - μ) by ring, show (1 : ℂ) - s - μ = 1 - (s + μ) by ring,
    hs, hs, add_comm]

theorem avg_conj {μ : ℝ} {f : ℂ → ℂ} (hc : ∀ s, f (conj s) = conj (f s)) (s : ℂ) :
    avg μ f (conj s) = conj (avg μ f s) := by
  unfold avg
  have e1 : conj s + (μ : ℂ) = conj (s + μ) := by
    rw [map_add, Complex.conj_ofReal]
  have e2 : conj s - (μ : ℂ) = conj (s - μ) := by
    rw [map_sub, Complex.conj_ofReal]
  rw [e1, e2, hc, hc, map_div₀, map_add, map_ofNat]

/-! ## The cosh-weighted kernel -/

theorem cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp x ≤ Real.exp |x| := Real.exp_le_exp.mpr (le_abs_self x)
  have h2 : Real.exp (-x) ≤ Real.exp |x| := Real.exp_le_exp.mpr (neg_le_abs x)
  linarith

/-- The kernel multiplied by `cosh(μu)`. -/
def coshMul (κ : Kernel) (μ : ℝ) : Kernel where
  K := fun u => Real.cosh (μ * u) * κ.K u
  cont := (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).mul κ.cont
  dom := by
    intro a b ha hb
    obtain ⟨C, hC0, hC⟩ := κ.dom a (b + |μ|) ha (by positivity)
    refine ⟨C, hC0, fun u => ?_⟩
    rw [abs_mul, abs_of_pos (Real.cosh_pos _)]
    have h1 : Real.exp (a * u ^ 2 + b * |u|) * Real.cosh (μ * u) ≤
        Real.exp (a * u ^ 2 + (b + |μ|) * |u|) := by
      calc Real.exp (a * u ^ 2 + b * |u|) * Real.cosh (μ * u)
          ≤ Real.exp (a * u ^ 2 + b * |u|) * Real.exp |μ * u| :=
            mul_le_mul_of_nonneg_left (cosh_le_exp_abs _) (Real.exp_pos _).le
        _ = Real.exp (a * u ^ 2 + (b + |μ|) * |u|) := by
            rw [← Real.exp_add, abs_mul]
            congr 1
            ring
    calc Real.exp (a * u ^ 2 + b * |u|) * (Real.cosh (μ * u) * |κ.K u|)
        = (Real.exp (a * u ^ 2 + b * |u|) * Real.cosh (μ * u)) * |κ.K u| := by ring
      _ ≤ Real.exp (a * u ^ 2 + (b + |μ|) * |u|) * |κ.K u| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ C * Real.exp (-u ^ 2) := hC u

theorem coshMul_K (κ : Kernel) (μ u : ℝ) : (coshMul κ μ).K u = Real.cosh (μ * u) * κ.K u := rfl

/-- **The transform of the cosh-weighted kernel is the average of the transform.** -/
theorem T_coshMul (κ : Kernel) (μ : ℝ) (s : ℂ) : (coshMul κ μ).T s = avg μ κ.T s := by
  unfold avg Kernel.T
  have h : ∀ u, (coshMul κ μ).lap s u = (κ.lap (s + μ) u + κ.lap (s - μ) u) / 2 := by
    intro u
    have e1 : Complex.exp ((s + μ - 1 / 2) * u) =
        Complex.exp ((s - 1 / 2) * u) * Complex.exp ((μ * u : ℝ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have e2 : Complex.exp ((s - μ - 1 / 2) * u) =
        Complex.exp ((s - 1 / 2) * u) * Complex.exp (-(μ * u : ℝ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only [Kernel.lap, coshMul_K]
    rw [e1, e2, Real.cosh_eq]
    push_cast
    ring
  rw [show (fun u => (coshMul κ μ).lap s u) = fun u => (κ.lap (s + μ) u + κ.lap (s - μ) u) / 2
    from funext h, integral_div, integral_add (κ.integrable_lap _) (κ.integrable_lap _)]

/-- The `k`-fold cosh weight. -/
def coshPow (κ : Kernel) (μ : ℝ) : ℕ → Kernel
  | 0 => κ
  | k + 1 => coshMul (coshPow κ μ k) μ

theorem coshPow_K (κ : Kernel) (μ : ℝ) (k : ℕ) (u : ℝ) :
    (coshPow κ μ k).K u = Real.cosh (μ * u) ^ k * κ.K u := by
  induction k with
  | zero => simp [coshPow]
  | succ k ih =>
    simp only [coshPow, coshMul_K, ih]
    ring

/-- **The iterated average is the transform of the `cosh^k`-weighted kernel.** -/
theorem T_coshPow (κ : Kernel) (μ : ℝ) (k : ℕ) : (coshPow κ μ k).T = (avg μ)^[k] κ.T := by
  induction k with
  | zero => simp [coshPow]
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_apply, ← ih]
    funext s
    exact T_coshMul _ _ _

/-! ## Positivity on the real axis, and the symmetries -/

theorem lap_ofReal (κ : Kernel) (σ u : ℝ) :
    κ.lap (σ : ℂ) u = ((Real.exp ((σ - 1 / 2) * u) * κ.K u : ℝ) : ℂ) := by
  simp only [Kernel.lap]
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  push_cast
  ring_nf

theorem norm_lap (κ : Kernel) (s : ℂ) (u : ℝ) :
    ‖κ.lap s u‖ = Real.exp ((s.re - 1 / 2) * u) * |κ.K u| := by
  simp only [Kernel.lap]
  have hre : ((s - 1 / 2) * (u : ℂ)).re = (s.re - 1 / 2) * u := by
    simp [Complex.mul_re, Complex.sub_re]
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, hre]

/-- **A positive kernel has a positive real transform on the real axis.** -/
theorem T_ofReal_pos (κ : Kernel) (hK : ∀ u, 0 < κ.K u) (σ : ℝ) :
    ∃ v : ℝ, 0 < v ∧ κ.T (σ : ℂ) = (v : ℂ) := by
  set g : ℝ → ℝ := fun u => Real.exp ((σ - 1 / 2) * u) * κ.K u with hg
  have hgpos : ∀ u, 0 < g u := fun u => mul_pos (Real.exp_pos _) (hK u)
  have hint : Integrable g := by
    have := (κ.integrable_lap (σ : ℂ)).norm
    refine this.congr (Eventually.of_forall fun u => ?_)
    show ‖κ.lap (σ : ℂ) u‖ = g u
    rw [norm_lap, abs_of_pos (hK u)]
    simp [hg]
  refine ⟨∫ u : ℝ, g u, ?_, ?_⟩
  · rw [integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall fun u => (hgpos u).le) hint]
    have hsupp : Function.support g = univ := by
      ext u
      simp only [Function.mem_support, mem_univ, iff_true]
      exact (hgpos u).ne'
    rw [hsupp]
    simp
  · unfold Kernel.T
    rw [show (fun u : ℝ => κ.lap (σ : ℂ) u) = fun u => ((g u : ℝ) : ℂ) from
      funext fun u => lap_ofReal κ σ u]
    exact integral_ofReal

theorem T_ofReal_ne_zero (κ : Kernel) (hK : ∀ u, 0 < κ.K u) (σ : ℝ) : κ.T (σ : ℂ) ≠ 0 := by
  obtain ⟨v, hv, h⟩ := T_ofReal_pos κ hK σ
  rw [h]
  exact_mod_cast hv.ne'

/-- A positive kernel: no zero of the transform is real. -/
theorem im_ne_zero_of_T_eq_zero (κ : Kernel) (hK : ∀ u, 0 < κ.K u) {s : ℂ} (h : κ.T s = 0) :
    s.im ≠ 0 := by
  intro him
  have hs : s = (s.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [hs] at h
  exact T_ofReal_ne_zero κ hK s.re h

theorem lap_conj (κ : Kernel) (s : ℂ) (u : ℝ) : κ.lap (conj s) u = conj (κ.lap s u) := by
  simp only [Kernel.lap]
  rw [map_mul, ← Complex.exp_conj, Complex.conj_ofReal, map_mul, map_sub, Complex.conj_ofReal,
    map_div₀, map_one, map_ofNat]

/-- **A real kernel has a conjugation-symmetric transform.** -/
theorem T_conj (κ : Kernel) (s : ℂ) : κ.T (conj s) = conj (κ.T s) := by
  unfold Kernel.T
  rw [← integral_conj (f := κ.lap s)]
  congr 1
  funext u
  exact lap_conj κ s u

/-- **An even kernel has a reflection-symmetric transform.** -/
theorem T_one_sub (κ : Kernel) (he : ∀ u, κ.K (-u) = κ.K u) (s : ℂ) : κ.T (1 - s) = κ.T s := by
  unfold Kernel.T
  have h : ∀ u, κ.lap (1 - s) u = κ.lap s (-u) := by
    intro u
    simp only [Kernel.lap]
    rw [he]
    congr 2
    push_cast
    ring
  rw [show (fun u => κ.lap (1 - s) u) = fun u => κ.lap s (-u) from funext h]
  exact MeasureTheory.integral_neg_eq_self (fun u : ℝ => κ.lap s u) volume

theorem coshPow_even (κ : Kernel) (he : ∀ u, κ.K (-u) = κ.K u) (μ : ℝ) (k : ℕ) (u : ℝ) :
    (coshPow κ μ k).K (-u) = (coshPow κ μ k).K u := by
  rw [coshPow_K, coshPow_K, he, mul_neg, Real.cosh_neg]

theorem coshPow_pos (κ : Kernel) (hK : ∀ u, 0 < κ.K u) (μ : ℝ) (k : ℕ) (u : ℝ) :
    0 < (coshPow κ μ k).K u := by
  rw [coshPow_K]
  exact mul_pos (pow_pos (Real.cosh_pos _) k) (hK u)

end Soma.Holonics.RH.KernelAverage
