import Mathlib
import ElementaryHolonics.RH.DeBruijnSeal

/-!
# DB5 (ii): the RH0/RH1 bridge — the tree's flow is the standard `H_t` through the critical chart

`H_t(z) = ⅛ · heatE(−t/4, ξ, ½ + iz/2)` with `H_t(z) = ½ ∫ e^{tv²} Φ_std(v) e^{izv} dv`,
`Φ_std(v) = ½ Φ(2v)`; the standard seam times are four times the tree's, and the standard
threshold is `4 Λ_DN`, so the tree's `[0, 1/8]` is the literature's `[0, ½]`.
-/

noncomputable section

namespace Soma.Holonics.RH.CriticalChart

open Real Set Filter Topology MeasureTheory Complex
open Soma.Holonics.RH.KernelFlow
open Soma.Holonics.RH.HeatKernelPhi
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.HeatFlowEntire
open Soma.Holonics.RH.RealZeroTimes
open Soma.Holonics.RH.DeBruijnSeal
open Soma.Holonics.RH.DescentZeros

/-- The critical chart `z ↦ ½ + iz/2`. -/
def criticalChart (z : ℂ) : ℂ := 1 / 2 + I * z / 2

/-- The standard kernel `Φ_std(v) = ½ Φ(2v)`, Rodgers–Tao's `Φ`. -/
def Φstd (v : ℝ) : ℝ := Φ (2 * v) / 2

/-- The standard de Bruijn–Newman family `H_t(z) = ½ ∫ e^{tv²} Φ_std(v) e^{izv} dv`. -/
def Hstd (t : ℝ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * ∫ v : ℝ, Complex.exp (t * v ^ 2) * Complex.exp (I * z * v) * (Φstd v : ℂ)

theorem criticalChart_re (z : ℂ) : (criticalChart z).re = 1 / 2 - z.im / 2 := by
  simp [criticalChart, Complex.mul_re, Complex.div_ofNat_re]
  first | done | ring

theorem criticalChart_on_seam_iff (z : ℂ) : (criticalChart z).re = 1 / 2 ↔ z.im = 0 := by
  rw [criticalChart_re]
  constructor <;> intro h <;> linarith

theorem criticalChart_surjective : Function.Surjective criticalChart := by
  intro s
  refine ⟨-2 * I * (s - 1 / 2), ?_⟩
  unfold criticalChart
  linear_combination (-(s - 1 / 2)) * Complex.I_sq

/-- The flowed integrand at the chart point, in the substituted variable. -/
theorem lap_flow_two_mul (t : ℝ) (z : ℂ) (v : ℝ) :
    (ΦK.flow (-t / 4)).lap (criticalChart z) (2 * v) =
      2 * (Complex.exp (t * v ^ 2) * Complex.exp (I * z * v) * (Φstd v : ℂ)) := by
  simp only [Kernel.lap, Kernel.flow, ΦK, Φstd, criticalChart]
  push_cast
  rw [show ((1 : ℂ) / 2 + I * z / 2 - 1 / 2) * (2 * (v : ℂ)) = I * z * v by ring,
    show -(-(t : ℂ) / 4) * (2 * (v : ℂ)) ^ 2 = t * v ^ 2 by ring]
  ring

/-- **The bridge:** `H_t(z) = ⅛ · heatE(−t/4, ξ, ½ + iz/2)`. -/
theorem Hstd_eq (t : ℝ) (z : ℂ) :
    Hstd t z = (1 / 8 : ℂ) * heatE (-t / 4) riemannXi (criticalChart z) := by
  rw [heatE_riemannXi_eq_T]
  unfold Hstd Kernel.T
  have hsub := Measure.integral_comp_mul_left (fun u : ℝ => (ΦK.flow (-t / 4)).lap (criticalChart z) u) 2
  try simp only at hsub
  rw [show (|(2 : ℝ)⁻¹|) = (1 / 2 : ℝ) by norm_num] at hsub
  have hlap : ∀ v : ℝ, (ΦK.flow (-t / 4)).lap (criticalChart z) (2 * v) =
      2 * (Complex.exp (t * v ^ 2) * Complex.exp (I * z * v) * (Φstd v : ℂ)) :=
    lap_flow_two_mul t z
  simp_rw [hlap] at hsub
  rw [integral_const_mul] at hsub
  rw [real_smul] at hsub
  push_cast at hsub
  -- hsub : 2 * ∫ … = (1/2) * ∫ u, lap u
  have h2 : ∫ u : ℝ, (ΦK.flow (-t / 4)).lap (criticalChart z) u =
      4 * ∫ v : ℝ, Complex.exp (t * v ^ 2) * Complex.exp (I * z * v) * (Φstd v : ℂ) := by
    linear_combination (-2) * hsub
  rw [h2]
  ring

/-- The standard seam times: every zero of `H_t` is real. -/
def seamTimesStd : Set ℝ := {t | ∀ z, Hstd t z = 0 → z.im = 0}

/-- **The standard seam times are four times the tree's.** -/
theorem mem_seamTimesStd_iff (t : ℝ) : t ∈ seamTimesStd ↔ t / 4 ∈ seamTimes := by
  constructor
  · intro h s hs
    obtain ⟨z, rfl⟩ := criticalChart_surjective s
    rw [criticalChart_on_seam_iff]
    apply h z
    rw [Hstd_eq]
    rw [show -t / 4 = -(t / 4) by ring, hs, mul_zero]
  · intro h z hz
    rw [Hstd_eq] at hz
    have h8 : (1 / 8 : ℂ) ≠ 0 := by norm_num
    have := (mul_eq_zero.mp hz).resolve_left h8
    rw [show -t / 4 = -(t / 4) by ring] at this
    exact (criticalChart_on_seam_iff z).mp (h _ this)

theorem seamTimesStd_eq : seamTimesStd = (fun τ => 4 * τ) '' seamTimes := by
  ext t
  rw [mem_seamTimesStd_iff]
  constructor
  · intro h
    exact ⟨t / 4, h, by ring⟩
  · rintro ⟨τ, hτ, rfl⟩
    rwa [show 4 * τ / 4 = τ by ring]

/-- The standard threshold. -/
def Λstd : ℝ := sInf seamTimesStd

/-- **`Λ_std = 4 Λ_DN`.** -/
theorem Λstd_eq : Λstd = 4 * Λ_DN := by
  have himg : (fun τ : ℝ => 4 * τ) '' Ici Λ_DN = Ici (4 * Λ_DN) := by
    ext x
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      exact mem_Ici.mpr (mul_le_mul_of_nonneg_left (mem_Ici.mp hτ) (by norm_num))
    · intro hx
      exact ⟨x / 4, by simp only [mem_Ici] at hx ⊢; linarith, by ring⟩
  unfold Λstd
  rw [seamTimesStd_eq, seamTimes_eq_Ici, himg, csInf_Ici]

/-- **`Λ_std ∈ [0, ½]`: de Bruijn's and Rodgers–Tao's bounds in the standard coordinate.** -/
theorem Λstd_mem_Icc : Λstd ∈ Icc (0 : ℝ) (1 / 2) := by
  rw [Λstd_eq]
  have := Λ_DN_mem_Icc_eighth
  constructor <;> linarith [this.1, this.2]

/-- **`RH ⟺ Λ_std = 0`.** -/
theorem riemannHypothesis_iff_Λstd_eq : RiemannHypothesis ↔ Λstd = 0 := by
  rw [Λstd_eq, riemannHypothesis_iff_Λ_DN_eq]
  constructor <;> intro h <;> linarith

end Soma.Holonics.RH.CriticalChart
