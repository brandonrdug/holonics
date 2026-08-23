import ElementaryHolonics.Millennium.BirchSwinnertonDyer
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
# FamilyPeriod: the real period at one is the Beta value

**The geometric side of the rank-zero ledger, in closed form.**  The real period
`Ω = 2∫₁^∞ dx/√(x³−x)` of `y² = x³ − x` folds through two power substitutions onto
Euler's integral:

* **`theRealPeriodIsTheBetaValue`** — `Ω = B(1/4, 1/2)`: the substitution `x = t⁻²`
  carries the unbounded branch onto the lemniscatic integral `2∫₀¹ dt/√(1−t⁴)`, and
  `t⁴ = s` carries that onto the Beta integrand — both through the measure-theoretic
  change of variables, with no integrability side conditions.
* **`theRealPeriodGammaRelation`** — `Γ(1/4)·Γ(1/2) = Γ(3/4)·Ω`: the ledger's
  period in the Gamma currency.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyPeriod

open Real MeasureTheory Set
open Soma.Holonics.Millennium.BirchSwinnertonDyer

/-- The zero-extended period integrand. -/
private def G (x : ℝ) : ℝ := if 1 < x then 1 / Real.sqrt (x ^ 3 - x) else 0

/-- The zero-extended lemniscatic integrand. -/
private def H (t : ℝ) : ℝ := if t < 1 then 1 / Real.sqrt (1 - t ^ 4) else 0

/-- The zero-extended Beta integrand. -/
private def K (s : ℝ) : ℝ :=
  if s < 1 then s ^ (-(3 : ℝ)/4) * (1 - s) ^ (-(1 : ℝ)/2) else 0

/-- **The unbounded branch is the lemniscatic integral**: `x = t⁻²`. -/
private lemma step_one :
    ∫ x in Ioi (1 : ℝ), 1 / Real.sqrt (x ^ 3 - x)
      = ∫ t in Ioi (0 : ℝ), 2 * H t := by
  have hsub := integral_comp_rpow_Ioi (fun x => G x) (p := (-2 : ℝ)) (by norm_num)
  have hR : ∫ y in Ioi (0 : ℝ), G y
      = ∫ x in Ioi (1 : ℝ), 1 / Real.sqrt (x ^ 3 - x) := by
    have hind : ∀ y : ℝ, G y = Set.indicator (Ioi (1 : ℝ))
        (fun x => 1 / Real.sqrt (x ^ 3 - x)) y := by
      intro y
      unfold G
      rw [Set.indicator_apply]
      simp [Set.mem_Ioi]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun y _ => hind y,
      MeasureTheory.setIntegral_indicator measurableSet_Ioi,
      show Ioi (0 : ℝ) ∩ Ioi 1 = Ioi 1 from by
        ext x
        simp only [mem_inter_iff, mem_Ioi]
        exact ⟨fun h => h.2, fun h => ⟨lt_trans one_pos h, h⟩⟩]
  have hL : ∀ t ∈ Ioi (0 : ℝ),
      (|(-2 : ℝ)| * t ^ ((-2 : ℝ) - 1)) • G (t ^ (-2 : ℝ)) = 2 * H t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have ht3 : (0 : ℝ) < t ^ 3 := by positivity
    have htp : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) from by norm_num, Real.rpow_neg ht0.le,
        Real.rpow_natCast]
    have htm3 : t ^ ((-2 : ℝ) - 1) = (t ^ 3)⁻¹ := by
      rw [show (-2 : ℝ) - 1 = -((3 : ℕ) : ℝ) from by norm_num, Real.rpow_neg ht0.le,
        Real.rpow_natCast]
    rw [htp, htm3, smul_eq_mul, show |(-2 : ℝ)| = 2 from by norm_num]
    unfold G H
    by_cases htlt : t < 1
    · have ht21 : t ^ 2 < 1 := by nlinarith
      have h1 : 1 < (t ^ 2)⁻¹ := (one_lt_inv_iff₀).mpr ⟨by positivity, ht21⟩
      rw [if_pos h1, if_pos htlt]
      have hpos4 : 0 < 1 - t ^ 4 := by nlinarith
      have hkey : ((t ^ 2)⁻¹) ^ 3 - (t ^ 2)⁻¹ = (1 - t ^ 4) / (t ^ 3) ^ 2 := by
        field_simp
        try ring
      have hsq : Real.sqrt (((t ^ 2)⁻¹) ^ 3 - (t ^ 2)⁻¹)
          = Real.sqrt (1 - t ^ 4) / t ^ 3 := by
        rw [hkey, Real.sqrt_div hpos4.le, Real.sqrt_sq ht3.le]
      rw [hsq]
      have hs0 : Real.sqrt (1 - t ^ 4) ≠ 0 := (Real.sqrt_pos.mpr hpos4).ne'
      field_simp
      try ring
    · push_neg at htlt
      have h2 : (t ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
      rw [if_neg (not_lt.mpr h2), if_neg (not_lt.mpr htlt)]
      ring
  rw [← hR, ← hsub]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => hL t ht

/-- **The lemniscatic integral is the Beta integral**: `s = t⁴`. -/
private lemma step_two :
    ∫ t in Ioi (0 : ℝ), 4 * H t = ∫ s in Ioi (0 : ℝ), K s := by
  have hsub := integral_comp_rpow_Ioi (fun s => K s) (p := (4 : ℝ)) (by norm_num)
  have hL : ∀ t ∈ Ioi (0 : ℝ),
      (|(4 : ℝ)| * t ^ ((4 : ℝ) - 1)) • K (t ^ (4 : ℝ)) = 4 * H t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have htp : t ^ (4 : ℝ) = t ^ (4 : ℕ) := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    have htm3 : t ^ ((4 : ℝ) - 1) = t ^ (3 : ℕ) := by
      rw [show (4 : ℝ) - 1 = ((3 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    rw [htp, htm3, smul_eq_mul, show |(4 : ℝ)| = 4 from by norm_num]
    unfold K H
    by_cases htlt : t < 1
    · have h1 : t ^ (4 : ℕ) < 1 := pow_lt_one₀ ht0.le htlt (by norm_num)
      rw [if_pos h1, if_pos htlt]
      have hpos4 : 0 < 1 - t ^ (4 : ℕ) := by nlinarith
      have hpow1 : (t ^ (4 : ℕ)) ^ (-(3 : ℝ)/4) = (t ^ (3 : ℕ))⁻¹ := by
        rw [← Real.rpow_natCast t 4, ← Real.rpow_natCast t 3,
          ← Real.rpow_mul ht0.le, show ((4 : ℕ) : ℝ) * (-(3 : ℝ)/4) = -3 from by
            norm_num, show (-3 : ℝ) = -((3 : ℕ) : ℝ) from by norm_num,
          Real.rpow_neg ht0.le]
      have hpow2 : (1 - t ^ (4 : ℕ)) ^ (-(1 : ℝ)/2)
          = (Real.sqrt (1 - t ^ (4 : ℕ)))⁻¹ := by
        rw [show -(1 : ℝ)/2 = -(1/2 : ℝ) from by norm_num, Real.rpow_neg hpos4.le,
          Real.sqrt_eq_rpow]
      rw [hpow1, hpow2]
      have hs0 : Real.sqrt (1 - t ^ (4 : ℕ)) ≠ 0 := (Real.sqrt_pos.mpr hpos4).ne'
      have ht3 : (t : ℝ) ^ (3 : ℕ) ≠ 0 := by positivity
      field_simp
    · push_neg at htlt
      have h2 : ¬ (t ^ (4 : ℕ) < 1) := not_lt.mpr (one_le_pow₀ htlt)
      rw [if_neg h2, if_neg (not_lt.mpr htlt)]
      ring
  rw [← hsub]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => (hL t ht).symm

/-- The Beta-integrand set integral is mathlib's Beta integral. -/
private lemma step_three :
    ((∫ s in Ioi (0 : ℝ), K s : ℝ) : ℂ)
      = Complex.betaIntegral (1/4) (1/2) := by
  have hset : ∫ s in Ioi (0 : ℝ), K s
      = ∫ s in Ioo (0 : ℝ) 1, s ^ (-(3 : ℝ)/4) * (1 - s) ^ (-(1 : ℝ)/2) := by
    have hind : ∀ s : ℝ, K s = Set.indicator (Iio (1 : ℝ))
        (fun s => s ^ (-(3 : ℝ)/4) * (1 - s) ^ (-(1 : ℝ)/2)) s := by
      intro s
      unfold K
      rw [Set.indicator_apply]
      simp [Set.mem_Iio]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun s _ => hind s,
      MeasureTheory.setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio]
  rw [hset]
  have hIoo : ∫ s in Ioo (0 : ℝ) 1, s ^ (-(3 : ℝ)/4) * (1 - s) ^ (-(1 : ℝ)/2)
      = ∫ s in (0 : ℝ)..1, s ^ (-(3 : ℝ)/4) * (1 - s) ^ (-(1 : ℝ)/2) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [hIoo]
  unfold Complex.betaIntegral
  rw [← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
  obtain ⟨hs0, hs1⟩ := hs
  push_cast
  rw [Complex.ofReal_cpow hs0, Complex.ofReal_cpow (by linarith : (0 : ℝ) ≤ 1 - s)]
  push_cast
  norm_num

/-- **THE REAL PERIOD AT ONE IS THE BETA VALUE**: `Ω = B(1/4, 1/2)` — the
geometric side of the rank-zero ledger in closed special-function form,
kernel-checked through two measure-theoretic power substitutions. -/
theorem theRealPeriodIsTheBetaValue :
    ((realPeriod 1 : ℝ) : ℂ) = Complex.betaIntegral (1/4) (1/2) := by
  have hΩ : realPeriod 1 = 2 * ∫ x in Ioi (1 : ℝ), 1 / Real.sqrt (x ^ 3 - x) := by
    unfold realPeriod
    norm_num
  have hchain : realPeriod 1 = ∫ s in Ioi (0 : ℝ), K s := by
    rw [hΩ, step_one, ← step_two, ← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
  rw [hchain, step_three]

/-- **The period in the Gamma currency**: `Γ(1/4)·Γ(1/2) = Γ(3/4)·Ω`. -/
theorem theRealPeriodGammaRelation :
    Complex.Gamma (1/4) * Complex.Gamma (1/2)
      = Complex.Gamma (3/4) * ((realPeriod 1 : ℝ) : ℂ) := by
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (s := (1/4 : ℂ)) (t := (1/2 : ℂ)) (by norm_num) (by norm_num)
  rw [theRealPeriodIsTheBetaValue, show (3/4 : ℂ) = 1/4 + 1/2 from by norm_num]
  exact h

end Soma.Holonics.Millennium.FamilyPeriod

