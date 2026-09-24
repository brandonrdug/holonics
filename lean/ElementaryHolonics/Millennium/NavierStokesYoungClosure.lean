import ElementaryHolonics.Millennium.NavierStokesYoungRiccati

/-!
# The closure form: dissipation at weight six against a drive at weight six times `K(t)`

The source bound of the Young-drive Riccati is paid entirely by the sixth moment,

```text
sourceBound ≤ K(t) · W₆,      K(t) = 3³ (2π)² · 3 · 2⁵ · [ (3/(2π)²) · 52 · W₂ + (ℓ¹(û(0)) + √(52·3/(2π)²) √W₂)² ],
```

by the interpolation `W₄² ≤ W₂ W₆` and the velocity mass in moments.  One arithmetic-geometric
step then returns, for every finite family of nonzero modes,

```text
M₄' ≤ −2 ν (2π)² M₆(F) + ν (2π)² W₆ + (3 K(t) / (ν (2π)²)) · M₄(F).
```

`K(t)` carries only the second moment and the zero mode.  Every constant is a product expansion.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Finset

namespace Soma.Holonics.Millennium.NavierStokesYoungClosure

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFullStrain
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFiniteBandBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionSourceModulus
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesH2StorageDissipationPayment
open Soma.Holonics.Millennium.NavierStokesAlignedStrainBudget
open Soma.Holonics.Millennium.NavierStokesModalRiccati
open Soma.Holonics.Millennium.NavierStokesHalfRadiusReach
open Soma.Holonics.Millennium.NavierStokesMomentSwap
open Soma.Holonics.Millennium.NavierStokesMomentGap
open Soma.Holonics.Millennium.NavierStokesFourthMomentRiccati
open Soma.Holonics.Millennium.NavierStokesWeightedYoung
open Soma.Holonics.Millennium.NavierStokesMomentInterpolation
open Soma.Holonics.Millennium.NavierStokesSixthYoung
open Soma.Holonics.Millennium.NavierStokesYoungRiccati

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
  (t : Ioo 0 T)

/-- The closure coefficient: the second moment and the zero mode. -/
def closureCoefficient (τ : ℝ) : ℝ :=
  3 ^ 3 * (2 * Real.pi) ^ 2 * 3 * 2 ^ 5 *
    (3 / (2 * Real.pi) ^ 2 * 52 * moment (velocity := velocity) 2 τ +
      (l1Pop solution t 0 + Real.sqrt (52 * (3 / (2 * Real.pi) ^ 2)) *
        Real.sqrt (moment (velocity := velocity) 2 τ)) ^ 2)

theorem closureCoefficient_nonneg (τ : ℝ) : 0 ≤ closureCoefficient (velocity := velocity) solution t τ := by
  unfold closureCoefficient
  have := moment_nonneg (velocity := velocity) 2 τ
  positivity

/-- **The source is paid by the sixth moment.** -/
theorem sourceBound_le (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) :
    sourceBound (velocity := velocity) solution t t.1 ≤
      closureCoefficient (velocity := velocity) solution t t.1 * moment (velocity := velocity) 6 t.1 := by
  unfold sourceBound closureCoefficient
  have hW2 := moment_nonneg (velocity := velocity) 2 t.1
  have hW6 := moment_nonneg (velocity := velocity) 6 t.1
  have hinterp := moment_four_sq_le (velocity := velocity) t.1 hsum
  have hl1 := tsum_l1Pop_le solution t hsum
  have hl10 : 0 ≤ ∑' p, l1Pop solution t p := tsum_nonneg fun p ↦ l1Pop_nonneg solution t p
  have hl1sq : (∑' p, l1Pop solution t p) ^ 2 ≤
      (l1Pop solution t 0 + Real.sqrt (52 * (3 / (2 * Real.pi) ^ 2)) *
        Real.sqrt (moment (velocity := velocity) 2 t.1)) ^ 2 :=
    pow_le_pow_left₀ hl10 hl1 2
  have hc : (0 : ℝ) ≤ 3 ^ 3 * (2 * Real.pi) ^ 2 * 3 := by positivity
  have hterm1 : 2 ^ 5 * (3 / (2 * Real.pi) ^ 2) * 52 * moment (velocity := velocity) 4 t.1 ^ 2 ≤
      2 ^ 5 * (3 / (2 * Real.pi) ^ 2) * 52 * (moment (velocity := velocity) 2 t.1 * moment (velocity := velocity) 6 t.1) :=
    mul_le_mul_of_nonneg_left hinterp (by positivity)
  have hterm2 : 2 ^ 5 * (∑' p, l1Pop solution t p) ^ 2 * moment (velocity := velocity) 6 t.1 ≤
      2 ^ 5 * (l1Pop solution t 0 + Real.sqrt (52 * (3 / (2 * Real.pi) ^ 2)) *
        Real.sqrt (moment (velocity := velocity) 2 t.1)) ^ 2 * moment (velocity := velocity) 6 t.1 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl1sq (by norm_num)) hW6
  calc 3 ^ 3 * (2 * Real.pi) ^ 2 * 3 *
        (2 ^ 5 * (3 / (2 * Real.pi) ^ 2) * 52 * moment (velocity := velocity) 4 t.1 ^ 2 +
          2 ^ 5 * (∑' p, l1Pop solution t p) ^ 2 * moment (velocity := velocity) 6 t.1)
      ≤ 3 ^ 3 * (2 * Real.pi) ^ 2 * 3 *
        (2 ^ 5 * (3 / (2 * Real.pi) ^ 2) * 52 * (moment (velocity := velocity) 2 t.1 * moment (velocity := velocity) 6 t.1) +
          2 ^ 5 * (l1Pop solution t 0 + Real.sqrt (52 * (3 / (2 * Real.pi) ^ 2)) *
            Real.sqrt (moment (velocity := velocity) 2 t.1)) ^ 2 * moment (velocity := velocity) 6 t.1) :=
        mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm2) hc
    _ = _ := by ring

/-- `2 √x √y ≤ x + y`. -/
theorem two_mul_sqrt_mul_sqrt_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * Real.sqrt x * Real.sqrt y ≤ x + y := by
  have h := sq_nonneg (Real.sqrt x - Real.sqrt y)
  have hx' := Real.sq_sqrt hx
  have hy' := Real.sq_sqrt hy
  nlinarith [h, hx', hy']

/-- **The closure form of the fourth-moment Riccati.** -/
theorem momentEnergy_riccati_closure (hnu : 0 < nu) {F : Finset SpatialFrequency}
    (hF : ∀ k ∈ F, 1 ≤ frequencySup k)
    (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) :
    ∃ D : ℝ, HasDerivAt (momentEnergy (velocity := velocity) 4 F) D t.1 ∧
      D ≤ -2 * nu * (2 * Real.pi) ^ 2 * momentEnergy (velocity := velocity) 6 F t.1 +
        nu * (2 * Real.pi) ^ 2 * moment (velocity := velocity) 6 t.1 +
        3 * closureCoefficient (velocity := velocity) solution t t.1 / (nu * (2 * Real.pi) ^ 2) *
          momentEnergy (velocity := velocity) 4 F t.1 := by
  obtain ⟨D, hD, hle⟩ := momentEnergy_riccati_young solution t hnu hF hsum
  refine ⟨D, hD, hle.trans ?_⟩
  set M4 := momentEnergy (velocity := velocity) 4 F t.1 with hM4
  set W6 := moment (velocity := velocity) 6 t.1 with hW6
  set K := closureCoefficient (velocity := velocity) solution t t.1 with hK
  have hM40 : 0 ≤ M4 := Finset.sum_nonneg fun k _ ↦ mul_nonneg (by positivity) (modalEnergy_nonneg k t.1)
  have hW60 : 0 ≤ W6 := moment_nonneg (velocity := velocity) 6 t.1
  have hK0 : 0 ≤ K := closureCoefficient_nonneg solution t t.1
  have hS := sourceBound_le solution t hsum
  have hS0 : 0 ≤ sourceBound (velocity := velocity) solution t t.1 := by
    unfold sourceBound
    have h4 := moment_nonneg (velocity := velocity) 4 t.1
    positivity
  have hnpi : 0 < nu * (2 * Real.pi) ^ 2 := by positivity
  -- 2 √(3 M4) √S ≤ 2 √(3 M4) √(K W6) = 2 √(ν(2π)² W6) √(3 K M4 / (ν(2π)²)) ≤ ν(2π)² W6 + 3 K M4/(ν(2π)²)
  have hstep1 : 2 * Real.sqrt (3 * M4) * Real.sqrt (sourceBound (velocity := velocity) solution t t.1) ≤
      2 * Real.sqrt (3 * M4) * Real.sqrt (K * W6) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hS) (by positivity)
  have hprod : Real.sqrt (3 * M4) * Real.sqrt (K * W6) =
      Real.sqrt (nu * (2 * Real.pi) ^ 2 * W6) * Real.sqrt (3 * K * M4 / (nu * (2 * Real.pi) ^ 2)) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have hamgm := two_mul_sqrt_mul_sqrt_le (x := nu * (2 * Real.pi) ^ 2 * W6)
    (y := 3 * K * M4 / (nu * (2 * Real.pi) ^ 2)) (by positivity) (by positivity)
  have hfinal : 2 * Real.sqrt (3 * M4) * Real.sqrt (sourceBound (velocity := velocity) solution t t.1) ≤
      nu * (2 * Real.pi) ^ 2 * W6 + 3 * K / (nu * (2 * Real.pi) ^ 2) * M4 := by
    calc 2 * Real.sqrt (3 * M4) * Real.sqrt (sourceBound (velocity := velocity) solution t t.1)
        ≤ 2 * Real.sqrt (3 * M4) * Real.sqrt (K * W6) := hstep1
      _ = 2 * Real.sqrt (nu * (2 * Real.pi) ^ 2 * W6) * Real.sqrt (3 * K * M4 / (nu * (2 * Real.pi) ^ 2)) := by
          rw [mul_assoc, hprod, ← mul_assoc]
      _ ≤ nu * (2 * Real.pi) ^ 2 * W6 + 3 * K * M4 / (nu * (2 * Real.pi) ^ 2) := hamgm
      _ = nu * (2 * Real.pi) ^ 2 * W6 + 3 * K / (nu * (2 * Real.pi) ^ 2) * M4 := by ring
  linarith [hfinal]

section Audit

#print axioms sourceBound_le
#print axioms momentEnergy_riccati_closure

end Audit

end Soma.Holonics.Millennium.NavierStokesYoungClosure
