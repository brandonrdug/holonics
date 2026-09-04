import ElementaryHolonics.Millennium.NavierStokesH2LowVelocitySliceConversion

/-!
# Summation of the calibrated low-velocity grade kernel

**[proved-derived; formal-checked]** The positive-grade low pin left by the physical `H2`
cyclic swing carries its actual dyadic radius.  Multiplying that radius by the sharp reciprocal
`H3` slice service leaves an `R^-1/2` grade kernel.  This owner proves the kernel summable by an
explicit rational geometric majorant and returns one terminal-independent grade service.

The result only sums the low-grade factor.  It does not bound the high-grade vorticity
populations, the comparable residue, a time integral, or a continuation receiver.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesH2LowVelocityGradeKernel

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesH2AdvectingLowGradeFaceMass
open Soma.Holonics.Millennium.NavierStokesH2LowVelocitySliceConversion
open Soma.Holonics.Millennium.NavierStokesH2TriadMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration

/-- The exact positive-grade coefficient multiplying the native `H3` norm after the low pin's
dyadic radius is combined with its reciprocal-shell Cauchy service. -/
def calibratedLowVelocityGradeKernel (level : ℕ) : ℝ :=
  (dyadicRadius (level + 1) : ℝ) *
    Real.sqrt (125 * ((primitiveTorusStokesScale ^ 3 *
      (dyadicRadius level : ℝ) ^ 3)⁻¹))

theorem calibratedLowVelocityGradeKernel_nonneg (level : ℕ) :
    0 ≤ calibratedLowVelocityGradeKernel level := by
  unfold calibratedLowVelocityGradeKernel
  exact mul_nonneg (by positivity) (Real.sqrt_nonneg _)

private theorem calibratedLowVelocityGradeKernel_sq (level : ℕ) :
    calibratedLowVelocityGradeKernel level ^ 2 =
      (4 * (125 * (primitiveTorusStokesScale ^ 3)⁻¹)) *
        (1 / 2 : ℝ) ^ level := by
  have hscaleNe : primitiveTorusStokesScale ≠ 0 :=
    primitiveTorusStokesScale_pos.ne'
  have hradiusPos : 0 < (dyadicRadius level : ℝ) := by
    exact_mod_cast (show 0 < dyadicRadius level by simp [dyadicRadius])
  have hradiusNe : (dyadicRadius level : ℝ) ≠ 0 := hradiusPos.ne'
  have hdenominator :
      0 < primitiveTorusStokesScale ^ 3 *
        (dyadicRadius level : ℝ) ^ 3 :=
    mul_pos (pow_pos primitiveTorusStokesScale_pos 3) (pow_pos hradiusPos 3)
  have hsqrtArgument :
      0 ≤ 125 * ((primitiveTorusStokesScale ^ 3 *
        (dyadicRadius level : ℝ) ^ 3)⁻¹) :=
    mul_nonneg (by norm_num) (inv_nonneg.mpr hdenominator.le)
  unfold calibratedLowVelocityGradeKernel
  rw [mul_pow, Real.sq_sqrt hsqrtArgument]
  simp only [dyadicRadius, pow_succ]
  push_cast
  field_simp [hscaleNe]
  have hcancel : (2 : ℝ) ^ level * (1 / 2 : ℝ) ^ level = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (2 : ℝ) ^ 2 = 4 := by norm_num
    _ = 4 * ((2 : ℝ) ^ level * (1 / 2 : ℝ) ^ level) := by rw [hcancel, mul_one]
    _ = (2 : ℝ) ^ level * 4 * (1 / 2 : ℝ) ^ level := by ring

/-- A rational ratio `3/4` dominates the exact square-root dyadic ratio while remaining strictly
below one.  This avoids hiding the grade service inside a decimal approximation. -/
theorem calibratedLowVelocityGradeKernel_le_geometric (level : ℕ) :
    calibratedLowVelocityGradeKernel level ≤
      (2 * Real.sqrt (125 * (primitiveTorusStokesScale ^ 3)⁻¹)) *
        (3 / 4 : ℝ) ^ level := by
  let amplitude : ℝ := 125 * (primitiveTorusStokesScale ^ 3)⁻¹
  have hamplitude : 0 ≤ amplitude := by
    unfold amplitude
    exact mul_nonneg (by norm_num)
      (inv_nonneg.mpr (pow_nonneg primitiveTorusStokesScale_pos.le 3))
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hratio : (1 / 2 : ℝ) ≤ (3 / 4 : ℝ) ^ 2 := by norm_num
  have hpow : (1 / 2 : ℝ) ^ level ≤ ((3 / 4 : ℝ) ^ 2) ^ level :=
    pow_le_pow_left₀ hhalf hratio level
  have hleftSquare :
      calibratedLowVelocityGradeKernel level ^ 2 =
        4 * amplitude * (1 / 2 : ℝ) ^ level := by
    rw [calibratedLowVelocityGradeKernel_sq]
  have hrightNonneg :
      0 ≤ (2 * Real.sqrt amplitude) * (3 / 4 : ℝ) ^ level := by positivity
  have hrightSquare :
      ((2 * Real.sqrt amplitude) * (3 / 4 : ℝ) ^ level) ^ 2 =
        4 * amplitude * ((3 / 4 : ℝ) ^ 2) ^ level := by
    have hsqrt : (2 * Real.sqrt amplitude) ^ 2 = 4 * amplitude := by
      rw [mul_pow, Real.sq_sqrt hamplitude]
      norm_num
    rw [mul_pow, hsqrt]
    congr 1
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  have hsquare : calibratedLowVelocityGradeKernel level ^ 2 ≤
      ((2 * Real.sqrt amplitude) * (3 / 4 : ℝ) ^ level) ^ 2 := by
    rw [hleftSquare, hrightSquare]
    exact mul_le_mul_of_nonneg_left hpow (mul_nonneg (by norm_num) hamplitude)
  nlinarith [calibratedLowVelocityGradeKernel_nonneg level]

theorem summable_calibratedLowVelocityGradeKernel :
    Summable calibratedLowVelocityGradeKernel := by
  let majorant : ℕ → ℝ := fun level ↦
    (2 * Real.sqrt (125 * (primitiveTorusStokesScale ^ 3)⁻¹)) *
      (3 / 4 : ℝ) ^ level
  have hmajorant : Summable majorant := by
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num : (3 / 4 : ℝ) < 1)).mul_left
      (2 * Real.sqrt (125 * (primitiveTorusStokesScale ^ 3)⁻¹))
  exact Summable.of_nonneg_of_le calibratedLowVelocityGradeKernel_nonneg
    calibratedLowVelocityGradeKernel_le_geometric hmajorant

/-- The complete terminal-independent low-grade coefficient service. -/
def calibratedLowVelocityGradeService : ℝ :=
  ∑' level : ℕ, calibratedLowVelocityGradeKernel level

theorem calibratedLowVelocityGradeService_nonneg :
    0 ≤ calibratedLowVelocityGradeService := by
  unfold calibratedLowVelocityGradeService
  exact tsum_nonneg calibratedLowVelocityGradeKernel_nonneg

theorem sum_calibratedLowVelocityGradeKernel_le_service
    (population : Finset ℕ) :
    (∑ level ∈ population, calibratedLowVelocityGradeKernel level) ≤
      calibratedLowVelocityGradeService := by
  unfold calibratedLowVelocityGradeService
  exact summable_calibratedLowVelocityGradeKernel.sum_le_tsum population
    (fun level _hlevel ↦ calibratedLowVelocityGradeKernel_nonneg level)

/-! ## Actual open-solution low factor -/

theorem radius_mul_openPeriodicVelocityL1MassOn_gradeSucc_le_kernel
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (level : ℕ) :
    (dyadicRadius (level + 1) : ℝ) *
        openPeriodicVelocityL1MassOn solution t
          (frequencyDyadicGradeSlice (level + 1)) ≤
      calibratedLowVelocityGradeKernel level *
        (3 * ‖openVelocityWeightedH3State solution t‖) := by
  have hradiusNonneg : 0 ≤ (dyadicRadius (level + 1) : ℝ) := by
    exact_mod_cast Nat.zero_le (dyadicRadius (level + 1))
  simpa [calibratedLowVelocityGradeKernel, mul_assoc] using
    (mul_le_mul_of_nonneg_left
      (openPeriodicVelocityL1MassOn_gradeSucc_le_explicit solution t level)
      hradiusNonneg)

theorem sum_radius_mul_openPeriodicVelocityL1MassOn_gradeSucc_le_service
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (population : Finset ℕ) :
    (∑ level ∈ population,
      (dyadicRadius (level + 1) : ℝ) *
        openPeriodicVelocityL1MassOn solution t
          (frequencyDyadicGradeSlice (level + 1))) ≤
      calibratedLowVelocityGradeService *
        (3 * ‖openVelocityWeightedH3State solution t‖) := by
  calc
    (∑ level ∈ population,
      (dyadicRadius (level + 1) : ℝ) *
        openPeriodicVelocityL1MassOn solution t
          (frequencyDyadicGradeSlice (level + 1))) ≤
        ∑ level ∈ population, calibratedLowVelocityGradeKernel level *
          (3 * ‖openVelocityWeightedH3State solution t‖) := by
      apply Finset.sum_le_sum
      intro level _hlevel
      exact radius_mul_openPeriodicVelocityL1MassOn_gradeSucc_le_kernel
        solution t level
    _ = (∑ level ∈ population, calibratedLowVelocityGradeKernel level) *
        (3 * ‖openVelocityWeightedH3State solution t‖) := by
      rw [Finset.sum_mul]
    _ ≤ calibratedLowVelocityGradeService *
        (3 * ‖openVelocityWeightedH3State solution t‖) :=
      mul_le_mul_of_nonneg_right
        (sum_calibratedLowVelocityGradeKernel_le_service population)
        (mul_nonneg (by norm_num) (norm_nonneg _))

section Audit

#print axioms calibratedLowVelocityGradeKernel_sq
#print axioms calibratedLowVelocityGradeKernel_le_geometric
#print axioms summable_calibratedLowVelocityGradeKernel
#print axioms radius_mul_openPeriodicVelocityL1MassOn_gradeSucc_le_kernel
#print axioms sum_radius_mul_openPeriodicVelocityL1MassOn_gradeSucc_le_service

end Audit

end Soma.Holonics.Millennium.NavierStokesH2LowVelocityGradeKernel
