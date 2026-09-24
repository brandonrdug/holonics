import ElementaryHolonics.Millennium.NavierStokesH2AdvectingLowGradeFaceMass
import ElementaryHolonics.Millennium.NavierStokesSharpDyadicH3Tail
import ElementaryHolonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
import ElementaryHolonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge

/-!
# The actual low-velocity slice in the physical H2 current

**[proved-derived; formal-checked]** The advecting-low face-mass receiver leaves one finite
velocity `L1` slice.  This owner performs Cauchy--Schwarz on that literal slice against the
order-three Sobolev amplitude.  A positive dyadic grade is the actual sharp cube shell, whose
reciprocal `H3` mass is `O(R^-3)`.  Consequently the low pin contributes `O(R^-3/2)` before the
multiplier lever, with every Fourier occurrence and component retained.

No time integral, terminal estimate, or absorption claim is made here.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesH2LowVelocitySliceConversion

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCompleteDyadicTriadSectorPartition
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianTailDecay
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH2AdvectingLowGradeFaceMass
open Soma.Holonics.Millennium.NavierStokesH2TriadMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesHighFrequencyHeatDecay
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration
open Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
open Soma.Holonics.Millennium.NavierStokesSharpDyadicH3Tail
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## The exact positive-grade shell -/

theorem frequencyDyadicGradeSlice_succ_eq_dyadicFrequencyShell (level : ℕ) :
    frequencyDyadicGradeSlice (level + 1) = dyadicFrequencyShell level := by
  ext frequency
  rw [mem_frequencyDyadicGradeSlice_iff,
    frequencyDyadicGrade_eq_succ_iff]

/-! ## Reciprocal H3 mass of one sharp shell -/

def reciprocalH3DyadicShellSquareMass (level : ℕ) : ℝ :=
  ∑ frequency ∈ dyadicFrequencyShell level,
    (periodicSobolevWeight 3 frequency)⁻¹

theorem inv_periodicSobolevWeight_three_le_calibrated_radius_inv
    (radius : ℕ) (hradius : 0 < radius)
    {frequency : SpatialFrequency} (hfrequency : frequency ∉ frequencyCube radius) :
    (periodicSobolevWeight 3 frequency)⁻¹ ≤
      ((primitiveTorusStokesScale * (radius : ℝ) ^ 2) ^ 3)⁻¹ := by
  have hradiusCast : 0 < (radius : ℝ) := by exact_mod_cast hradius
  have hfrequencyLower :
      (radius : ℝ) ^ 2 ≤ frequencySquared frequency := by
    have hstrong :=
      radius_add_one_sq_le_frequencySquared_of_not_mem_frequencyCube
        radius hfrequency
    have hweak : (radius : ℝ) ^ 2 ≤ (radius + 1 : ℝ) ^ 2 := by
      apply pow_le_pow_left₀ (Nat.cast_nonneg radius)
      exact_mod_cast Nat.le_succ radius
    exact hweak.trans hstrong
  have hcalibratedLower :
      primitiveTorusStokesScale * (radius : ℝ) ^ 2 ≤
        torusStokesEigenvalue frequency := by
    rw [torusStokesEigenvalue_eq_primitiveScale_mul_frequencySquared]
    exact mul_le_mul_of_nonneg_left hfrequencyLower
      primitiveTorusStokesScale_pos.le
  have hbaseLower :
      primitiveTorusStokesScale * (radius : ℝ) ^ 2 ≤
        1 + torusStokesEigenvalue frequency := by
    linarith
  have hcalibratedNonneg :
      0 ≤ primitiveTorusStokesScale * (radius : ℝ) ^ 2 :=
    mul_nonneg primitiveTorusStokesScale_pos.le (sq_nonneg _)
  have hweightLower :
      (primitiveTorusStokesScale * (radius : ℝ) ^ 2) ^ 3 ≤
        periodicSobolevWeight 3 frequency := by
    rw [periodicSobolevWeight]
    exact pow_le_pow_left₀ hcalibratedNonneg hbaseLower 3
  exact (inv_le_inv₀ (periodicSobolevWeight_pos 3 frequency)
    (pow_pos (mul_pos primitiveTorusStokesScale_pos (sq_pos_of_pos hradiusCast)) 3)).2
      hweightLower

theorem reciprocalH3DyadicShellSquareMass_nonneg (level : ℕ) :
    0 ≤ reciprocalH3DyadicShellSquareMass level := by
  unfold reciprocalH3DyadicShellSquareMass
  exact Finset.sum_nonneg fun frequency _ ↦
    inv_nonneg.mpr (periodicSobolevWeight_nonneg 3 frequency)

theorem reciprocalH3DyadicShellSquareMass_le (level : ℕ) :
    reciprocalH3DyadicShellSquareMass level ≤
      125 * ((primitiveTorusStokesScale ^ 3 *
        (dyadicRadius level : ℝ) ^ 3)⁻¹) := by
  have hradius : 0 < dyadicRadius level := by simp [dyadicRadius]
  have hpoint (frequency : SpatialFrequency)
      (hfrequency : frequency ∈ dyadicFrequencyShell level) :
      (periodicSobolevWeight 3 frequency)⁻¹ ≤
        ((primitiveTorusStokesScale *
          (dyadicRadius level : ℝ) ^ 2) ^ 3)⁻¹ :=
    inv_periodicSobolevWeight_three_le_calibrated_radius_inv
      (dyadicRadius level) hradius (Finset.mem_sdiff.mp hfrequency).2
  unfold reciprocalH3DyadicShellSquareMass
  calc
    (∑ frequency ∈ dyadicFrequencyShell level,
          (periodicSobolevWeight 3 frequency)⁻¹) ≤
        (dyadicFrequencyShell level).card •
          ((primitiveTorusStokesScale *
            (dyadicRadius level : ℝ) ^ 2) ^ 3)⁻¹ :=
      Finset.sum_le_card_nsmul _ _ _ hpoint
    _ = ((dyadicFrequencyShell level).card : ℝ) *
          ((primitiveTorusStokesScale *
            (dyadicRadius level : ℝ) ^ 2) ^ 3)⁻¹ := by simp
    _ ≤ (125 * (dyadicRadius level) ^ 3 : ℕ) *
          ((primitiveTorusStokesScale *
            (dyadicRadius level : ℝ) ^ 2) ^ 3)⁻¹ := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast
          card_dyadicFrequencyShell_le_one_hundred_twenty_five_mul_cube level
      · exact inv_nonneg.mpr (pow_nonneg
          (mul_nonneg primitiveTorusStokesScale_pos.le (sq_nonneg _)) 3)
    _ = 125 * ((primitiveTorusStokesScale ^ 3 *
        (dyadicRadius level : ℝ) ^ 3)⁻¹) := by
      have hradiusNe : (dyadicRadius level : ℝ) ≠ 0 := by positivity
      have hscaleNe : primitiveTorusStokesScale ≠ 0 :=
        primitiveTorusStokesScale_pos.ne'
      push_cast
      field_simp [hscaleNe, hradiusNe]

/-! ## Finite weighted Cauchy on the literal coefficient population -/

theorem sum_norm_coeff_on_le_sqrt_reciprocalH3Mass_mul_norm
    (coeff : PeriodicSobolevCoefficients 3)
    (population : Finset SpatialFrequency) :
    (∑ frequency ∈ population, ‖coeff.1 frequency‖) ≤
      Real.sqrt
          (∑ frequency ∈ population,
            (periodicSobolevWeight 3 frequency)⁻¹) *
        periodicH3CoefficientNorm coeff := by
  let reciprocal : SpatialFrequency → ℝ := fun frequency ↦
    (Real.sqrt (periodicSobolevWeight 3 frequency))⁻¹
  let weighted : SpatialFrequency → ℝ := fun frequency ↦
    sobolevThreeAmplitude frequency * ‖coeff.1 frequency‖
  have hproduct (frequency : SpatialFrequency) :
      reciprocal frequency * weighted frequency = ‖coeff.1 frequency‖ := by
    have hsqrt : 0 < Real.sqrt (periodicSobolevWeight 3 frequency) :=
      Real.sqrt_pos.2 (periodicSobolevWeight_pos 3 frequency)
    dsimp only [reciprocal, weighted, sobolevThreeAmplitude]
    field_simp
  have hreciprocalSquare :
      (∑ frequency ∈ population, reciprocal frequency ^ 2) =
        ∑ frequency ∈ population,
          (periodicSobolevWeight 3 frequency)⁻¹ := by
    apply Finset.sum_congr rfl
    intro frequency _hfrequency
    dsimp only [reciprocal]
    rw [inv_pow, Real.sq_sqrt (periodicSobolevWeight_nonneg 3 frequency)]
  have hweightedSummable : Summable fun frequency : SpatialFrequency ↦
      weighted frequency ^ 2 := by
    have h := (lp.memℓp (weightedAbsoluteCoefficient coeff)).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
      weightedAbsoluteCoefficient, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sobolevThreeAmplitude_nonneg _)
        (norm_nonneg _))] using h
  have hweightedFinite :
      (∑ frequency ∈ population, weighted frequency ^ 2) ≤
        periodicH3CoefficientNorm coeff ^ 2 := by
    have hfinite := hweightedSummable.sum_le_tsum population
      (fun frequency _hfrequency ↦ sq_nonneg (weighted frequency))
    have hnorm := lp.norm_rpow_eq_tsum
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      (weightedAbsoluteCoefficient coeff)
    have hnorm' :
        (∑' frequency : SpatialFrequency, weighted frequency ^ 2) =
          periodicH3CoefficientNorm coeff ^ 2 := by
      unfold periodicH3CoefficientNorm
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
        weightedAbsoluteCoefficient, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (sobolevThreeAmplitude_nonneg _)
          (norm_nonneg _))] using hnorm.symm
    exact hfinite.trans_eq hnorm'
  have hsqrtWeighted :
      Real.sqrt (∑ frequency ∈ population, weighted frequency ^ 2) ≤
        periodicH3CoefficientNorm coeff := by
    calc
      Real.sqrt (∑ frequency ∈ population, weighted frequency ^ 2) ≤
          Real.sqrt (periodicH3CoefficientNorm coeff ^ 2) :=
        Real.sqrt_le_sqrt hweightedFinite
      _ = periodicH3CoefficientNorm coeff := by
        rw [Real.sqrt_sq_eq_abs,
          abs_of_nonneg (periodicH3CoefficientNorm_nonneg coeff)]
  calc
    (∑ frequency ∈ population, ‖coeff.1 frequency‖) =
        ∑ frequency ∈ population,
          reciprocal frequency * weighted frequency := by
      apply Finset.sum_congr rfl
      intro frequency _hfrequency
      exact (hproduct frequency).symm
    _ ≤ Real.sqrt (∑ frequency ∈ population, reciprocal frequency ^ 2) *
          Real.sqrt (∑ frequency ∈ population, weighted frequency ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt population reciprocal weighted
    _ ≤ Real.sqrt
          (∑ frequency ∈ population,
            (periodicSobolevWeight 3 frequency)⁻¹) *
        periodicH3CoefficientNorm coeff := by
      rw [hreciprocalSquare]
      exact mul_le_mul_of_nonneg_left hsqrtWeighted (Real.sqrt_nonneg _)

/-! ## The actual open-solution low slice -/

theorem sum_openVelocityH3CoefficientNorm_le_three_mul_native
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    (∑ component : Fin 3,
        periodicH3CoefficientNorm (openVelocityH3State solution t component)) ≤
      3 * ‖openVelocityWeightedH3State solution t‖ := by
  have hstate := unweightedVectorThree_openVelocityWeightedH3State solution t
  calc
    (∑ component : Fin 3,
        periodicH3CoefficientNorm (openVelocityH3State solution t component)) =
        ∑ component : Fin 3,
          periodicH3CoefficientNorm
            (unweightedVectorThree (openVelocityWeightedH3State solution t) component) := by
      apply Finset.sum_congr rfl
      intro component _hcomponent
      rw [hstate]
    _ = ∑ component : Fin 3,
        ‖openVelocityWeightedH3State solution t component‖ := by
      apply Finset.sum_congr rfl
      intro component _hcomponent
      exact periodicH3CoefficientNorm_weightedSobolevCoefficients _
    _ ≤ ∑ _component : Fin 3,
        ‖openVelocityWeightedH3State solution t‖ := by
      apply Finset.sum_le_sum
      intro component _hcomponent
      exact norm_le_pi_norm (openVelocityWeightedH3State solution t) component
    _ = 3 * ‖openVelocityWeightedH3State solution t‖ := by simp

theorem openPeriodicVelocityL1MassOn_gradeSucc_le
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (level : ℕ) :
    openPeriodicVelocityL1MassOn solution t
        (frequencyDyadicGradeSlice (level + 1)) ≤
      Real.sqrt (reciprocalH3DyadicShellSquareMass level) *
        (3 * ‖openVelocityWeightedH3State solution t‖) := by
  rw [frequencyDyadicGradeSlice_succ_eq_dyadicFrequencyShell]
  have hcomponent (component : Fin 3) :
      (∑ frequency ∈ dyadicFrequencyShell level,
          ‖openPeriodicVelocityFourierMode solution t frequency component‖) ≤
        Real.sqrt (reciprocalH3DyadicShellSquareMass level) *
          periodicH3CoefficientNorm (openVelocityH3State solution t component) := by
    simpa only [openVelocityH3State_mode_eq_openPeriodicVelocityFourierMode,
      reciprocalH3DyadicShellSquareMass] using
      (sum_norm_coeff_on_le_sqrt_reciprocalH3Mass_mul_norm
        (openVelocityH3State solution t component)
        (dyadicFrequencyShell level))
  unfold openPeriodicVelocityL1MassOn complexVectorL1
  calc
    (∑ frequency ∈ dyadicFrequencyShell level,
        (‖openPeriodicVelocityFourierMode solution t frequency 0‖ +
          ‖openPeriodicVelocityFourierMode solution t frequency 1‖ +
          ‖openPeriodicVelocityFourierMode solution t frequency 2‖)) =
        ∑ component : Fin 3, ∑ frequency ∈ dyadicFrequencyShell level,
          ‖openPeriodicVelocityFourierMode solution t frequency component‖ := by
      simp only [Fin.sum_univ_three]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ ∑ component : Fin 3,
        Real.sqrt (reciprocalH3DyadicShellSquareMass level) *
          periodicH3CoefficientNorm (openVelocityH3State solution t component) := by
      exact Finset.sum_le_sum fun component _hcomponent ↦ hcomponent component
    _ = Real.sqrt (reciprocalH3DyadicShellSquareMass level) *
        (∑ component : Fin 3,
          periodicH3CoefficientNorm (openVelocityH3State solution t component)) := by
      rw [Finset.mul_sum]
    _ ≤ Real.sqrt (reciprocalH3DyadicShellSquareMass level) *
        (3 * ‖openVelocityWeightedH3State solution t‖) :=
      mul_le_mul_of_nonneg_left
        (sum_openVelocityH3CoefficientNorm_le_three_mul_native solution t)
        (Real.sqrt_nonneg _)

theorem openPeriodicVelocityL1MassOn_gradeSucc_le_explicit
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (level : ℕ) :
    openPeriodicVelocityL1MassOn solution t
        (frequencyDyadicGradeSlice (level + 1)) ≤
      Real.sqrt (125 * ((primitiveTorusStokesScale ^ 3 *
        (dyadicRadius level : ℝ) ^ 3)⁻¹)) *
        (3 * ‖openVelocityWeightedH3State solution t‖) := by
  exact (openPeriodicVelocityL1MassOn_gradeSucc_le solution t level).trans
    (mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (reciprocalH3DyadicShellSquareMass_le level))
      (mul_nonneg (by norm_num) (norm_nonneg _)))

/-! ## Kernel audit -/

#print axioms frequencyDyadicGradeSlice_succ_eq_dyadicFrequencyShell
#print axioms inv_periodicSobolevWeight_three_le_calibrated_radius_inv
#print axioms reciprocalH3DyadicShellSquareMass_le
#print axioms sum_norm_coeff_on_le_sqrt_reciprocalH3Mass_mul_norm
#print axioms sum_openVelocityH3CoefficientNorm_le_three_mul_native
#print axioms openPeriodicVelocityL1MassOn_gradeSucc_le_explicit

end Soma.Holonics.Millennium.NavierStokesH2LowVelocitySliceConversion
