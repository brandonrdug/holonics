import ElementaryHolonics.Millennium.NavierStokesH2LowVelocitySliceConversion
import ElementaryHolonics.Millennium.NavierStokesPhysicalFourierH2ProductionBridge
import ElementaryHolonics.Millennium.NavierStokesH2TriadMultiplierSwing

/-!
# Vorticity shell squares in the native H3 dissipation chart

**[proved-derived; formal-checked]** The finite vorticity `L1` square populations left by the
physical `H2` triad estimates are returned to the actual velocity coefficient carrier.  The curl
scale is read from the primitive torus character, and the two finite three-coordinate Cauchy
inequalities retain the frequency and velocity component incidences.  Thus every finite shell is
paid by the corresponding Stokes-weighted velocity square population, without a mode count or a
terminal-time premise.

No summation over dyadic grades, time integration, absorption, or continuation claim is made.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesH2VorticityShellDissipationBridge

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH2AdvectingLowGradeFaceMass
open Soma.Holonics.Millennium.NavierStokesH2LowVelocitySliceConversion
open Soma.Holonics.Millennium.NavierStokesH2TriadMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration
open Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
open Soma.Holonics.Millennium.NavierStokesPhysicalFourierH2ProductionBridge
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCrossReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear

/-! ## Finite three-coordinate receivers -/

theorem complexVectorL1_sq_le_three_mul_sum_norm_sq
    (coefficient : ComplexVector) :
    complexVectorL1 coefficient ^ 2 ≤
      3 * ∑ component : Fin 3, ‖coefficient component‖ ^ 2 := by
  rw [show complexVectorL1 coefficient =
      ∑ component : Fin 3, ‖coefficient component‖ by
    simp [complexVectorL1, Fin.sum_univ_succ]
    ring]
  simpa using (sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (Fin 3)))
    (f := fun component ↦ ‖coefficient component‖))

theorem unitTorusCurlScale_norm_sq_mul_frequencySquared
    (frequency : SpatialFrequency) :
    ‖unitTorusCurlScale‖ ^ 2 * frequencySquared frequency =
      torusStokesEigenvalue frequency := by
  have hcomplex := unitTorusCurlScale_normSquare_frequencySquared frequency
  have hnorm :
      (starRingEnd ℂ) unitTorusCurlScale * unitTorusCurlScale =
        ((‖unitTorusCurlScale‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  rw [hnorm] at hcomplex
  exact_mod_cast hcomplex

/-! ## One actual curl coefficient -/

theorem complexVectorL1_frequencyCurlMultiplier_sq_le
    (frequency : SpatialFrequency) (velocityMode : ComplexVector) :
    complexVectorL1 (frequencyCurlMultiplier frequency velocityMode) ^ 2 ≤
      9 * torusStokesEigenvalue frequency *
        (∑ component : Fin 3, ‖velocityMode component‖ ^ 2) := by
  have hcurl :
      complexVectorL1 (frequencyCurlMultiplier frequency velocityMode) ≤
        ‖unitTorusCurlScale‖ * frequencyL1 frequency *
          complexVectorL1 velocityMode := by
    rw [frequencyCurlMultiplier_eq_unitTorusCurlScale_smul,
      complexVectorL1_smul]
    calc
      ‖unitTorusCurlScale‖ *
          complexVectorL1
            (complexCross (complexFrequencyVector frequency) velocityMode) ≤
        ‖unitTorusCurlScale‖ *
          (complexVectorL1 (complexFrequencyVector frequency) *
            complexVectorL1 velocityMode) :=
        mul_le_mul_of_nonneg_left
          (complexVectorL1_cross_le_mul
            (complexFrequencyVector frequency) velocityMode)
          (norm_nonneg unitTorusCurlScale)
      _ = ‖unitTorusCurlScale‖ * frequencyL1 frequency *
          complexVectorL1 velocityMode := by
        rw [complexVectorL1_complexFrequencyVector]
        ring
  have hcurlNonneg :
      0 ≤ complexVectorL1 (frequencyCurlMultiplier frequency velocityMode) :=
    complexVectorL1_nonneg _
  have hrightNonneg :
      0 ≤ ‖unitTorusCurlScale‖ * frequencyL1 frequency *
        complexVectorL1 velocityMode :=
    mul_nonneg
      (mul_nonneg (norm_nonneg _) (frequencyL1_nonneg frequency))
      (complexVectorL1_nonneg _)
  have hsquare := (sq_le_sq₀ hcurlNonneg hrightNonneg).2 hcurl
  have hfrequency := frequencyL1_sq_le_three_mul_frequencySquared frequency
  have hvelocity := complexVectorL1_sq_le_three_mul_sum_norm_sq velocityMode
  have hfrequencySquared : 0 ≤ frequencySquared frequency := by
    unfold frequencySquared
    exact Finset.sum_nonneg fun coordinate _hcoordinate ↦
      sq_nonneg (frequency coordinate : ℝ)
  calc
    complexVectorL1 (frequencyCurlMultiplier frequency velocityMode) ^ 2 ≤
        (‖unitTorusCurlScale‖ * frequencyL1 frequency *
          complexVectorL1 velocityMode) ^ 2 := hsquare
    _ = ‖unitTorusCurlScale‖ ^ 2 * frequencyL1 frequency ^ 2 *
        complexVectorL1 velocityMode ^ 2 := by ring
    _ ≤ ‖unitTorusCurlScale‖ ^ 2 *
        (3 * frequencySquared frequency) *
        (3 * ∑ component : Fin 3, ‖velocityMode component‖ ^ 2) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hfrequency (sq_nonneg ‖unitTorusCurlScale‖))
        hvelocity (sq_nonneg (complexVectorL1 velocityMode))
        (mul_nonneg (sq_nonneg ‖unitTorusCurlScale‖)
          (mul_nonneg (by norm_num) hfrequencySquared))
    _ = 9 * torusStokesEigenvalue frequency *
        (∑ component : Fin 3, ‖velocityMode component‖ ^ 2) := by
      rw [← unitTorusCurlScale_norm_sq_mul_frequencySquared]
      ring

/-! ## Actual finite shell population -/

theorem openPeriodicVorticityL1SquareMassOn_le_velocityStokesSquareMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (population : Finset SpatialFrequency) :
    openPeriodicVorticityL1SquareMassOn solution t population ≤
      9 * ∑ frequency ∈ population,
        torusStokesEigenvalue frequency *
          (∑ component : Fin 3,
            ‖openPeriodicVelocityFourierMode solution t frequency component‖ ^ 2) := by
  unfold openPeriodicVorticityL1SquareMassOn
  calc
    (∑ frequency ∈ population,
        complexVectorL1
          (openPeriodicVorticityFourierMode solution t frequency) ^ 2) ≤
      ∑ frequency ∈ population,
        9 * torusStokesEigenvalue frequency *
          (∑ component : Fin 3,
            ‖openPeriodicVelocityFourierMode solution t frequency component‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro frequency _hfrequency
      rw [openPeriodicSolutionOn_vorticityFourierMode_eq_frequencyCurlMultiplier]
      exact complexVectorL1_frequencyCurlMultiplier_sq_le frequency
        (openPeriodicVelocityFourierMode solution t frequency)
    _ = 9 * ∑ frequency ∈ population,
        torusStokesEigenvalue frequency *
          (∑ component : Fin 3,
            ‖openPeriodicVelocityFourierMode solution t frequency component‖ ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro frequency _hfrequency
      ring

/-! ## The scale-critical H3 payment -/

/-- The multiplier which remains after the completed physical `H2` lever is attached to one
vorticity square occurrence is paid by the order-three velocity coefficient weight. -/
theorem stokes_mul_one_add_stokes_mul_complexVectorL1_frequencyCurlMultiplier_sq_le
    (frequency : SpatialFrequency) (velocityMode : ComplexVector) :
    torusStokesEigenvalue frequency *
        (1 + torusStokesEigenvalue frequency) *
        complexVectorL1 (frequencyCurlMultiplier frequency velocityMode) ^ 2 ≤
      9 * periodicSobolevWeight 3 frequency *
        (∑ component : Fin 3, ‖velocityMode component‖ ^ 2) := by
  let eigenvalue := torusStokesEigenvalue frequency
  let squareMass := ∑ component : Fin 3, ‖velocityMode component‖ ^ 2
  have heigenvalue : 0 ≤ eigenvalue := torusStokesEigenvalue_nonneg frequency
  have hsquareMass : 0 ≤ squareMass :=
    Finset.sum_nonneg fun component _hcomponent ↦ sq_nonneg _
  have hcurl := complexVectorL1_frequencyCurlMultiplier_sq_le frequency velocityMode
  have hweight : eigenvalue ^ 2 * (1 + eigenvalue) ≤ (1 + eigenvalue) ^ 3 := by
    nlinarith [sq_nonneg eigenvalue, sq_nonneg (1 + eigenvalue)]
  calc
    eigenvalue * (1 + eigenvalue) *
        complexVectorL1 (frequencyCurlMultiplier frequency velocityMode) ^ 2 ≤
      eigenvalue * (1 + eigenvalue) * (9 * eigenvalue * squareMass) := by
        exact mul_le_mul_of_nonneg_left hcurl
          (mul_nonneg heigenvalue (by linarith))
    _ = 9 * (eigenvalue ^ 2 * (1 + eigenvalue)) * squareMass := by ring
    _ ≤ 9 * (1 + eigenvalue) ^ 3 * squareMass := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hweight (by norm_num)) hsquareMass
    _ = 9 * periodicSobolevWeight 3 frequency * squareMass := by
      simp [periodicSobolevWeight, eigenvalue]

/-- The actual finite population carrying the scale-critical multiplier on every addressed
vorticity coefficient. -/
def openPeriodicH2WeightedVorticityL1SquareMassOn
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (population : Finset SpatialFrequency) : ℝ :=
  ∑ frequency ∈ population,
    torusStokesEigenvalue frequency *
      (1 + torusStokesEigenvalue frequency) *
      complexVectorL1
        (openPeriodicVorticityFourierMode solution t frequency) ^ 2

theorem openPeriodicH2WeightedVorticityL1SquareMassOn_le_velocityH3SquareMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (population : Finset SpatialFrequency) :
    openPeriodicH2WeightedVorticityL1SquareMassOn solution t population ≤
      9 * ∑ frequency ∈ population,
        periodicSobolevWeight 3 frequency *
          (∑ component : Fin 3,
            ‖openPeriodicVelocityFourierMode solution t frequency component‖ ^ 2) := by
  unfold openPeriodicH2WeightedVorticityL1SquareMassOn
  calc
    (∑ frequency ∈ population,
      torusStokesEigenvalue frequency *
        (1 + torusStokesEigenvalue frequency) *
        complexVectorL1
          (openPeriodicVorticityFourierMode solution t frequency) ^ 2) ≤
      ∑ frequency ∈ population,
        9 * periodicSobolevWeight 3 frequency *
          (∑ component : Fin 3,
            ‖openPeriodicVelocityFourierMode solution t frequency component‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro frequency _hfrequency
      rw [openPeriodicSolutionOn_vorticityFourierMode_eq_frequencyCurlMultiplier]
      exact
        stokes_mul_one_add_stokes_mul_complexVectorL1_frequencyCurlMultiplier_sq_le
          frequency (openPeriodicVelocityFourierMode solution t frequency)
    _ = 9 * ∑ frequency ∈ population,
        periodicSobolevWeight 3 frequency *
          (∑ component : Fin 3,
            ‖openPeriodicVelocityFourierMode solution t frequency component‖ ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro frequency _hfrequency
      ring

theorem sum_periodicSobolevWeight_three_norm_sq_le_coefficientNorm_sq
    (coeff : PeriodicSobolevCoefficients 3)
    (population : Finset SpatialFrequency) :
    (∑ frequency ∈ population,
      periodicSobolevWeight 3 frequency * ‖coeff.1 frequency‖ ^ 2) ≤
      periodicH3CoefficientNorm coeff ^ 2 := by
  have hsummable : Summable fun frequency : SpatialFrequency ↦
      periodicSobolevWeight 3 frequency * ‖coeff.1 frequency‖ ^ 2 :=
    coeff.2
  have hfinite := hsummable.sum_le_tsum population
    (fun frequency _hfrequency ↦
      mul_nonneg (periodicSobolevWeight_nonneg 3 frequency) (sq_nonneg _))
  have hnorm := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (weightedAbsoluteCoefficient coeff)
  have hnorm' :
      (∑' frequency : SpatialFrequency,
        periodicSobolevWeight 3 frequency * ‖coeff.1 frequency‖ ^ 2) =
        periodicH3CoefficientNorm coeff ^ 2 := by
    unfold periodicH3CoefficientNorm
    calc
      (∑' frequency : SpatialFrequency,
          periodicSobolevWeight 3 frequency * ‖coeff.1 frequency‖ ^ 2) =
        ∑' frequency : SpatialFrequency,
          ‖weightedAbsoluteCoefficient coeff frequency‖ ^ 2 := by
            apply tsum_congr
            intro frequency
            simp only [weightedAbsoluteCoefficient, Real.norm_eq_abs,
              abs_of_nonneg (mul_nonneg (sobolevThreeAmplitude_nonneg frequency)
                (norm_nonneg _)), mul_pow, sobolevThreeAmplitude_sq]
      _ = ‖weightedAbsoluteCoefficient coeff‖ ^ 2 := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hnorm.symm
  exact hfinite.trans_eq hnorm'

theorem finite_velocityH3SquareMass_le_native
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (population : Finset SpatialFrequency) :
    (∑ frequency ∈ population,
      periodicSobolevWeight 3 frequency *
        (∑ component : Fin 3,
          ‖openPeriodicVelocityFourierMode solution t frequency component‖ ^ 2)) ≤
      3 * ‖openVelocityWeightedH3State solution t‖ ^ 2 := by
  have hcomponent (component : Fin 3) :
      (∑ frequency ∈ population,
        periodicSobolevWeight 3 frequency *
          ‖openPeriodicVelocityFourierMode solution t frequency component‖ ^ 2) ≤
        periodicH3CoefficientNorm (openVelocityH3State solution t component) ^ 2 := by
    simpa only [openVelocityH3State_mode_eq_openPeriodicVelocityFourierMode] using
      sum_periodicSobolevWeight_three_norm_sq_le_coefficientNorm_sq
        (openVelocityH3State solution t component) population
  calc
    (∑ frequency ∈ population,
      periodicSobolevWeight 3 frequency *
        (∑ component : Fin 3,
          ‖openPeriodicVelocityFourierMode solution t frequency component‖ ^ 2)) =
      ∑ component : Fin 3, ∑ frequency ∈ population,
        periodicSobolevWeight 3 frequency *
          ‖openPeriodicVelocityFourierMode solution t frequency component‖ ^ 2 := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
    _ ≤ ∑ component : Fin 3,
        periodicH3CoefficientNorm (openVelocityH3State solution t component) ^ 2 := by
      exact Finset.sum_le_sum fun component _hcomponent ↦ hcomponent component
    _ ≤ ∑ _component : Fin 3, ‖openVelocityWeightedH3State solution t‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro component _hcomponent
      rw [show periodicH3CoefficientNorm (openVelocityH3State solution t component) =
          ‖openVelocityWeightedH3State solution t component‖ by
        have hstate := unweightedVectorThree_openVelocityWeightedH3State solution t
        rw [← hstate]
        exact periodicH3CoefficientNorm_weightedSobolevCoefficients _]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (norm_le_pi_norm (openVelocityWeightedH3State solution t) component) 2
    _ = 3 * ‖openVelocityWeightedH3State solution t‖ ^ 2 := by simp

theorem openPeriodicH2WeightedVorticityL1SquareMassOn_le_nativeH3
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (population : Finset SpatialFrequency) :
    openPeriodicH2WeightedVorticityL1SquareMassOn solution t population ≤
      27 * ‖openVelocityWeightedH3State solution t‖ ^ 2 := by
  calc
    openPeriodicH2WeightedVorticityL1SquareMassOn solution t population ≤
      9 * ∑ frequency ∈ population,
        periodicSobolevWeight 3 frequency *
          (∑ component : Fin 3,
            ‖openPeriodicVelocityFourierMode solution t frequency component‖ ^ 2) :=
      openPeriodicH2WeightedVorticityL1SquareMassOn_le_velocityH3SquareMass
        solution t population
    _ ≤ 9 * (3 * ‖openVelocityWeightedH3State solution t‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (finite_velocityH3SquareMass_le_native solution t population) (by norm_num)
    _ = 27 * ‖openVelocityWeightedH3State solution t‖ ^ 2 := by ring

section Audit

#print axioms complexVectorL1_sq_le_three_mul_sum_norm_sq
#print axioms unitTorusCurlScale_norm_sq_mul_frequencySquared
#print axioms complexVectorL1_frequencyCurlMultiplier_sq_le
#print axioms openPeriodicVorticityL1SquareMassOn_le_velocityStokesSquareMass
#print axioms stokes_mul_one_add_stokes_mul_complexVectorL1_frequencyCurlMultiplier_sq_le
#print axioms openPeriodicH2WeightedVorticityL1SquareMassOn_le_velocityH3SquareMass
#print axioms sum_periodicSobolevWeight_three_norm_sq_le_coefficientNorm_sq
#print axioms finite_velocityH3SquareMass_le_native
#print axioms openPeriodicH2WeightedVorticityL1SquareMassOn_le_nativeH3

end Audit

end Soma.Holonics.Millennium.NavierStokesH2VorticityShellDissipationBridge
