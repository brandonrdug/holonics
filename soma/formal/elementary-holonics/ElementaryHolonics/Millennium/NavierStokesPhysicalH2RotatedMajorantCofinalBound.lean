import ElementaryHolonics.Millennium.NavierStokesPhysicalH2RotatedMajorantBound

/-!
# Cofinal closure of the two rotated physical H2 majorants

**[proved-derived; formal-checked]** The named finite second and third rotated populations are
regrouped through their exact high-grade fibres before any native norm payment.  At fixed high
grade the least-pin factors are summed first: grade zero remains one explicit low-frequency
receiver and all positive low grades pass through the summable calibrated low-velocity kernel.

The completed Stokes coefficient remains attached to its actual high/predecessor velocity band.
The grade slices are reindexed injectively through their frequency incidence, proving that the
current-grade family and predecessor-grade family each pay the native `H3` square at most once.
Thus the union bands have overlap at most two, and the final finite bounds are independent of the
cube radius.  No time integration, absorption, continuation, comparable-residue estimate, cyclic
cancellation, rotated-face equality, or velocity/vorticity chart identification is asserted.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2RotatedMajorantCofinalBound

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCalibratedTriadicFaceBound
open Soma.Holonics.Millennium.NavierStokesCompleteDyadicTriadSectorPartition
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH2AdvectingLowGradeFaceMass
open Soma.Holonics.Millennium.NavierStokesH2LowVelocityGradeKernel
open Soma.Holonics.Millennium.NavierStokesH2LowVelocitySliceConversion
open Soma.Holonics.Millennium.NavierStokesH2VorticityShellDissipationBridge
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
open Soma.Holonics.Millennium.NavierStokesPhysicalH2RotatedMajorantBound
open Soma.Holonics.Millennium.NavierStokesPhysicalH2UniqueLowRotationPopulation
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.Turn

/-! ## Localized low and high grade factors -/

/-- The least-pin occurrence left after the exact low/high ratio is collapsed. -/
def rotatedLowVelocityGradeFactor
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (lowGrade : ℕ) : ℝ :=
  (dyadicRadius lowGrade : ℝ) *
    openPeriodicVelocityL1MassOn solution t
      (frequencyDyadicGradeSlice lowGrade)

/-- The completed Stokes multiplier stays attached to its actual current/predecessor high band. -/
def rotatedLocalizedHighBandPayment
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (highGrade : ℕ) : ℝ :=
  rotatedLowPinStokesCoefficient highGrade *
    velocityL1SquareMassOn (openPeriodicVelocityFourierMode solution t)
      (advectingLowHighVelocityBand highGrade)

theorem rotatedLowVelocityGradeFactor_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (lowGrade : ℕ) :
    0 ≤ rotatedLowVelocityGradeFactor solution t lowGrade := by
  unfold rotatedLowVelocityGradeFactor
  exact mul_nonneg (Nat.cast_nonneg _)
    (openPeriodicVelocityL1MassOn_nonneg solution t _)

theorem rotatedLocalizedHighBandPayment_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (highGrade : ℕ) :
    0 ≤ rotatedLocalizedHighBandPayment solution t highGrade := by
  unfold rotatedLocalizedHighBandPayment
  exact mul_nonneg (rotatedLowPinStokesCoefficient_nonneg highGrade)
    (velocityL1SquareMassOn_nonneg _ _)

/-- Fixed-grade separation for the actual second oriented population. -/
theorem finiteOpenAdvectingLowSecondGradeRatioPopulationAt_le_separatedFactors
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius lowGrade highGrade : ℕ) :
    finiteAdvectingLowSecondGradeRatioPopulationAt calibration radius
        lowGrade highGrade (openPeriodicVelocityFourierMode solution t) ≤
      (calibration.fullTurn * 3) *
        (rotatedLowVelocityGradeFactor solution t lowGrade *
          rotatedLocalizedHighBandPayment solution t highGrade) := by
  have hbase := finiteAdvectingLowSecondGradeRatioPopulationAt_le_cauchyBand
    calibration radius lowGrade highGrade
      (openPeriodicVelocityFourierMode solution t)
  rw [rotatedLowPinGradeCoefficient_eq_lowRadius] at hbase
  have hmass : 0 ≤ velocityL1SquareMassOn
      (openPeriodicVelocityFourierMode solution t)
      (advectingLowHighVelocityBand highGrade) :=
    velocityL1SquareMassOn_nonneg _ _
  have hsqrt :
      Real.sqrt (velocityL1SquareMassOn
          (openPeriodicVelocityFourierMode solution t)
          (advectingLowHighVelocityBand highGrade)) *
        Real.sqrt (velocityL1SquareMassOn
          (openPeriodicVelocityFourierMode solution t)
          (advectingLowHighVelocityBand highGrade)) =
      velocityL1SquareMassOn (openPeriodicVelocityFourierMode solution t)
        (advectingLowHighVelocityBand highGrade) := by
    rw [← sq, Real.sq_sqrt hmass]
  calc
    _ ≤ (rotatedLowPinStokesCoefficient highGrade *
          (calibration.fullTurn * 3) * (dyadicRadius lowGrade : ℝ)) *
        ((∑ advecting ∈ frequencyDyadicGradeSlice lowGrade,
            complexVectorL1
              (openPeriodicVelocityFourierMode solution t advecting)) *
          (Real.sqrt (velocityL1SquareMassOn
              (openPeriodicVelocityFourierMode solution t)
              (advectingLowHighVelocityBand highGrade)) *
            Real.sqrt (velocityL1SquareMassOn
              (openPeriodicVelocityFourierMode solution t)
              (advectingLowHighVelocityBand highGrade)))) := by
      simpa [mul_assoc] using hbase
    _ = (calibration.fullTurn * 3) *
        (rotatedLowVelocityGradeFactor solution t lowGrade *
          rotatedLocalizedHighBandPayment solution t highGrade) := by
      rw [hsqrt]
      unfold rotatedLowVelocityGradeFactor rotatedLocalizedHighBandPayment
        openPeriodicVelocityL1MassOn
      ring

/-- Fixed-grade separation for the actual third oriented population. -/
theorem finiteOpenAdvectingLowThirdGradeRatioPopulationAt_le_separatedFactors
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius lowGrade highGrade : ℕ) :
    finiteAdvectingLowThirdGradeRatioPopulationAt calibration radius
        lowGrade highGrade (openPeriodicVelocityFourierMode solution t) ≤
      (calibration.fullTurn * 3) *
        (rotatedLowVelocityGradeFactor solution t lowGrade *
          rotatedLocalizedHighBandPayment solution t highGrade) := by
  have hbase := finiteAdvectingLowThirdGradeRatioPopulationAt_le_cauchyBand
    calibration radius lowGrade highGrade
      (openPeriodicVelocityFourierMode solution t)
  rw [rotatedLowPinGradeCoefficient_eq_lowRadius] at hbase
  have hmass : 0 ≤ velocityL1SquareMassOn
      (openPeriodicVelocityFourierMode solution t)
      (advectingLowHighVelocityBand highGrade) :=
    velocityL1SquareMassOn_nonneg _ _
  have hsqrt :
      Real.sqrt (velocityL1SquareMassOn
          (openPeriodicVelocityFourierMode solution t)
          (advectingLowHighVelocityBand highGrade)) *
        Real.sqrt (velocityL1SquareMassOn
          (openPeriodicVelocityFourierMode solution t)
          (advectingLowHighVelocityBand highGrade)) =
      velocityL1SquareMassOn (openPeriodicVelocityFourierMode solution t)
        (advectingLowHighVelocityBand highGrade) := by
    rw [← sq, Real.sq_sqrt hmass]
  calc
    _ ≤ (rotatedLowPinStokesCoefficient highGrade *
          (calibration.fullTurn * 3) * (dyadicRadius lowGrade : ℝ)) *
        ((∑ advecting ∈ frequencyDyadicGradeSlice lowGrade,
            complexVectorL1
              (openPeriodicVelocityFourierMode solution t advecting)) *
          (Real.sqrt (velocityL1SquareMassOn
              (openPeriodicVelocityFourierMode solution t)
              (advectingLowHighVelocityBand highGrade)) *
            Real.sqrt (velocityL1SquareMassOn
              (openPeriodicVelocityFourierMode solution t)
              (advectingLowHighVelocityBand highGrade)))) := by
      simpa [mul_assoc] using hbase
    _ = (calibration.fullTurn * 3) *
        (rotatedLowVelocityGradeFactor solution t lowGrade *
          rotatedLocalizedHighBandPayment solution t highGrade) := by
      rw [hsqrt]
      unfold rotatedLowVelocityGradeFactor rotatedLocalizedHighBandPayment
        openPeriodicVelocityL1MassOn
      ring

/-! ## The low-grade family is summed before the high receiver -/

/-- Every finite low-grade population is paid by one explicit grade-zero factor and the complete
summable positive-grade service. -/
theorem sum_rotatedLowVelocityGradeFactor_le_service
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (grades : Finset ℕ) :
    (∑ grade ∈ grades, rotatedLowVelocityGradeFactor solution t grade) ≤
      rotatedLowVelocityGradeFactor solution t 0 +
        calibratedLowVelocityGradeService *
          (3 * ‖openVelocityWeightedH3State solution t‖) := by
  classical
  let positiveGrades := grades.erase 0
  let levels := positiveGrades.image (fun grade ↦ grade - 1)
  have hsplit :
      (∑ grade ∈ grades, rotatedLowVelocityGradeFactor solution t grade) ≤
        rotatedLowVelocityGradeFactor solution t 0 +
          ∑ grade ∈ positiveGrades,
            rotatedLowVelocityGradeFactor solution t grade := by
    by_cases hzero : 0 ∈ grades
    · rw [show positiveGrades = grades.erase 0 by rfl]
      rw [← Finset.sum_erase_add _ _ hzero]
      simp [add_comm]
    · have herase : positiveGrades = grades := by simp [positiveGrades, hzero]
      rw [herase]
      exact le_add_of_nonneg_left
        (rotatedLowVelocityGradeFactor_nonneg solution t 0)
  have hpositive (grade : ℕ) (hgrade : grade ∈ positiveGrades) : 0 < grade := by
    exact Nat.pos_of_ne_zero (Finset.mem_erase.mp hgrade).1
  have hfactor (grade : ℕ) (hgrade : grade ∈ positiveGrades) :
      rotatedLowVelocityGradeFactor solution t grade ≤
        calibratedLowVelocityGradeKernel (grade - 1) *
          (3 * ‖openVelocityWeightedH3State solution t‖) := by
    obtain ⟨level, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
      (ne_of_gt (hpositive grade hgrade))
    simpa [rotatedLowVelocityGradeFactor] using
      radius_mul_openPeriodicVelocityL1MassOn_gradeSucc_le_kernel
        solution t level
  have hinjective : Set.InjOn (fun grade : ℕ ↦ grade - 1)
      (positiveGrades : Set ℕ) := by
    intro left hleft right hright hequal
    have hleftPos := hpositive left hleft
    have hrightPos := hpositive right hright
    change left - 1 = right - 1 at hequal
    omega
  have hreindex :
      (∑ grade ∈ positiveGrades,
          calibratedLowVelocityGradeKernel (grade - 1)) =
        ∑ level ∈ levels, calibratedLowVelocityGradeKernel level := by
    exact (Finset.sum_image (f := calibratedLowVelocityGradeKernel) hinjective).symm
  calc
    (∑ grade ∈ grades, rotatedLowVelocityGradeFactor solution t grade) ≤
        rotatedLowVelocityGradeFactor solution t 0 +
          ∑ grade ∈ positiveGrades,
            rotatedLowVelocityGradeFactor solution t grade := hsplit
    _ ≤ rotatedLowVelocityGradeFactor solution t 0 +
        ∑ grade ∈ positiveGrades,
          calibratedLowVelocityGradeKernel (grade - 1) *
            (3 * ‖openVelocityWeightedH3State solution t‖) := by
      exact add_le_add le_rfl (Finset.sum_le_sum hfactor)
    _ = rotatedLowVelocityGradeFactor solution t 0 +
        (∑ grade ∈ positiveGrades,
          calibratedLowVelocityGradeKernel (grade - 1)) *
            (3 * ‖openVelocityWeightedH3State solution t‖) := by
      rw [Finset.sum_mul]
    _ = rotatedLowVelocityGradeFactor solution t 0 +
        (∑ level ∈ levels, calibratedLowVelocityGradeKernel level) *
          (3 * ‖openVelocityWeightedH3State solution t‖) := by rw [hreindex]
    _ ≤ rotatedLowVelocityGradeFactor solution t 0 +
        calibratedLowVelocityGradeService *
          (3 * ‖openVelocityWeightedH3State solution t‖) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_right
          (sum_calibratedLowVelocityGradeKernel_le_service levels)
          (mul_nonneg (by norm_num) (norm_nonneg _)))

/-! ## Bounded overlap of the adjacent high bands -/

/-- Native order-three velocity square mass on one finite frequency population. -/
def openVelocityH3SquareMassOn
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (population : Finset SpatialFrequency) : ℝ :=
  ∑ frequency ∈ population,
    periodicSobolevWeight 3 frequency *
      (∑ component : Fin 3,
        ‖openPeriodicVelocityFourierMode solution t frequency component‖ ^ 2)

/-- The dependent occurrence population retaining which exact current grade supplied a mode. -/
def rotatedCurrentGradeOccurrences (grades : Finset ℕ) :
    Finset (Σ _grade : ℕ, SpatialFrequency) :=
  grades.sigma frequencyDyadicGradeSlice

/-- The dependent occurrence population retaining which high grade supplied a predecessor mode. -/
def rotatedPredecessorGradeOccurrences (grades : Finset ℕ) :
    Finset (Σ _grade : ℕ, SpatialFrequency) :=
  grades.sigma frequencyDyadicPredecessorSlice

theorem rotatedCurrentGradeOccurrences_second_injective
    (grades : Finset ℕ) :
    Set.InjOn (fun occurrence : Σ _grade : ℕ, SpatialFrequency ↦ occurrence.2)
      (rotatedCurrentGradeOccurrences grades :
        Set (Σ _grade : ℕ, SpatialFrequency)) := by
  rintro ⟨leftGrade, leftFrequency⟩ hleft
    ⟨rightGrade, rightFrequency⟩ hright hequal
  change leftFrequency = rightFrequency at hequal
  have hleftMem := (Finset.mem_sigma.mp hleft).2
  have hrightMem := (Finset.mem_sigma.mp hright).2
  have hleftGrade : frequencyDyadicGrade leftFrequency = leftGrade := by
    simpa using
      (mem_frequencyDyadicGradeSlice_iff leftGrade leftFrequency).mp hleftMem
  have hrightGrade : frequencyDyadicGrade rightFrequency = rightGrade := by
    simpa using
      (mem_frequencyDyadicGradeSlice_iff rightGrade rightFrequency).mp hrightMem
  have hgrade : leftGrade = rightGrade := by
    rw [← hleftGrade, ← hrightGrade, hequal]
  cases hgrade
  cases hequal
  rfl

theorem rotatedPredecessorGradeOccurrences_second_injective
    (grades : Finset ℕ) :
    Set.InjOn (fun occurrence : Σ _grade : ℕ, SpatialFrequency ↦ occurrence.2)
      (rotatedPredecessorGradeOccurrences grades :
        Set (Σ _grade : ℕ, SpatialFrequency)) := by
  rintro ⟨leftGrade, leftFrequency⟩ hleft
    ⟨rightGrade, rightFrequency⟩ hright hequal
  change leftFrequency = rightFrequency at hequal
  have hleftMem := (Finset.mem_sigma.mp hleft).2
  have hrightMem := (Finset.mem_sigma.mp hright).2
  have hleftGrade : frequencyDyadicGrade leftFrequency + 1 = leftGrade := by
    simpa using
      (mem_frequencyDyadicPredecessorSlice_iff leftGrade leftFrequency).mp hleftMem
  have hrightGrade : frequencyDyadicGrade rightFrequency + 1 = rightGrade := by
    simpa using
      (mem_frequencyDyadicPredecessorSlice_iff rightGrade rightFrequency).mp hrightMem
  have hgrade : leftGrade = rightGrade := by
    rw [← hleftGrade, ← hrightGrade, hequal]
  cases hgrade
  cases hequal
  rfl

/-- Exact current-grade slices are disjoint across their retained grade occurrences, so their
finite native mass pays the global state once. -/
theorem sum_openVelocityH3SquareMassOn_currentGradeSlices_le_native
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (grades : Finset ℕ) :
    (∑ grade ∈ grades,
      openVelocityH3SquareMassOn solution t (frequencyDyadicGradeSlice grade)) ≤
      3 * ‖openVelocityWeightedH3State solution t‖ ^ 2 := by
  let occurrences := rotatedCurrentGradeOccurrences grades
  let population := occurrences.image
    (fun occurrence : Σ _grade : ℕ, SpatialFrequency ↦ occurrence.2)
  have hreindex :
      (∑ grade ∈ grades,
        openVelocityH3SquareMassOn solution t (frequencyDyadicGradeSlice grade)) =
      openVelocityH3SquareMassOn solution t population := by
    unfold openVelocityH3SquareMassOn population occurrences
      rotatedCurrentGradeOccurrences
    rw [Finset.sum_sigma']
    exact (Finset.sum_image
      (f := fun frequency ↦
        periodicSobolevWeight 3 frequency *
          (∑ component : Fin 3,
            ‖openPeriodicVelocityFourierMode solution t frequency component‖ ^ 2))
      (rotatedCurrentGradeOccurrences_second_injective grades)).symm
  rw [hreindex]
  exact finite_velocityH3SquareMass_le_native solution t population

/-- Exact predecessor slices are likewise disjoint across their retained high-grade occurrences. -/
theorem sum_openVelocityH3SquareMassOn_predecessorGradeSlices_le_native
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (grades : Finset ℕ) :
    (∑ grade ∈ grades,
      openVelocityH3SquareMassOn solution t
        (frequencyDyadicPredecessorSlice grade)) ≤
      3 * ‖openVelocityWeightedH3State solution t‖ ^ 2 := by
  let occurrences := rotatedPredecessorGradeOccurrences grades
  let population := occurrences.image
    (fun occurrence : Σ _grade : ℕ, SpatialFrequency ↦ occurrence.2)
  have hreindex :
      (∑ grade ∈ grades,
        openVelocityH3SquareMassOn solution t
          (frequencyDyadicPredecessorSlice grade)) =
      openVelocityH3SquareMassOn solution t population := by
    unfold openVelocityH3SquareMassOn population occurrences
      rotatedPredecessorGradeOccurrences
    rw [Finset.sum_sigma']
    exact (Finset.sum_image
      (f := fun frequency ↦
        periodicSobolevWeight 3 frequency *
          (∑ component : Fin 3,
            ‖openPeriodicVelocityFourierMode solution t frequency component‖ ^ 2))
      (rotatedPredecessorGradeOccurrences_second_injective grades)).symm
  rw [hreindex]
  exact finite_velocityH3SquareMass_le_native solution t population

theorem frequencyDyadicGradeSlice_disjoint_predecessorSlice (highGrade : ℕ) :
    Disjoint (frequencyDyadicGradeSlice highGrade)
      (frequencyDyadicPredecessorSlice highGrade) := by
  rw [Finset.disjoint_left]
  intro frequency hcurrent hpredecessor
  have hcurrentGrade :=
    (mem_frequencyDyadicGradeSlice_iff highGrade frequency).mp hcurrent
  have hpredecessorGrade :=
    (mem_frequencyDyadicPredecessorSlice_iff highGrade frequency).mp hpredecessor
  omega

theorem openVelocityH3SquareMassOn_highBand_eq_add
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (highGrade : ℕ) :
    openVelocityH3SquareMassOn solution t
        (advectingLowHighVelocityBand highGrade) =
      openVelocityH3SquareMassOn solution t
          (frequencyDyadicGradeSlice highGrade) +
        openVelocityH3SquareMassOn solution t
          (frequencyDyadicPredecessorSlice highGrade) := by
  unfold openVelocityH3SquareMassOn advectingLowHighVelocityBand
  exact Finset.sum_union
    (frequencyDyadicGradeSlice_disjoint_predecessorSlice highGrade)

/-- One localized high-grade payment is bounded before any global native norm is charged. -/
theorem rotatedLocalizedHighBandPayment_le_weightedBand
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (highGrade : ℕ) (hpositive : 0 < highGrade) :
    rotatedLocalizedHighBandPayment solution t highGrade ≤
      (3 * rotatedHighBandH3Calibration) *
        openVelocityH3SquareMassOn solution t
          (advectingLowHighVelocityBand highGrade) := by
  unfold rotatedLocalizedHighBandPayment velocityL1SquareMassOn
    openVelocityH3SquareMassOn
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro frequency hfrequency
  have hcoefficient := rotatedLowPinStokesCoefficient_le_highBandH3Weight
    highGrade hpositive frequency hfrequency
  have hl1 := complexVectorL1_sq_le_three_mul_sum_norm_sq
    (openPeriodicVelocityFourierMode solution t frequency)
  have hsum : 0 ≤ ∑ component : Fin 3,
      ‖openPeriodicVelocityFourierMode solution t frequency component‖ ^ 2 :=
    Finset.sum_nonneg fun component _hcomponent ↦ sq_nonneg _
  calc
    rotatedLowPinStokesCoefficient highGrade *
        complexVectorL1
          (openPeriodicVelocityFourierMode solution t frequency) ^ 2 ≤
      rotatedLowPinStokesCoefficient highGrade *
        (3 * ∑ component : Fin 3,
          ‖openPeriodicVelocityFourierMode solution t frequency component‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hl1
        (rotatedLowPinStokesCoefficient_nonneg highGrade)
    _ ≤ (rotatedHighBandH3Calibration * periodicSobolevWeight 3 frequency) *
        (3 * ∑ component : Fin 3,
          ‖openPeriodicVelocityFourierMode solution t frequency component‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hcoefficient
        (mul_nonneg (by norm_num) hsum)
    _ = (3 * rotatedHighBandH3Calibration) *
        (periodicSobolevWeight 3 frequency *
          (∑ component : Fin 3,
            ‖openPeriodicVelocityFourierMode solution t frequency component‖ ^ 2)) := by
      ring

/-- The actual current/predecessor band family overlaps at most twice.  Consequently all
localized completed-Stokes payments charge the native state only twice, independent of the
chosen finite grade population. -/
theorem sum_rotatedLocalizedHighBandPayment_le_boundedOverlap
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (grades : Finset ℕ)
    (hpositive : ∀ highGrade ∈ grades, 0 < highGrade) :
    (∑ highGrade ∈ grades,
      rotatedLocalizedHighBandPayment solution t highGrade) ≤
      18 * rotatedHighBandH3Calibration *
        ‖openVelocityWeightedH3State solution t‖ ^ 2 := by
  have hcurrent :=
    sum_openVelocityH3SquareMassOn_currentGradeSlices_le_native solution t grades
  have hpredecessor :=
    sum_openVelocityH3SquareMassOn_predecessorGradeSlices_le_native solution t grades
  have hcalibration : 0 ≤ 3 * rotatedHighBandH3Calibration :=
    mul_nonneg (by norm_num) rotatedHighBandH3Calibration_nonneg
  calc
    (∑ highGrade ∈ grades,
      rotatedLocalizedHighBandPayment solution t highGrade) ≤
      ∑ highGrade ∈ grades,
        (3 * rotatedHighBandH3Calibration) *
          openVelocityH3SquareMassOn solution t
            (advectingLowHighVelocityBand highGrade) := by
      exact Finset.sum_le_sum fun highGrade hhighGrade ↦
        rotatedLocalizedHighBandPayment_le_weightedBand solution t highGrade
          (hpositive highGrade hhighGrade)
    _ = (3 * rotatedHighBandH3Calibration) *
        (∑ highGrade ∈ grades,
          openVelocityH3SquareMassOn solution t
            (advectingLowHighVelocityBand highGrade)) := by
      rw [Finset.mul_sum]
    _ = (3 * rotatedHighBandH3Calibration) *
        (∑ highGrade ∈ grades,
          (openVelocityH3SquareMassOn solution t
              (frequencyDyadicGradeSlice highGrade) +
            openVelocityH3SquareMassOn solution t
              (frequencyDyadicPredecessorSlice highGrade))) := by
      congr 1
      apply Finset.sum_congr rfl
      intro highGrade _hhighGrade
      rw [openVelocityH3SquareMassOn_highBand_eq_add]
    _ = (3 * rotatedHighBandH3Calibration) *
        ((∑ highGrade ∈ grades,
          openVelocityH3SquareMassOn solution t
            (frequencyDyadicGradeSlice highGrade)) +
        (∑ highGrade ∈ grades,
          openVelocityH3SquareMassOn solution t
            (frequencyDyadicPredecessorSlice highGrade))) := by
      rw [Finset.sum_add_distrib]
    _ ≤ (3 * rotatedHighBandH3Calibration) *
        ((3 * ‖openVelocityWeightedH3State solution t‖ ^ 2) +
          (3 * ‖openVelocityWeightedH3State solution t‖ ^ 2)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hcurrent hpredecessor) hcalibration
    _ = 18 * rotatedHighBandH3Calibration *
        ‖openVelocityWeightedH3State solution t‖ ^ 2 := by ring

/-! ## Exact high-grade regrouping of the retained grade pairs -/

/-- The high grades which actually occur in the named finite ordered address population. -/
def finiteRotatedAdvectingHighGrades (radius : ℕ) : Finset ℕ :=
  (finitePhysicalH2AdvectingLowGradePairs radius).image Prod.snd

/-- The literal grade-pair fibre over one retained high grade.  No pair is added or collapsed. -/
def finiteRotatedAdvectingGradePairsAtHigh
    (radius highGrade : ℕ) : Finset (ℕ × ℕ) :=
  (finitePhysicalH2AdvectingLowGradePairs radius).filter fun grades ↦
    grades.2 = highGrade

/-- The low-grade receiver of one exact high-grade fibre.  Its image is collision-free because
the second coordinate has already been fixed. -/
def finiteRotatedAdvectingLowGradesAtHigh
    (radius highGrade : ℕ) : Finset ℕ :=
  (finiteRotatedAdvectingGradePairsAtHigh radius highGrade).image Prod.fst

theorem finiteRotatedAdvectingHighGrades_pos
    (radius : ℕ) {highGrade : ℕ}
    (hhigh : highGrade ∈ finiteRotatedAdvectingHighGrades radius) :
    0 < highGrade := by
  classical
  rcases Finset.mem_image.mp hhigh with ⟨grades, hgrades, rfl⟩
  exact lt_of_le_of_lt (Nat.zero_le grades.1)
    (finitePhysicalH2AdvectingLowGradePairs_low_lt_high radius grades hgrades)

/-- Exact finite disintegration by the second coordinate.  This is an equality of the original
ordered pair population, not an enclosing Cartesian-product estimate. -/
theorem sum_finiteRotatedAdvectingGradePairs_eq_highFibres
    (radius : ℕ) (face : ℕ × ℕ → ℝ) :
    (∑ grades ∈ finitePhysicalH2AdvectingLowGradePairs radius, face grades) =
      ∑ highGrade ∈ finiteRotatedAdvectingHighGrades radius,
        ∑ grades ∈ finiteRotatedAdvectingGradePairsAtHigh radius highGrade,
          face grades := by
  classical
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := finitePhysicalH2AdvectingLowGradePairs radius)
    (t := finiteRotatedAdvectingHighGrades radius)
    (g := Prod.snd)
    (fun grades hgrades ↦ Finset.mem_image_of_mem Prod.snd hgrades)
    face
  symm
  simpa [finiteRotatedAdvectingGradePairsAtHigh] using hfiber

theorem finiteRotatedAdvectingGradePairsAtHigh_fst_injective
    (radius highGrade : ℕ) :
    Set.InjOn Prod.fst
      (finiteRotatedAdvectingGradePairsAtHigh radius highGrade :
        Set (ℕ × ℕ)) := by
  intro left hleft right hright hfirst
  have hleftHigh := (Finset.mem_filter.mp hleft).2
  have hrightHigh := (Finset.mem_filter.mp hright).2
  apply Prod.ext hfirst
  exact hleftHigh.trans hrightHigh.symm

/-- The least-pin factors in one exact high fibre are summed without pair multiplicity loss and
then paid by the common calibrated low-grade service. -/
theorem sum_rotatedLowVelocityGradeFactor_on_highFibre_le_service
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius highGrade : ℕ) :
    (∑ grades ∈ finiteRotatedAdvectingGradePairsAtHigh radius highGrade,
      rotatedLowVelocityGradeFactor solution t grades.1) ≤
      rotatedLowVelocityGradeFactor solution t 0 +
        calibratedLowVelocityGradeService *
          (3 * ‖openVelocityWeightedH3State solution t‖) := by
  classical
  calc
    (∑ grades ∈ finiteRotatedAdvectingGradePairsAtHigh radius highGrade,
      rotatedLowVelocityGradeFactor solution t grades.1) =
        ∑ lowGrade ∈ finiteRotatedAdvectingLowGradesAtHigh radius highGrade,
          rotatedLowVelocityGradeFactor solution t lowGrade := by
      unfold finiteRotatedAdvectingLowGradesAtHigh
      exact (Finset.sum_image
        (f := rotatedLowVelocityGradeFactor solution t)
        (finiteRotatedAdvectingGradePairsAtHigh_fst_injective
          radius highGrade)).symm
    _ ≤ rotatedLowVelocityGradeFactor solution t 0 +
        calibratedLowVelocityGradeService *
          (3 * ‖openVelocityWeightedH3State solution t‖) :=
      sum_rotatedLowVelocityGradeFactor_le_service solution t
        (finiteRotatedAdvectingLowGradesAtHigh radius highGrade)

/-- Multiplicity-preserving high-fibre regrouping of the exact separated product. -/
theorem sum_rotatedGradePairProducts_eq_highFibres
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius : ℕ) :
    (∑ grades ∈ finitePhysicalH2AdvectingLowGradePairs radius,
      rotatedLowVelocityGradeFactor solution t grades.1 *
        rotatedLocalizedHighBandPayment solution t grades.2) =
      ∑ highGrade ∈ finiteRotatedAdvectingHighGrades radius,
        (∑ grades ∈ finiteRotatedAdvectingGradePairsAtHigh radius highGrade,
          rotatedLowVelocityGradeFactor solution t grades.1) *
            rotatedLocalizedHighBandPayment solution t highGrade := by
  rw [sum_finiteRotatedAdvectingGradePairs_eq_highFibres]
  apply Finset.sum_congr rfl
  intro highGrade _hhighGrade
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro grades hgrades
  rw [(Finset.mem_filter.mp hgrades).2]

/-- The complete exact grade-pair product pays the low family first and the adjacent high-band
family second.  Both services are independent of the finite cube radius. -/
theorem sum_rotatedGradePairProducts_le_cofinalUniform
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius : ℕ) :
    (∑ grades ∈ finitePhysicalH2AdvectingLowGradePairs radius,
      rotatedLowVelocityGradeFactor solution t grades.1 *
        rotatedLocalizedHighBandPayment solution t grades.2) ≤
      (rotatedLowVelocityGradeFactor solution t 0 +
        calibratedLowVelocityGradeService *
          (3 * ‖openVelocityWeightedH3State solution t‖)) *
        (18 * rotatedHighBandH3Calibration *
          ‖openVelocityWeightedH3State solution t‖ ^ 2) := by
  let lowService := rotatedLowVelocityGradeFactor solution t 0 +
    calibratedLowVelocityGradeService *
      (3 * ‖openVelocityWeightedH3State solution t‖)
  have hlowService : 0 ≤ lowService := by
    dsimp [lowService]
    exact add_nonneg
      (rotatedLowVelocityGradeFactor_nonneg solution t 0)
      (mul_nonneg calibratedLowVelocityGradeService_nonneg
        (mul_nonneg (by norm_num) (norm_nonneg _)))
  have hhigh := sum_rotatedLocalizedHighBandPayment_le_boundedOverlap
    solution t (finiteRotatedAdvectingHighGrades radius)
      (fun highGrade hhighGrade ↦
        finiteRotatedAdvectingHighGrades_pos radius hhighGrade)
  rw [sum_rotatedGradePairProducts_eq_highFibres]
  calc
    (∑ highGrade ∈ finiteRotatedAdvectingHighGrades radius,
      (∑ grades ∈ finiteRotatedAdvectingGradePairsAtHigh radius highGrade,
        rotatedLowVelocityGradeFactor solution t grades.1) *
          rotatedLocalizedHighBandPayment solution t highGrade) ≤
        ∑ highGrade ∈ finiteRotatedAdvectingHighGrades radius,
          lowService * rotatedLocalizedHighBandPayment solution t highGrade := by
      exact Finset.sum_le_sum fun highGrade _hhighGrade ↦
        mul_le_mul_of_nonneg_right
          (sum_rotatedLowVelocityGradeFactor_on_highFibre_le_service
            solution t radius highGrade)
          (rotatedLocalizedHighBandPayment_nonneg solution t highGrade)
    _ = lowService *
        (∑ highGrade ∈ finiteRotatedAdvectingHighGrades radius,
          rotatedLocalizedHighBandPayment solution t highGrade) := by
      rw [Finset.mul_sum]
    _ ≤ lowService *
        (18 * rotatedHighBandH3Calibration *
          ‖openVelocityWeightedH3State solution t‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hhigh hlowService

/-! ## Radius-independent bounds for the two named rotated populations -/

/-- Cofinal-uniform majorant for the actual second orientation.  Its exact face and multiplier
orientation remain those of the named second population. -/
theorem finiteOpenAdvectingLowSecondGradeRatioPopulation_le_cofinalUniform
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius : ℕ) :
    finiteAdvectingLowSecondGradeRatioPopulation calibration radius
        (openPeriodicVelocityFourierMode solution t) ≤
      (calibration.fullTurn * 3) *
        ((rotatedLowVelocityGradeFactor solution t 0 +
          calibratedLowVelocityGradeService *
            (3 * ‖openVelocityWeightedH3State solution t‖)) *
          (18 * rotatedHighBandH3Calibration *
            ‖openVelocityWeightedH3State solution t‖ ^ 2)) := by
  rw [finiteAdvectingLowSecondGradeRatioPopulation_eq_sum_gradeFibres]
  have hconstant : 0 ≤ calibration.fullTurn * 3 :=
    mul_nonneg (fullTurn_nonneg_from_arcRadial calibration) (by norm_num)
  calc
    (∑ grades ∈ finitePhysicalH2AdvectingLowGradePairs radius,
      finiteAdvectingLowSecondGradeRatioPopulationAt calibration radius
        grades.1 grades.2 (openPeriodicVelocityFourierMode solution t)) ≤
      ∑ grades ∈ finitePhysicalH2AdvectingLowGradePairs radius,
        (calibration.fullTurn * 3) *
          (rotatedLowVelocityGradeFactor solution t grades.1 *
            rotatedLocalizedHighBandPayment solution t grades.2) := by
      exact Finset.sum_le_sum fun grades _hgrades ↦
        finiteOpenAdvectingLowSecondGradeRatioPopulationAt_le_separatedFactors
          calibration solution t radius grades.1 grades.2
    _ = (calibration.fullTurn * 3) *
        (∑ grades ∈ finitePhysicalH2AdvectingLowGradePairs radius,
          rotatedLowVelocityGradeFactor solution t grades.1 *
            rotatedLocalizedHighBandPayment solution t grades.2) := by
      rw [Finset.mul_sum]
    _ ≤ (calibration.fullTurn * 3) *
        ((rotatedLowVelocityGradeFactor solution t 0 +
          calibratedLowVelocityGradeService *
            (3 * ‖openVelocityWeightedH3State solution t‖)) *
          (18 * rotatedHighBandH3Calibration *
            ‖openVelocityWeightedH3State solution t‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (sum_rotatedGradePairProducts_le_cofinalUniform solution t radius)
        hconstant

/-- Cofinal-uniform majorant for the actual third orientation, proved from its own fixed-grade
face theorem rather than an equality with the second orientation. -/
theorem finiteOpenAdvectingLowThirdGradeRatioPopulation_le_cofinalUniform
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius : ℕ) :
    finiteAdvectingLowThirdGradeRatioPopulation calibration radius
        (openPeriodicVelocityFourierMode solution t) ≤
      (calibration.fullTurn * 3) *
        ((rotatedLowVelocityGradeFactor solution t 0 +
          calibratedLowVelocityGradeService *
            (3 * ‖openVelocityWeightedH3State solution t‖)) *
          (18 * rotatedHighBandH3Calibration *
            ‖openVelocityWeightedH3State solution t‖ ^ 2)) := by
  rw [finiteAdvectingLowThirdGradeRatioPopulation_eq_sum_gradeFibres]
  have hconstant : 0 ≤ calibration.fullTurn * 3 :=
    mul_nonneg (fullTurn_nonneg_from_arcRadial calibration) (by norm_num)
  calc
    (∑ grades ∈ finitePhysicalH2AdvectingLowGradePairs radius,
      finiteAdvectingLowThirdGradeRatioPopulationAt calibration radius
        grades.1 grades.2 (openPeriodicVelocityFourierMode solution t)) ≤
      ∑ grades ∈ finitePhysicalH2AdvectingLowGradePairs radius,
        (calibration.fullTurn * 3) *
          (rotatedLowVelocityGradeFactor solution t grades.1 *
            rotatedLocalizedHighBandPayment solution t grades.2) := by
      exact Finset.sum_le_sum fun grades _hgrades ↦
        finiteOpenAdvectingLowThirdGradeRatioPopulationAt_le_separatedFactors
          calibration solution t radius grades.1 grades.2
    _ = (calibration.fullTurn * 3) *
        (∑ grades ∈ finitePhysicalH2AdvectingLowGradePairs radius,
          rotatedLowVelocityGradeFactor solution t grades.1 *
            rotatedLocalizedHighBandPayment solution t grades.2) := by
      rw [Finset.mul_sum]
    _ ≤ (calibration.fullTurn * 3) *
        ((rotatedLowVelocityGradeFactor solution t 0 +
          calibratedLowVelocityGradeService *
            (3 * ‖openVelocityWeightedH3State solution t‖)) *
          (18 * rotatedHighBandH3Calibration *
            ‖openVelocityWeightedH3State solution t‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (sum_rotatedGradePairProducts_le_cofinalUniform solution t radius)
        hconstant

section Audit

#print axioms sum_finiteRotatedAdvectingGradePairs_eq_highFibres
#print axioms sum_rotatedLocalizedHighBandPayment_le_boundedOverlap
#print axioms sum_rotatedGradePairProducts_le_cofinalUniform
#print axioms finiteOpenAdvectingLowSecondGradeRatioPopulation_le_cofinalUniform
#print axioms finiteOpenAdvectingLowThirdGradeRatioPopulation_le_cofinalUniform

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2RotatedMajorantCofinalBound
