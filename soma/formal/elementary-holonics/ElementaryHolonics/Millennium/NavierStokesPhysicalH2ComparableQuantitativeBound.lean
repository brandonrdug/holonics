import ElementaryHolonics.Millennium.NavierStokesPhysicalH2ComparableResidueBound
import ElementaryHolonics.Millennium.NavierStokesPhysicalH2PrimaryMajorantCofinalBound

/-!
# Quantitative velocity-chart bound for the physical H2 comparable residue

**[proved-derived; formal-checked]**  The exact maximum-grade comparable fibre is placed in the
two adjacent velocity bands already returned by its grade geometry.  At fixed grade the closed
triad relation is retained as an injective transported/receiver convolution row.  The completed
receiver multiplier and transported derivative are opened only after this address-preserving
placement.

The resulting coefficient is paid directly by the native velocity `H3` chart.  Grades zero and
one are boundary receivers; every grade `level + 2` is paid by a calibrated geometric kernel.
No vorticity identification, time integration, absorption, or continuation claim is made.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2ComparableQuantitativeBound

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCalibratedTriadicFaceBound
open Soma.Holonics.Millennium.NavierStokesCompleteDyadicTriadSectorPartition
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH2AdvectingLowGradeFaceMass
open Soma.Holonics.Millennium.NavierStokesH2LowVelocitySliceConversion
open Soma.Holonics.Millennium.NavierStokesH2TriadMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesH2VorticityShellDissipationBridge
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration
open Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ComparableResidueBound
open Soma.Holonics.Millennium.NavierStokesPhysicalH2CurlMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesPhysicalH2PrimaryMajorantCofinalBound
open Soma.Holonics.Millennium.NavierStokesPhysicalH2UniqueLowRotationPopulation
open Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityTriadJoin
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.Turn

/-! ## Complete fixed-grade comparable population -/

theorem comparableGradePinSlice_eq_frequencyDyadicHighBand (topGrade : ℕ) :
    comparableGradePinSlice topGrade = frequencyDyadicHighBand topGrade := rfl

theorem frequencyDyadicHighBand_subset_cube (topGrade : ℕ) :
    frequencyDyadicHighBand topGrade ⊆ frequencyCube (dyadicRadius topGrade) := by
  intro frequency hfrequency
  rcases Finset.mem_union.mp hfrequency with htop | hpredecessor
  · exact (frequencyDyadicGrade_le_iff_mem frequency topGrade).mp
      ((mem_frequencyDyadicGradeSlice_iff topGrade frequency).mp htop).le
  · have hgrade :=
      (mem_frequencyDyadicPredecessorSlice_iff topGrade frequency).mp hpredecessor
    exact (frequencyDyadicGrade_le_iff_mem frequency topGrade).mp (by omega)

/-- The finite complete band carrier for one comparable maximum grade. -/
def completePhysicalH2ComparableGradePopulation (topGrade : ℕ) :
    Finset CompleteTransportAddress := by
  classical
  exact ((frequencyDyadicHighBand topGrade).product
    (frequencyDyadicHighBand topGrade)).filter fun address ↦
      completeTransportReceiver address ∈ frequencyDyadicHighBand topGrade ∧
      ComparableSector (completeTransportTriad address) ∧
      comparableTopGrade (completeTransportTriad address) = topGrade

@[simp]
theorem mem_completePhysicalH2ComparableGradePopulation_iff
    (topGrade : ℕ) (address : CompleteTransportAddress) :
    address ∈ completePhysicalH2ComparableGradePopulation topGrade ↔
      address.1 ∈ frequencyDyadicHighBand topGrade ∧
      address.2 ∈ frequencyDyadicHighBand topGrade ∧
      completeTransportReceiver address ∈ frequencyDyadicHighBand topGrade ∧
      ComparableSector (completeTransportTriad address) ∧
      comparableTopGrade (completeTransportTriad address) = topGrade := by
  classical
  simp [completePhysicalH2ComparableGradePopulation, and_assoc]

theorem finitePhysicalH2ComparableGradeAperture_subset_complete
    (radius topGrade : ℕ) :
    (finitePhysicalH2ComparableAperture radius).filter
        (fun address ↦ comparableTopGrade (completeTransportTriad address) = topGrade) ⊆
      completePhysicalH2ComparableGradePopulation topGrade := by
  classical
  intro address haddress
  rcases Finset.mem_filter.mp haddress with ⟨hcomparableAperture, hgrade⟩
  have hsector := (Finset.mem_filter.mp hcomparableAperture).2
  have hpins := comparableSector_pin_mem_topSlice hsector
  rw [comparableGradePinSlice_eq_frequencyDyadicHighBand] at hpins
  rw [hgrade] at hpins
  exact (mem_completePhysicalH2ComparableGradePopulation_iff topGrade address).mpr
    ⟨hpins.1, hpins.2.1, hpins.2.2, hsector, hgrade⟩

/-- One transported-frequency row of the complete comparable band population. -/
def completePhysicalH2ComparableGradeRow
    (topGrade : ℕ) (advecting : SpatialFrequency) : Finset SpatialFrequency := by
  classical
  exact (frequencyDyadicHighBand topGrade).filter fun transported ↦
    (advecting, transported) ∈ completePhysicalH2ComparableGradePopulation topGrade

/-! ## Closed-triad velocity convolution -/

theorem sum_openPeriodicVelocityL1_mul_receiver_on_comparableGradeRow_le_squareMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (topGrade : ℕ) (advecting : SpatialFrequency) :
    (∑ transported ∈ completePhysicalH2ComparableGradeRow topGrade advecting,
      complexVectorL1 (openPeriodicVelocityFourierMode solution t transported) *
        complexVectorL1 (openPeriodicVelocityFourierMode solution t
          (completeTransportReceiver (advecting, transported)))) ≤
      openPeriodicVelocityL1SquareMassOn solution t
        (frequencyDyadicHighBand topGrade) := by
  let row := completePhysicalH2ComparableGradeRow topGrade advecting
  let band := frequencyDyadicHighBand topGrade
  let modeL1 : SpatialFrequency → ℝ := fun frequency ↦
    complexVectorL1 (openPeriodicVelocityFourierMode solution t frequency)
  let receiver : SpatialFrequency → SpatialFrequency := fun transported ↦
    completeTransportReceiver (advecting, transported)
  have hsource : row ⊆ band := by
    intro transported htransported
    exact (Finset.mem_filter.mp htransported).1
  have htarget : row.image receiver ⊆ band := by
    intro receiving hreceiving
    rcases Finset.mem_image.mp hreceiving with ⟨transported, htransported, rfl⟩
    exact (mem_completePhysicalH2ComparableGradePopulation_iff topGrade
      (advecting, transported)).mp (Finset.mem_filter.mp htransported).2 |>.2.2.1
  have hinjective : Set.InjOn receiver (row : Set SpatialFrequency) :=
    (completeTransportReceiver_fixed_advecting_injective advecting).injOn
  have hleft : (∑ transported ∈ row, modeL1 transported ^ 2) ≤
      ∑ frequency ∈ band, modeL1 frequency ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsource
      (fun frequency _hfrequency _hnot ↦ sq_nonneg (modeL1 frequency))
  have hright : (∑ transported ∈ row, modeL1 (receiver transported) ^ 2) ≤
      ∑ frequency ∈ band, modeL1 frequency ^ 2 := by
    calc
      (∑ transported ∈ row, modeL1 (receiver transported) ^ 2) =
          ∑ receiving ∈ row.image receiver, modeL1 receiving ^ 2 :=
        (Finset.sum_image (f := fun receiving ↦ modeL1 receiving ^ 2) hinjective).symm
      _ ≤ ∑ frequency ∈ band, modeL1 frequency ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg htarget
          (fun frequency _hfrequency _hnot ↦ sq_nonneg (modeL1 frequency))
  calc
    (∑ transported ∈ row, modeL1 transported * modeL1 (receiver transported)) ≤
        Real.sqrt (∑ transported ∈ row, modeL1 transported ^ 2) *
          Real.sqrt (∑ transported ∈ row, modeL1 (receiver transported) ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt row modeL1 (modeL1 ∘ receiver)
    _ ≤ Real.sqrt (∑ frequency ∈ band, modeL1 frequency ^ 2) *
        Real.sqrt (∑ frequency ∈ band, modeL1 frequency ^ 2) := by
      exact mul_le_mul (Real.sqrt_le_sqrt hleft) (Real.sqrt_le_sqrt hright)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = ∑ frequency ∈ band, modeL1 frequency ^ 2 := by
      rw [← sq, Real.sq_sqrt]
      exact Finset.sum_nonneg fun frequency _hfrequency ↦ sq_nonneg (modeL1 frequency)

theorem sum_completePhysicalH2ComparableGradePopulation_velocityProduct_eq_rows
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (topGrade : ℕ) :
    (∑ address ∈ completePhysicalH2ComparableGradePopulation topGrade,
      complexVectorL1 (openPeriodicVelocityFourierMode solution t address.1) *
        complexVectorL1 (openPeriodicVelocityFourierMode solution t address.2) *
        complexVectorL1 (openPeriodicVelocityFourierMode solution t
          (completeTransportReceiver address))) =
      ∑ advecting ∈ frequencyDyadicHighBand topGrade,
        complexVectorL1 (openPeriodicVelocityFourierMode solution t advecting) *
          ∑ transported ∈ completePhysicalH2ComparableGradeRow topGrade advecting,
            complexVectorL1 (openPeriodicVelocityFourierMode solution t transported) *
              complexVectorL1 (openPeriodicVelocityFourierMode solution t
                (completeTransportReceiver (advecting, transported))) := by
  classical
  unfold completePhysicalH2ComparableGradePopulation
    completePhysicalH2ComparableGradeRow
  rw [Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro advecting hadvecting
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro transported htransported
  split_ifs <;> simp_all [Finset.mem_filter, Finset.mem_product] <;> ring

theorem sum_completePhysicalH2ComparableGradePopulation_velocityProduct_le
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (topGrade : ℕ) :
    (∑ address ∈ completePhysicalH2ComparableGradePopulation topGrade,
      complexVectorL1 (openPeriodicVelocityFourierMode solution t address.1) *
        complexVectorL1 (openPeriodicVelocityFourierMode solution t address.2) *
        complexVectorL1 (openPeriodicVelocityFourierMode solution t
          (completeTransportReceiver address))) ≤
      openPeriodicVelocityL1MassOn solution t (frequencyDyadicHighBand topGrade) *
        openPeriodicVelocityL1SquareMassOn solution t
          (frequencyDyadicHighBand topGrade) := by
  rw [sum_completePhysicalH2ComparableGradePopulation_velocityProduct_eq_rows]
  unfold openPeriodicVelocityL1MassOn
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun advecting _hadvecting ↦
    mul_le_mul_of_nonneg_left
      (sum_openPeriodicVelocityL1_mul_receiver_on_comparableGradeRow_le_squareMass
        solution t topGrade advecting)
      (complexVectorL1_nonneg _)

/-! ## Pointwise completed receiver payment -/

def calibratedComparableReceiverGradeCoefficient
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (topGrade : ℕ) : ℝ :=
  (primitiveTorusStokesScale * (3 * (dyadicRadius topGrade : ℝ) ^ 2) *
      (1 + primitiveTorusStokesScale *
        (3 * (dyadicRadius topGrade : ℝ) ^ 2))) *
    (calibration.fullTurn * (3 * (dyadicRadius topGrade : ℝ)))

theorem norm_receiverWeightedPhysicalH2VelocityAdvectionFace_le_calibratedComparable
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (hcircle : calibration.IsEuclideanCircle)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) {topGrade : ℕ} (address : CompleteTransportAddress)
    (haddress : address ∈ completePhysicalH2ComparableGradePopulation topGrade) :
    ‖receiverWeightedPhysicalH2VelocityAdvectionFace
        (openPeriodicVelocityFourierMode solution t) address‖ ≤
      calibratedComparableReceiverGradeCoefficient calibration topGrade *
        (complexVectorL1 (openPeriodicVelocityFourierMode solution t address.1) *
          complexVectorL1 (openPeriodicVelocityFourierMode solution t address.2) *
          complexVectorL1 (openPeriodicVelocityFourierMode solution t
            (completeTransportReceiver address))) := by
  rcases (mem_completePhysicalH2ComparableGradePopulation_iff topGrade address).mp
    haddress with ⟨hadvectingBand, htransportedBand, hreceiverBand, _hsector, _hgrade⟩
  have htransportedCube := frequencyDyadicHighBand_subset_cube topGrade htransportedBand
  have hreceiverCube := frequencyDyadicHighBand_subset_cube topGrade hreceiverBand
  have hfrequency := frequencyL1_le_three_mul_cubeRadius htransportedCube
  have heigen :=
    torusStokesEigenvalue_le_primitiveScale_three_mul_cubeRadius_sq hreceiverCube
  let eigenBound : ℝ := primitiveTorusStokesScale *
    (3 * (dyadicRadius topGrade : ℝ) ^ 2)
  have heigenNonneg := torusStokesEigenvalue_nonneg (completeTransportReceiver address)
  have heigenBoundNonneg : 0 ≤ eigenBound := by
    exact mul_nonneg primitiveTorusStokesScale_pos.le
      (mul_nonneg (by norm_num) (sq_nonneg _))
  have hmultiplier :
      ‖physicalH2CurlEnergyMultiplier (completeTransportReceiver address)‖ ≤
        eigenBound * (1 + eigenBound) := by
    unfold physicalH2CurlEnergyMultiplier
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg heigenNonneg (by linarith))]
    exact mul_le_mul heigen (add_le_add le_rfl heigen)
      (by linarith) heigenBoundNonneg
  have hface := norm_triadicEnergyFace_le_of_calibration calibration hcircle
    address.1 address.2
    (openPeriodicVelocityFourierMode solution t address.1)
    (openPeriodicVelocityFourierMode solution t address.2)
    (openPeriodicVelocityFourierMode solution t
      (completeTransportReceiver address))
  have hturn := fullTurn_nonneg_from_arcRadial calibration
  have hfaceBoundNonneg : 0 ≤ calibration.fullTurn *
      frequencyL1 address.2 *
      complexVectorL1 (openPeriodicVelocityFourierMode solution t address.1) *
      complexVectorL1 (openPeriodicVelocityFourierMode solution t address.2) *
      complexVectorL1 (openPeriodicVelocityFourierMode solution t
        (completeTransportReceiver address)) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hturn (frequencyL1_nonneg address.2))
          (complexVectorL1_nonneg _))
        (complexVectorL1_nonneg _))
      (complexVectorL1_nonneg _)
  unfold receiverWeightedPhysicalH2VelocityAdvectionFace
    calibratedComparableReceiverGradeCoefficient
  rw [norm_mul]
  calc
    ‖physicalH2CurlEnergyMultiplier (completeTransportReceiver address)‖ *
        ‖triadicEnergyFace address.1 address.2
          (openPeriodicVelocityFourierMode solution t address.1)
          (openPeriodicVelocityFourierMode solution t address.2)
          (openPeriodicVelocityFourierMode solution t
            (completeTransportReceiver address))‖ ≤
      (eigenBound * (1 + eigenBound)) *
        (calibration.fullTurn * frequencyL1 address.2 *
          complexVectorL1 (openPeriodicVelocityFourierMode solution t address.1) *
          complexVectorL1 (openPeriodicVelocityFourierMode solution t address.2) *
          complexVectorL1 (openPeriodicVelocityFourierMode solution t
            (completeTransportReceiver address))) :=
      mul_le_mul hmultiplier hface (norm_nonneg _)
        (mul_nonneg heigenBoundNonneg (by linarith))
    _ ≤ (eigenBound * (1 + eigenBound)) *
        (calibration.fullTurn * (3 * (dyadicRadius topGrade : ℝ)) *
          complexVectorL1 (openPeriodicVelocityFourierMode solution t address.1) *
          complexVectorL1 (openPeriodicVelocityFourierMode solution t address.2) *
          complexVectorL1 (openPeriodicVelocityFourierMode solution t
            (completeTransportReceiver address))) := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg heigenBoundNonneg (by linarith))
      gcongr
      all_goals first | exact hfrequency | exact complexVectorL1_nonneg _
    _ = _ := by
      dsimp only [eigenBound]
      ring

/-! ## Fixed-grade finite current -/

theorem norm_finiteReceiverWeightedPhysicalH2ComparableGradeCurrent_le_bandProduct
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (hcircle : calibration.IsEuclideanCircle)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius topGrade : ℕ) :
    ‖finiteReceiverWeightedPhysicalH2ComparableGradeCurrent radius topGrade
        (openPeriodicVelocityFourierMode solution t)‖ ≤
      calibratedComparableReceiverGradeCoefficient calibration topGrade *
        (openPeriodicVelocityL1MassOn solution t (frequencyDyadicHighBand topGrade) *
          openPeriodicVelocityL1SquareMassOn solution t
            (frequencyDyadicHighBand topGrade)) := by
  unfold finiteReceiverWeightedPhysicalH2ComparableGradeCurrent
  let finiteGrade := (finitePhysicalH2ComparableAperture radius).filter
    (fun address ↦ comparableTopGrade (completeTransportTriad address) = topGrade)
  have hsubset := finitePhysicalH2ComparableGradeAperture_subset_complete radius topGrade
  have hcoefficient : 0 ≤ calibratedComparableReceiverGradeCoefficient calibration topGrade := by
    unfold calibratedComparableReceiverGradeCoefficient
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg primitiveTorusStokesScale_pos.le
          (mul_nonneg (by norm_num) (sq_nonneg _)))
        (add_nonneg (by norm_num)
          (mul_nonneg primitiveTorusStokesScale_pos.le
            (mul_nonneg (by norm_num) (sq_nonneg _)))))
      (mul_nonneg (fullTurn_nonneg_from_arcRadial calibration)
        (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
  calc
    ‖∑ address ∈ finiteGrade,
        receiverWeightedPhysicalH2VelocityAdvectionFace
          (openPeriodicVelocityFourierMode solution t) address‖ ≤
      ∑ address ∈ finiteGrade,
        ‖receiverWeightedPhysicalH2VelocityAdvectionFace
          (openPeriodicVelocityFourierMode solution t) address‖ := norm_sum_le _ _
    _ ≤ ∑ address ∈ completePhysicalH2ComparableGradePopulation topGrade,
        ‖receiverWeightedPhysicalH2VelocityAdvectionFace
          (openPeriodicVelocityFourierMode solution t) address‖ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun address _haddress _hnot ↦ norm_nonneg _)
    _ ≤ ∑ address ∈ completePhysicalH2ComparableGradePopulation topGrade,
        calibratedComparableReceiverGradeCoefficient calibration topGrade *
          (complexVectorL1 (openPeriodicVelocityFourierMode solution t address.1) *
            complexVectorL1 (openPeriodicVelocityFourierMode solution t address.2) *
            complexVectorL1 (openPeriodicVelocityFourierMode solution t
              (completeTransportReceiver address))) := by
      exact Finset.sum_le_sum fun address haddress ↦
        norm_receiverWeightedPhysicalH2VelocityAdvectionFace_le_calibratedComparable
          calibration hcircle solution t address haddress
    _ = calibratedComparableReceiverGradeCoefficient calibration topGrade *
        (∑ address ∈ completePhysicalH2ComparableGradePopulation topGrade,
          complexVectorL1 (openPeriodicVelocityFourierMode solution t address.1) *
            complexVectorL1 (openPeriodicVelocityFourierMode solution t address.2) *
            complexVectorL1 (openPeriodicVelocityFourierMode solution t
              (completeTransportReceiver address))) := by rw [Finset.mul_sum]
    _ ≤ calibratedComparableReceiverGradeCoefficient calibration topGrade *
        (openPeriodicVelocityL1MassOn solution t (frequencyDyadicHighBand topGrade) *
          openPeriodicVelocityL1SquareMassOn solution t
            (frequencyDyadicHighBand topGrade)) :=
      mul_le_mul_of_nonneg_left
        (sum_completePhysicalH2ComparableGradePopulation_velocityProduct_le
          solution t topGrade) hcoefficient

theorem norm_finiteOpenPhysicalH2ComparableGradeCurrent_le_two_bandProduct
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (hcircle : calibration.IsEuclideanCircle)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius topGrade : ℕ) :
    ‖finitePhysicalH2ComparableGradeCurrent radius topGrade
        (openPeriodicVelocityFourierMode solution t)‖ ≤
      2 * calibratedComparableReceiverGradeCoefficient calibration topGrade *
        (openPeriodicVelocityL1MassOn solution t (frequencyDyadicHighBand topGrade) *
          openPeriodicVelocityL1SquareMassOn solution t
            (frequencyDyadicHighBand topGrade)) := by
  have hexchange :=
    finiteReceiverWeightedPhysicalH2ComparableGradeCurrent_eq_neg_half_exchanged
      radius topGrade (openPeriodicVelocityFourierMode solution t)
      (fun frequency _hfrequency ↦
        openPeriodicVelocityFourierMode_divergenceFree solution t frequency)
  have hcurrent :
      finitePhysicalH2ComparableGradeCurrent radius topGrade
          (openPeriodicVelocityFourierMode solution t) =
        -(2 : ℂ) * finiteReceiverWeightedPhysicalH2ComparableGradeCurrent radius topGrade
          (openPeriodicVelocityFourierMode solution t) := by
    rw [hexchange]
    ring
  calc
    ‖finitePhysicalH2ComparableGradeCurrent radius topGrade
        (openPeriodicVelocityFourierMode solution t)‖ =
      2 * ‖finiteReceiverWeightedPhysicalH2ComparableGradeCurrent radius topGrade
        (openPeriodicVelocityFourierMode solution t)‖ := by
      rw [hcurrent, norm_mul]
      norm_num
    _ ≤ 2 * (calibratedComparableReceiverGradeCoefficient calibration topGrade *
        (openPeriodicVelocityL1MassOn solution t (frequencyDyadicHighBand topGrade) *
          openPeriodicVelocityL1SquareMassOn solution t
            (frequencyDyadicHighBand topGrade))) :=
      mul_le_mul_of_nonneg_left
        (norm_finiteReceiverWeightedPhysicalH2ComparableGradeCurrent_le_bandProduct
          calibration hcircle solution t radius topGrade) (by norm_num)
    _ = _ := by ring

/-! ## Native `H3` payment and summable calibrated grade kernel -/

/-- Every finite velocity population is paid in the native `H3` chart without identifying
velocity with vorticity. -/
theorem openPeriodicVelocityL1MassOn_le_embedding_nativeH3
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (population : Finset SpatialFrequency) :
    openPeriodicVelocityL1MassOn solution t population ≤
      periodicH3EmbeddingConstant *
        (3 * ‖openVelocityWeightedH3State solution t‖) := by
  have hcomponent (component : Fin 3) :
      (∑ frequency ∈ population,
          ‖openPeriodicVelocityFourierMode solution t frequency component‖) ≤
        coefficientL1Mass (openVelocityH3State solution t component) := by
    unfold coefficientL1Mass
    have hsummable :=
      summable_norm_openPeriodicVelocityFourierMode_component solution t component
    have hfinite := hsummable.sum_le_tsum population
      (fun frequency _hfrequency ↦ norm_nonneg _)
    simpa only [openVelocityH3State_mode_eq_openPeriodicVelocityFourierMode] using hfinite
  unfold openPeriodicVelocityL1MassOn complexVectorL1
  calc
    (∑ frequency ∈ population,
        (‖openPeriodicVelocityFourierMode solution t frequency 0‖ +
          ‖openPeriodicVelocityFourierMode solution t frequency 1‖ +
          ‖openPeriodicVelocityFourierMode solution t frequency 2‖)) =
      ∑ component : Fin 3, ∑ frequency ∈ population,
        ‖openPeriodicVelocityFourierMode solution t frequency component‖ := by
      simp only [Fin.sum_univ_three]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ ∑ component : Fin 3,
        coefficientL1Mass (openVelocityH3State solution t component) :=
      Finset.sum_le_sum fun component _hcomponent ↦ hcomponent component
    _ ≤ ∑ component : Fin 3,
        periodicH3EmbeddingConstant *
          periodicH3CoefficientNorm (openVelocityH3State solution t component) := by
      exact Finset.sum_le_sum fun component _hcomponent ↦
        coefficientL1Mass_le_periodicH3EmbeddingConstant_mul _
    _ = periodicH3EmbeddingConstant *
        (∑ component : Fin 3,
          periodicH3CoefficientNorm (openVelocityH3State solution t component)) := by
      rw [Finset.mul_sum]
    _ ≤ periodicH3EmbeddingConstant *
        (3 * ‖openVelocityWeightedH3State solution t‖) :=
      mul_le_mul_of_nonneg_left
        (sum_openVelocityH3CoefficientNorm_le_three_mul_native solution t)
        periodicH3EmbeddingConstant_nonneg

/-- The calibrated, radius-independent high-grade service for the comparable cubic residue. -/
def calibratedComparableVelocityGradeKernel
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (level : ℕ) : ℝ :=
  31104 * periodicH3EmbeddingConstant * calibration.fullTurn *
      (primitiveTorusStokesScale ^ 2)⁻¹ * (1 / 8 : ℝ) ^ level +
    1492992 * periodicH3EmbeddingConstant * calibration.fullTurn *
      primitiveTorusStokesScale⁻¹ * (1 / 2 : ℝ) ^ level

theorem calibratedComparableVelocityGradeKernel_nonneg
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι) (level : ℕ) :
    0 ≤ calibratedComparableVelocityGradeKernel calibration level := by
  unfold calibratedComparableVelocityGradeKernel
  have hturn := fullTurn_nonneg_from_arcRadial calibration
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) periodicH3EmbeddingConstant_nonneg) hturn)
        (inv_nonneg.mpr (pow_nonneg primitiveTorusStokesScale_pos.le 2)))
      (pow_nonneg (by norm_num) level))
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) periodicH3EmbeddingConstant_nonneg) hturn)
        (inv_nonneg.mpr primitiveTorusStokesScale_pos.le))
      (pow_nonneg (by norm_num) level))

theorem summable_calibratedComparableVelocityGradeKernel
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι) :
    Summable (calibratedComparableVelocityGradeKernel calibration) := by
  unfold calibratedComparableVelocityGradeKernel
  exact
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 8 : ℝ) < 1)).mul_left
      (31104 * periodicH3EmbeddingConstant * calibration.fullTurn *
        (primitiveTorusStokesScale ^ 2)⁻¹)).add
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)).mul_left
      (1492992 * periodicH3EmbeddingConstant * calibration.fullTurn *
        primitiveTorusStokesScale⁻¹))

theorem calibratedComparableVelocityGradeKernel_eq_raw
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι) (level : ℕ) :
    calibratedComparableVelocityGradeKernel calibration level =
      2 * calibratedComparableReceiverGradeCoefficient calibration (level + 2) *
        (periodicH3EmbeddingConstant * 3) *
        (9 * ((primitiveTorusStokesScale ^ 3 *
          (dyadicRadius level : ℝ) ^ 6)⁻¹)) := by
  have hscale : primitiveTorusStokesScale ≠ 0 :=
    primitiveTorusStokesScale_pos.ne'
  simp only [calibratedComparableVelocityGradeKernel,
    calibratedComparableReceiverGradeCoefficient, dyadicRadius, pow_add]
  push_cast
  field_simp [hscale]
  have height (n : ℕ) : (8 : ℝ) ^ n * (1 / 8 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  have htwo (n : ℕ) : (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  have hpowEight : ((2 : ℝ) ^ level) ^ 3 = (8 : ℝ) ^ level := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hpowFour : ((2 : ℝ) ^ level) ^ 2 = (4 : ℝ) ^ level := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rw [hpowEight]
  have ha : (1 / 8 : ℝ) ^ level * (8 : ℝ) ^ level = 1 := by
    simpa [mul_comm] using height level
  have hb : (1 / 2 : ℝ) ^ level * (8 : ℝ) ^ level = (4 : ℝ) ^ level := by
    have hpow : (8 : ℝ) ^ level = (2 : ℝ) ^ level * (4 : ℝ) ^ level := by
      rw [← mul_pow]
      norm_num
    rw [hpow]
    calc
      (1 / 2 : ℝ) ^ level * ((2 : ℝ) ^ level * (4 : ℝ) ^ level) =
          ((1 / 2 : ℝ) ^ level * (2 : ℝ) ^ level) * (4 : ℝ) ^ level := by ring
      _ = (4 : ℝ) ^ level := by
        rw [show (1 / 2 : ℝ) ^ level * (2 : ℝ) ^ level = 1 by
          simpa [mul_comm] using htwo level]
        ring
  calc
    periodicH3EmbeddingConstant * calibration.fullTurn *
        (31104 * (1 / 8 : ℝ) ^ level + primitiveTorusStokesScale * 1492992 *
          (1 / 2 : ℝ) ^ level) * (8 : ℝ) ^ level =
      31104 * periodicH3EmbeddingConstant * calibration.fullTurn *
          ((1 / 8 : ℝ) ^ level * (8 : ℝ) ^ level) +
        primitiveTorusStokesScale *
          (1492992 * periodicH3EmbeddingConstant * calibration.fullTurn *
            ((1 / 2 : ℝ) ^ level * (8 : ℝ) ^ level)) := by ring
    _ = 31104 * periodicH3EmbeddingConstant * calibration.fullTurn +
        primitiveTorusStokesScale *
          (1492992 * periodicH3EmbeddingConstant * calibration.fullTurn *
            (4 : ℝ) ^ level) := by rw [ha, hb]; ring
    _ = periodicH3EmbeddingConstant * calibration.fullTurn * 2 * 3 ^ 3 * 4 ^ 3 *
        (1 + primitiveTorusStokesScale * 3 *
          ((2 : ℝ) ^ level) ^ 2 * 4 ^ 2) * 9 := by
      rw [hpowFour]
      ring

theorem norm_finiteOpenPhysicalH2ComparableGradeCurrent_add_two_le_kernel
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (hcircle : calibration.IsEuclideanCircle)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius level : ℕ) :
    ‖finitePhysicalH2ComparableGradeCurrent radius (level + 2)
        (openPeriodicVelocityFourierMode solution t)‖ ≤
      calibratedComparableVelocityGradeKernel calibration level *
        ‖openVelocityWeightedH3State solution t‖ ^ 3 := by
  rw [calibratedComparableVelocityGradeKernel_eq_raw]
  have hbandL1 := openPeriodicVelocityL1MassOn_le_embedding_nativeH3 solution t
    (frequencyDyadicHighBand (level + 2))
  have hbandSquare :=
    openPeriodicVelocityL1SquareMassOn_highBand_add_two_le solution t level
  have hcoefficient : 0 ≤ 2 *
      calibratedComparableReceiverGradeCoefficient calibration (level + 2) := by
    unfold calibratedComparableReceiverGradeCoefficient
    have hturn := fullTurn_nonneg_from_arcRadial calibration
    exact mul_nonneg (by norm_num)
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg primitiveTorusStokesScale_pos.le
            (mul_nonneg (by norm_num) (sq_nonneg _)))
          (add_nonneg (by norm_num)
            (mul_nonneg primitiveTorusStokesScale_pos.le
              (mul_nonneg (by norm_num) (sq_nonneg _)))))
        (mul_nonneg hturn
          (mul_nonneg (by norm_num) (Nat.cast_nonneg _))))
  calc
    ‖finitePhysicalH2ComparableGradeCurrent radius (level + 2)
        (openPeriodicVelocityFourierMode solution t)‖ ≤
      2 * calibratedComparableReceiverGradeCoefficient calibration (level + 2) *
        (openPeriodicVelocityL1MassOn solution t
            (frequencyDyadicHighBand (level + 2)) *
          openPeriodicVelocityL1SquareMassOn solution t
            (frequencyDyadicHighBand (level + 2))) :=
      norm_finiteOpenPhysicalH2ComparableGradeCurrent_le_two_bandProduct
        calibration hcircle solution t radius (level + 2)
    _ ≤ 2 * calibratedComparableReceiverGradeCoefficient calibration (level + 2) *
        ((periodicH3EmbeddingConstant *
            (3 * ‖openVelocityWeightedH3State solution t‖)) *
          (9 * ((primitiveTorusStokesScale ^ 3 *
            (dyadicRadius level : ℝ) ^ 6)⁻¹) *
              ‖openVelocityWeightedH3State solution t‖ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hcoefficient
      exact mul_le_mul hbandL1 hbandSquare
        (openPeriodicVelocityL1SquareMassOn_nonneg solution t _)
        (mul_nonneg periodicH3EmbeddingConstant_nonneg
          (mul_nonneg (by norm_num) (norm_nonneg _)))
    _ = _ := by ring

/-! ## Grade-zero boundary and radius-independent complete estimate -/

/-- The unsharpened native `H3` service for one of the two boundary grades. -/
def calibratedComparableVelocityBoundaryGradeKernel
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (topGrade : ℕ) : ℝ :=
  2 * calibratedComparableReceiverGradeCoefficient calibration topGrade *
    (periodicH3EmbeddingConstant * 3) * 9

theorem calibratedComparableVelocityBoundaryGradeKernel_nonneg
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι) (topGrade : ℕ) :
    0 ≤ calibratedComparableVelocityBoundaryGradeKernel calibration topGrade := by
  unfold calibratedComparableVelocityBoundaryGradeKernel
    calibratedComparableReceiverGradeCoefficient
  have hturn := fullTurn_nonneg_from_arcRadial calibration
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg primitiveTorusStokesScale_pos.le
              (mul_nonneg (by norm_num) (sq_nonneg _)))
            (add_nonneg (by norm_num)
              (mul_nonneg primitiveTorusStokesScale_pos.le
                (mul_nonneg (by norm_num) (sq_nonneg _)))))
          (mul_nonneg hturn
            (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))))
      (mul_nonneg periodicH3EmbeddingConstant_nonneg (by norm_num)))
    (by norm_num)

def calibratedComparableVelocityBoundaryService
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι) : ℝ :=
  ∑ topGrade ∈ Finset.range 2,
    calibratedComparableVelocityBoundaryGradeKernel calibration topGrade

theorem calibratedComparableVelocityBoundaryService_nonneg
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι) :
    0 ≤ calibratedComparableVelocityBoundaryService calibration := by
  unfold calibratedComparableVelocityBoundaryService
  exact Finset.sum_nonneg fun topGrade _htopGrade ↦
    calibratedComparableVelocityBoundaryGradeKernel_nonneg calibration topGrade

theorem norm_finiteOpenPhysicalH2ComparableGradeCurrent_le_boundaryKernel
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (hcircle : calibration.IsEuclideanCircle)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius topGrade : ℕ) :
    ‖finitePhysicalH2ComparableGradeCurrent radius topGrade
        (openPeriodicVelocityFourierMode solution t)‖ ≤
      calibratedComparableVelocityBoundaryGradeKernel calibration topGrade *
        ‖openVelocityWeightedH3State solution t‖ ^ 3 := by
  have hbandL1 := openPeriodicVelocityL1MassOn_le_embedding_nativeH3 solution t
    (frequencyDyadicHighBand topGrade)
  have hbandSquare :=
    openPeriodicVelocityL1SquareMassOn_le_nine_mul_nativeH3_sq solution t
      (frequencyDyadicHighBand topGrade)
  have hcoefficient : 0 ≤ 2 *
      calibratedComparableReceiverGradeCoefficient calibration topGrade := by
    unfold calibratedComparableReceiverGradeCoefficient
    have hturn := fullTurn_nonneg_from_arcRadial calibration
    exact mul_nonneg (by norm_num)
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg primitiveTorusStokesScale_pos.le
            (mul_nonneg (by norm_num) (sq_nonneg _)))
          (add_nonneg (by norm_num)
            (mul_nonneg primitiveTorusStokesScale_pos.le
              (mul_nonneg (by norm_num) (sq_nonneg _)))))
        (mul_nonneg hturn
          (mul_nonneg (by norm_num) (Nat.cast_nonneg _))))
  calc
    ‖finitePhysicalH2ComparableGradeCurrent radius topGrade
        (openPeriodicVelocityFourierMode solution t)‖ ≤
      2 * calibratedComparableReceiverGradeCoefficient calibration topGrade *
        (openPeriodicVelocityL1MassOn solution t
            (frequencyDyadicHighBand topGrade) *
          openPeriodicVelocityL1SquareMassOn solution t
            (frequencyDyadicHighBand topGrade)) :=
      norm_finiteOpenPhysicalH2ComparableGradeCurrent_le_two_bandProduct
        calibration hcircle solution t radius topGrade
    _ ≤ 2 * calibratedComparableReceiverGradeCoefficient calibration topGrade *
        ((periodicH3EmbeddingConstant *
            (3 * ‖openVelocityWeightedH3State solution t‖)) *
          (9 * ‖openVelocityWeightedH3State solution t‖ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hcoefficient
      exact mul_le_mul hbandL1 hbandSquare
        (openPeriodicVelocityL1SquareMassOn_nonneg solution t _)
        (mul_nonneg periodicH3EmbeddingConstant_nonneg
          (mul_nonneg (by norm_num) (norm_nonneg _)))
    _ = calibratedComparableVelocityBoundaryGradeKernel calibration topGrade *
        ‖openVelocityWeightedH3State solution t‖ ^ 3 := by
      unfold calibratedComparableVelocityBoundaryGradeKernel
      ring

theorem sum_norm_finiteOpenPhysicalH2ComparableGradeCurrent_le_completeService
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (hcircle : calibration.IsEuclideanCircle)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius : ℕ) (grades : Finset ℕ) :
    (∑ topGrade ∈ grades,
      ‖finitePhysicalH2ComparableGradeCurrent radius topGrade
        (openPeriodicVelocityFourierMode solution t)‖) ≤
      (calibratedComparableVelocityBoundaryService calibration +
          ∑' level : ℕ, calibratedComparableVelocityGradeKernel calibration level) *
        ‖openVelocityWeightedH3State solution t‖ ^ 3 := by
  classical
  let boundaryGrades := grades.filter fun topGrade ↦ topGrade < 2
  let upperGrades := grades.filter fun topGrade ↦ 2 ≤ topGrade
  let levels := upperGrades.image fun topGrade ↦ topGrade - 2
  have hupper (topGrade : ℕ) (htopGrade : topGrade ∈ upperGrades) :
      2 ≤ topGrade := (Finset.mem_filter.mp htopGrade).2
  have hpartition :
      (∑ topGrade ∈ grades,
        ‖finitePhysicalH2ComparableGradeCurrent radius topGrade
          (openPeriodicVelocityFourierMode solution t)‖) =
      (∑ topGrade ∈ boundaryGrades,
        ‖finitePhysicalH2ComparableGradeCurrent radius topGrade
          (openPeriodicVelocityFourierMode solution t)‖) +
      ∑ topGrade ∈ upperGrades,
        ‖finitePhysicalH2ComparableGradeCurrent radius topGrade
          (openPeriodicVelocityFourierMode solution t)‖ := by
    have hsplit := Finset.sum_filter_add_sum_filter_not grades
      (fun topGrade ↦ topGrade < 2)
      (fun topGrade ↦
        ‖finitePhysicalH2ComparableGradeCurrent radius topGrade
          (openPeriodicVelocityFourierMode solution t)‖)
    have hupperEq : grades.filter (fun topGrade ↦ ¬ topGrade < 2) = upperGrades := by
      ext topGrade
      dsimp only [upperGrades]
      simp only [Finset.mem_filter]
      change (topGrade ∈ grades ∧ ¬ topGrade < 2) ↔
        (topGrade ∈ grades ∧ 2 ≤ topGrade)
      constructor
      · rintro ⟨hmem, hnot⟩
        exact ⟨hmem, by omega⟩
      · rintro ⟨hmem, hlower⟩
        exact ⟨hmem, by omega⟩
    exact hsplit.symm.trans (by rw [hupperEq])
  have hboundarySubset : boundaryGrades ⊆ Finset.range 2 := by
    intro topGrade htopGrade
    exact Finset.mem_range.mpr (Finset.mem_filter.mp htopGrade).2
  have hboundary :
      (∑ topGrade ∈ boundaryGrades,
        ‖finitePhysicalH2ComparableGradeCurrent radius topGrade
          (openPeriodicVelocityFourierMode solution t)‖) ≤
      calibratedComparableVelocityBoundaryService calibration *
        ‖openVelocityWeightedH3State solution t‖ ^ 3 := by
    calc
      (∑ topGrade ∈ boundaryGrades,
        ‖finitePhysicalH2ComparableGradeCurrent radius topGrade
          (openPeriodicVelocityFourierMode solution t)‖) ≤
        ∑ topGrade ∈ boundaryGrades,
          calibratedComparableVelocityBoundaryGradeKernel calibration topGrade *
            ‖openVelocityWeightedH3State solution t‖ ^ 3 := by
        exact Finset.sum_le_sum fun topGrade _htopGrade ↦
          norm_finiteOpenPhysicalH2ComparableGradeCurrent_le_boundaryKernel
            calibration hcircle solution t radius topGrade
      _ ≤ ∑ topGrade ∈ Finset.range 2,
          calibratedComparableVelocityBoundaryGradeKernel calibration topGrade *
            ‖openVelocityWeightedH3State solution t‖ ^ 3 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hboundarySubset
          (fun topGrade _htopGrade _hnot ↦ mul_nonneg
            (calibratedComparableVelocityBoundaryGradeKernel_nonneg calibration topGrade)
            (pow_nonneg (norm_nonneg _) 3))
      _ = calibratedComparableVelocityBoundaryService calibration *
          ‖openVelocityWeightedH3State solution t‖ ^ 3 := by
        unfold calibratedComparableVelocityBoundaryService
        rw [Finset.sum_mul]
  have hfactor (topGrade : ℕ) (htopGrade : topGrade ∈ upperGrades) :
      ‖finitePhysicalH2ComparableGradeCurrent radius topGrade
          (openPeriodicVelocityFourierMode solution t)‖ ≤
        calibratedComparableVelocityGradeKernel calibration (topGrade - 2) *
          ‖openVelocityWeightedH3State solution t‖ ^ 3 := by
    have htopLower := hupper topGrade htopGrade
    have hgradeEq : topGrade = (topGrade - 2) + 2 := by
      exact (Nat.sub_add_cancel htopLower).symm
    rw [hgradeEq]
    exact norm_finiteOpenPhysicalH2ComparableGradeCurrent_add_two_le_kernel
      calibration hcircle solution t radius (topGrade - 2)
  have hinjective : Set.InjOn (fun topGrade : ℕ ↦ topGrade - 2)
      (upperGrades : Set ℕ) := by
    intro left hleft right hright hequal
    have hleftLower := hupper left hleft
    have hrightLower := hupper right hright
    change left - 2 = right - 2 at hequal
    calc
      left = (left - 2) + 2 := (Nat.sub_add_cancel hleftLower).symm
      _ = (right - 2) + 2 := by rw [hequal]
      _ = right := Nat.sub_add_cancel hrightLower
  have hreindex :
      (∑ topGrade ∈ upperGrades,
        calibratedComparableVelocityGradeKernel calibration (topGrade - 2)) =
      ∑ level ∈ levels,
        calibratedComparableVelocityGradeKernel calibration level := by
    exact (Finset.sum_image
      (f := calibratedComparableVelocityGradeKernel calibration) hinjective).symm
  have hkernelService :
      (∑ level ∈ levels,
        calibratedComparableVelocityGradeKernel calibration level) ≤
      ∑' level : ℕ, calibratedComparableVelocityGradeKernel calibration level :=
    (summable_calibratedComparableVelocityGradeKernel calibration).sum_le_tsum levels
      (fun level _hlevel ↦
        calibratedComparableVelocityGradeKernel_nonneg calibration level)
  have hupperSum :
      (∑ topGrade ∈ upperGrades,
        ‖finitePhysicalH2ComparableGradeCurrent radius topGrade
          (openPeriodicVelocityFourierMode solution t)‖) ≤
      (∑' level : ℕ, calibratedComparableVelocityGradeKernel calibration level) *
        ‖openVelocityWeightedH3State solution t‖ ^ 3 := by
    calc
      (∑ topGrade ∈ upperGrades,
        ‖finitePhysicalH2ComparableGradeCurrent radius topGrade
          (openPeriodicVelocityFourierMode solution t)‖) ≤
        ∑ topGrade ∈ upperGrades,
          calibratedComparableVelocityGradeKernel calibration (topGrade - 2) *
            ‖openVelocityWeightedH3State solution t‖ ^ 3 :=
        Finset.sum_le_sum hfactor
      _ = (∑ topGrade ∈ upperGrades,
          calibratedComparableVelocityGradeKernel calibration (topGrade - 2)) *
          ‖openVelocityWeightedH3State solution t‖ ^ 3 := by
        rw [Finset.sum_mul]
      _ = (∑ level ∈ levels,
          calibratedComparableVelocityGradeKernel calibration level) *
          ‖openVelocityWeightedH3State solution t‖ ^ 3 := by rw [hreindex]
      _ ≤ (∑' level : ℕ,
          calibratedComparableVelocityGradeKernel calibration level) *
          ‖openVelocityWeightedH3State solution t‖ ^ 3 :=
        mul_le_mul_of_nonneg_right hkernelService (pow_nonneg (norm_nonneg _) 3)
  rw [hpartition]
  calc
    (∑ topGrade ∈ boundaryGrades,
        ‖finitePhysicalH2ComparableGradeCurrent radius topGrade
          (openPeriodicVelocityFourierMode solution t)‖) +
      ∑ topGrade ∈ upperGrades,
        ‖finitePhysicalH2ComparableGradeCurrent radius topGrade
          (openPeriodicVelocityFourierMode solution t)‖ ≤
      calibratedComparableVelocityBoundaryService calibration *
          ‖openVelocityWeightedH3State solution t‖ ^ 3 +
        (∑' level : ℕ,
          calibratedComparableVelocityGradeKernel calibration level) *
          ‖openVelocityWeightedH3State solution t‖ ^ 3 :=
      add_le_add hboundary hupperSum
    _ = _ := by ring

/-- Radius-independent complete quantitative bound for the actual finite signed comparable
current.  The endpoint is static and cubic in the native velocity `H3` norm. -/
theorem norm_finiteOpenPhysicalH2ComparableCurrent_le_completeVelocityH3Service
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (hcircle : calibration.IsEuclideanCircle)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius : ℕ) :
    ‖finitePhysicalH2ComparableCurrent radius
        (openPeriodicVelocityFourierMode solution t)‖ ≤
      (calibratedComparableVelocityBoundaryService calibration +
          ∑' level : ℕ, calibratedComparableVelocityGradeKernel calibration level) *
        ‖openVelocityWeightedH3State solution t‖ ^ 3 := by
  rw [finitePhysicalH2ComparableCurrent_eq_sum_gradeCurrent]
  calc
    ‖∑ topGrade ∈ finitePhysicalH2ComparableGradeSet radius,
        finitePhysicalH2ComparableGradeCurrent radius topGrade
          (openPeriodicVelocityFourierMode solution t)‖ ≤
      ∑ topGrade ∈ finitePhysicalH2ComparableGradeSet radius,
        ‖finitePhysicalH2ComparableGradeCurrent radius topGrade
          (openPeriodicVelocityFourierMode solution t)‖ := norm_sum_le _ _
    _ ≤ _ :=
      sum_norm_finiteOpenPhysicalH2ComparableGradeCurrent_le_completeService
        calibration hcircle solution t radius (finitePhysicalH2ComparableGradeSet radius)

#print axioms calibratedComparableVelocityGradeKernel_eq_raw
#print axioms summable_calibratedComparableVelocityGradeKernel
#print axioms norm_finiteOpenPhysicalH2ComparableGradeCurrent_add_two_le_kernel
#print axioms norm_finiteOpenPhysicalH2ComparableCurrent_le_completeVelocityH3Service

end Soma.Holonics.Millennium.NavierStokesPhysicalH2ComparableQuantitativeBound
