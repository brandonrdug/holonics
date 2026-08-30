import ElementaryHolonics.Millennium.NavierStokesPhysicalH2UniqueLowRotationPopulation
import ElementaryHolonics.Millennium.NavierStokesPhysicalH2VelocityCubeExhaustion
import ElementaryHolonics.Millennium.NavierStokesH2LowVelocityGradeKernel
import ElementaryHolonics.Millennium.NavierStokesH2VorticityShellDissipationBridge

/-!
# Cofinal primary-majorant bound for the physical H2 velocity swing

**[proved-derived; formal-checked]** The finite primary grade-ratio population is first
disintegrated over its exact `(lowGrade, highGrade)` fibres.  No address is quotiented: the
ordered transported pin and its reconstructed receiver remain distinct occurrences.  Each finite
fibre embeds in the already-founded complete fixed-grade population.  Its two high velocity pins
are then paid by the same injective receiver-convolution geometry used by the physical vorticity
face receiver, without identifying the velocity and vorticity charts.

The positive low grades are serviced by the calibrated summable `R⁻¹ᐟ²` kernel; grade zero is
retained separately.  The high receiver below is an actual finite square-mass face.  Subsequent
sections establish its calibrated `H3` service and the resulting radius-independent majorant.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2PrimaryMajorantCofinalBound

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCalibratedTriadicFaceBound
open Soma.Holonics.Millennium.NavierStokesCompleteDyadicTriadSectorPartition
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesH2AdvectingLowGradeFaceMass
open Soma.Holonics.Millennium.NavierStokesH2AdvectingLowGradeLeverBound
open Soma.Holonics.Millennium.NavierStokesH2LowVelocityGradeKernel
open Soma.Holonics.Millennium.NavierStokesH2LowVelocitySliceConversion
open Soma.Holonics.Millennium.NavierStokesH2TriadMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesH2VorticityShellDissipationBridge
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesHighFrequencyHeatDecay
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
open Soma.Holonics.Millennium.NavierStokesPhysicalH2CurlMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesPhysicalH2UniqueLowRotationPopulation
open Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityCubeExhaustion
open Soma.Holonics.Millennium.NavierStokesSharpDyadicH3Tail
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert
open Soma.Holonics.Millennium.Turn

/-! ## Exact finite grade fibres -/

/-- The grade-pair receiver of one advecting-low address. -/
def advectingLowGradePair (address : CompleteTransportAddress) : ℕ × ℕ :=
  (advectingGrade (completeTransportTriad address),
    advectingLowHighGrade (completeTransportTriad address))

/-- The exact grade pairs which actually occur in a finite physical aperture. -/
def finitePhysicalH2AdvectingLowGradePairs (radius : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (finitePhysicalH2AdvectingLowAperture radius).image advectingLowGradePair

/-- The literal finite `(lowGrade, highGrade)` fibre.  This filter retains address multiplicity. -/
def finitePhysicalH2AdvectingLowGradeFiber
    (radius lowGrade highGrade : ℕ) : Finset CompleteTransportAddress := by
  classical
  exact (finitePhysicalH2AdvectingLowAperture radius).filter fun address ↦
    advectingLowGradePair address = (lowGrade, highGrade)

@[simp]
theorem mem_finitePhysicalH2AdvectingLowGradeFiber_iff
    {radius lowGrade highGrade : ℕ} (address : CompleteTransportAddress) :
    address ∈ finitePhysicalH2AdvectingLowGradeFiber radius lowGrade highGrade ↔
      address ∈ finitePhysicalH2AdvectingLowAperture radius ∧
        advectingGrade (completeTransportTriad address) = lowGrade ∧
        advectingLowHighGrade (completeTransportTriad address) = highGrade := by
  classical
  simp [finitePhysicalH2AdvectingLowGradeFiber, advectingLowGradePair,
    Prod.ext_iff]

/-- Every finite fibre is a multiplicity-preserving subset of the existing complete fixed-grade
address population. -/
theorem finitePhysicalH2AdvectingLowGradeFiber_subset_complete
    (radius lowGrade highGrade : ℕ) :
    finitePhysicalH2AdvectingLowGradeFiber radius lowGrade highGrade ⊆
      completeAdvectingLowGradePopulation lowGrade highGrade := by
  classical
  intro address haddress
  rcases (mem_finitePhysicalH2AdvectingLowGradeFiber_iff address).mp haddress with
    ⟨haperture, hlow, hhigh⟩
  have hsector := (Finset.mem_filter.mp haperture).2
  exact (mem_completeAdvectingLowGradePopulation_iff address).mpr
    ⟨hsector, hlow, hhigh⟩

/-- Exact disintegration of the finite primary population over the grade pairs which occur. -/
theorem finiteAdvectingLowPrimaryGradeRatioPopulation_eq_gradeFibers
    (radius : ℕ) (velocityMode : SpatialFrequency → ComplexVector) :
    finiteAdvectingLowPrimaryGradeRatioPopulation radius velocityMode =
      ∑ grades ∈ finitePhysicalH2AdvectingLowGradePairs radius,
        ∑ address ∈ finitePhysicalH2AdvectingLowGradeFiber
            radius grades.1 grades.2,
          advectingLowPrimaryGradeRatioFace velocityMode address := by
  classical
  unfold finiteAdvectingLowPrimaryGradeRatioPopulation
    finitePhysicalH2AdvectingLowGradePairs
    finitePhysicalH2AdvectingLowGradeFiber
  rw [Finset.sum_fiberwise_of_maps_to (fun address haddress ↦
    Finset.mem_image_of_mem advectingLowGradePair haddress)]

/-! ## The actual high-band convolution receiver in the velocity chart -/

/-- The union of the exact high grade and its possible adjacent predecessor. -/
def frequencyDyadicHighBand (highGrade : ℕ) : Finset SpatialFrequency :=
  frequencyDyadicGradeSlice highGrade ∪
    frequencyDyadicPredecessorSlice highGrade

/-- Finite square mass of actual velocity coefficients on a declared frequency population. -/
def openPeriodicVelocityL1SquareMassOn
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (population : Finset SpatialFrequency) : ℝ :=
  ∑ frequency ∈ population,
    complexVectorL1 (openPeriodicVelocityFourierMode solution t frequency) ^ 2

theorem openPeriodicVelocityL1SquareMassOn_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (population : Finset SpatialFrequency) :
    0 ≤ openPeriodicVelocityL1SquareMassOn solution t population := by
  exact Finset.sum_nonneg fun _frequency _hfrequency ↦ sq_nonneg _

/-- The exact transported row of one complete fixed-grade population. -/
def completeAdvectingLowGradeRow
    (lowGrade highGrade : ℕ) (advecting : SpatialFrequency) :
    Finset SpatialFrequency := by
  classical
  exact (frequencyCube (dyadicRadius highGrade)).filter fun transported ↦
    (advecting, transported) ∈
      completeAdvectingLowGradePopulation lowGrade highGrade

theorem completeAdvectingLowGradePopulation_highPins_mem_highBand
    {lowGrade highGrade : ℕ} {address : CompleteTransportAddress}
    (haddress : address ∈
      completeAdvectingLowGradePopulation lowGrade highGrade) :
    address.2 ∈ frequencyDyadicHighBand highGrade ∧
      completeTransportReceiver address ∈ frequencyDyadicHighBand highGrade := by
  rcases completeAdvectingLowGradePopulation_highPattern_exhaustive haddress with
    hequal | htransported | hreceiver
  · constructor
    · exact Finset.mem_union_left _
        ((mem_frequencyDyadicGradeSlice_iff highGrade address.2).mpr hequal.1)
    · exact Finset.mem_union_left _
        ((mem_frequencyDyadicGradeSlice_iff highGrade _).mpr hequal.2)
  · constructor
    · exact Finset.mem_union_left _
        ((mem_frequencyDyadicGradeSlice_iff highGrade address.2).mpr htransported.1)
    · exact Finset.mem_union_right _
        ((mem_frequencyDyadicPredecessorSlice_iff highGrade _).mpr htransported.2)
  · constructor
    · exact Finset.mem_union_right _
        ((mem_frequencyDyadicPredecessorSlice_iff highGrade address.2).mpr hreceiver.2)
    · exact Finset.mem_union_left _
        ((mem_frequencyDyadicGradeSlice_iff highGrade _).mpr hreceiver.1)

/-- Injective receiver Cauchy on the actual velocity row. -/
theorem sum_openPeriodicVelocityL1_mul_receiver_on_gradeRow_le_squareMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (lowGrade highGrade : ℕ)
    (advecting : SpatialFrequency) :
    (∑ transported ∈ completeAdvectingLowGradeRow
        lowGrade highGrade advecting,
      complexVectorL1 (openPeriodicVelocityFourierMode solution t transported) *
        complexVectorL1 (openPeriodicVelocityFourierMode solution t
          (completeTransportReceiver (advecting, transported)))) ≤
      openPeriodicVelocityL1SquareMassOn solution t
        (frequencyDyadicHighBand highGrade) := by
  let row := completeAdvectingLowGradeRow lowGrade highGrade advecting
  let band := frequencyDyadicHighBand highGrade
  let modeL1 : SpatialFrequency → ℝ := fun frequency ↦
    complexVectorL1 (openPeriodicVelocityFourierMode solution t frequency)
  let receiver : SpatialFrequency → SpatialFrequency := fun transported ↦
    completeTransportReceiver (advecting, transported)
  have hsource : row ⊆ band := by
    intro transported htransported
    exact (completeAdvectingLowGradePopulation_highPins_mem_highBand
      (Finset.mem_filter.mp htransported).2).1
  have htarget : row.image receiver ⊆ band := by
    intro receiving hreceiving
    rcases Finset.mem_image.mp hreceiving with ⟨transported, htransported, rfl⟩
    exact (completeAdvectingLowGradePopulation_highPins_mem_highBand
      (Finset.mem_filter.mp htransported).2).2
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

theorem sum_completeAdvectingLowGradePopulation_velocityModeProduct_eq_rows
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (lowGrade highGrade : ℕ) :
    (∑ address ∈ completeAdvectingLowGradePopulation lowGrade highGrade,
      complexVectorL1 (openPeriodicVelocityFourierMode solution t address.1) *
        complexVectorL1 (openPeriodicVelocityFourierMode solution t address.2) *
        complexVectorL1 (openPeriodicVelocityFourierMode solution t
          (completeTransportReceiver address))) =
      ∑ advecting ∈ frequencyDyadicGradeSlice lowGrade,
        complexVectorL1 (openPeriodicVelocityFourierMode solution t advecting) *
          ∑ transported ∈ completeAdvectingLowGradeRow
              lowGrade highGrade advecting,
            complexVectorL1 (openPeriodicVelocityFourierMode solution t transported) *
              complexVectorL1 (openPeriodicVelocityFourierMode solution t
                (completeTransportReceiver (advecting, transported))) := by
  classical
  unfold completeAdvectingLowGradePopulation
  unfold completeAdvectingLowGradeRow
  unfold completeAdvectingLowGradePopulation
  rw [Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro advecting hadvecting
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro transported htransported
  split_ifs <;> simp_all [Finset.mem_filter, Finset.mem_product] <;> ring

/-- The exact fixed-grade velocity mode product is controlled by one low `L1` slice and the
injective high-band square mass. -/
theorem sum_completeAdvectingLowGradePopulation_velocityModeProduct_le
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (lowGrade highGrade : ℕ) :
    (∑ address ∈ completeAdvectingLowGradePopulation lowGrade highGrade,
      complexVectorL1 (openPeriodicVelocityFourierMode solution t address.1) *
        complexVectorL1 (openPeriodicVelocityFourierMode solution t address.2) *
        complexVectorL1 (openPeriodicVelocityFourierMode solution t
          (completeTransportReceiver address))) ≤
      openPeriodicVelocityL1MassOn solution t
          (frequencyDyadicGradeSlice lowGrade) *
        openPeriodicVelocityL1SquareMassOn solution t
          (frequencyDyadicHighBand highGrade) := by
  classical
  rw [sum_completeAdvectingLowGradePopulation_velocityModeProduct_eq_rows]
  unfold openPeriodicVelocityL1MassOn
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro advecting hadvecting
  exact mul_le_mul_of_nonneg_left
    (sum_openPeriodicVelocityL1_mul_receiver_on_gradeRow_le_squareMass
      solution t lowGrade highGrade advecting)
    (complexVectorL1_nonneg _)

/-! ## Fixed-grade primary face payment -/

/-- The calibrated coefficient left after the multiplier and triadic-face apertures are opened. -/
def calibratedPrimaryGradeCoefficient
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (lowGrade highGrade : ℕ) : ℝ :=
  (primitiveTorusStokesScale *
      (6 * dyadicGradeLengthRatio lowGrade highGrade *
        (dyadicRadius highGrade : ℝ) ^ 2) *
      (1 + primitiveTorusStokesScale *
        (6 * (dyadicRadius highGrade : ℝ) ^ 2))) *
    (calibration.fullTurn * (3 * (dyadicRadius highGrade : ℝ)))

theorem advectingLowPrimaryGradeRatioFace_nonneg
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) :
    0 ≤ advectingLowPrimaryGradeRatioFace velocityMode address := by
  unfold advectingLowPrimaryGradeRatioFace
  have hratio : 0 ≤ dyadicGradeLengthRatio
      (advectingGrade (completeTransportTriad address))
      (advectingLowHighGrade (completeTransportTriad address)) := by
    unfold dyadicGradeLengthRatio
    positivity
  have hmultiplier : 0 ≤
      1 + torusStokesEigenvalue address.2 +
        torusStokesEigenvalue (completeTransportReceiver address) := by
    linarith [torusStokesEigenvalue_nonneg address.2,
      torusStokesEigenvalue_nonneg (completeTransportReceiver address)]
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg primitiveTorusStokesScale_pos.le
        (mul_nonneg (mul_nonneg (by norm_num) hratio) (sq_nonneg _)))
      hmultiplier)
    (norm_nonneg _)

theorem advectingLowPrimaryGradeRatioFace_le_calibrated_velocityProduct
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (hcircle : calibration.IsEuclideanCircle)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) {lowGrade highGrade : ℕ}
    (address : CompleteTransportAddress)
    (haddress : address ∈
      completeAdvectingLowGradePopulation lowGrade highGrade) :
    advectingLowPrimaryGradeRatioFace
        (openPeriodicVelocityFourierMode solution t) address ≤
      calibratedPrimaryGradeCoefficient calibration lowGrade highGrade *
        (complexVectorL1 (openPeriodicVelocityFourierMode solution t address.1) *
          complexVectorL1 (openPeriodicVelocityFourierMode solution t address.2) *
          complexVectorL1 (openPeriodicVelocityFourierMode solution t
            (completeTransportReceiver address))) := by
  rcases (mem_completeAdvectingLowGradePopulation_iff address).mp haddress with
    ⟨hsector, hlow, hhigh⟩
  have htransported := transported_mem_advectingLowHighGradeCube
    (completeTransportTriad address)
  have hreceiver := receiver_mem_advectingLowHighGradeCube
    (completeTransportTriad address)
  have hhigh' : advectingLowHighGrade (completeTransportTriad address) = highGrade :=
    hhigh
  rw [hhigh'] at htransported hreceiver
  have hfrequency := frequencyL1_le_three_mul_cubeRadius htransported
  have hfrequency' : frequencyL1 address.2 ≤
      3 * (dyadicRadius highGrade : ℝ) := by
    simpa [completeTransportTriad] using hfrequency
  have htransportedSquare := frequencySquared_le_three_mul_cubeRadius_sq htransported
  have hreceiverSquare := frequencySquared_le_three_mul_cubeRadius_sq hreceiver
  have htransportedSquare' : frequencySquared address.2 ≤
      3 * (dyadicRadius highGrade : ℝ) ^ 2 := by
    simpa [completeTransportTriad] using htransportedSquare
  have hreceiverSquare' : frequencySquared (completeTransportReceiver address) ≤
      3 * (dyadicRadius highGrade : ℝ) ^ 2 := by
    simpa [completeTransportTriad] using hreceiverSquare
  have hmultiplier :
      1 + torusStokesEigenvalue address.2 +
          torusStokesEigenvalue (completeTransportReceiver address) ≤
        1 + primitiveTorusStokesScale *
          (6 * (dyadicRadius highGrade : ℝ) ^ 2) := by
    rw [torusStokesEigenvalue_eq_primitiveScale_mul_frequencySquared,
      torusStokesEigenvalue_eq_primitiveScale_mul_frequencySquared]
    nlinarith [primitiveTorusStokesScale_pos]
  have hface := norm_triadicEnergyFace_le_of_calibration calibration hcircle
    address.1 address.2
    (openPeriodicVelocityFourierMode solution t address.1)
    (openPeriodicVelocityFourierMode solution t address.2)
    (openPeriodicVelocityFourierMode solution t
      (completeTransportReceiver address))
  have hturn : 0 ≤ calibration.fullTurn :=
    fullTurn_nonneg_from_arcRadial calibration
  have hratio : 0 ≤ dyadicGradeLengthRatio lowGrade highGrade := by
    unfold dyadicGradeLengthRatio
    positivity
  have hlever : 0 ≤ primitiveTorusStokesScale *
      (6 * dyadicGradeLengthRatio lowGrade highGrade *
        (dyadicRadius highGrade : ℝ) ^ 2) := by
    exact mul_nonneg primitiveTorusStokesScale_pos.le
      (mul_nonneg (mul_nonneg (by norm_num) hratio) (sq_nonneg _))
  have hexplicitLever : 0 ≤
      primitiveTorusStokesScale *
        (6 * dyadicGradeLengthRatio lowGrade highGrade *
          (dyadicRadius highGrade : ℝ) ^ 2) *
        (1 + primitiveTorusStokesScale *
          (6 * (dyadicRadius highGrade : ℝ) ^ 2)) := by
    exact mul_nonneg hlever
      (add_nonneg (by norm_num)
        (mul_nonneg primitiveTorusStokesScale_pos.le
          (mul_nonneg (by norm_num) (sq_nonneg _))))
  unfold calibratedPrimaryGradeCoefficient
  simp only [advectingLowPrimaryGradeRatioFace, hlow, hhigh']
  calc
    (primitiveTorusStokesScale *
        (6 * dyadicGradeLengthRatio lowGrade highGrade *
          (dyadicRadius highGrade : ℝ) ^ 2) *
        (1 + torusStokesEigenvalue address.2 +
          torusStokesEigenvalue (completeTransportReceiver address))) *
        ‖triadicEnergyFace address.1 address.2
          (openPeriodicVelocityFourierMode solution t address.1)
          (openPeriodicVelocityFourierMode solution t address.2)
          (openPeriodicVelocityFourierMode solution t
            (completeTransportReceiver address))‖ ≤
      (primitiveTorusStokesScale *
        (6 * dyadicGradeLengthRatio lowGrade highGrade *
          (dyadicRadius highGrade : ℝ) ^ 2) *
        (1 + primitiveTorusStokesScale *
          (6 * (dyadicRadius highGrade : ℝ) ^ 2))) *
        (calibration.fullTurn * frequencyL1 address.2 *
          complexVectorL1 (openPeriodicVelocityFourierMode solution t address.1) *
          complexVectorL1 (openPeriodicVelocityFourierMode solution t address.2) *
          complexVectorL1 (openPeriodicVelocityFourierMode solution t
            (completeTransportReceiver address))) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hmultiplier hlever
      · exact hface
      · exact norm_nonneg _
      · exact hexplicitLever
    _ ≤ (primitiveTorusStokesScale *
        (6 * dyadicGradeLengthRatio lowGrade highGrade *
          (dyadicRadius highGrade : ℝ) ^ 2) *
        (1 + primitiveTorusStokesScale *
          (6 * (dyadicRadius highGrade : ℝ) ^ 2))) *
        (calibration.fullTurn * (3 * (dyadicRadius highGrade : ℝ)) *
          complexVectorL1 (openPeriodicVelocityFourierMode solution t address.1) *
          complexVectorL1 (openPeriodicVelocityFourierMode solution t address.2) *
          complexVectorL1 (openPeriodicVelocityFourierMode solution t
            (completeTransportReceiver address))) := by
      apply mul_le_mul_of_nonneg_left _ hexplicitLever
      gcongr
      all_goals first | exact hfrequency' | exact complexVectorL1_nonneg _
    _ = _ := by ring

/-- The finite physical fibre is paid by the already-founded complete fixed-grade convolution
receiver, with no address-cardinality factor. -/
theorem sum_finitePhysicalH2AdvectingLowGradeFiber_primary_le
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (hcircle : calibration.IsEuclideanCircle)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius lowGrade highGrade : ℕ) :
    (∑ address ∈ finitePhysicalH2AdvectingLowGradeFiber
        radius lowGrade highGrade,
      advectingLowPrimaryGradeRatioFace
        (openPeriodicVelocityFourierMode solution t) address) ≤
      calibratedPrimaryGradeCoefficient calibration lowGrade highGrade *
        (openPeriodicVelocityL1MassOn solution t
            (frequencyDyadicGradeSlice lowGrade) *
          openPeriodicVelocityL1SquareMassOn solution t
            (frequencyDyadicHighBand highGrade)) := by
  have hsubset := finitePhysicalH2AdvectingLowGradeFiber_subset_complete
    radius lowGrade highGrade
  have hnonneg : ∀ address ∈ completeAdvectingLowGradePopulation lowGrade highGrade,
      address ∉ finitePhysicalH2AdvectingLowGradeFiber radius lowGrade highGrade →
      0 ≤ advectingLowPrimaryGradeRatioFace
        (openPeriodicVelocityFourierMode solution t) address := by
    intro address _haddress _hnot
    exact advectingLowPrimaryGradeRatioFace_nonneg
      (openPeriodicVelocityFourierMode solution t) address
  calc
    (∑ address ∈ finitePhysicalH2AdvectingLowGradeFiber
        radius lowGrade highGrade,
      advectingLowPrimaryGradeRatioFace
        (openPeriodicVelocityFourierMode solution t) address) ≤
      ∑ address ∈ completeAdvectingLowGradePopulation lowGrade highGrade,
        advectingLowPrimaryGradeRatioFace
          (openPeriodicVelocityFourierMode solution t) address :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
    _ ≤ calibratedPrimaryGradeCoefficient calibration lowGrade highGrade *
        (∑ address ∈ completeAdvectingLowGradePopulation lowGrade highGrade,
          complexVectorL1 (openPeriodicVelocityFourierMode solution t address.1) *
            complexVectorL1 (openPeriodicVelocityFourierMode solution t address.2) *
            complexVectorL1 (openPeriodicVelocityFourierMode solution t
              (completeTransportReceiver address))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro address haddress
      exact advectingLowPrimaryGradeRatioFace_le_calibrated_velocityProduct
        calibration hcircle solution t address haddress
    _ ≤ calibratedPrimaryGradeCoefficient calibration lowGrade highGrade *
        (openPeriodicVelocityL1MassOn solution t
            (frequencyDyadicGradeSlice lowGrade) *
          openPeriodicVelocityL1SquareMassOn solution t
            (frequencyDyadicHighBand highGrade)) := by
      apply mul_le_mul_of_nonneg_left
      · exact sum_completeAdvectingLowGradePopulation_velocityModeProduct_le
          solution t lowGrade highGrade
      · unfold calibratedPrimaryGradeCoefficient
        have hturn := fullTurn_nonneg_from_arcRadial calibration
        have hratio : 0 ≤ dyadicGradeLengthRatio lowGrade highGrade := by
          unfold dyadicGradeLengthRatio
          positivity
        have hmultiplier : 0 ≤ 1 + primitiveTorusStokesScale *
            (6 * (dyadicRadius highGrade : ℝ) ^ 2) := by
          exact add_nonneg (by norm_num)
            (mul_nonneg primitiveTorusStokesScale_pos.le
              (mul_nonneg (by norm_num) (sq_nonneg _)))
        exact mul_nonneg (mul_nonneg
          (mul_nonneg primitiveTorusStokesScale_pos.le
            (mul_nonneg (mul_nonneg (by norm_num) hratio) (sq_nonneg _)))
          hmultiplier)
          (mul_nonneg hturn (mul_nonneg (by norm_num)
            (Nat.cast_nonneg (dyadicRadius highGrade))))

/-! ## Separated low and high grade factors -/

def physicalH2PrimaryLowGradeFactor
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (lowGrade : ℕ) : ℝ :=
  (dyadicRadius lowGrade : ℝ) *
    openPeriodicVelocityL1MassOn solution t
      (frequencyDyadicGradeSlice lowGrade)

def physicalH2PrimaryHighGradeFactor
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (highGrade : ℕ) : ℝ :=
  (dyadicRadius highGrade : ℝ) ^ 2 *
    (1 + primitiveTorusStokesScale *
      (6 * (dyadicRadius highGrade : ℝ) ^ 2)) *
    openPeriodicVelocityL1SquareMassOn solution t
      (frequencyDyadicHighBand highGrade)

theorem sum_finitePhysicalH2AdvectingLowGradeFiber_primary_le_separatedFactors
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (hcircle : calibration.IsEuclideanCircle)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius lowGrade highGrade : ℕ) :
    (∑ address ∈ finitePhysicalH2AdvectingLowGradeFiber
        radius lowGrade highGrade,
      advectingLowPrimaryGradeRatioFace
        (openPeriodicVelocityFourierMode solution t) address) ≤
      (18 * primitiveTorusStokesScale * calibration.fullTurn) *
        (physicalH2PrimaryLowGradeFactor solution t lowGrade *
          physicalH2PrimaryHighGradeFactor solution t highGrade) := by
  have hbase := sum_finitePhysicalH2AdvectingLowGradeFiber_primary_le
    calibration hcircle solution t radius lowGrade highGrade
  calc
    _ ≤ calibratedPrimaryGradeCoefficient calibration lowGrade highGrade *
        (openPeriodicVelocityL1MassOn solution t
            (frequencyDyadicGradeSlice lowGrade) *
          openPeriodicVelocityL1SquareMassOn solution t
            (frequencyDyadicHighBand highGrade)) := hbase
    _ = (18 * primitiveTorusStokesScale * calibration.fullTurn) *
        (physicalH2PrimaryLowGradeFactor solution t lowGrade *
          physicalH2PrimaryHighGradeFactor solution t highGrade) := by
      unfold calibratedPrimaryGradeCoefficient physicalH2PrimaryLowGradeFactor
        physicalH2PrimaryHighGradeFactor
      unfold dyadicGradeLengthRatio
      have hhighRadiusNat : dyadicRadius highGrade ≠ 0 := by
        simp [dyadicRadius]
      have hhighRadius : (dyadicRadius highGrade : ℝ) ≠ 0 := by
        exact_mod_cast hhighRadiusNat
      field_simp [hhighRadius]
      <;> ring

/-! ## Calibrated high-grade service -/

theorem openPeriodicVelocityL1SquareMassOn_le_nine_mul_nativeH3_sq
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (population : Finset SpatialFrequency) :
    openPeriodicVelocityL1SquareMassOn solution t population ≤
      9 * ‖openVelocityWeightedH3State solution t‖ ^ 2 := by
  have hpoint (frequency : SpatialFrequency) :
      complexVectorL1 (openPeriodicVelocityFourierMode solution t frequency) ^ 2 ≤
        3 * periodicSobolevWeight 3 frequency *
          (∑ component : Fin 3,
            ‖openPeriodicVelocityFourierMode solution t frequency component‖ ^ 2) := by
    have hl1 := complexVectorL1_sq_le_three_mul_sum_norm_sq
      (openPeriodicVelocityFourierMode solution t frequency)
    have hweight : 1 ≤ periodicSobolevWeight 3 frequency := by
      unfold periodicSobolevWeight
      have heigen := torusStokesEigenvalue_nonneg frequency
      nlinarith [sq_nonneg (1 + torusStokesEigenvalue frequency)]
    have hsum : 0 ≤ ∑ component : Fin 3,
        ‖openPeriodicVelocityFourierMode solution t frequency component‖ ^ 2 :=
      Finset.sum_nonneg fun component _hcomponent ↦ sq_nonneg _
    exact hl1.trans (by nlinarith)
  calc
    openPeriodicVelocityL1SquareMassOn solution t population ≤
      3 * ∑ frequency ∈ population,
        periodicSobolevWeight 3 frequency *
          (∑ component : Fin 3,
            ‖openPeriodicVelocityFourierMode solution t frequency component‖ ^ 2) := by
      unfold openPeriodicVelocityL1SquareMassOn
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun frequency _hfrequency ↦ by
        simpa [mul_assoc] using hpoint frequency
    _ ≤ 3 * (3 * ‖openVelocityWeightedH3State solution t‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (finite_velocityH3SquareMass_le_native solution t population) (by norm_num)
    _ = 9 * ‖openVelocityWeightedH3State solution t‖ ^ 2 := by ring

theorem calibratedH3Weight_le_of_not_mem_frequencyCube
    (radius : ℕ) (hradius : 0 < radius)
    {frequency : SpatialFrequency} (hfrequency : frequency ∉ frequencyCube radius) :
    (primitiveTorusStokesScale * (radius : ℝ) ^ 2) ^ 3 ≤
      periodicSobolevWeight 3 frequency := by
  have hradiusCast : 0 < (radius : ℝ) := by exact_mod_cast hradius
  have hfrequencyLower : (radius : ℝ) ^ 2 ≤ frequencySquared frequency := by
    have hstrong := radius_add_one_sq_le_frequencySquared_of_not_mem_frequencyCube
      radius hfrequency
    have hweak : (radius : ℝ) ^ 2 ≤ (radius + 1 : ℝ) ^ 2 := by
      apply pow_le_pow_left₀ (Nat.cast_nonneg radius)
      exact_mod_cast Nat.le_succ radius
    exact hweak.trans hstrong
  have heigen : primitiveTorusStokesScale * (radius : ℝ) ^ 2 ≤
      torusStokesEigenvalue frequency := by
    rw [torusStokesEigenvalue_eq_primitiveScale_mul_frequencySquared]
    exact mul_le_mul_of_nonneg_left hfrequencyLower primitiveTorusStokesScale_pos.le
  have hbase : primitiveTorusStokesScale * (radius : ℝ) ^ 2 ≤
      1 + torusStokesEigenvalue frequency := by linarith
  rw [periodicSobolevWeight]
  exact pow_le_pow_left₀
    (mul_nonneg primitiveTorusStokesScale_pos.le (sq_nonneg _)) hbase 3

theorem frequency_mem_highBand_add_two_not_mem_lowerCube
    (level : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∈ frequencyDyadicHighBand (level + 2)) :
    frequency ∉ frequencyCube (dyadicRadius level) := by
  intro hlower
  have hgradeLe :=
    (frequencyDyadicGrade_le_iff_mem frequency level).mpr hlower
  rcases Finset.mem_union.mp hfrequency with hhigh | hpredecessor
  · have hgrade := (mem_frequencyDyadicGradeSlice_iff (level + 2) frequency).mp hhigh
    omega
  · have hgrade :=
      (mem_frequencyDyadicPredecessorSlice_iff (level + 2) frequency).mp hpredecessor
    omega

theorem openPeriodicVelocityL1SquareMassOn_highBand_add_two_le
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (level : ℕ) :
    openPeriodicVelocityL1SquareMassOn solution t
        (frequencyDyadicHighBand (level + 2)) ≤
      9 * ((primitiveTorusStokesScale ^ 3 *
        (dyadicRadius level : ℝ) ^ 6)⁻¹) *
        ‖openVelocityWeightedH3State solution t‖ ^ 2 := by
  let aperture : ℝ :=
    (primitiveTorusStokesScale * (dyadicRadius level : ℝ) ^ 2) ^ 3
  have hradius : 0 < dyadicRadius level := by simp [dyadicRadius]
  have haperture : 0 < aperture := by
    dsimp only [aperture]
    exact pow_pos (mul_pos primitiveTorusStokesScale_pos
      (sq_pos_of_pos (by exact_mod_cast hradius))) 3
  have hpoint (frequency : SpatialFrequency)
      (hfrequency : frequency ∈ frequencyDyadicHighBand (level + 2)) :
      aperture *
          complexVectorL1 (openPeriodicVelocityFourierMode solution t frequency) ^ 2 ≤
        3 * periodicSobolevWeight 3 frequency *
          (∑ component : Fin 3,
            ‖openPeriodicVelocityFourierMode solution t frequency component‖ ^ 2) := by
    have hweight := calibratedH3Weight_le_of_not_mem_frequencyCube
      (dyadicRadius level) hradius
      (frequency_mem_highBand_add_two_not_mem_lowerCube level hfrequency)
    have hl1 := complexVectorL1_sq_le_three_mul_sum_norm_sq
      (openPeriodicVelocityFourierMode solution t frequency)
    have hl1Nonneg := complexVectorL1_nonneg
      (openPeriodicVelocityFourierMode solution t frequency)
    have hsum : 0 ≤ ∑ component : Fin 3,
        ‖openPeriodicVelocityFourierMode solution t frequency component‖ ^ 2 :=
      Finset.sum_nonneg fun component _hcomponent ↦ sq_nonneg _
    dsimp only [aperture]
    nlinarith
  have hpaid : aperture *
      openPeriodicVelocityL1SquareMassOn solution t
        (frequencyDyadicHighBand (level + 2)) ≤
      9 * ‖openVelocityWeightedH3State solution t‖ ^ 2 := by
    calc
      aperture * openPeriodicVelocityL1SquareMassOn solution t
          (frequencyDyadicHighBand (level + 2)) =
        ∑ frequency ∈ frequencyDyadicHighBand (level + 2),
          aperture * complexVectorL1
            (openPeriodicVelocityFourierMode solution t frequency) ^ 2 := by
          unfold openPeriodicVelocityL1SquareMassOn
          rw [Finset.mul_sum]
      _ ≤ 3 * ∑ frequency ∈ frequencyDyadicHighBand (level + 2),
          periodicSobolevWeight 3 frequency *
            (∑ component : Fin 3,
              ‖openPeriodicVelocityFourierMode solution t frequency component‖ ^ 2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun frequency hfrequency ↦ by
          simpa [mul_assoc] using hpoint frequency hfrequency
      _ ≤ 3 * (3 * ‖openVelocityWeightedH3State solution t‖ ^ 2) :=
        mul_le_mul_of_nonneg_left
          (finite_velocityH3SquareMass_le_native solution t
            (frequencyDyadicHighBand (level + 2))) (by norm_num)
      _ = 9 * ‖openVelocityWeightedH3State solution t‖ ^ 2 := by ring
  have hpaid' : openPeriodicVelocityL1SquareMassOn solution t
        (frequencyDyadicHighBand (level + 2)) * aperture ≤
      9 * ‖openVelocityWeightedH3State solution t‖ ^ 2 := by
    simpa [mul_comm] using hpaid
  have hdivision := (le_div_iff₀ haperture).2 hpaid'
  have hapertureFormula : aperture = primitiveTorusStokesScale ^ 3 *
      (dyadicRadius level : ℝ) ^ 6 := by
    dsimp only [aperture]
    ring
  rw [hapertureFormula] at hdivision
  calc
    openPeriodicVelocityL1SquareMassOn solution t
        (frequencyDyadicHighBand (level + 2)) ≤
      (9 * ‖openVelocityWeightedH3State solution t‖ ^ 2) /
        (primitiveTorusStokesScale ^ 3 *
          (dyadicRadius level : ℝ) ^ 6) := hdivision
    _ = 9 * ((primitiveTorusStokesScale ^ 3 *
        (dyadicRadius level : ℝ) ^ 6)⁻¹) *
          ‖openVelocityWeightedH3State solution t‖ ^ 2 := by ring

/-- Explicit summable high-grade kernel after the high square mass is paid by native `H3`. -/
def calibratedHighVelocityGradeKernel (level : ℕ) : ℝ :=
  144 * (primitiveTorusStokesScale ^ 3)⁻¹ * (1 / 16 : ℝ) ^ level +
    13824 * (primitiveTorusStokesScale ^ 2)⁻¹ * (1 / 4 : ℝ) ^ level

theorem calibratedHighVelocityGradeKernel_nonneg (level : ℕ) :
    0 ≤ calibratedHighVelocityGradeKernel level := by
  unfold calibratedHighVelocityGradeKernel
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (inv_nonneg.mpr (pow_nonneg primitiveTorusStokesScale_pos.le 3)))
      (pow_nonneg (by norm_num) level))
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (inv_nonneg.mpr (pow_nonneg primitiveTorusStokesScale_pos.le 2)))
      (pow_nonneg (by norm_num) level))

theorem summable_calibratedHighVelocityGradeKernel :
    Summable calibratedHighVelocityGradeKernel := by
  unfold calibratedHighVelocityGradeKernel
  exact ((summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 16 : ℝ) < 1)).mul_left
      (144 * (primitiveTorusStokesScale ^ 3)⁻¹)).add
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 4 : ℝ) < 1)).mul_left
      (13824 * (primitiveTorusStokesScale ^ 2)⁻¹))

theorem calibratedHighVelocityGradeKernel_eq_raw (level : ℕ) :
    calibratedHighVelocityGradeKernel level =
      9 * (dyadicRadius (level + 2) : ℝ) ^ 2 *
        (1 + primitiveTorusStokesScale *
          (6 * (dyadicRadius (level + 2) : ℝ) ^ 2)) *
        ((primitiveTorusStokesScale ^ 3 *
          (dyadicRadius level : ℝ) ^ 6)⁻¹) := by
  have hscale : primitiveTorusStokesScale ≠ 0 :=
    primitiveTorusStokesScale_pos.ne'
  simp only [calibratedHighVelocityGradeKernel, dyadicRadius, pow_add]
  push_cast
  field_simp [hscale]
  have hfour (n : ℕ) : (4 : ℝ) ^ n * (1 / 4 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  have hsixteen (n : ℕ) : (16 : ℝ) ^ n * (1 / 16 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  have hpowFour : ((2 : ℝ) ^ level) ^ 2 = (4 : ℝ) ^ level := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hpowSixteen : ((2 : ℝ) ^ level) ^ 4 = (16 : ℝ) ^ level := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rw [hpowFour, hpowSixteen]
  have ha : (1 / 16 : ℝ) ^ level * (16 : ℝ) ^ level = 1 := by
    simpa [mul_comm] using hsixteen level
  have hsixteenFour : (16 : ℝ) ^ level = ((4 : ℝ) ^ level) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hb : (1 / 4 : ℝ) ^ level * (16 : ℝ) ^ level = (4 : ℝ) ^ level := by
    rw [hsixteenFour]
    calc
      (1 / 4 : ℝ) ^ level * ((4 : ℝ) ^ level) ^ 2 =
          ((1 / 4 : ℝ) ^ level * (4 : ℝ) ^ level) * (4 : ℝ) ^ level := by ring
      _ = (4 : ℝ) ^ level := by
        rw [show (1 / 4 : ℝ) ^ level * (4 : ℝ) ^ level = 1 by
          simpa [mul_comm] using hfour level]
        ring
  calc
    (144 * (1 / 16 : ℝ) ^ level +
        primitiveTorusStokesScale * 13824 * (1 / 4 : ℝ) ^ level) *
        (16 : ℝ) ^ level =
      144 * ((1 / 16 : ℝ) ^ level * (16 : ℝ) ^ level) +
        primitiveTorusStokesScale * 13824 *
          ((1 / 4 : ℝ) ^ level * (16 : ℝ) ^ level) := by ring
    _ = 144 + primitiveTorusStokesScale * 13824 * (4 : ℝ) ^ level := by
      rw [ha, hb]
      ring
    _ = (4 : ℝ) ^ 2 * 9 *
        (1 + primitiveTorusStokesScale * (4 : ℝ) ^ 2 *
          (4 : ℝ) ^ level * 6) := by ring

theorem physicalH2PrimaryHighGradeFactor_add_two_le_kernel
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (level : ℕ) :
    physicalH2PrimaryHighGradeFactor solution t (level + 2) ≤
      calibratedHighVelocityGradeKernel level *
        ‖openVelocityWeightedH3State solution t‖ ^ 2 := by
  rw [calibratedHighVelocityGradeKernel_eq_raw]
  unfold physicalH2PrimaryHighGradeFactor
  have hcoefficient : 0 ≤ (dyadicRadius (level + 2) : ℝ) ^ 2 *
      (1 + primitiveTorusStokesScale *
        (6 * (dyadicRadius (level + 2) : ℝ) ^ 2)) :=
    mul_nonneg (sq_nonneg _)
    (add_nonneg (by norm_num)
      (mul_nonneg primitiveTorusStokesScale_pos.le
        (mul_nonneg (by norm_num) (sq_nonneg _))))
  have h := mul_le_mul_of_nonneg_left
    (openPeriodicVelocityL1SquareMassOn_highBand_add_two_le solution t level)
    hcoefficient
  calc
    _ ≤ ((dyadicRadius (level + 2) : ℝ) ^ 2 *
        (1 + primitiveTorusStokesScale *
          (6 * (dyadicRadius (level + 2) : ℝ) ^ 2))) *
        (9 * ((primitiveTorusStokesScale ^ 3 *
          (dyadicRadius level : ℝ) ^ 6)⁻¹) *
          ‖openVelocityWeightedH3State solution t‖ ^ 2) := h
    _ = _ := by ring

/-- Grade one is the unique high-grade boundary whose predecessor is grade zero. -/
def calibratedHighVelocityBoundaryKernel : ℝ :=
  9 * (dyadicRadius 1 : ℝ) ^ 2 *
    (1 + primitiveTorusStokesScale *
      (6 * (dyadicRadius 1 : ℝ) ^ 2))

theorem calibratedHighVelocityBoundaryKernel_nonneg :
    0 ≤ calibratedHighVelocityBoundaryKernel := by
  unfold calibratedHighVelocityBoundaryKernel
  exact mul_nonneg
    (mul_nonneg (by norm_num) (sq_nonneg _))
    (add_nonneg (by norm_num)
      (mul_nonneg primitiveTorusStokesScale_pos.le
        (mul_nonneg (by norm_num) (sq_nonneg _))))

theorem physicalH2PrimaryHighGradeFactor_one_le_boundary
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    physicalH2PrimaryHighGradeFactor solution t 1 ≤
      calibratedHighVelocityBoundaryKernel *
        ‖openVelocityWeightedH3State solution t‖ ^ 2 := by
  unfold physicalH2PrimaryHighGradeFactor calibratedHighVelocityBoundaryKernel
  have hcoefficient : 0 ≤ (dyadicRadius 1 : ℝ) ^ 2 *
      (1 + primitiveTorusStokesScale * (6 * (dyadicRadius 1 : ℝ) ^ 2)) :=
    mul_nonneg (sq_nonneg _)
      (add_nonneg (by norm_num)
        (mul_nonneg primitiveTorusStokesScale_pos.le
          (mul_nonneg (by norm_num) (sq_nonneg _))))
  have h := mul_le_mul_of_nonneg_left
    (openPeriodicVelocityL1SquareMassOn_le_nine_mul_nativeH3_sq
      solution t (frequencyDyadicHighBand 1)) hcoefficient
  calc
    _ ≤ ((dyadicRadius 1 : ℝ) ^ 2 *
        (1 + primitiveTorusStokesScale * (6 * (dyadicRadius 1 : ℝ) ^ 2))) *
        (9 * ‖openVelocityWeightedH3State solution t‖ ^ 2) := h
    _ = _ := by ring

def calibratedHighVelocityGradeService : ℝ :=
  calibratedHighVelocityBoundaryKernel +
    ∑' level : ℕ, calibratedHighVelocityGradeKernel level

theorem calibratedHighVelocityGradeService_nonneg :
    0 ≤ calibratedHighVelocityGradeService := by
  unfold calibratedHighVelocityGradeService
  exact add_nonneg calibratedHighVelocityBoundaryKernel_nonneg
    (tsum_nonneg calibratedHighVelocityGradeKernel_nonneg)

/-! ## Finite grade services -/

theorem physicalH2PrimaryLowGradeFactor_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (grade : ℕ) :
    0 ≤ physicalH2PrimaryLowGradeFactor solution t grade := by
  unfold physicalH2PrimaryLowGradeFactor
  exact mul_nonneg (Nat.cast_nonneg _)
    (openPeriodicVelocityL1MassOn_nonneg solution t _)

theorem physicalH2PrimaryHighGradeFactor_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (grade : ℕ) :
    0 ≤ physicalH2PrimaryHighGradeFactor solution t grade := by
  unfold physicalH2PrimaryHighGradeFactor
  exact mul_nonneg
    (mul_nonneg (sq_nonneg _)
      (add_nonneg (by norm_num)
        (mul_nonneg primitiveTorusStokesScale_pos.le
          (mul_nonneg (by norm_num) (sq_nonneg _)))))
    (openPeriodicVelocityL1SquareMassOn_nonneg solution t _)

theorem sum_physicalH2PrimaryLowGradeFactor_le_service
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (grades : Finset ℕ) :
    (∑ grade ∈ grades, physicalH2PrimaryLowGradeFactor solution t grade) ≤
      physicalH2PrimaryLowGradeFactor solution t 0 +
        calibratedLowVelocityGradeService *
          (3 * ‖openVelocityWeightedH3State solution t‖) := by
  classical
  let positiveGrades := grades.erase 0
  let levels := positiveGrades.image (fun grade ↦ grade - 1)
  have hsplit : (∑ grade ∈ grades,
      physicalH2PrimaryLowGradeFactor solution t grade) ≤
      physicalH2PrimaryLowGradeFactor solution t 0 +
        ∑ grade ∈ positiveGrades,
          physicalH2PrimaryLowGradeFactor solution t grade := by
    by_cases hzero : 0 ∈ grades
    · calc
        (∑ grade ∈ grades,
            physicalH2PrimaryLowGradeFactor solution t grade) ≤
          (∑ grade ∈ grades.erase 0,
              physicalH2PrimaryLowGradeFactor solution t grade) +
            physicalH2PrimaryLowGradeFactor solution t 0 :=
          (Finset.sum_erase_add _ _ hzero).symm.le
        _ ≤ physicalH2PrimaryLowGradeFactor solution t 0 +
            ∑ grade ∈ positiveGrades,
              physicalH2PrimaryLowGradeFactor solution t grade := by
          change (∑ grade ∈ grades.erase 0,
              physicalH2PrimaryLowGradeFactor solution t grade) +
              physicalH2PrimaryLowGradeFactor solution t 0 ≤
            physicalH2PrimaryLowGradeFactor solution t 0 +
              ∑ grade ∈ grades.erase 0,
                physicalH2PrimaryLowGradeFactor solution t grade
          exact (add_comm _ _).le
    · have herase : positiveGrades = grades := by
        simp [positiveGrades, hzero]
      rw [herase]
      exact le_add_of_nonneg_left
        (physicalH2PrimaryLowGradeFactor_nonneg solution t 0)
  have hpositive (grade : ℕ) (hgrade : grade ∈ positiveGrades) : 0 < grade := by
    have hne : grade ≠ 0 := by
      exact (Finset.mem_erase.mp hgrade).1
    omega
  have hfactor (grade : ℕ) (hgrade : grade ∈ positiveGrades) :
      physicalH2PrimaryLowGradeFactor solution t grade ≤
        calibratedLowVelocityGradeKernel (grade - 1) *
          (3 * ‖openVelocityWeightedH3State solution t‖) := by
    obtain ⟨level, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
      (ne_of_gt (hpositive grade hgrade))
    simpa [physicalH2PrimaryLowGradeFactor] using
      radius_mul_openPeriodicVelocityL1MassOn_gradeSucc_le_kernel solution t level
  have hinjective : Set.InjOn (fun grade : ℕ ↦ grade - 1)
      (positiveGrades : Set ℕ) := by
    intro left hleft right hright hequal
    have hleftPos := hpositive left hleft
    have hrightPos := hpositive right hright
    change left - 1 = right - 1 at hequal
    calc
      left = (left - 1) + 1 := (Nat.sub_add_cancel hleftPos).symm
      _ = (right - 1) + 1 := by rw [hequal]
      _ = right := Nat.sub_add_cancel hrightPos
  have hreindex :
      (∑ grade ∈ positiveGrades,
        calibratedLowVelocityGradeKernel (grade - 1)) =
      ∑ level ∈ levels, calibratedLowVelocityGradeKernel level := by
    exact (Finset.sum_image (f := calibratedLowVelocityGradeKernel) hinjective).symm
  calc
    (∑ grade ∈ grades, physicalH2PrimaryLowGradeFactor solution t grade) ≤
      physicalH2PrimaryLowGradeFactor solution t 0 +
        ∑ grade ∈ positiveGrades,
          physicalH2PrimaryLowGradeFactor solution t grade := hsplit
    _ ≤ physicalH2PrimaryLowGradeFactor solution t 0 +
        ∑ grade ∈ positiveGrades,
          calibratedLowVelocityGradeKernel (grade - 1) *
            (3 * ‖openVelocityWeightedH3State solution t‖) := by
      exact add_le_add le_rfl (Finset.sum_le_sum hfactor)
    _ = physicalH2PrimaryLowGradeFactor solution t 0 +
        (∑ grade ∈ positiveGrades,
          calibratedLowVelocityGradeKernel (grade - 1)) *
            (3 * ‖openVelocityWeightedH3State solution t‖) := by
      rw [Finset.sum_mul]
    _ = physicalH2PrimaryLowGradeFactor solution t 0 +
        (∑ level ∈ levels, calibratedLowVelocityGradeKernel level) *
          (3 * ‖openVelocityWeightedH3State solution t‖) := by rw [hreindex]
    _ ≤ physicalH2PrimaryLowGradeFactor solution t 0 +
        calibratedLowVelocityGradeService *
          (3 * ‖openVelocityWeightedH3State solution t‖) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (sum_calibratedLowVelocityGradeKernel_le_service levels)
        (mul_nonneg (by norm_num) (norm_nonneg _)))

theorem sum_physicalH2PrimaryHighGradeFactor_le_service
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (grades : Finset ℕ)
    (hpositive : ∀ grade ∈ grades, 0 < grade) :
    (∑ grade ∈ grades, physicalH2PrimaryHighGradeFactor solution t grade) ≤
      calibratedHighVelocityGradeService *
        ‖openVelocityWeightedH3State solution t‖ ^ 2 := by
  classical
  let upperGrades := grades.erase 1
  let levels := upperGrades.image (fun grade ↦ grade - 2)
  have hsplit : (∑ grade ∈ grades,
      physicalH2PrimaryHighGradeFactor solution t grade) ≤
      physicalH2PrimaryHighGradeFactor solution t 1 +
        ∑ grade ∈ upperGrades,
          physicalH2PrimaryHighGradeFactor solution t grade := by
    by_cases hone : 1 ∈ grades
    · calc
        (∑ grade ∈ grades,
            physicalH2PrimaryHighGradeFactor solution t grade) ≤
          (∑ grade ∈ grades.erase 1,
              physicalH2PrimaryHighGradeFactor solution t grade) +
            physicalH2PrimaryHighGradeFactor solution t 1 :=
          (Finset.sum_erase_add _ _ hone).symm.le
        _ ≤ physicalH2PrimaryHighGradeFactor solution t 1 +
            ∑ grade ∈ upperGrades,
              physicalH2PrimaryHighGradeFactor solution t grade := by
          change (∑ grade ∈ grades.erase 1,
              physicalH2PrimaryHighGradeFactor solution t grade) +
              physicalH2PrimaryHighGradeFactor solution t 1 ≤
            physicalH2PrimaryHighGradeFactor solution t 1 +
              ∑ grade ∈ grades.erase 1,
                physicalH2PrimaryHighGradeFactor solution t grade
          exact (add_comm _ _).le
    · have herase : upperGrades = grades := by simp [upperGrades, hone]
      rw [herase]
      exact le_add_of_nonneg_left
        (physicalH2PrimaryHighGradeFactor_nonneg solution t 1)
  have hupper (grade : ℕ) (hgrade : grade ∈ upperGrades) : 2 ≤ grade := by
    have hmem := (Finset.mem_erase.mp hgrade)
    have hpos := hpositive grade hmem.2
    have hne : grade ≠ 1 := hmem.1
    exact Nat.succ_le_iff.mpr (lt_of_le_of_ne hpos (Ne.symm hne))
  have hfactor (grade : ℕ) (hgrade : grade ∈ upperGrades) :
      physicalH2PrimaryHighGradeFactor solution t grade ≤
        calibratedHighVelocityGradeKernel (grade - 2) *
          ‖openVelocityWeightedH3State solution t‖ ^ 2 := by
    have hlower := hupper grade hgrade
    have hgradeEq : grade = (grade - 2) + 2 := by omega
    rw [hgradeEq]
    exact physicalH2PrimaryHighGradeFactor_add_two_le_kernel
      solution t (grade - 2)
  have hinjective : Set.InjOn (fun grade : ℕ ↦ grade - 2)
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
      (∑ grade ∈ upperGrades,
        calibratedHighVelocityGradeKernel (grade - 2)) =
      ∑ level ∈ levels, calibratedHighVelocityGradeKernel level := by
    exact (Finset.sum_image (f := calibratedHighVelocityGradeKernel) hinjective).symm
  have hkernelService : (∑ level ∈ levels,
      calibratedHighVelocityGradeKernel level) ≤
      ∑' level : ℕ, calibratedHighVelocityGradeKernel level :=
    summable_calibratedHighVelocityGradeKernel.sum_le_tsum levels
      (fun level _hlevel ↦ calibratedHighVelocityGradeKernel_nonneg level)
  calc
    (∑ grade ∈ grades, physicalH2PrimaryHighGradeFactor solution t grade) ≤
      physicalH2PrimaryHighGradeFactor solution t 1 +
        ∑ grade ∈ upperGrades,
          physicalH2PrimaryHighGradeFactor solution t grade := hsplit
    _ ≤ calibratedHighVelocityBoundaryKernel *
          ‖openVelocityWeightedH3State solution t‖ ^ 2 +
        ∑ grade ∈ upperGrades,
          calibratedHighVelocityGradeKernel (grade - 2) *
            ‖openVelocityWeightedH3State solution t‖ ^ 2 :=
      add_le_add
        (physicalH2PrimaryHighGradeFactor_one_le_boundary solution t)
        (Finset.sum_le_sum hfactor)
    _ = (calibratedHighVelocityBoundaryKernel +
          ∑ grade ∈ upperGrades,
            calibratedHighVelocityGradeKernel (grade - 2)) *
        ‖openVelocityWeightedH3State solution t‖ ^ 2 := by
      rw [← Finset.sum_mul]
      ring
    _ = (calibratedHighVelocityBoundaryKernel +
          ∑ level ∈ levels, calibratedHighVelocityGradeKernel level) *
        ‖openVelocityWeightedH3State solution t‖ ^ 2 := by rw [hreindex]
    _ ≤ (calibratedHighVelocityBoundaryKernel +
          ∑' level : ℕ, calibratedHighVelocityGradeKernel level) *
        ‖openVelocityWeightedH3State solution t‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_right (add_le_add le_rfl hkernelService)
        (sq_nonneg _)
    _ = calibratedHighVelocityGradeService *
        ‖openVelocityWeightedH3State solution t‖ ^ 2 := rfl

/-! ## Cofinal-uniform primary population -/

def finitePhysicalH2AdvectingLowGrades (radius : ℕ) : Finset ℕ :=
  (finitePhysicalH2AdvectingLowGradePairs radius).image Prod.fst

def finitePhysicalH2AdvectingHighGrades (radius : ℕ) : Finset ℕ :=
  (finitePhysicalH2AdvectingLowGradePairs radius).image Prod.snd

theorem finitePhysicalH2AdvectingLowGradePairs_subset_product (radius : ℕ) :
    finitePhysicalH2AdvectingLowGradePairs radius ⊆
      (finitePhysicalH2AdvectingLowGrades radius).product
        (finitePhysicalH2AdvectingHighGrades radius) := by
  intro grades hgrades
  exact Finset.mem_product.mpr
    ⟨Finset.mem_image_of_mem Prod.fst hgrades,
      Finset.mem_image_of_mem Prod.snd hgrades⟩

theorem finitePhysicalH2AdvectingHighGrades_pos
    (radius : ℕ) {highGrade : ℕ}
    (hhigh : highGrade ∈ finitePhysicalH2AdvectingHighGrades radius) :
    0 < highGrade := by
  classical
  rcases Finset.mem_image.mp hhigh with ⟨grades, hgrades, hgradeEq⟩
  rcases Finset.mem_image.mp hgrades with ⟨address, haddress, hpair⟩
  have hsector := (Finset.mem_filter.mp haddress).2
  have hstrict : advectingGrade (completeTransportTriad address) <
      advectingLowHighGrade (completeTransportTriad address) := by
    unfold AdvectingLowSector at hsector
    unfold advectingLowHighGrade
    omega
  have hpairs : advectingLowGradePair address = grades := hpair
  unfold advectingLowGradePair at hpairs
  have hhighEq : advectingLowHighGrade (completeTransportTriad address) = highGrade := by
    simpa [← hgradeEq] using congrArg Prod.snd hpairs
  omega

theorem sum_gradePair_factors_le_product_gradeSums
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius : ℕ) :
    (∑ grades ∈ finitePhysicalH2AdvectingLowGradePairs radius,
      physicalH2PrimaryLowGradeFactor solution t grades.1 *
        physicalH2PrimaryHighGradeFactor solution t grades.2) ≤
      (∑ lowGrade ∈ finitePhysicalH2AdvectingLowGrades radius,
          physicalH2PrimaryLowGradeFactor solution t lowGrade) *
        (∑ highGrade ∈ finitePhysicalH2AdvectingHighGrades radius,
          physicalH2PrimaryHighGradeFactor solution t highGrade) := by
  let productGrades := (finitePhysicalH2AdvectingLowGrades radius).product
    (finitePhysicalH2AdvectingHighGrades radius)
  calc
    (∑ grades ∈ finitePhysicalH2AdvectingLowGradePairs radius,
      physicalH2PrimaryLowGradeFactor solution t grades.1 *
        physicalH2PrimaryHighGradeFactor solution t grades.2) ≤
      ∑ grades ∈ productGrades,
        physicalH2PrimaryLowGradeFactor solution t grades.1 *
          physicalH2PrimaryHighGradeFactor solution t grades.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (finitePhysicalH2AdvectingLowGradePairs_subset_product radius)
      intro grades _hgrades _hnot
      exact mul_nonneg
        (physicalH2PrimaryLowGradeFactor_nonneg solution t grades.1)
        (physicalH2PrimaryHighGradeFactor_nonneg solution t grades.2)
    _ = (∑ lowGrade ∈ finitePhysicalH2AdvectingLowGrades radius,
          physicalH2PrimaryLowGradeFactor solution t lowGrade) *
        (∑ highGrade ∈ finitePhysicalH2AdvectingHighGrades radius,
          physicalH2PrimaryHighGradeFactor solution t highGrade) := by
      unfold productGrades
      rw [Finset.product_eq_sprod, Finset.sum_product, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro lowGrade _hlowGrade
      rw [Finset.mul_sum]

/-- **Actual cofinal-uniform primary majorant.**  The right side is independent of the finite
cube radius.  Grade zero remains visible, every positive low grade is paid by the summable
`R⁻¹ᐟ²` kernel, and every high grade is paid by the summable `R⁻²`/`R⁻⁴` velocity-square kernel. -/
theorem finiteAdvectingLowPrimaryGradeRatioPopulation_le_cofinalUniform
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (hcircle : calibration.IsEuclideanCircle)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius : ℕ) :
    finiteAdvectingLowPrimaryGradeRatioPopulation radius
        (openPeriodicVelocityFourierMode solution t) ≤
      (18 * primitiveTorusStokesScale * calibration.fullTurn) *
        ((physicalH2PrimaryLowGradeFactor solution t 0 +
            calibratedLowVelocityGradeService *
              (3 * ‖openVelocityWeightedH3State solution t‖)) *
          (calibratedHighVelocityGradeService *
            ‖openVelocityWeightedH3State solution t‖ ^ 2)) := by
  rw [finiteAdvectingLowPrimaryGradeRatioPopulation_eq_gradeFibers]
  have hconstant : 0 ≤ 18 * primitiveTorusStokesScale * calibration.fullTurn :=
    mul_nonneg
      (mul_nonneg (by norm_num) primitiveTorusStokesScale_pos.le)
      (fullTurn_nonneg_from_arcRadial calibration)
  have hlow := sum_physicalH2PrimaryLowGradeFactor_le_service solution t
    (finitePhysicalH2AdvectingLowGrades radius)
  have hhigh := sum_physicalH2PrimaryHighGradeFactor_le_service solution t
    (finitePhysicalH2AdvectingHighGrades radius)
    (fun grade hgrade ↦ finitePhysicalH2AdvectingHighGrades_pos radius hgrade)
  calc
    (∑ grades ∈ finitePhysicalH2AdvectingLowGradePairs radius,
      ∑ address ∈ finitePhysicalH2AdvectingLowGradeFiber
          radius grades.1 grades.2,
        advectingLowPrimaryGradeRatioFace
          (openPeriodicVelocityFourierMode solution t) address) ≤
      ∑ grades ∈ finitePhysicalH2AdvectingLowGradePairs radius,
        (18 * primitiveTorusStokesScale * calibration.fullTurn) *
          (physicalH2PrimaryLowGradeFactor solution t grades.1 *
            physicalH2PrimaryHighGradeFactor solution t grades.2) := by
      exact Finset.sum_le_sum fun grades _hgrades ↦
        sum_finitePhysicalH2AdvectingLowGradeFiber_primary_le_separatedFactors
          calibration hcircle solution t radius grades.1 grades.2
    _ = (18 * primitiveTorusStokesScale * calibration.fullTurn) *
        ∑ grades ∈ finitePhysicalH2AdvectingLowGradePairs radius,
          physicalH2PrimaryLowGradeFactor solution t grades.1 *
            physicalH2PrimaryHighGradeFactor solution t grades.2 := by
      rw [Finset.mul_sum]
    _ ≤ (18 * primitiveTorusStokesScale * calibration.fullTurn) *
        ((∑ lowGrade ∈ finitePhysicalH2AdvectingLowGrades radius,
            physicalH2PrimaryLowGradeFactor solution t lowGrade) *
          (∑ highGrade ∈ finitePhysicalH2AdvectingHighGrades radius,
            physicalH2PrimaryHighGradeFactor solution t highGrade)) :=
      mul_le_mul_of_nonneg_left
        (sum_gradePair_factors_le_product_gradeSums solution t radius) hconstant
    _ ≤ (18 * primitiveTorusStokesScale * calibration.fullTurn) *
        ((physicalH2PrimaryLowGradeFactor solution t 0 +
            calibratedLowVelocityGradeService *
              (3 * ‖openVelocityWeightedH3State solution t‖)) *
          (calibratedHighVelocityGradeService *
            ‖openVelocityWeightedH3State solution t‖ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hconstant
      exact mul_le_mul hlow hhigh
        (Finset.sum_nonneg fun grade _hgrade ↦
          physicalH2PrimaryHighGradeFactor_nonneg solution t grade)
        (add_nonneg
          (physicalH2PrimaryLowGradeFactor_nonneg solution t 0)
          (mul_nonneg calibratedLowVelocityGradeService_nonneg
            (mul_nonneg (by norm_num) (norm_nonneg _))))

section Audit

#print axioms finiteAdvectingLowPrimaryGradeRatioPopulation_eq_gradeFibers
#print axioms sum_openPeriodicVelocityL1_mul_receiver_on_gradeRow_le_squareMass
#print axioms sum_finitePhysicalH2AdvectingLowGradeFiber_primary_le_separatedFactors
#print axioms summable_calibratedHighVelocityGradeKernel
#print axioms finiteAdvectingLowPrimaryGradeRatioPopulation_le_cofinalUniform

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2PrimaryMajorantCofinalBound
