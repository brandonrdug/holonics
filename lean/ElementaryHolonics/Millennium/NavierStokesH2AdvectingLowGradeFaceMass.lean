import ElementaryHolonics.Millennium.NavierStokesH2AdvectingLowGradePopulation
import ElementaryHolonics.Millennium.NavierStokesH2AdvectingLowGradeLeverBound
import ElementaryHolonics.Millennium.NavierStokesCalibratedTriadicFaceBound
import Mathlib.Analysis.Real.Sqrt

/-!
# Fixed-grade face mass of the complete advecting-low physical H2 sector

**[proved-derived; formal-checked]** This owner retains every ordered complete transport address
at one least/high dyadic-grade pair.  It splits the two high pins into the equal and two adjacent
patterns before taking a norm receiver.  The receiver map at a fixed advecting pin is injective,
so finite Cauchy--Schwarz bounds the transported/receiver convolution without collapsing address
multiplicity.

The final receiver is pointwise in the actual open periodic solution and carries an explicit
Euclidean-circle calibration witness.  No time integral, continuation, or terminal absorption is
claimed here.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesH2AdvectingLowGradeFaceMass


open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCalibratedTriadicFaceBound
open Soma.Holonics.Millennium.NavierStokesCompleteDyadicTriadSectorPartition
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesH2AdvectingLowGradeLeverBound
open Soma.Holonics.Millennium.NavierStokesH2AdvectingLowGradePopulation
open Soma.Holonics.Millennium.NavierStokesH2TriadMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPhysicalH2CurrentTriadJoin
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.Turn

/-! ## Exact finite grade populations -/

/-- The finite lattice slice carrying one exact least dyadic grade.  At grade zero this is the
actual low-frequency cube; at positive grade it is the corresponding sharp shell. -/
def frequencyDyadicGradeSlice (grade : ℕ) : Finset SpatialFrequency :=
  (frequencyCube (dyadicRadius grade)).filter
    (fun frequency ↦ frequencyDyadicGrade frequency = grade)

@[simp]
theorem mem_frequencyDyadicGradeSlice_iff
    (grade : ℕ) (frequency : SpatialFrequency) :
    frequency ∈ frequencyDyadicGradeSlice grade ↔
      frequencyDyadicGrade frequency = grade := by
  constructor
  · intro hfrequency
    exact (Finset.mem_filter.mp hfrequency).2
  · intro hgrade
    apply Finset.mem_filter.mpr
    exact ⟨hgrade ▸ frequencyDyadicGrade_mem frequency, hgrade⟩

/-- The lower of two adjacent high-grade pins.  This population is empty at `highGrade = 0`,
which is the exact boundary rather than an invented predecessor shell. -/
def frequencyDyadicPredecessorSlice (highGrade : ℕ) : Finset SpatialFrequency :=
  (frequencyCube (dyadicRadius highGrade)).filter
    (fun frequency ↦ frequencyDyadicGrade frequency + 1 = highGrade)

@[simp]
theorem mem_frequencyDyadicPredecessorSlice_iff
    (highGrade : ℕ) (frequency : SpatialFrequency) :
    frequency ∈ frequencyDyadicPredecessorSlice highGrade ↔
      frequencyDyadicGrade frequency + 1 = highGrade := by
  constructor
  · intro hfrequency
    exact (Finset.mem_filter.mp hfrequency).2
  · intro hgrade
    apply Finset.mem_filter.mpr
    have hle : frequencyDyadicGrade frequency ≤ highGrade := by omega
    exact ⟨(frequencyDyadicGrade_le_iff_mem frequency highGrade).mp hle, hgrade⟩

theorem frequencyDyadicPredecessorSlice_zero :
    frequencyDyadicPredecessorSlice 0 = ∅ := by
  ext frequency
  simp

theorem frequencyDyadicPredecessorSlice_succ (grade : ℕ) :
    frequencyDyadicPredecessorSlice (grade + 1) =
      frequencyDyadicGradeSlice grade := by
  ext frequency
  simp

/-- The complete finite ordered address population at one `(lowGrade, highGrade)` pair.  Both
pins remain ordered occurrences.  The receiver is still reconstructed as `-p-q`; it is not a
quotient key. -/
def completeAdvectingLowGradePopulation (lowGrade highGrade : ℕ) :
    Finset CompleteTransportAddress := by
  classical
  exact
    ((frequencyDyadicGradeSlice lowGrade).product
        (frequencyCube (dyadicRadius highGrade))).filter fun address ↦
      AdvectingLowSector (completeTransportTriad address) ∧
        max
          (transportedGrade (completeTransportTriad address))
          (receiverGrade (completeTransportTriad address)) = highGrade

theorem mem_completeAdvectingLowGradePopulation_iff
    {lowGrade highGrade : ℕ} (address : CompleteTransportAddress) :
    address ∈ completeAdvectingLowGradePopulation lowGrade highGrade ↔
      AdvectingLowSector (completeTransportTriad address) ∧
      advectingGrade (completeTransportTriad address) = lowGrade ∧
      max
        (transportedGrade (completeTransportTriad address))
        (receiverGrade (completeTransportTriad address)) = highGrade := by
  classical
  unfold completeAdvectingLowGradePopulation
  constructor
  · intro haddress
    rcases Finset.mem_filter.mp haddress with ⟨hproduct, hsector, hhigh⟩
    have hp := (Finset.mem_product.mp hproduct).1
    exact ⟨hsector,
      (mem_frequencyDyadicGradeSlice_iff lowGrade address.1).mp hp,
      hhigh⟩
  · rintro ⟨hsector, hlow, hhigh⟩
    apply Finset.mem_filter.mpr
    have hp : address.1 ∈ frequencyDyadicGradeSlice lowGrade :=
      (mem_frequencyDyadicGradeSlice_iff lowGrade address.1).mpr hlow
    have hqgrade : transportedGrade (completeTransportTriad address) ≤ highGrade :=
      hhigh ▸ Nat.le_max_left _ _
    have hq : address.2 ∈ frequencyCube (dyadicRadius highGrade) :=
      (frequencyDyadicGrade_le_iff_mem address.2 highGrade).mp hqgrade
    exact ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hsector, hhigh⟩

/-- The finite address presentation is exactly the standing subtype grade fibre. -/
def completeAdvectingLowGradePopulationEquiv
    (lowGrade highGrade : ℕ) :
    {address : CompleteTransportAddress //
        address ∈ completeAdvectingLowGradePopulation lowGrade highGrade} ≃
      CompleteAdvectingLowGradeFiber lowGrade highGrade where
  toFun := fun address ↦ by
    have h := (mem_completeAdvectingLowGradePopulation_iff address.1).mp address.2
    exact ⟨⟨address.1, h.1⟩, h.2.1, h.2.2⟩
  invFun := fun address ↦ by
    refine ⟨address.1.1, ?_⟩
    exact (mem_completeAdvectingLowGradePopulation_iff address.1.1).mpr
      ⟨address.1.2, address.2.1, address.2.2⟩
  left_inv := by
    intro address
    apply Subtype.ext
    rfl
  right_inv := by
    intro address
    apply Subtype.ext
    apply Subtype.ext
    rfl

theorem completeTransportReceiver_fixed_advecting_injective
    (advecting : SpatialFrequency) :
    Function.Injective
      (fun transported ↦ completeTransportReceiver (advecting, transported)) := by
  intro left right hequal
  funext coordinate
  have hcoordinate := congrFun hequal coordinate
  change -advecting coordinate - left coordinate =
    -advecting coordinate - right coordinate at hcoordinate
  omega

/-! ## Cube and finite-convolution receivers -/

theorem frequencyL1_le_three_mul_cubeRadius
    {radius : ℕ} {frequency : SpatialFrequency}
    (hfrequency : frequency ∈ frequencyCube radius) :
    frequencyL1 frequency ≤ 3 * (radius : ℝ) := by
  have hbounds := (mem_frequencyCube_iff radius frequency).mp hfrequency
  have hcoordinate (coordinate : Fin 3) :
      |(frequency coordinate : ℝ)| ≤ (radius : ℝ) := by
    have hlower : -(radius : ℝ) ≤ (frequency coordinate : ℝ) := by
      exact_mod_cast (hbounds coordinate).1
    have hupper : (frequency coordinate : ℝ) ≤ (radius : ℝ) := by
      exact_mod_cast (hbounds coordinate).2
    exact (abs_le).mpr ⟨hlower, hupper⟩
  unfold frequencyL1
  nlinarith [hcoordinate 0, hcoordinate 1, hcoordinate 2]

def openPeriodicVelocityL1MassOn
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (population : Finset SpatialFrequency) : ℝ :=
  ∑ frequency ∈ population,
    complexVectorL1 (openPeriodicVelocityFourierMode solution t frequency)

def openPeriodicVorticityL1SquareMassOn
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (population : Finset SpatialFrequency) : ℝ :=
  ∑ frequency ∈ population,
    complexVectorL1 (openPeriodicVorticityFourierMode solution t frequency) ^ 2

theorem openPeriodicVelocityL1MassOn_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (population : Finset SpatialFrequency) :
    0 ≤ openPeriodicVelocityL1MassOn solution t population := by
  exact Finset.sum_nonneg fun _frequency _hfrequency ↦ complexVectorL1_nonneg _

theorem openPeriodicVorticityL1SquareMassOn_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (population : Finset SpatialFrequency) :
    0 ≤ openPeriodicVorticityL1SquareMassOn solution t population := by
  exact Finset.sum_nonneg fun _frequency _hfrequency ↦ sq_nonneg _

/-- Finite convolution Cauchy row at one fixed advecting pin.  The receiving pin is reindexed
injectively as `q ↦ -p-q`; hence its square mass is paid on the declared target population rather
than once per source collision. -/
theorem sum_openPeriodicVorticityL1_mul_receiver_le_sqrt_masses
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (advecting : SpatialFrequency)
    (row source target : Finset SpatialFrequency)
    (hsource : row ⊆ source)
    (htarget : ∀ transported ∈ row,
      completeTransportReceiver (advecting, transported) ∈ target) :
    (∑ transported ∈ row,
        complexVectorL1
            (openPeriodicVorticityFourierMode solution t transported) *
          complexVectorL1 (openPeriodicVorticityFourierMode solution t
            (completeTransportReceiver (advecting, transported)))) ≤
      Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t source) *
        Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t target) := by
  let omegaL1 : SpatialFrequency → ℝ := fun frequency ↦
    complexVectorL1 (openPeriodicVorticityFourierMode solution t frequency)
  let receiver : SpatialFrequency → SpatialFrequency := fun transported ↦
    completeTransportReceiver (advecting, transported)
  have hleft :
      (∑ transported ∈ row, omegaL1 transported ^ 2) ≤
        ∑ transported ∈ source, omegaL1 transported ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsource
      (fun frequency _hfrequency _hnot ↦ sq_nonneg (omegaL1 frequency))
  have himage : row.image receiver ⊆ target := by
    intro receiving hreceiving
    rcases Finset.mem_image.mp hreceiving with ⟨transported, htransported, rfl⟩
    exact htarget transported htransported
  have hinjective : Set.InjOn receiver (row : Set SpatialFrequency) :=
    (completeTransportReceiver_fixed_advecting_injective advecting).injOn
  have hright :
      (∑ transported ∈ row, omegaL1 (receiver transported) ^ 2) ≤
        ∑ receiving ∈ target, omegaL1 receiving ^ 2 := by
    calc
      (∑ transported ∈ row, omegaL1 (receiver transported) ^ 2) =
          ∑ receiving ∈ row.image receiver, omegaL1 receiving ^ 2 :=
        (Finset.sum_image
          (f := fun receiving ↦ omegaL1 receiving ^ 2) hinjective).symm
      _ ≤ ∑ receiving ∈ target, omegaL1 receiving ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg himage
          (fun frequency _hfrequency _hnot ↦ sq_nonneg (omegaL1 frequency))
  calc
    (∑ transported ∈ row,
        omegaL1 transported * omegaL1 (receiver transported)) ≤
      Real.sqrt (∑ transported ∈ row, omegaL1 transported ^ 2) *
        Real.sqrt (∑ transported ∈ row, omegaL1 (receiver transported) ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt row omegaL1 (omegaL1 ∘ receiver)
    _ ≤ Real.sqrt (∑ transported ∈ source, omegaL1 transported ^ 2) *
        Real.sqrt (∑ receiving ∈ target, omegaL1 receiving ^ 2) := by
      exact mul_le_mul (Real.sqrt_le_sqrt hleft) (Real.sqrt_le_sqrt hright)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t source) *
        Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t target) := rfl

/-! ## Equal/adjacent high-pin rows -/

def completeAdvectingLowEqualHighRow
    (lowGrade highGrade : ℕ) (advecting : SpatialFrequency) :
    Finset SpatialFrequency := by
  classical
  exact (frequencyDyadicGradeSlice highGrade).filter fun transported ↦
    (advecting, transported) ∈
        completeAdvectingLowGradePopulation lowGrade highGrade ∧
      receiverGrade (completeTransportTriad (advecting, transported)) = highGrade

def completeAdvectingLowTransportedHighAdjacentRow
    (lowGrade highGrade : ℕ) (advecting : SpatialFrequency) :
    Finset SpatialFrequency := by
  classical
  exact (frequencyDyadicGradeSlice highGrade).filter fun transported ↦
    (advecting, transported) ∈
        completeAdvectingLowGradePopulation lowGrade highGrade ∧
      receiverGrade (completeTransportTriad (advecting, transported)) + 1 = highGrade

def completeAdvectingLowReceiverHighAdjacentRow
    (lowGrade highGrade : ℕ) (advecting : SpatialFrequency) :
    Finset SpatialFrequency := by
  classical
  exact (frequencyDyadicPredecessorSlice highGrade).filter fun transported ↦
    (advecting, transported) ∈
        completeAdvectingLowGradePopulation lowGrade highGrade ∧
      receiverGrade (completeTransportTriad (advecting, transported)) = highGrade

theorem sum_equalHighRow_vorticity_product_le
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (lowGrade highGrade : ℕ)
    (advecting : SpatialFrequency) :
    (∑ transported ∈
        completeAdvectingLowEqualHighRow lowGrade highGrade advecting,
        complexVectorL1
            (openPeriodicVorticityFourierMode solution t transported) *
          complexVectorL1 (openPeriodicVorticityFourierMode solution t
            (completeTransportReceiver (advecting, transported)))) ≤
      Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
        (frequencyDyadicGradeSlice highGrade)) *
      Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
        (frequencyDyadicGradeSlice highGrade)) := by
  apply sum_openPeriodicVorticityL1_mul_receiver_le_sqrt_masses
  · intro transported htransported
    exact (Finset.mem_filter.mp htransported).1
  · intro transported htransported
    have hgrade := (Finset.mem_filter.mp htransported).2.2
    exact (mem_frequencyDyadicGradeSlice_iff highGrade _).mpr hgrade

theorem sum_transportedHighAdjacentRow_vorticity_product_le
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (lowGrade highGrade : ℕ)
    (advecting : SpatialFrequency) :
    (∑ transported ∈
        completeAdvectingLowTransportedHighAdjacentRow
          lowGrade highGrade advecting,
        complexVectorL1
            (openPeriodicVorticityFourierMode solution t transported) *
          complexVectorL1 (openPeriodicVorticityFourierMode solution t
            (completeTransportReceiver (advecting, transported)))) ≤
      Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
        (frequencyDyadicGradeSlice highGrade)) *
      Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
        (frequencyDyadicPredecessorSlice highGrade)) := by
  apply sum_openPeriodicVorticityL1_mul_receiver_le_sqrt_masses
  · intro transported htransported
    exact (Finset.mem_filter.mp htransported).1
  · intro transported htransported
    have hgrade := (Finset.mem_filter.mp htransported).2.2
    exact (mem_frequencyDyadicPredecessorSlice_iff highGrade _).mpr hgrade

theorem sum_receiverHighAdjacentRow_vorticity_product_le
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (lowGrade highGrade : ℕ)
    (advecting : SpatialFrequency) :
    (∑ transported ∈
        completeAdvectingLowReceiverHighAdjacentRow
          lowGrade highGrade advecting,
        complexVectorL1
            (openPeriodicVorticityFourierMode solution t transported) *
          complexVectorL1 (openPeriodicVorticityFourierMode solution t
            (completeTransportReceiver (advecting, transported)))) ≤
      Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
        (frequencyDyadicPredecessorSlice highGrade)) *
      Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
        (frequencyDyadicGradeSlice highGrade)) := by
  apply sum_openPeriodicVorticityL1_mul_receiver_le_sqrt_masses
  · intro transported htransported
    exact (Finset.mem_filter.mp htransported).1
  · intro transported htransported
    have hgrade := (Finset.mem_filter.mp htransported).2.2
    exact (mem_frequencyDyadicGradeSlice_iff highGrade _).mpr hgrade

/-! ## The actual fixed-grade physical face mass -/

def completePhysicalH2AdvectingLowGradeFaceMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (lowGrade highGrade : ℕ) : ℝ :=
  ∑ address ∈ completeAdvectingLowGradePopulation lowGrade highGrade,
    |(completePhysicalH2ExchangedTransportFace solution t address).re|

def completePhysicalAdvectingLowGradeModeProductMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (lowGrade highGrade : ℕ) : ℝ :=
  ∑ address ∈ completeAdvectingLowGradePopulation lowGrade highGrade,
    complexVectorL1 (openPeriodicVelocityFourierMode solution t address.1) *
      complexVectorL1 (openPeriodicVorticityFourierMode solution t address.2) *
      complexVectorL1 (openPeriodicVorticityFourierMode solution t
        (completeTransportReceiver address))

theorem abs_re_completePhysicalH2ExchangedTransportFace_le_calibrated_grade_product
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
    |(completePhysicalH2ExchangedTransportFace solution t address).re| ≤
      ((primitiveTorusStokesScale *
          (6 * dyadicGradeLengthRatio lowGrade highGrade *
            (dyadicRadius highGrade : ℝ) ^ 2)) *
        (calibration.fullTurn * (3 * (dyadicRadius highGrade : ℝ)))) *
      (complexVectorL1
          (openPeriodicVelocityFourierMode solution t address.1) *
        complexVectorL1
          (openPeriodicVorticityFourierMode solution t address.2) *
        complexVectorL1 (openPeriodicVorticityFourierMode solution t
          (completeTransportReceiver address))) := by
  rcases (mem_completeAdvectingLowGradePopulation_iff address).mp haddress with
    ⟨hsector, hlow, hhigh⟩
  have hhigh' :
      advectingLowHighGrade (completeTransportTriad address) = highGrade := by
    exact hhigh
  have hlever :=
    abs_re_completePhysicalH2ExchangedTransportFace_le_advectingLowGradeRatio
      solution t address hsector
  rw [hlow, hhigh'] at hlever
  have hface := norm_triadicEnergyFace_le_of_calibration calibration hcircle
    address.1 address.2
    (openPeriodicVelocityFourierMode solution t address.1)
    (openPeriodicVorticityFourierMode solution t address.2)
    (openPeriodicVorticityFourierMode solution t
      (completeTransportReceiver address))
  change ‖completeOpenVorticityTransportFace solution t address‖ ≤ _ at hface
  have htransportedGrade : transportedGrade (completeTransportTriad address) ≤ highGrade :=
    hhigh ▸ Nat.le_max_left _ _
  have htransported : address.2 ∈ frequencyCube (dyadicRadius highGrade) :=
    (frequencyDyadicGrade_le_iff_mem address.2 highGrade).mp htransportedGrade
  have hfrequency := frequencyL1_le_three_mul_cubeRadius htransported
  have hturn : 0 ≤ calibration.fullTurn :=
    fullTurn_nonneg_from_arcRadial calibration
  have hleverCoefficient :
      0 ≤ primitiveTorusStokesScale *
        (6 * dyadicGradeLengthRatio lowGrade highGrade *
          (dyadicRadius highGrade : ℝ) ^ 2) := by
    have hratio : 0 ≤ dyadicGradeLengthRatio lowGrade highGrade := by
      unfold dyadicGradeLengthRatio
      exact div_nonneg (by positivity) (by positivity)
    exact mul_nonneg primitiveTorusStokesScale_pos.le
      (mul_nonneg (mul_nonneg (by norm_num) hratio) (sq_nonneg _))
  have hmodeProduct :
      calibration.fullTurn * frequencyL1 address.2 *
          complexVectorL1 (openPeriodicVelocityFourierMode solution t address.1) *
          complexVectorL1 (openPeriodicVorticityFourierMode solution t address.2) *
          complexVectorL1 (openPeriodicVorticityFourierMode solution t
            (completeTransportReceiver address)) ≤
        calibration.fullTurn * (3 * (dyadicRadius highGrade : ℝ)) *
          complexVectorL1 (openPeriodicVelocityFourierMode solution t address.1) *
          complexVectorL1 (openPeriodicVorticityFourierMode solution t address.2) *
          complexVectorL1 (openPeriodicVorticityFourierMode solution t
            (completeTransportReceiver address)) := by
    gcongr
    all_goals exact complexVectorL1_nonneg _
  calc
    |(completePhysicalH2ExchangedTransportFace solution t address).re| ≤
        (primitiveTorusStokesScale *
          (6 * dyadicGradeLengthRatio lowGrade highGrade *
            (dyadicRadius highGrade : ℝ) ^ 2)) *
          ‖completeOpenVorticityTransportFace solution t address‖ := hlever
    _ ≤ (primitiveTorusStokesScale *
          (6 * dyadicGradeLengthRatio lowGrade highGrade *
            (dyadicRadius highGrade : ℝ) ^ 2)) *
        (calibration.fullTurn * frequencyL1 address.2 *
          complexVectorL1 (openPeriodicVelocityFourierMode solution t address.1) *
          complexVectorL1 (openPeriodicVorticityFourierMode solution t address.2) *
          complexVectorL1 (openPeriodicVorticityFourierMode solution t
            (completeTransportReceiver address))) :=
      mul_le_mul_of_nonneg_left hface hleverCoefficient
    _ ≤ (primitiveTorusStokesScale *
          (6 * dyadicGradeLengthRatio lowGrade highGrade *
            (dyadicRadius highGrade : ℝ) ^ 2)) *
        (calibration.fullTurn * (3 * (dyadicRadius highGrade : ℝ)) *
          complexVectorL1 (openPeriodicVelocityFourierMode solution t address.1) *
          complexVectorL1 (openPeriodicVorticityFourierMode solution t address.2) *
          complexVectorL1 (openPeriodicVorticityFourierMode solution t
            (completeTransportReceiver address))) :=
      mul_le_mul_of_nonneg_left hmodeProduct hleverCoefficient
    _ = _ := by ring

theorem completePhysicalH2AdvectingLowGradeFaceMass_le_calibrated_modeProductMass
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (hcircle : calibration.IsEuclideanCircle)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (lowGrade highGrade : ℕ) :
    completePhysicalH2AdvectingLowGradeFaceMass solution t lowGrade highGrade ≤
      ((primitiveTorusStokesScale *
          (6 * dyadicGradeLengthRatio lowGrade highGrade *
            (dyadicRadius highGrade : ℝ) ^ 2)) *
        (calibration.fullTurn * (3 * (dyadicRadius highGrade : ℝ)))) *
      completePhysicalAdvectingLowGradeModeProductMass
        solution t lowGrade highGrade := by
  unfold completePhysicalH2AdvectingLowGradeFaceMass
  unfold completePhysicalAdvectingLowGradeModeProductMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro address haddress
  exact abs_re_completePhysicalH2ExchangedTransportFace_le_calibrated_grade_product
    calibration hcircle solution t address haddress

/-! ## Exact high-pattern split before the convolution receiver -/

def EqualHighPattern (highGrade : ℕ) (address : CompleteTransportAddress) : Prop :=
  transportedGrade (completeTransportTriad address) = highGrade ∧
    receiverGrade (completeTransportTriad address) = highGrade

def TransportedHighAdjacentPattern
    (highGrade : ℕ) (address : CompleteTransportAddress) : Prop :=
  transportedGrade (completeTransportTriad address) = highGrade ∧
    receiverGrade (completeTransportTriad address) + 1 = highGrade

def ReceiverHighAdjacentPattern
    (highGrade : ℕ) (address : CompleteTransportAddress) : Prop :=
  receiverGrade (completeTransportTriad address) = highGrade ∧
    transportedGrade (completeTransportTriad address) + 1 = highGrade

theorem completeAdvectingLowGradePopulation_highPattern_exhaustive
    {lowGrade highGrade : ℕ} {address : CompleteTransportAddress}
    (haddress : address ∈
      completeAdvectingLowGradePopulation lowGrade highGrade) :
    EqualHighPattern highGrade address ∨
      TransportedHighAdjacentPattern highGrade address ∨
      ReceiverHighAdjacentPattern highGrade address := by
  have h := (mem_completeAdvectingLowGradePopulation_iff address).mp haddress
  let graded : CompleteAdvectingLowGradeFiber lowGrade highGrade :=
    ⟨⟨address, h.1⟩, h.2.1, h.2.2⟩
  exact graded.highGrade_pattern

theorem EqualHighPattern.not_transportedHighAdjacent
    {highGrade : ℕ} {address : CompleteTransportAddress}
    (hequal : EqualHighPattern highGrade address) :
    ¬TransportedHighAdjacentPattern highGrade address := by
  intro hadjacent
  simp only [EqualHighPattern] at hequal
  simp only [TransportedHighAdjacentPattern] at hadjacent
  omega

theorem EqualHighPattern.not_receiverHighAdjacent
    {highGrade : ℕ} {address : CompleteTransportAddress}
    (hequal : EqualHighPattern highGrade address) :
    ¬ReceiverHighAdjacentPattern highGrade address := by
  intro hadjacent
  simp only [EqualHighPattern] at hequal
  simp only [ReceiverHighAdjacentPattern] at hadjacent
  omega

theorem TransportedHighAdjacentPattern.not_receiverHighAdjacent
    {highGrade : ℕ} {address : CompleteTransportAddress}
    (htransported : TransportedHighAdjacentPattern highGrade address) :
    ¬ReceiverHighAdjacentPattern highGrade address := by
  intro hreceiver
  simp only [TransportedHighAdjacentPattern] at htransported
  simp only [ReceiverHighAdjacentPattern] at hreceiver
  omega

def completeAdvectingLowEqualHighPopulation
    (lowGrade highGrade : ℕ) : Finset CompleteTransportAddress := by
  classical
  exact (completeAdvectingLowGradePopulation lowGrade highGrade).filter
    (EqualHighPattern highGrade)

def completeAdvectingLowTransportedHighAdjacentPopulation
    (lowGrade highGrade : ℕ) : Finset CompleteTransportAddress := by
  classical
  exact (completeAdvectingLowGradePopulation lowGrade highGrade).filter
    (TransportedHighAdjacentPattern highGrade)

def completeAdvectingLowReceiverHighAdjacentPopulation
    (lowGrade highGrade : ℕ) : Finset CompleteTransportAddress := by
  classical
  exact (completeAdvectingLowGradePopulation lowGrade highGrade).filter
    (ReceiverHighAdjacentPattern highGrade)

theorem sum_completeAdvectingLowGradePopulation_eq_highPatterns
    (lowGrade highGrade : ℕ) (face : CompleteTransportAddress → ℝ) :
    (∑ address ∈ completeAdvectingLowGradePopulation lowGrade highGrade,
        face address) =
      (∑ address ∈
          completeAdvectingLowEqualHighPopulation lowGrade highGrade,
            face address) +
      (∑ address ∈
          completeAdvectingLowTransportedHighAdjacentPopulation lowGrade highGrade,
            face address) +
      (∑ address ∈
          completeAdvectingLowReceiverHighAdjacentPopulation lowGrade highGrade,
            face address) := by
  classical
  unfold completeAdvectingLowEqualHighPopulation
  unfold completeAdvectingLowTransportedHighAdjacentPopulation
  unfold completeAdvectingLowReceiverHighAdjacentPopulation
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro address haddress
  rcases completeAdvectingLowGradePopulation_highPattern_exhaustive haddress with
    hequal | htransported | hreceiver
  · simp [hequal, hequal.not_transportedHighAdjacent,
      hequal.not_receiverHighAdjacent]
  · have hnotEqual : ¬EqualHighPattern highGrade address := by
      intro hequal
      exact hequal.not_transportedHighAdjacent htransported
    simp [hnotEqual, htransported,
      htransported.not_receiverHighAdjacent]
  · have hnotEqual : ¬EqualHighPattern highGrade address := by
      intro hequal
      exact hequal.not_receiverHighAdjacent hreceiver
    have hnotTransported :
        ¬TransportedHighAdjacentPattern highGrade address := by
      intro htransported
      exact htransported.not_receiverHighAdjacent hreceiver
    simp [hnotEqual, hnotTransported, hreceiver]

theorem sum_equalHighPopulation_modeProduct_eq_rows
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (lowGrade highGrade : ℕ) :
    (∑ address ∈
        completeAdvectingLowEqualHighPopulation lowGrade highGrade,
        complexVectorL1
            (openPeriodicVelocityFourierMode solution t address.1) *
          complexVectorL1
            (openPeriodicVorticityFourierMode solution t address.2) *
          complexVectorL1 (openPeriodicVorticityFourierMode solution t
            (completeTransportReceiver address))) =
      ∑ advecting ∈ frequencyDyadicGradeSlice lowGrade,
        complexVectorL1
            (openPeriodicVelocityFourierMode solution t advecting) *
          ∑ transported ∈
              completeAdvectingLowEqualHighRow lowGrade highGrade advecting,
            complexVectorL1
                (openPeriodicVorticityFourierMode solution t transported) *
              complexVectorL1 (openPeriodicVorticityFourierMode solution t
                (completeTransportReceiver (advecting, transported))) := by
  classical
  unfold completeAdvectingLowEqualHighPopulation
  unfold completeAdvectingLowEqualHighRow
  unfold completeAdvectingLowGradePopulation
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [Finset.product_eq_sprod]
  rw [Finset.sum_product
    (frequencyDyadicGradeSlice lowGrade)
    (frequencyCube (dyadicRadius highGrade))]
  apply Finset.sum_congr rfl
  intro advecting hadvecting
  rw [Finset.mul_sum]
  change
    (∑ transported ∈ frequencyCube (dyadicRadius highGrade),
      if AdvectingLowSector (completeTransportTriad (advecting, transported)) ∧
          max (transportedGrade (completeTransportTriad (advecting, transported)))
            (receiverGrade (completeTransportTriad (advecting, transported))) = highGrade then
        if EqualHighPattern highGrade (advecting, transported) then
          complexVectorL1 (openPeriodicVelocityFourierMode solution t advecting) *
            complexVectorL1 (openPeriodicVorticityFourierMode solution t transported) *
            complexVectorL1 (openPeriodicVorticityFourierMode solution t
              (completeTransportReceiver (advecting, transported)))
        else 0
      else 0) = _
  unfold frequencyDyadicGradeSlice
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro transported htransported
  have hadvectingGrade :=
    (mem_frequencyDyadicGradeSlice_iff lowGrade advecting).mp hadvecting
  have hadvectingCube : advecting ∈ frequencyCube (dyadicRadius lowGrade) := by
    rw [← hadvectingGrade]
    exact frequencyDyadicGrade_mem advecting
  simp only [Finset.mem_product, Finset.mem_filter, EqualHighPattern]
  by_cases htransportedGrade :
      frequencyDyadicGrade transported = highGrade
  · have htransportedGrade' :
        transportedGrade (completeTransportTriad (advecting, transported)) = highGrade := by
      simpa only [transportedGrade, completeTransportTriad] using htransportedGrade
    by_cases hsector : AdvectingLowSector (completeTransportTriad (advecting, transported))
    · by_cases hreceiver :
          receiverGrade (completeTransportTriad (advecting, transported)) = highGrade
      · simp [hsector, hreceiver, hadvectingCube, hadvectingGrade, htransported,
          htransportedGrade, htransportedGrade', mul_assoc]
      · simp [hsector, hreceiver, hadvectingCube, hadvectingGrade, htransported,
          htransportedGrade, htransportedGrade']
    · simp [hsector, hadvectingCube, hadvectingGrade, htransported,
        htransportedGrade, htransportedGrade']
  · have htransportedGrade' :
        ¬transportedGrade (completeTransportTriad (advecting, transported)) = highGrade := by
      simpa only [transportedGrade, completeTransportTriad] using htransportedGrade
    simp [htransportedGrade, htransportedGrade']

theorem sum_transportedHighAdjacentPopulation_modeProduct_eq_rows
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (lowGrade highGrade : ℕ) :
    (∑ address ∈ completeAdvectingLowTransportedHighAdjacentPopulation
        lowGrade highGrade,
        complexVectorL1
            (openPeriodicVelocityFourierMode solution t address.1) *
          complexVectorL1
            (openPeriodicVorticityFourierMode solution t address.2) *
          complexVectorL1 (openPeriodicVorticityFourierMode solution t
            (completeTransportReceiver address))) =
      ∑ advecting ∈ frequencyDyadicGradeSlice lowGrade,
        complexVectorL1
            (openPeriodicVelocityFourierMode solution t advecting) *
          ∑ transported ∈ completeAdvectingLowTransportedHighAdjacentRow
              lowGrade highGrade advecting,
            complexVectorL1
                (openPeriodicVorticityFourierMode solution t transported) *
              complexVectorL1 (openPeriodicVorticityFourierMode solution t
                (completeTransportReceiver (advecting, transported))) := by
  classical
  unfold completeAdvectingLowTransportedHighAdjacentPopulation
  unfold completeAdvectingLowTransportedHighAdjacentRow
  unfold completeAdvectingLowGradePopulation
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [Finset.product_eq_sprod]
  rw [Finset.sum_product
    (frequencyDyadicGradeSlice lowGrade)
    (frequencyCube (dyadicRadius highGrade))]
  apply Finset.sum_congr rfl
  intro advecting hadvecting
  rw [Finset.mul_sum]
  change
    (∑ transported ∈ frequencyCube (dyadicRadius highGrade),
      if AdvectingLowSector (completeTransportTriad (advecting, transported)) ∧
          max (transportedGrade (completeTransportTriad (advecting, transported)))
            (receiverGrade (completeTransportTriad (advecting, transported))) = highGrade then
        if TransportedHighAdjacentPattern highGrade (advecting, transported) then
          complexVectorL1 (openPeriodicVelocityFourierMode solution t advecting) *
            complexVectorL1 (openPeriodicVorticityFourierMode solution t transported) *
            complexVectorL1 (openPeriodicVorticityFourierMode solution t
              (completeTransportReceiver (advecting, transported)))
        else 0
      else 0) = _
  unfold frequencyDyadicGradeSlice
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro transported htransported
  have hadvectingGrade :=
    (mem_frequencyDyadicGradeSlice_iff lowGrade advecting).mp hadvecting
  have hadvectingCube : advecting ∈ frequencyCube (dyadicRadius lowGrade) := by
    rw [← hadvectingGrade]
    exact frequencyDyadicGrade_mem advecting
  simp only [Finset.mem_product, Finset.mem_filter,
    TransportedHighAdjacentPattern]
  by_cases htransportedGrade : frequencyDyadicGrade transported = highGrade
  · have htransportedGrade' :
        transportedGrade (completeTransportTriad (advecting, transported)) = highGrade := by
      simpa only [transportedGrade, completeTransportTriad] using htransportedGrade
    by_cases hsector : AdvectingLowSector (completeTransportTriad (advecting, transported))
    · by_cases hreceiver :
          receiverGrade (completeTransportTriad (advecting, transported)) + 1 = highGrade
      · have hreceiverLe :
            receiverGrade (completeTransportTriad (advecting, transported)) ≤ highGrade := by
          omega
        simp [hsector, hreceiver, hreceiverLe, hadvectingCube, hadvectingGrade,
          htransported, htransportedGrade, htransportedGrade', mul_assoc]
      · simp [hsector, hreceiver, hadvectingCube, hadvectingGrade, htransported,
          htransportedGrade, htransportedGrade']
    · simp [hsector, hadvectingCube, hadvectingGrade, htransported,
        htransportedGrade, htransportedGrade']
  · have htransportedGrade' :
        ¬transportedGrade (completeTransportTriad (advecting, transported)) = highGrade := by
      simpa only [transportedGrade, completeTransportTriad] using htransportedGrade
    simp [htransportedGrade, htransportedGrade']

theorem sum_receiverHighAdjacentPopulation_modeProduct_eq_rows
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (lowGrade highGrade : ℕ) :
    (∑ address ∈ completeAdvectingLowReceiverHighAdjacentPopulation
        lowGrade highGrade,
        complexVectorL1
            (openPeriodicVelocityFourierMode solution t address.1) *
          complexVectorL1
            (openPeriodicVorticityFourierMode solution t address.2) *
          complexVectorL1 (openPeriodicVorticityFourierMode solution t
            (completeTransportReceiver address))) =
      ∑ advecting ∈ frequencyDyadicGradeSlice lowGrade,
        complexVectorL1
            (openPeriodicVelocityFourierMode solution t advecting) *
          ∑ transported ∈ completeAdvectingLowReceiverHighAdjacentRow
              lowGrade highGrade advecting,
            complexVectorL1
                (openPeriodicVorticityFourierMode solution t transported) *
              complexVectorL1 (openPeriodicVorticityFourierMode solution t
                (completeTransportReceiver (advecting, transported))) := by
  classical
  unfold completeAdvectingLowReceiverHighAdjacentPopulation
  unfold completeAdvectingLowReceiverHighAdjacentRow
  unfold completeAdvectingLowGradePopulation
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [Finset.product_eq_sprod]
  rw [Finset.sum_product
    (frequencyDyadicGradeSlice lowGrade)
    (frequencyCube (dyadicRadius highGrade))]
  apply Finset.sum_congr rfl
  intro advecting hadvecting
  rw [Finset.mul_sum]
  change
    (∑ transported ∈ frequencyCube (dyadicRadius highGrade),
      if AdvectingLowSector (completeTransportTriad (advecting, transported)) ∧
          max (transportedGrade (completeTransportTriad (advecting, transported)))
            (receiverGrade (completeTransportTriad (advecting, transported))) = highGrade then
        if ReceiverHighAdjacentPattern highGrade (advecting, transported) then
          complexVectorL1 (openPeriodicVelocityFourierMode solution t advecting) *
            complexVectorL1 (openPeriodicVorticityFourierMode solution t transported) *
            complexVectorL1 (openPeriodicVorticityFourierMode solution t
              (completeTransportReceiver (advecting, transported)))
        else 0
      else 0) = _
  unfold frequencyDyadicPredecessorSlice
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro transported htransported
  have hadvectingGrade :=
    (mem_frequencyDyadicGradeSlice_iff lowGrade advecting).mp hadvecting
  simp only [Finset.mem_product, Finset.mem_filter,
    ReceiverHighAdjacentPattern]
  by_cases htransportedGrade : frequencyDyadicGrade transported + 1 = highGrade
  · have htransportedGrade' :
        transportedGrade (completeTransportTriad (advecting, transported)) + 1 =
          highGrade := by
      simpa only [transportedGrade, completeTransportTriad] using htransportedGrade
    have htransportedLe :
        transportedGrade (completeTransportTriad (advecting, transported)) ≤ highGrade := by
      omega
    by_cases hsector : AdvectingLowSector (completeTransportTriad (advecting, transported))
    · by_cases hreceiver :
          receiverGrade (completeTransportTriad (advecting, transported)) = highGrade
      · simp [hsector, hreceiver, htransportedLe, hadvectingGrade,
          htransported, htransportedGrade, htransportedGrade', mul_assoc]
      · simp [hsector, hreceiver, hadvectingGrade, htransported,
          htransportedGrade, htransportedGrade']
    · simp [hsector, hadvectingGrade, htransported, htransportedGrade]
  · have htransportedGrade' :
        ¬transportedGrade (completeTransportTriad (advecting, transported)) + 1 =
          highGrade := by
      simpa only [transportedGrade, completeTransportTriad] using htransportedGrade
    simp [htransportedGrade, htransportedGrade']

theorem sum_equalHighPopulation_modeProduct_le_cauchy
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (lowGrade highGrade : ℕ) :
    (∑ address ∈ completeAdvectingLowEqualHighPopulation lowGrade highGrade,
        complexVectorL1
            (openPeriodicVelocityFourierMode solution t address.1) *
          complexVectorL1
            (openPeriodicVorticityFourierMode solution t address.2) *
          complexVectorL1 (openPeriodicVorticityFourierMode solution t
            (completeTransportReceiver address))) ≤
      openPeriodicVelocityL1MassOn solution t
          (frequencyDyadicGradeSlice lowGrade) *
        (Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
            (frequencyDyadicGradeSlice highGrade)) *
          Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
            (frequencyDyadicGradeSlice highGrade))) := by
  rw [sum_equalHighPopulation_modeProduct_eq_rows]
  calc
    (∑ advecting ∈ frequencyDyadicGradeSlice lowGrade,
        complexVectorL1 (openPeriodicVelocityFourierMode solution t advecting) *
          ∑ transported ∈ completeAdvectingLowEqualHighRow
              lowGrade highGrade advecting,
            complexVectorL1
                (openPeriodicVorticityFourierMode solution t transported) *
              complexVectorL1 (openPeriodicVorticityFourierMode solution t
                (completeTransportReceiver (advecting, transported)))) ≤
      ∑ advecting ∈ frequencyDyadicGradeSlice lowGrade,
        complexVectorL1 (openPeriodicVelocityFourierMode solution t advecting) *
          (Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
              (frequencyDyadicGradeSlice highGrade)) *
            Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
              (frequencyDyadicGradeSlice highGrade))) := by
        apply Finset.sum_le_sum
        intro advecting _hadvecting
        exact mul_le_mul_of_nonneg_left
          (sum_equalHighRow_vorticity_product_le
            solution t lowGrade highGrade advecting)
          (complexVectorL1_nonneg _)
    _ = openPeriodicVelocityL1MassOn solution t
          (frequencyDyadicGradeSlice lowGrade) *
        (Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
            (frequencyDyadicGradeSlice highGrade)) *
          Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
            (frequencyDyadicGradeSlice highGrade))) := by
      unfold openPeriodicVelocityL1MassOn
      rw [Finset.sum_mul]

theorem sum_transportedHighAdjacentPopulation_modeProduct_le_cauchy
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (lowGrade highGrade : ℕ) :
    (∑ address ∈ completeAdvectingLowTransportedHighAdjacentPopulation
        lowGrade highGrade,
        complexVectorL1
            (openPeriodicVelocityFourierMode solution t address.1) *
          complexVectorL1
            (openPeriodicVorticityFourierMode solution t address.2) *
          complexVectorL1 (openPeriodicVorticityFourierMode solution t
            (completeTransportReceiver address))) ≤
      openPeriodicVelocityL1MassOn solution t
          (frequencyDyadicGradeSlice lowGrade) *
        (Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
            (frequencyDyadicGradeSlice highGrade)) *
          Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
            (frequencyDyadicPredecessorSlice highGrade))) := by
  rw [sum_transportedHighAdjacentPopulation_modeProduct_eq_rows]
  calc
    (∑ advecting ∈ frequencyDyadicGradeSlice lowGrade,
        complexVectorL1 (openPeriodicVelocityFourierMode solution t advecting) *
          ∑ transported ∈ completeAdvectingLowTransportedHighAdjacentRow
              lowGrade highGrade advecting,
            complexVectorL1
                (openPeriodicVorticityFourierMode solution t transported) *
              complexVectorL1 (openPeriodicVorticityFourierMode solution t
                (completeTransportReceiver (advecting, transported)))) ≤
      ∑ advecting ∈ frequencyDyadicGradeSlice lowGrade,
        complexVectorL1 (openPeriodicVelocityFourierMode solution t advecting) *
          (Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
              (frequencyDyadicGradeSlice highGrade)) *
            Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
              (frequencyDyadicPredecessorSlice highGrade))) := by
        apply Finset.sum_le_sum
        intro advecting _hadvecting
        exact mul_le_mul_of_nonneg_left
          (sum_transportedHighAdjacentRow_vorticity_product_le
            solution t lowGrade highGrade advecting)
          (complexVectorL1_nonneg _)
    _ = openPeriodicVelocityL1MassOn solution t
          (frequencyDyadicGradeSlice lowGrade) *
        (Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
            (frequencyDyadicGradeSlice highGrade)) *
          Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
            (frequencyDyadicPredecessorSlice highGrade))) := by
      unfold openPeriodicVelocityL1MassOn
      rw [Finset.sum_mul]

theorem sum_receiverHighAdjacentPopulation_modeProduct_le_cauchy
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (lowGrade highGrade : ℕ) :
    (∑ address ∈ completeAdvectingLowReceiverHighAdjacentPopulation
        lowGrade highGrade,
        complexVectorL1
            (openPeriodicVelocityFourierMode solution t address.1) *
          complexVectorL1
            (openPeriodicVorticityFourierMode solution t address.2) *
          complexVectorL1 (openPeriodicVorticityFourierMode solution t
            (completeTransportReceiver address))) ≤
      openPeriodicVelocityL1MassOn solution t
          (frequencyDyadicGradeSlice lowGrade) *
        (Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
            (frequencyDyadicPredecessorSlice highGrade)) *
          Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
            (frequencyDyadicGradeSlice highGrade))) := by
  rw [sum_receiverHighAdjacentPopulation_modeProduct_eq_rows]
  calc
    (∑ advecting ∈ frequencyDyadicGradeSlice lowGrade,
        complexVectorL1 (openPeriodicVelocityFourierMode solution t advecting) *
          ∑ transported ∈ completeAdvectingLowReceiverHighAdjacentRow
              lowGrade highGrade advecting,
            complexVectorL1
                (openPeriodicVorticityFourierMode solution t transported) *
              complexVectorL1 (openPeriodicVorticityFourierMode solution t
                (completeTransportReceiver (advecting, transported)))) ≤
      ∑ advecting ∈ frequencyDyadicGradeSlice lowGrade,
        complexVectorL1 (openPeriodicVelocityFourierMode solution t advecting) *
          (Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
              (frequencyDyadicPredecessorSlice highGrade)) *
            Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
              (frequencyDyadicGradeSlice highGrade))) := by
        apply Finset.sum_le_sum
        intro advecting _hadvecting
        exact mul_le_mul_of_nonneg_left
          (sum_receiverHighAdjacentRow_vorticity_product_le
            solution t lowGrade highGrade advecting)
          (complexVectorL1_nonneg _)
    _ = openPeriodicVelocityL1MassOn solution t
          (frequencyDyadicGradeSlice lowGrade) *
        (Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
            (frequencyDyadicPredecessorSlice highGrade)) *
          Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
            (frequencyDyadicGradeSlice highGrade))) := by
      unfold openPeriodicVelocityL1MassOn
      rw [Finset.sum_mul]

/-- **Actual closed-triad convolution row.**  Equal high grades cost the high square mass once;
the two oriented adjacent patterns cost the same high/predecessor product twice. -/
theorem completePhysicalAdvectingLowGradeModeProductMass_le_cauchy_patterns
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (lowGrade highGrade : ℕ) :
    completePhysicalAdvectingLowGradeModeProductMass solution t lowGrade highGrade ≤
      openPeriodicVelocityL1MassOn solution t
          (frequencyDyadicGradeSlice lowGrade) *
        (Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
              (frequencyDyadicGradeSlice highGrade)) *
            Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
              (frequencyDyadicGradeSlice highGrade)) +
          2 * (Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
                (frequencyDyadicGradeSlice highGrade)) *
            Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
              (frequencyDyadicPredecessorSlice highGrade)))) := by
  let face : CompleteTransportAddress → ℝ := fun address ↦
    complexVectorL1 (openPeriodicVelocityFourierMode solution t address.1) *
      complexVectorL1 (openPeriodicVorticityFourierMode solution t address.2) *
      complexVectorL1 (openPeriodicVorticityFourierMode solution t
        (completeTransportReceiver address))
  have hsplit := sum_completeAdvectingLowGradePopulation_eq_highPatterns
    lowGrade highGrade face
  change completePhysicalAdvectingLowGradeModeProductMass
      solution t lowGrade highGrade = _ at hsplit
  rw [hsplit]
  have hequal := sum_equalHighPopulation_modeProduct_le_cauchy
    solution t lowGrade highGrade
  have htransported :=
    sum_transportedHighAdjacentPopulation_modeProduct_le_cauchy
      solution t lowGrade highGrade
  have hreceiver := sum_receiverHighAdjacentPopulation_modeProduct_le_cauchy
    solution t lowGrade highGrade
  calc
    _ ≤
        openPeriodicVelocityL1MassOn solution t
            (frequencyDyadicGradeSlice lowGrade) *
          (Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
              (frequencyDyadicGradeSlice highGrade)) *
            Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
              (frequencyDyadicGradeSlice highGrade))) +
        openPeriodicVelocityL1MassOn solution t
            (frequencyDyadicGradeSlice lowGrade) *
          (Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
              (frequencyDyadicGradeSlice highGrade)) *
            Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
              (frequencyDyadicPredecessorSlice highGrade))) +
        openPeriodicVelocityL1MassOn solution t
            (frequencyDyadicGradeSlice lowGrade) *
          (Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
              (frequencyDyadicPredecessorSlice highGrade)) *
            Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
              (frequencyDyadicGradeSlice highGrade))) := by
      exact add_le_add (add_le_add hequal htransported) hreceiver
    _ = _ := by ring

/-- **Fixed-grade physical face-mass estimate.**  This is the actual complete advecting-low
closed-triad address fibre, not a hypothesis-taking shell wrapper.  The low factor remains the
finite velocity `L¹` mass; the two high vorticity pins are controlled directly by the injective
receiver convolution and its equal/adjacent grade split. -/
theorem completePhysicalH2AdvectingLowGradeFaceMass_le_calibrated_cauchy_patterns
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (hcircle : calibration.IsEuclideanCircle)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (lowGrade highGrade : ℕ) :
    completePhysicalH2AdvectingLowGradeFaceMass solution t lowGrade highGrade ≤
      ((primitiveTorusStokesScale *
          (6 * dyadicGradeLengthRatio lowGrade highGrade *
            (dyadicRadius highGrade : ℝ) ^ 2)) *
        (calibration.fullTurn * (3 * (dyadicRadius highGrade : ℝ)))) *
      (openPeriodicVelocityL1MassOn solution t
          (frequencyDyadicGradeSlice lowGrade) *
        (Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
              (frequencyDyadicGradeSlice highGrade)) *
            Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
              (frequencyDyadicGradeSlice highGrade)) +
          2 * (Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
                (frequencyDyadicGradeSlice highGrade)) *
            Real.sqrt (openPeriodicVorticityL1SquareMassOn solution t
              (frequencyDyadicPredecessorSlice highGrade))))) := by
  have hface :=
    completePhysicalH2AdvectingLowGradeFaceMass_le_calibrated_modeProductMass
      calibration hcircle solution t lowGrade highGrade
  have hconvolution :=
    completePhysicalAdvectingLowGradeModeProductMass_le_cauchy_patterns
      solution t lowGrade highGrade
  have hratio : 0 ≤ dyadicGradeLengthRatio lowGrade highGrade := by
    unfold dyadicGradeLengthRatio
    exact div_nonneg (by positivity) (by positivity)
  have hturn : 0 ≤ calibration.fullTurn :=
    fullTurn_nonneg_from_arcRadial calibration
  have hcoefficient :
      0 ≤
        (primitiveTorusStokesScale *
          (6 * dyadicGradeLengthRatio lowGrade highGrade *
            (dyadicRadius highGrade : ℝ) ^ 2)) *
        (calibration.fullTurn * (3 * (dyadicRadius highGrade : ℝ))) := by
    exact mul_nonneg
      (mul_nonneg primitiveTorusStokesScale_pos.le
        (mul_nonneg (mul_nonneg (by norm_num) hratio) (sq_nonneg _)))
      (mul_nonneg hturn (mul_nonneg (by norm_num) (by positivity)))
  exact hface.trans (mul_le_mul_of_nonneg_left hconvolution hcoefficient)

/-! ## Kernel audit -/

#print axioms completeAdvectingLowGradePopulationEquiv
#print axioms completeTransportReceiver_fixed_advecting_injective
#print axioms sum_openPeriodicVorticityL1_mul_receiver_le_sqrt_masses
#print axioms abs_re_completePhysicalH2ExchangedTransportFace_le_calibrated_grade_product
#print axioms sum_completeAdvectingLowGradePopulation_eq_highPatterns
#print axioms sum_equalHighPopulation_modeProduct_eq_rows
#print axioms sum_transportedHighAdjacentPopulation_modeProduct_eq_rows
#print axioms sum_receiverHighAdjacentPopulation_modeProduct_eq_rows
#print axioms completePhysicalAdvectingLowGradeModeProductMass_le_cauchy_patterns
#print axioms completePhysicalH2AdvectingLowGradeFaceMass_le_calibrated_cauchy_patterns

end Soma.Holonics.Millennium.NavierStokesH2AdvectingLowGradeFaceMass
