import ElementaryHolonics.Millennium.NavierStokesPhysicalH2UniqueLowRotationPopulation
import ElementaryHolonics.Millennium.NavierStokesH2LowVelocityGradeKernel
import ElementaryHolonics.Millennium.NavierStokesH2VorticityShellDissipationBridge

/-!
# Fixed-grade majorants for the two rotated physical H2 legs

**[proved-derived; formal-checked]**  The second and third members of the unique-low cyclic
orbit have different ordered Fourier faces and different Stokes multiplier occurrences.  This
owner keeps those occurrences separate, bounds each actual low/high multiplier, and only then
passes their common nonnegative velocity-mode product through the finite closed-triad address
fibre.

The receiving frequency is reindexed injectively at every fixed advecting frequency.  Thus the
finite Cauchy receiver pays the two adjacent high shells once and preserves every ordered address.
Positive low grades then use the already proved summable calibrated low-velocity kernel; grade
zero remains an explicit finite low-frequency receiver.  No equality of rotated faces, cyclic
cancellation, infinite cofinal passage, time estimate, terminal absorption, or continuation claim
is made here.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2RotatedMajorantBound

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCalibratedTriadicFaceBound
open Soma.Holonics.Millennium.NavierStokesCompleteDyadicTriadSectorPartition
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH2AdvectingLowGradeFaceMass
open Soma.Holonics.Millennium.NavierStokesH2AdvectingLowGradePopulation
open Soma.Holonics.Millennium.NavierStokesH2AdvectingLowGradeLeverBound
open Soma.Holonics.Millennium.NavierStokesH2LowVelocityGradeKernel
open Soma.Holonics.Millennium.NavierStokesH2LowVelocitySliceConversion
open Soma.Holonics.Millennium.NavierStokesH2TriadMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesH2VorticityShellDissipationBridge
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
open Soma.Holonics.Millennium.NavierStokesPhysicalH2CurlMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesPhysicalH2UniqueLowRotationPopulation
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.Turn

/-! ## The actual ordered fixed-grade address fibre -/

/-- The two possible high grades, retained as a union rather than a cube.  At `highGrade = 0`
the predecessor slice is empty. -/
def advectingLowHighVelocityBand (highGrade : ℕ) : Finset SpatialFrequency :=
  frequencyDyadicGradeSlice highGrade ∪ frequencyDyadicPredecessorSlice highGrade

/-- Square `L¹` mass of a velocity coefficient section on a declared finite population. -/
def velocityL1SquareMassOn
    (velocityMode : SpatialFrequency → ComplexVector)
    (population : Finset SpatialFrequency) : ℝ :=
  ∑ frequency ∈ population, complexVectorL1 (velocityMode frequency) ^ 2

theorem velocityL1SquareMassOn_nonneg
    (velocityMode : SpatialFrequency → ComplexVector)
    (population : Finset SpatialFrequency) :
    0 ≤ velocityL1SquareMassOn velocityMode population := by
  exact Finset.sum_nonneg fun frequency _hfrequency ↦
    sq_nonneg (complexVectorL1 (velocityMode frequency))

/-- The complete row at one first pin.  The ambient transported cube is only a presentation;
membership still carries the full ordered closed-triad address. -/
def completeAdvectingLowVelocityRow
    (lowGrade highGrade : ℕ) (advecting : SpatialFrequency) :
    Finset SpatialFrequency :=
  (frequencyCube (dyadicRadius highGrade)).filter fun transported ↦
    (advecting, transported) ∈
      completeAdvectingLowGradePopulation lowGrade highGrade

theorem completeAdvectingLowVelocityRow_subset_highBand
    (lowGrade highGrade : ℕ) (advecting : SpatialFrequency) :
    completeAdvectingLowVelocityRow lowGrade highGrade advecting ⊆
      advectingLowHighVelocityBand highGrade := by
  intro transported htransported
  have haddress := (Finset.mem_filter.mp htransported).2
  rcases completeAdvectingLowGradePopulation_highPattern_exhaustive haddress with
      hequal | htransportedHigh | hreceiverHigh
  · apply Finset.mem_union_left
    exact (mem_frequencyDyadicGradeSlice_iff highGrade transported).mpr (by
      simpa [EqualHighPattern, transportedGrade, completeTransportTriad] using hequal.1)
  · apply Finset.mem_union_left
    exact (mem_frequencyDyadicGradeSlice_iff highGrade transported).mpr (by
      simpa [TransportedHighAdjacentPattern, transportedGrade,
        completeTransportTriad] using htransportedHigh.1)
  · apply Finset.mem_union_right
    exact (mem_frequencyDyadicPredecessorSlice_iff highGrade transported).mpr (by
      simpa [ReceiverHighAdjacentPattern, transportedGrade,
        completeTransportTriad] using hreceiverHigh.2)

theorem completeAdvectingLowVelocityRow_receiver_mem_highBand
    (lowGrade highGrade : ℕ) (advecting transported : SpatialFrequency)
    (htransported : transported ∈
      completeAdvectingLowVelocityRow lowGrade highGrade advecting) :
    completeTransportReceiver (advecting, transported) ∈
      advectingLowHighVelocityBand highGrade := by
  have haddress := (Finset.mem_filter.mp htransported).2
  rcases completeAdvectingLowGradePopulation_highPattern_exhaustive haddress with
      hequal | htransportedHigh | hreceiverHigh
  · apply Finset.mem_union_left
    exact (mem_frequencyDyadicGradeSlice_iff highGrade _).mpr (by
      simpa [EqualHighPattern, receiverGrade, completeTransportTriad] using hequal.2)
  · apply Finset.mem_union_right
    exact (mem_frequencyDyadicPredecessorSlice_iff highGrade _).mpr (by
      simpa [TransportedHighAdjacentPattern, receiverGrade,
        completeTransportTriad] using htransportedHigh.2)
  · apply Finset.mem_union_left
    exact (mem_frequencyDyadicGradeSlice_iff highGrade _).mpr (by
      simpa [ReceiverHighAdjacentPattern, receiverGrade,
        completeTransportTriad] using hreceiverHigh.1)

/-- Finite convolution Cauchy on one ordered row.  Receiver injectivity prevents collision
multiplicity from being paid twice. -/
theorem sum_velocityL1_mul_receiver_le_sqrt_masses
    (velocityMode : SpatialFrequency → ComplexVector)
    (advecting : SpatialFrequency) (row source target : Finset SpatialFrequency)
    (hsource : row ⊆ source)
    (htarget : ∀ transported ∈ row,
      completeTransportReceiver (advecting, transported) ∈ target) :
    (∑ transported ∈ row,
        complexVectorL1 (velocityMode transported) *
          complexVectorL1
            (velocityMode (completeTransportReceiver (advecting, transported)))) ≤
      Real.sqrt (velocityL1SquareMassOn velocityMode source) *
        Real.sqrt (velocityL1SquareMassOn velocityMode target) := by
  let modeL1 : SpatialFrequency → ℝ := fun frequency ↦
    complexVectorL1 (velocityMode frequency)
  let receiver : SpatialFrequency → SpatialFrequency := fun transported ↦
    completeTransportReceiver (advecting, transported)
  have hleft :
      (∑ transported ∈ row, modeL1 transported ^ 2) ≤
        ∑ transported ∈ source, modeL1 transported ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsource
      (fun frequency _hfrequency _hnot ↦ sq_nonneg (modeL1 frequency))
  have himage : row.image receiver ⊆ target := by
    intro receiving hreceiving
    rcases Finset.mem_image.mp hreceiving with ⟨transported, htransported, rfl⟩
    exact htarget transported htransported
  have hinjective : Set.InjOn receiver (row : Set SpatialFrequency) :=
    (completeTransportReceiver_fixed_advecting_injective advecting).injOn
  have hright :
      (∑ transported ∈ row, modeL1 (receiver transported) ^ 2) ≤
        ∑ receiving ∈ target, modeL1 receiving ^ 2 := by
    calc
      (∑ transported ∈ row, modeL1 (receiver transported) ^ 2) =
          ∑ receiving ∈ row.image receiver, modeL1 receiving ^ 2 :=
        (Finset.sum_image
          (f := fun receiving ↦ modeL1 receiving ^ 2) hinjective).symm
      _ ≤ ∑ receiving ∈ target, modeL1 receiving ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg himage
          (fun frequency _hfrequency _hnot ↦ sq_nonneg (modeL1 frequency))
  calc
    (∑ transported ∈ row,
        modeL1 transported * modeL1 (receiver transported)) ≤
      Real.sqrt (∑ transported ∈ row, modeL1 transported ^ 2) *
        Real.sqrt (∑ transported ∈ row, modeL1 (receiver transported) ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt row modeL1 (modeL1 ∘ receiver)
    _ ≤ Real.sqrt (∑ transported ∈ source, modeL1 transported ^ 2) *
        Real.sqrt (∑ receiving ∈ target, modeL1 receiving ^ 2) := by
      exact mul_le_mul (Real.sqrt_le_sqrt hleft) (Real.sqrt_le_sqrt hright)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt (velocityL1SquareMassOn velocityMode source) *
        Real.sqrt (velocityL1SquareMassOn velocityMode target) := rfl

theorem sum_completeAdvectingLowVelocityRow_le_highBand
    (velocityMode : SpatialFrequency → ComplexVector)
    (lowGrade highGrade : ℕ) (advecting : SpatialFrequency) :
    (∑ transported ∈ completeAdvectingLowVelocityRow
        lowGrade highGrade advecting,
        complexVectorL1 (velocityMode transported) *
          complexVectorL1
            (velocityMode (completeTransportReceiver (advecting, transported)))) ≤
      Real.sqrt (velocityL1SquareMassOn velocityMode
          (advectingLowHighVelocityBand highGrade)) *
        Real.sqrt (velocityL1SquareMassOn velocityMode
          (advectingLowHighVelocityBand highGrade)) := by
  exact sum_velocityL1_mul_receiver_le_sqrt_masses velocityMode advecting
    (completeAdvectingLowVelocityRow lowGrade highGrade advecting)
    (advectingLowHighVelocityBand highGrade)
    (advectingLowHighVelocityBand highGrade)
    (completeAdvectingLowVelocityRow_subset_highBand lowGrade highGrade advecting)
    (completeAdvectingLowVelocityRow_receiver_mem_highBand
      lowGrade highGrade advecting)

/-- The common nonnegative mode product of the two differently oriented rotated faces.  This is
an address population, not a quotient by its three frequencies. -/
def completeAdvectingLowVelocityModeProductMass
    (velocityMode : SpatialFrequency → ComplexVector)
    (lowGrade highGrade : ℕ) : ℝ :=
  ∑ address ∈ completeAdvectingLowGradePopulation lowGrade highGrade,
    complexVectorL1 (velocityMode address.1) *
      complexVectorL1 (velocityMode address.2) *
      complexVectorL1 (velocityMode (completeTransportReceiver address))

theorem completeAdvectingLowVelocityModeProductMass_eq_rows
    (velocityMode : SpatialFrequency → ComplexVector)
    (lowGrade highGrade : ℕ) :
    completeAdvectingLowVelocityModeProductMass velocityMode lowGrade highGrade =
      ∑ advecting ∈ frequencyDyadicGradeSlice lowGrade,
        complexVectorL1 (velocityMode advecting) *
          ∑ transported ∈ completeAdvectingLowVelocityRow
              lowGrade highGrade advecting,
            complexVectorL1 (velocityMode transported) *
              complexVectorL1
                (velocityMode (completeTransportReceiver (advecting, transported))) := by
  classical
  unfold completeAdvectingLowVelocityModeProductMass
    completeAdvectingLowVelocityRow completeAdvectingLowGradePopulation
  rw [Finset.sum_filter, Finset.product_eq_sprod,
    Finset.sum_product]
  apply Finset.sum_congr rfl
  intro advecting hadvecting
  rw [Finset.mul_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro transported htransported
  by_cases haddress :
      AdvectingLowSector (completeTransportTriad (advecting, transported)) ∧
        max (transportedGrade (completeTransportTriad (advecting, transported)))
          (receiverGrade (completeTransportTriad (advecting, transported))) = highGrade
  · simp [haddress, hadvecting, htransported, mul_assoc]
  · simp [haddress, hadvecting, htransported]

theorem completeAdvectingLowVelocityModeProductMass_le_cauchyBand
    (velocityMode : SpatialFrequency → ComplexVector)
    (lowGrade highGrade : ℕ) :
    completeAdvectingLowVelocityModeProductMass velocityMode lowGrade highGrade ≤
      (∑ advecting ∈ frequencyDyadicGradeSlice lowGrade,
        complexVectorL1 (velocityMode advecting)) *
      (Real.sqrt (velocityL1SquareMassOn velocityMode
          (advectingLowHighVelocityBand highGrade)) *
        Real.sqrt (velocityL1SquareMassOn velocityMode
          (advectingLowHighVelocityBand highGrade))) := by
  rw [completeAdvectingLowVelocityModeProductMass_eq_rows]
  calc
    _ ≤ ∑ advecting ∈ frequencyDyadicGradeSlice lowGrade,
        complexVectorL1 (velocityMode advecting) *
          (Real.sqrt (velocityL1SquareMassOn velocityMode
              (advectingLowHighVelocityBand highGrade)) *
            Real.sqrt (velocityL1SquareMassOn velocityMode
              (advectingLowHighVelocityBand highGrade))) := by
      apply Finset.sum_le_sum
      intro advecting _hadvecting
      exact mul_le_mul_of_nonneg_left
        (sum_completeAdvectingLowVelocityRow_le_highBand
          velocityMode lowGrade highGrade advecting)
        (complexVectorL1_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

/-! ## Distinct second/third Stokes coefficients -/

/-- Common cube majorant of either actual low/high completed Stokes coefficient. -/
def rotatedLowPinStokesCoefficient (highGrade : ℕ) : ℝ :=
  (primitiveTorusStokesScale *
      (6 * (dyadicRadius highGrade : ℝ) ^ 2)) *
    (1 + primitiveTorusStokesScale *
      (6 * (dyadicRadius highGrade : ℝ) ^ 2))

/-- The complete coefficient after the least-pin derivative and turn calibration remain
separate occurrences. -/
def rotatedLowPinGradeCoefficient
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (lowGrade highGrade : ℕ) : ℝ :=
  rotatedLowPinStokesCoefficient highGrade *
    (calibration.fullTurn *
      (3 * dyadicGradeLengthRatio lowGrade highGrade *
        (dyadicRadius highGrade : ℝ)))

theorem rotatedLowPinStokesCoefficient_nonneg (highGrade : ℕ) :
    0 ≤ rotatedLowPinStokesCoefficient highGrade := by
  unfold rotatedLowPinStokesCoefficient
  exact mul_nonneg
    (mul_nonneg primitiveTorusStokesScale_pos.le
      (mul_nonneg (by norm_num) (sq_nonneg _)))
    (by
      have hscale : 0 ≤ primitiveTorusStokesScale *
          (6 * (dyadicRadius highGrade : ℝ) ^ 2) :=
        mul_nonneg primitiveTorusStokesScale_pos.le
          (mul_nonneg (by norm_num) (sq_nonneg _))
      linarith)

theorem rotatedLowPinGradeCoefficient_nonneg
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (lowGrade highGrade : ℕ) :
    0 ≤ rotatedLowPinGradeCoefficient calibration lowGrade highGrade := by
  have hratio : 0 ≤ dyadicGradeLengthRatio lowGrade highGrade := by
    unfold dyadicGradeLengthRatio
    exact div_nonneg (by positivity) (by positivity)
  unfold rotatedLowPinGradeCoefficient
  exact mul_nonneg (rotatedLowPinStokesCoefficient_nonneg highGrade)
    (mul_nonneg (fullTurn_nonneg_from_arcRadial calibration)
      (mul_nonneg (mul_nonneg (by norm_num) hratio) (by positivity)))

theorem norm_lowHighCompletedStokesCoefficient_le
    (highGrade : ℕ) (left right : SpatialFrequency)
    (hleft : left ∈ frequencyCube (dyadicRadius highGrade))
    (hright : right ∈ frequencyCube (dyadicRadius highGrade)) :
    ‖(((torusStokesEigenvalue left - torusStokesEigenvalue right) *
        (1 + torusStokesEigenvalue left + torusStokesEigenvalue right) : ℝ) : ℂ)‖ ≤
      rotatedLowPinStokesCoefficient highGrade := by
  have hleftBound :=
    torusStokesEigenvalue_le_primitiveScale_three_mul_cubeRadius_sq hleft
  have hrightBound :=
    torusStokesEigenvalue_le_primitiveScale_three_mul_cubeRadius_sq hright
  have hleftNonneg := torusStokesEigenvalue_nonneg left
  have hrightNonneg := torusStokesEigenvalue_nonneg right
  have hdiff :
      |torusStokesEigenvalue left - torusStokesEigenvalue right| ≤
        primitiveTorusStokesScale *
          (6 * (dyadicRadius highGrade : ℝ) ^ 2) := by
    calc
      |_ - _| ≤ |torusStokesEigenvalue left| +
          |torusStokesEigenvalue right| := abs_sub _ _
      _ = torusStokesEigenvalue left + torusStokesEigenvalue right := by
        rw [abs_of_nonneg hleftNonneg, abs_of_nonneg hrightNonneg]
      _ ≤ primitiveTorusStokesScale *
          (6 * (dyadicRadius highGrade : ℝ) ^ 2) := by
        nlinarith [primitiveTorusStokesScale_pos]
  have hsum :
      1 + torusStokesEigenvalue left + torusStokesEigenvalue right ≤
        1 + primitiveTorusStokesScale *
          (6 * (dyadicRadius highGrade : ℝ) ^ 2) := by
    nlinarith [primitiveTorusStokesScale_pos]
  have hsumNonneg :
      0 ≤ 1 + torusStokesEigenvalue left + torusStokesEigenvalue right := by
    linarith
  have hdiffMajorNonneg :
      0 ≤ primitiveTorusStokesScale *
        (6 * (dyadicRadius highGrade : ℝ) ^ 2) :=
    mul_nonneg primitiveTorusStokesScale_pos.le
      (mul_nonneg (by norm_num) (sq_nonneg _))
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hsumNonneg]
  unfold rotatedLowPinStokesCoefficient
  exact mul_le_mul hdiff hsum hsumNonneg hdiffMajorNonneg

/-! ## Uniform payment of the actual high velocity band -/

/-- A mode in the high grade or its predecessor sees the displayed high radius at most four
times beyond its own inner cube.  The inhomogeneous `1` retains the initial-grade boundary. -/
theorem dyadicRadius_sq_le_sixteen_mul_one_add_frequencySquared_of_mem_highBand
    (highGrade : ℕ) (hpositive : 0 < highGrade)
    (frequency : SpatialFrequency)
    (hfrequency : frequency ∈ advectingLowHighVelocityBand highGrade) :
    (dyadicRadius highGrade : ℝ) ^ 2 ≤
      16 * (1 + frequencySquared frequency) := by
  have hfrequencySquared : 0 ≤ frequencySquared frequency := by
    unfold frequencySquared
    exact Finset.sum_nonneg fun coordinate _hcoordinate ↦
      sq_nonneg (frequency coordinate : ℝ)
  cases highGrade with
  | zero => omega
  | succ predecessorGrade =>
      cases predecessorGrade with
      | zero =>
          norm_num [dyadicRadius]
          linarith
      | succ innerGrade =>
          have hgrade :
              frequencyDyadicGrade frequency = innerGrade + 2 ∨
                frequencyDyadicGrade frequency + 1 = innerGrade + 2 := by
            rcases Finset.mem_union.mp hfrequency with hcurrent | hpredecessor
            · left
              simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                (mem_frequencyDyadicGradeSlice_iff
                  (innerGrade + 2) frequency).mp hcurrent
            · right
              simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                (mem_frequencyDyadicPredecessorSlice_iff
                  (innerGrade + 2) frequency).mp hpredecessor
          have hnotInner :
              frequency ∉ frequencyCube (dyadicRadius innerGrade) := by
            intro hinner
            have hle :=
              (frequencyDyadicGrade_le_iff_mem frequency innerGrade).mpr hinner
            rcases hgrade with hgrade | hgrade <;> omega
          have houtside : ∃ coordinate : Fin 3,
              frequency coordinate < -(dyadicRadius innerGrade : ℤ) ∨
                (dyadicRadius innerGrade : ℤ) < frequency coordinate := by
            rw [mem_frequencyCube_iff] at hnotInner
            push Not at hnotInner
            rcases hnotInner with ⟨coordinate, houtside⟩
            refine ⟨coordinate, ?_⟩
            by_cases hlower :
                -(dyadicRadius innerGrade : ℤ) ≤ frequency coordinate
            · exact Or.inr (houtside hlower)
            · exact Or.inl (by omega)
          rcases houtside with ⟨coordinate, hleft | hright⟩
          · have hleftReal :
                (frequency coordinate : ℝ) < -(dyadicRadius innerGrade : ℝ) := by
              exact_mod_cast hleft
            have hcoordinate :
                (dyadicRadius innerGrade : ℝ) ^ 2 ≤
                  (frequency coordinate : ℝ) ^ 2 := by
              nlinarith [sq_nonneg
                ((frequency coordinate : ℝ) + (dyadicRadius innerGrade : ℝ))]
            have hcoordinateSum :
                (frequency coordinate : ℝ) ^ 2 ≤ frequencySquared frequency := by
              unfold frequencySquared
              exact Finset.single_le_sum
                (fun index _hindex ↦ sq_nonneg (frequency index : ℝ))
                (Finset.mem_univ coordinate)
            have hradius :
                (dyadicRadius (innerGrade + 2) : ℝ) =
                  4 * (dyadicRadius innerGrade : ℝ) := by
              simp [dyadicRadius, pow_succ]
              ring
            rw [hradius]
            nlinarith
          · have hrightReal :
                (dyadicRadius innerGrade : ℝ) < (frequency coordinate : ℝ) := by
              exact_mod_cast hright
            have hcoordinate :
                (dyadicRadius innerGrade : ℝ) ^ 2 ≤
                  (frequency coordinate : ℝ) ^ 2 := by
              nlinarith [sq_nonneg
                ((frequency coordinate : ℝ) - (dyadicRadius innerGrade : ℝ))]
            have hcoordinateSum :
                (frequency coordinate : ℝ) ^ 2 ≤ frequencySquared frequency := by
              unfold frequencySquared
              exact Finset.single_le_sum
                (fun index _hindex ↦ sq_nonneg (frequency index : ℝ))
                (Finset.mem_univ coordinate)
            have hradius :
                (dyadicRadius (innerGrade + 2) : ℝ) =
                  4 * (dyadicRadius innerGrade : ℝ) := by
              simp [dyadicRadius, pow_succ]
              ring
            rw [hradius]
            nlinarith

/-- Grade-independent calibration which rebases the cube coefficient into the native order-three
Sobolev weight.  Its scale is the primitive torus character, not an external literal. -/
def rotatedHighBandH3Calibration : ℝ :=
  (96 * (1 + primitiveTorusStokesScale)) *
    (1 + 96 * (1 + primitiveTorusStokesScale))

theorem rotatedHighBandH3Calibration_nonneg :
    0 ≤ rotatedHighBandH3Calibration := by
  unfold rotatedHighBandH3Calibration
  have hscale := primitiveTorusStokesScale_pos
  exact mul_nonneg
    (mul_nonneg (by norm_num) (by linarith))
    (by nlinarith)

theorem rotatedLowPinStokesCoefficient_le_highBandH3Weight
    (highGrade : ℕ) (hpositive : 0 < highGrade)
    (frequency : SpatialFrequency)
    (hfrequency : frequency ∈ advectingLowHighVelocityBand highGrade) :
    rotatedLowPinStokesCoefficient highGrade ≤
      rotatedHighBandH3Calibration * periodicSobolevWeight 3 frequency := by
  let scale := primitiveTorusStokesScale
  let radiusSquare := (dyadicRadius highGrade : ℝ) ^ 2
  let eigenvalue := torusStokesEigenvalue frequency
  let calibration := 96 * (1 + scale)
  have hscale : 0 ≤ scale := primitiveTorusStokesScale_pos.le
  have hradiusSquare : 0 ≤ radiusSquare := sq_nonneg _
  have heigenvalue : 0 ≤ eigenvalue := torusStokesEigenvalue_nonneg frequency
  have hcalibration : 0 ≤ calibration := by
    dsimp [calibration]
    positivity
  have hradius :=
    dyadicRadius_sq_le_sixteen_mul_one_add_frequencySquared_of_mem_highBand
      highGrade hpositive frequency hfrequency
  have heigenvalueIdentity :
      eigenvalue = scale * frequencySquared frequency := by
    exact torusStokesEigenvalue_eq_primitiveScale_mul_frequencySquared frequency
  have hlever :
      6 * scale * radiusSquare ≤ calibration * (1 + eigenvalue) := by
    dsimp [radiusSquare, scale] at hradius ⊢
    dsimp [calibration, eigenvalue, scale]
    rw [torusStokesEigenvalue_eq_primitiveScale_mul_frequencySquared]
    nlinarith [mul_nonneg primitiveTorusStokesScale_pos.le
      (show 0 ≤ frequencySquared frequency by
        unfold frequencySquared
        exact Finset.sum_nonneg fun coordinate _hcoordinate ↦ sq_nonneg _)]
  have honeAddLever :
      1 + 6 * scale * radiusSquare ≤
        (1 + calibration) * (1 + eigenvalue) := by
    nlinarith [mul_nonneg hcalibration heigenvalue]
  have honeAddEigenvalue : 1 ≤ 1 + eigenvalue := by linarith
  unfold rotatedLowPinStokesCoefficient rotatedHighBandH3Calibration
    periodicSobolevWeight
  change (scale * (6 * radiusSquare)) * (1 + scale * (6 * radiusSquare)) ≤
    (calibration * (1 + calibration)) * (1 + eigenvalue) ^ 3
  calc
    (scale * (6 * radiusSquare)) * (1 + scale * (6 * radiusSquare)) =
        (6 * scale * radiusSquare) * (1 + 6 * scale * radiusSquare) := by ring
    _ ≤ (calibration * (1 + eigenvalue)) *
        ((1 + calibration) * (1 + eigenvalue)) :=
      mul_le_mul hlever honeAddLever
        (by positivity) (mul_nonneg hcalibration (by linarith))
    _ = (calibration * (1 + calibration)) * (1 + eigenvalue) ^ 2 := by ring
    _ ≤ (calibration * (1 + calibration)) * (1 + eigenvalue) ^ 3 := by
      exact mul_le_mul_of_nonneg_left
        (by nlinarith [sq_nonneg (1 + eigenvalue)])
        (mul_nonneg hcalibration (by linarith))

/-- The completed high coefficient and its actual two-shell velocity square receiver are paid by
the native `H3` state with no velocity/vorticity chart identification.  The imported bridge is
used only after the coefficient has been rebased into the actual velocity Sobolev weight. -/
theorem rotatedLowPinStokesCoefficient_mul_velocityL1SquareMassOn_highBand_le_nativeH3
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (highGrade : ℕ) (hpositive : 0 < highGrade) :
    rotatedLowPinStokesCoefficient highGrade *
        velocityL1SquareMassOn (openPeriodicVelocityFourierMode solution t)
          (advectingLowHighVelocityBand highGrade) ≤
      9 * rotatedHighBandH3Calibration *
        ‖openVelocityWeightedH3State solution t‖ ^ 2 := by
  let population := advectingLowHighVelocityBand highGrade
  let mode := openPeriodicVelocityFourierMode solution t
  have hpoint (frequency : SpatialFrequency) (hfrequency : frequency ∈ population) :
      rotatedLowPinStokesCoefficient highGrade *
          complexVectorL1 (mode frequency) ^ 2 ≤
        (3 * rotatedHighBandH3Calibration) *
          (periodicSobolevWeight 3 frequency *
            (∑ component : Fin 3, ‖mode frequency component‖ ^ 2)) := by
    have hcoefficient :=
      rotatedLowPinStokesCoefficient_le_highBandH3Weight
        highGrade hpositive frequency hfrequency
    have hl1 := complexVectorL1_sq_le_three_mul_sum_norm_sq (mode frequency)
    have hsum : 0 ≤ ∑ component : Fin 3, ‖mode frequency component‖ ^ 2 :=
      Finset.sum_nonneg fun component _hcomponent ↦ sq_nonneg _
    calc
      rotatedLowPinStokesCoefficient highGrade *
          complexVectorL1 (mode frequency) ^ 2 ≤
        rotatedLowPinStokesCoefficient highGrade *
          (3 * ∑ component : Fin 3, ‖mode frequency component‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hl1
          (rotatedLowPinStokesCoefficient_nonneg highGrade)
      _ ≤ (rotatedHighBandH3Calibration * periodicSobolevWeight 3 frequency) *
          (3 * ∑ component : Fin 3, ‖mode frequency component‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hcoefficient
          (mul_nonneg (by norm_num) hsum)
      _ = (3 * rotatedHighBandH3Calibration) *
          (periodicSobolevWeight 3 frequency *
            (∑ component : Fin 3, ‖mode frequency component‖ ^ 2)) := by ring
  have hfinite := finite_velocityH3SquareMass_le_native solution t population
  unfold velocityL1SquareMassOn
  rw [Finset.mul_sum]
  calc
    (∑ frequency ∈ population,
        rotatedLowPinStokesCoefficient highGrade *
          complexVectorL1 (mode frequency) ^ 2) ≤
      ∑ frequency ∈ population,
        (3 * rotatedHighBandH3Calibration) *
          (periodicSobolevWeight 3 frequency *
            (∑ component : Fin 3, ‖mode frequency component‖ ^ 2)) := by
      exact Finset.sum_le_sum fun frequency hfrequency ↦ hpoint frequency hfrequency
    _ = (3 * rotatedHighBandH3Calibration) *
        (∑ frequency ∈ population,
          periodicSobolevWeight 3 frequency *
            (∑ component : Fin 3, ‖mode frequency component‖ ^ 2)) := by
      rw [Finset.mul_sum]
    _ ≤ (3 * rotatedHighBandH3Calibration) *
        (3 * ‖openVelocityWeightedH3State solution t‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left hfinite
        (mul_nonneg (by norm_num) rotatedHighBandH3Calibration_nonneg)
    _ = 9 * rotatedHighBandH3Calibration *
        ‖openVelocityWeightedH3State solution t‖ ^ 2 := by ring

/-! ## The two actual fixed-grade face populations -/

def completeAdvectingLowSecondGradeRatioPopulation
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (velocityMode : SpatialFrequency → ComplexVector)
    (lowGrade highGrade : ℕ) : ℝ :=
  ∑ address ∈ completeAdvectingLowGradePopulation lowGrade highGrade,
    advectingLowSecondGradeRatioFace calibration velocityMode address

def completeAdvectingLowThirdGradeRatioPopulation
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (velocityMode : SpatialFrequency → ComplexVector)
    (lowGrade highGrade : ℕ) : ℝ :=
  ∑ address ∈ completeAdvectingLowGradePopulation lowGrade highGrade,
    advectingLowThirdGradeRatioFace calibration velocityMode address

theorem advectingLowSecondGradeRatioFace_le_fixedGradeCoefficient
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (velocityMode : SpatialFrequency → ComplexVector)
    {lowGrade highGrade : ℕ} (address : CompleteTransportAddress)
    (haddress : address ∈ completeAdvectingLowGradePopulation lowGrade highGrade) :
    advectingLowSecondGradeRatioFace calibration velocityMode address ≤
      rotatedLowPinGradeCoefficient calibration lowGrade highGrade *
        (complexVectorL1 (velocityMode address.1) *
          complexVectorL1 (velocityMode address.2) *
          complexVectorL1
            (velocityMode (completeTransportReceiver address))) := by
  rcases (mem_completeAdvectingLowGradePopulation_iff address).mp haddress with
    ⟨hsector, hlow, hhigh⟩
  have hlowHigh : lowGrade < highGrade := by
    rw [← hlow, ← hhigh]
    exact lt_of_lt_of_le hsector.1 (Nat.le_max_left _ _)
  have hlowLe : frequencyDyadicGrade address.1 ≤ highGrade := by
    change advectingGrade (completeTransportTriad address) ≤ highGrade
    rw [hlow]
    exact Nat.le_of_lt hlowHigh
  have hadvecting : address.1 ∈ frequencyCube (dyadicRadius highGrade) :=
    (frequencyDyadicGrade_le_iff_mem address.1 highGrade).mp hlowLe
  have hreceiverGrade :
      receiverGrade (completeTransportTriad address) ≤ highGrade :=
    hhigh.symm ▸ Nat.le_max_right _ _
  have hreceiver : completeTransportReceiver address ∈
      frequencyCube (dyadicRadius highGrade) :=
    (frequencyDyadicGrade_le_iff_mem _ highGrade).mp hreceiverGrade
  have hcoefficient := norm_lowHighCompletedStokesCoefficient_le highGrade
    (completeTransportReceiver address) address.1 hreceiver hadvecting
  have hturn := fullTurn_nonneg_from_arcRadial calibration
  have hratio : 0 ≤ dyadicGradeLengthRatio lowGrade highGrade := by
    unfold dyadicGradeLengthRatio
    exact div_nonneg (by positivity) (by positivity)
  dsimp only [advectingLowSecondGradeRatioFace]
  unfold rotatedLowPinGradeCoefficient
  rw [show advectingGrade (completeTransportTriad address) = lowGrade from hlow,
    show advectingLowHighGrade (completeTransportTriad address) = highGrade by
      exact hhigh]
  have hrest : 0 ≤
      calibration.fullTurn *
          (3 * dyadicGradeLengthRatio lowGrade highGrade *
            (dyadicRadius highGrade : ℝ)) *
        complexVectorL1 (velocityMode address.2) *
        complexVectorL1 (velocityMode address.1) *
        complexVectorL1 (velocityMode (completeTransportReceiver address)) := by
    have hderivative : 0 ≤
        3 * dyadicGradeLengthRatio lowGrade highGrade *
          (dyadicRadius highGrade : ℝ) :=
      mul_nonneg (mul_nonneg (by norm_num) hratio) (by positivity)
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hturn hderivative)
          (complexVectorL1_nonneg _))
        (complexVectorL1_nonneg _))
      (complexVectorL1_nonneg _)
  calc
    _ ≤ rotatedLowPinStokesCoefficient highGrade *
        (calibration.fullTurn *
          (3 * dyadicGradeLengthRatio lowGrade highGrade *
            (dyadicRadius highGrade : ℝ)) *
          complexVectorL1 (velocityMode address.2) *
          complexVectorL1 (velocityMode address.1) *
          complexVectorL1 (velocityMode (completeTransportReceiver address))) :=
      mul_le_mul_of_nonneg_right hcoefficient hrest
    _ = _ := by ring

theorem advectingLowThirdGradeRatioFace_le_fixedGradeCoefficient
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (velocityMode : SpatialFrequency → ComplexVector)
    {lowGrade highGrade : ℕ} (address : CompleteTransportAddress)
    (haddress : address ∈ completeAdvectingLowGradePopulation lowGrade highGrade) :
    advectingLowThirdGradeRatioFace calibration velocityMode address ≤
      rotatedLowPinGradeCoefficient calibration lowGrade highGrade *
        (complexVectorL1 (velocityMode address.1) *
          complexVectorL1 (velocityMode address.2) *
          complexVectorL1
            (velocityMode (completeTransportReceiver address))) := by
  rcases (mem_completeAdvectingLowGradePopulation_iff address).mp haddress with
    ⟨hsector, hlow, hhigh⟩
  have hlowHigh : lowGrade < highGrade := by
    rw [← hlow, ← hhigh]
    exact lt_of_lt_of_le hsector.1 (Nat.le_max_left _ _)
  have hlowLe : frequencyDyadicGrade address.1 ≤ highGrade := by
    change advectingGrade (completeTransportTriad address) ≤ highGrade
    rw [hlow]
    exact Nat.le_of_lt hlowHigh
  have hadvecting : address.1 ∈ frequencyCube (dyadicRadius highGrade) :=
    (frequencyDyadicGrade_le_iff_mem address.1 highGrade).mp hlowLe
  have htransportedGrade :
      transportedGrade (completeTransportTriad address) ≤ highGrade :=
    hhigh.symm ▸ Nat.le_max_left _ _
  have htransported : address.2 ∈ frequencyCube (dyadicRadius highGrade) :=
    (frequencyDyadicGrade_le_iff_mem _ highGrade).mp htransportedGrade
  have hcoefficient := norm_lowHighCompletedStokesCoefficient_le highGrade
    address.1 address.2 hadvecting htransported
  have hturn := fullTurn_nonneg_from_arcRadial calibration
  have hratio : 0 ≤ dyadicGradeLengthRatio lowGrade highGrade := by
    unfold dyadicGradeLengthRatio
    exact div_nonneg (by positivity) (by positivity)
  dsimp only [advectingLowThirdGradeRatioFace]
  unfold rotatedLowPinGradeCoefficient
  rw [show advectingGrade (completeTransportTriad address) = lowGrade from hlow,
    show advectingLowHighGrade (completeTransportTriad address) = highGrade by
      exact hhigh]
  have hrest : 0 ≤
      calibration.fullTurn *
          (3 * dyadicGradeLengthRatio lowGrade highGrade *
            (dyadicRadius highGrade : ℝ)) *
        complexVectorL1 (velocityMode (completeTransportReceiver address)) *
        complexVectorL1 (velocityMode address.1) *
        complexVectorL1 (velocityMode address.2) := by
    have hderivative : 0 ≤
        3 * dyadicGradeLengthRatio lowGrade highGrade *
          (dyadicRadius highGrade : ℝ) :=
      mul_nonneg (mul_nonneg (by norm_num) hratio) (by positivity)
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hturn hderivative)
          (complexVectorL1_nonneg _))
        (complexVectorL1_nonneg _))
      (complexVectorL1_nonneg _)
  calc
    _ ≤ rotatedLowPinStokesCoefficient highGrade *
        (calibration.fullTurn *
          (3 * dyadicGradeLengthRatio lowGrade highGrade *
            (dyadicRadius highGrade : ℝ)) *
          complexVectorL1 (velocityMode (completeTransportReceiver address)) *
          complexVectorL1 (velocityMode address.1) *
          complexVectorL1 (velocityMode address.2)) :=
      mul_le_mul_of_nonneg_right hcoefficient hrest
    _ = _ := by ring

theorem completeAdvectingLowSecondGradeRatioPopulation_le_modeProduct
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (velocityMode : SpatialFrequency → ComplexVector)
    (lowGrade highGrade : ℕ) :
    completeAdvectingLowSecondGradeRatioPopulation calibration velocityMode
        lowGrade highGrade ≤
      rotatedLowPinGradeCoefficient calibration lowGrade highGrade *
        completeAdvectingLowVelocityModeProductMass velocityMode lowGrade highGrade := by
  unfold completeAdvectingLowSecondGradeRatioPopulation
    completeAdvectingLowVelocityModeProductMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro address haddress
  exact advectingLowSecondGradeRatioFace_le_fixedGradeCoefficient
    calibration velocityMode address haddress

theorem completeAdvectingLowThirdGradeRatioPopulation_le_modeProduct
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (velocityMode : SpatialFrequency → ComplexVector)
    (lowGrade highGrade : ℕ) :
    completeAdvectingLowThirdGradeRatioPopulation calibration velocityMode
        lowGrade highGrade ≤
      rotatedLowPinGradeCoefficient calibration lowGrade highGrade *
        completeAdvectingLowVelocityModeProductMass velocityMode lowGrade highGrade := by
  unfold completeAdvectingLowThirdGradeRatioPopulation
    completeAdvectingLowVelocityModeProductMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro address haddress
  exact advectingLowThirdGradeRatioFace_le_fixedGradeCoefficient
    calibration velocityMode address haddress

theorem completeAdvectingLowSecondGradeRatioPopulation_le_cauchyBand
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (velocityMode : SpatialFrequency → ComplexVector)
    (lowGrade highGrade : ℕ) :
    completeAdvectingLowSecondGradeRatioPopulation calibration velocityMode
        lowGrade highGrade ≤
      rotatedLowPinGradeCoefficient calibration lowGrade highGrade *
        ((∑ advecting ∈ frequencyDyadicGradeSlice lowGrade,
            complexVectorL1 (velocityMode advecting)) *
          (Real.sqrt (velocityL1SquareMassOn velocityMode
              (advectingLowHighVelocityBand highGrade)) *
            Real.sqrt (velocityL1SquareMassOn velocityMode
              (advectingLowHighVelocityBand highGrade)))) := by
  exact (completeAdvectingLowSecondGradeRatioPopulation_le_modeProduct
      calibration velocityMode lowGrade highGrade).trans
    (mul_le_mul_of_nonneg_left
      (completeAdvectingLowVelocityModeProductMass_le_cauchyBand
        velocityMode lowGrade highGrade)
      (rotatedLowPinGradeCoefficient_nonneg calibration lowGrade highGrade))

theorem completeAdvectingLowThirdGradeRatioPopulation_le_cauchyBand
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (velocityMode : SpatialFrequency → ComplexVector)
    (lowGrade highGrade : ℕ) :
    completeAdvectingLowThirdGradeRatioPopulation calibration velocityMode
        lowGrade highGrade ≤
      rotatedLowPinGradeCoefficient calibration lowGrade highGrade *
        ((∑ advecting ∈ frequencyDyadicGradeSlice lowGrade,
            complexVectorL1 (velocityMode advecting)) *
          (Real.sqrt (velocityL1SquareMassOn velocityMode
              (advectingLowHighVelocityBand highGrade)) *
            Real.sqrt (velocityL1SquareMassOn velocityMode
              (advectingLowHighVelocityBand highGrade)))) := by
  exact (completeAdvectingLowThirdGradeRatioPopulation_le_modeProduct
      calibration velocityMode lowGrade highGrade).trans
    (mul_le_mul_of_nonneg_left
      (completeAdvectingLowVelocityModeProductMass_le_cauchyBand
        velocityMode lowGrade highGrade)
      (rotatedLowPinGradeCoefficient_nonneg calibration lowGrade highGrade))

/-! ## The actual finite-cube grade fibres -/

def finitePhysicalH2AdvectingLowGradeAperture
    (radius lowGrade highGrade : ℕ) : Finset CompleteTransportAddress := by
  classical
  exact (finitePhysicalH2AdvectingLowAperture radius).filter fun address ↦
    advectingGrade (completeTransportTriad address) = lowGrade ∧
      advectingLowHighGrade (completeTransportTriad address) = highGrade

theorem finitePhysicalH2AdvectingLowGradeAperture_subset_complete
    (radius lowGrade highGrade : ℕ) :
    finitePhysicalH2AdvectingLowGradeAperture radius lowGrade highGrade ⊆
      completeAdvectingLowGradePopulation lowGrade highGrade := by
  classical
  intro address haddress
  rcases Finset.mem_filter.mp haddress with ⟨hfinite, hlow, hhigh⟩
  have hsector := (Finset.mem_filter.mp hfinite).2
  exact (mem_completeAdvectingLowGradePopulation_iff address).mpr
    ⟨hsector, hlow, by simpa [advectingLowHighGrade] using hhigh⟩

def finiteAdvectingLowSecondGradeRatioPopulationAt
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (radius lowGrade highGrade : ℕ)
    (velocityMode : SpatialFrequency → ComplexVector) : ℝ :=
  ∑ address ∈ finitePhysicalH2AdvectingLowGradeAperture
      radius lowGrade highGrade,
    advectingLowSecondGradeRatioFace calibration velocityMode address

def finiteAdvectingLowThirdGradeRatioPopulationAt
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (radius lowGrade highGrade : ℕ)
    (velocityMode : SpatialFrequency → ComplexVector) : ℝ :=
  ∑ address ∈ finitePhysicalH2AdvectingLowGradeAperture
      radius lowGrade highGrade,
    advectingLowThirdGradeRatioFace calibration velocityMode address

theorem advectingLowSecondGradeRatioFace_nonneg
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) :
    0 ≤ advectingLowSecondGradeRatioFace calibration velocityMode address := by
  have hturn := fullTurn_nonneg_from_arcRadial calibration
  have hratio : 0 ≤ dyadicGradeLengthRatio
      (advectingGrade (completeTransportTriad address))
      (advectingLowHighGrade (completeTransportTriad address)) := by
    unfold dyadicGradeLengthRatio
    exact div_nonneg (by positivity) (by positivity)
  dsimp only [advectingLowSecondGradeRatioFace]
  have hderivative : 0 ≤
      3 * dyadicGradeLengthRatio
          (advectingGrade (completeTransportTriad address))
          (advectingLowHighGrade (completeTransportTriad address)) *
        (dyadicRadius
          (advectingLowHighGrade (completeTransportTriad address)) : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) hratio) (by positivity)
  exact mul_nonneg (norm_nonneg _)
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hturn hderivative)
          (complexVectorL1_nonneg _))
        (complexVectorL1_nonneg _))
      (complexVectorL1_nonneg _))

theorem advectingLowThirdGradeRatioFace_nonneg
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) :
    0 ≤ advectingLowThirdGradeRatioFace calibration velocityMode address := by
  have hturn := fullTurn_nonneg_from_arcRadial calibration
  have hratio : 0 ≤ dyadicGradeLengthRatio
      (advectingGrade (completeTransportTriad address))
      (advectingLowHighGrade (completeTransportTriad address)) := by
    unfold dyadicGradeLengthRatio
    exact div_nonneg (by positivity) (by positivity)
  dsimp only [advectingLowThirdGradeRatioFace]
  have hderivative : 0 ≤
      3 * dyadicGradeLengthRatio
          (advectingGrade (completeTransportTriad address))
          (advectingLowHighGrade (completeTransportTriad address)) *
        (dyadicRadius
          (advectingLowHighGrade (completeTransportTriad address)) : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) hratio) (by positivity)
  exact mul_nonneg (norm_nonneg _)
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hturn hderivative)
          (complexVectorL1_nonneg _))
        (complexVectorL1_nonneg _))
      (complexVectorL1_nonneg _))

theorem finiteAdvectingLowSecondGradeRatioPopulationAt_le_complete
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (radius lowGrade highGrade : ℕ)
    (velocityMode : SpatialFrequency → ComplexVector) :
    finiteAdvectingLowSecondGradeRatioPopulationAt calibration
        radius lowGrade highGrade velocityMode ≤
      completeAdvectingLowSecondGradeRatioPopulation calibration velocityMode
        lowGrade highGrade := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (finitePhysicalH2AdvectingLowGradeAperture_subset_complete
      radius lowGrade highGrade)
    (fun address _haddress _hnot ↦
      advectingLowSecondGradeRatioFace_nonneg calibration velocityMode address)

theorem finiteAdvectingLowThirdGradeRatioPopulationAt_le_complete
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (radius lowGrade highGrade : ℕ)
    (velocityMode : SpatialFrequency → ComplexVector) :
    finiteAdvectingLowThirdGradeRatioPopulationAt calibration
        radius lowGrade highGrade velocityMode ≤
      completeAdvectingLowThirdGradeRatioPopulation calibration velocityMode
        lowGrade highGrade := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (finitePhysicalH2AdvectingLowGradeAperture_subset_complete
      radius lowGrade highGrade)
    (fun address _haddress _hnot ↦
      advectingLowThirdGradeRatioFace_nonneg calibration velocityMode address)

theorem finiteAdvectingLowSecondGradeRatioPopulationAt_le_cauchyBand
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (radius lowGrade highGrade : ℕ)
    (velocityMode : SpatialFrequency → ComplexVector) :
    finiteAdvectingLowSecondGradeRatioPopulationAt calibration
        radius lowGrade highGrade velocityMode ≤
      rotatedLowPinGradeCoefficient calibration lowGrade highGrade *
        ((∑ advecting ∈ frequencyDyadicGradeSlice lowGrade,
            complexVectorL1 (velocityMode advecting)) *
          (Real.sqrt (velocityL1SquareMassOn velocityMode
              (advectingLowHighVelocityBand highGrade)) *
            Real.sqrt (velocityL1SquareMassOn velocityMode
              (advectingLowHighVelocityBand highGrade)))) := by
  exact (finiteAdvectingLowSecondGradeRatioPopulationAt_le_complete
      calibration radius lowGrade highGrade velocityMode).trans
    (completeAdvectingLowSecondGradeRatioPopulation_le_cauchyBand
      calibration velocityMode lowGrade highGrade)

theorem finiteAdvectingLowThirdGradeRatioPopulationAt_le_cauchyBand
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (radius lowGrade highGrade : ℕ)
    (velocityMode : SpatialFrequency → ComplexVector) :
    finiteAdvectingLowThirdGradeRatioPopulationAt calibration
        radius lowGrade highGrade velocityMode ≤
      rotatedLowPinGradeCoefficient calibration lowGrade highGrade *
        ((∑ advecting ∈ frequencyDyadicGradeSlice lowGrade,
            complexVectorL1 (velocityMode advecting)) *
          (Real.sqrt (velocityL1SquareMassOn velocityMode
              (advectingLowHighVelocityBand highGrade)) *
            Real.sqrt (velocityL1SquareMassOn velocityMode
              (advectingLowHighVelocityBand highGrade)))) := by
  exact (finiteAdvectingLowThirdGradeRatioPopulationAt_le_complete
      calibration radius lowGrade highGrade velocityMode).trans
    (completeAdvectingLowThirdGradeRatioPopulation_le_cauchyBand
      calibration velocityMode lowGrade highGrade)

/-! ## Exact decomposition of the named finite populations -/

def finiteAdvectingLowGradeKey (address : CompleteTransportAddress) : ℕ × ℕ :=
  (advectingGrade (completeTransportTriad address),
    advectingLowHighGrade (completeTransportTriad address))

def finitePhysicalH2AdvectingLowGradePairs (radius : ℕ) : Finset (ℕ × ℕ) :=
  (finitePhysicalH2AdvectingLowAperture radius).image finiteAdvectingLowGradeKey

theorem finiteAdvectingLowGradeKey_mem_pairs
    (radius : ℕ) (address : CompleteTransportAddress)
    (haddress : address ∈ finitePhysicalH2AdvectingLowAperture radius) :
    finiteAdvectingLowGradeKey address ∈
      finitePhysicalH2AdvectingLowGradePairs radius := by
  exact Finset.mem_image.mpr ⟨address, haddress, rfl⟩

/-- Every retained grade address is genuinely unique-low. -/
theorem finitePhysicalH2AdvectingLowGradePairs_low_lt_high
    (radius : ℕ) (grades : ℕ × ℕ)
    (hgrades : grades ∈ finitePhysicalH2AdvectingLowGradePairs radius) :
    grades.1 < grades.2 := by
  classical
  rcases Finset.mem_image.mp hgrades with ⟨address, haddress, hkey⟩
  have hsector := (Finset.mem_filter.mp haddress).2
  rw [← hkey]
  exact advectingLowSector_lowGrade_lt_highGrade hsector

/-- Exact finite fibre decomposition of the named second rotated population.  Ordered address
multiplicity is retained inside every grade fibre. -/
theorem finiteAdvectingLowSecondGradeRatioPopulation_eq_sum_gradeFibres
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (radius : ℕ) (velocityMode : SpatialFrequency → ComplexVector) :
    finiteAdvectingLowSecondGradeRatioPopulation calibration radius velocityMode =
      ∑ grades ∈ finitePhysicalH2AdvectingLowGradePairs radius,
        finiteAdvectingLowSecondGradeRatioPopulationAt calibration radius
          grades.1 grades.2 velocityMode := by
  classical
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := finitePhysicalH2AdvectingLowAperture radius)
    (t := finitePhysicalH2AdvectingLowGradePairs radius)
    (g := finiteAdvectingLowGradeKey)
    (fun address haddress ↦
      finiteAdvectingLowGradeKey_mem_pairs radius address haddress)
    (fun address ↦
      advectingLowSecondGradeRatioFace calibration velocityMode address)
  symm
  simpa [finiteAdvectingLowSecondGradeRatioPopulation,
    finiteAdvectingLowSecondGradeRatioPopulationAt,
    finitePhysicalH2AdvectingLowGradeAperture,
    finiteAdvectingLowGradeKey, Prod.ext_iff] using hfiber

/-- Exact finite fibre decomposition of the named third rotated population. -/
theorem finiteAdvectingLowThirdGradeRatioPopulation_eq_sum_gradeFibres
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (radius : ℕ) (velocityMode : SpatialFrequency → ComplexVector) :
    finiteAdvectingLowThirdGradeRatioPopulation calibration radius velocityMode =
      ∑ grades ∈ finitePhysicalH2AdvectingLowGradePairs radius,
        finiteAdvectingLowThirdGradeRatioPopulationAt calibration radius
          grades.1 grades.2 velocityMode := by
  classical
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := finitePhysicalH2AdvectingLowAperture radius)
    (t := finitePhysicalH2AdvectingLowGradePairs radius)
    (g := finiteAdvectingLowGradeKey)
    (fun address haddress ↦
      finiteAdvectingLowGradeKey_mem_pairs radius address haddress)
    (fun address ↦
      advectingLowThirdGradeRatioFace calibration velocityMode address)
  symm
  simpa [finiteAdvectingLowThirdGradeRatioPopulation,
    finiteAdvectingLowThirdGradeRatioPopulationAt,
    finitePhysicalH2AdvectingLowGradeAperture,
    finiteAdvectingLowGradeKey, Prod.ext_iff] using hfiber

/-- The actual complete finite second population is bounded by its explicit fixed-grade Cauchy
receivers. -/
theorem finiteAdvectingLowSecondGradeRatioPopulation_le_sum_gradeCauchyBands
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (radius : ℕ) (velocityMode : SpatialFrequency → ComplexVector) :
    finiteAdvectingLowSecondGradeRatioPopulation calibration radius velocityMode ≤
      ∑ grades ∈ finitePhysicalH2AdvectingLowGradePairs radius,
        rotatedLowPinGradeCoefficient calibration grades.1 grades.2 *
          ((∑ advecting ∈ frequencyDyadicGradeSlice grades.1,
              complexVectorL1 (velocityMode advecting)) *
            (Real.sqrt (velocityL1SquareMassOn velocityMode
                (advectingLowHighVelocityBand grades.2)) *
              Real.sqrt (velocityL1SquareMassOn velocityMode
                (advectingLowHighVelocityBand grades.2)))) := by
  rw [finiteAdvectingLowSecondGradeRatioPopulation_eq_sum_gradeFibres]
  apply Finset.sum_le_sum
  intro grades _hgrades
  exact finiteAdvectingLowSecondGradeRatioPopulationAt_le_cauchyBand
    calibration radius grades.1 grades.2 velocityMode

/-- The actual complete finite third population has its own fixed-grade theorem; no rotated face
is identified with the second one. -/
theorem finiteAdvectingLowThirdGradeRatioPopulation_le_sum_gradeCauchyBands
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (radius : ℕ) (velocityMode : SpatialFrequency → ComplexVector) :
    finiteAdvectingLowThirdGradeRatioPopulation calibration radius velocityMode ≤
      ∑ grades ∈ finitePhysicalH2AdvectingLowGradePairs radius,
        rotatedLowPinGradeCoefficient calibration grades.1 grades.2 *
          ((∑ advecting ∈ frequencyDyadicGradeSlice grades.1,
              complexVectorL1 (velocityMode advecting)) *
            (Real.sqrt (velocityL1SquareMassOn velocityMode
                (advectingLowHighVelocityBand grades.2)) *
              Real.sqrt (velocityL1SquareMassOn velocityMode
                (advectingLowHighVelocityBand grades.2)))) := by
  rw [finiteAdvectingLowThirdGradeRatioPopulation_eq_sum_gradeFibres]
  apply Finset.sum_le_sum
  intro grades _hgrades
  exact finiteAdvectingLowThirdGradeRatioPopulationAt_le_cauchyBand
    calibration radius grades.1 grades.2 velocityMode

/-! ## Positive low-grade service and explicit grade-zero boundary -/

theorem rotatedLowPinGradeCoefficient_eq_lowRadius
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (lowGrade highGrade : ℕ) :
    rotatedLowPinGradeCoefficient calibration lowGrade highGrade =
      rotatedLowPinStokesCoefficient highGrade *
        (calibration.fullTurn * 3) * (dyadicRadius lowGrade : ℝ) := by
  unfold rotatedLowPinGradeCoefficient
  rw [lowGradeRadius_eq_gradeRatio_mul_highRadius lowGrade highGrade]
  ring

theorem finiteOpenAdvectingLowSecondGradeRatioPopulationAt_positiveLow_le_kernel
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius level highGrade : ℕ) :
    finiteAdvectingLowSecondGradeRatioPopulationAt calibration radius
        (level + 1) highGrade (openPeriodicVelocityFourierMode solution t) ≤
      (rotatedLowPinStokesCoefficient highGrade *
          (calibration.fullTurn * 3)) *
        (calibratedLowVelocityGradeKernel level *
          (3 * ‖openVelocityWeightedH3State solution t‖)) *
        (Real.sqrt (velocityL1SquareMassOn
            (openPeriodicVelocityFourierMode solution t)
            (advectingLowHighVelocityBand highGrade)) *
          Real.sqrt (velocityL1SquareMassOn
            (openPeriodicVelocityFourierMode solution t)
            (advectingLowHighVelocityBand highGrade))) := by
  have hbase := finiteAdvectingLowSecondGradeRatioPopulationAt_le_cauchyBand
    calibration radius (level + 1) highGrade
      (openPeriodicVelocityFourierMode solution t)
  rw [rotatedLowPinGradeCoefficient_eq_lowRadius] at hbase
  have hlow := radius_mul_openPeriodicVelocityL1MassOn_gradeSucc_le_kernel
    solution t level
  have hcoefficient :
      0 ≤ rotatedLowPinStokesCoefficient highGrade *
        (calibration.fullTurn * 3) :=
    mul_nonneg (rotatedLowPinStokesCoefficient_nonneg highGrade)
      (mul_nonneg (fullTurn_nonneg_from_arcRadial calibration) (by norm_num))
  have hhigh : 0 ≤
      Real.sqrt (velocityL1SquareMassOn
          (openPeriodicVelocityFourierMode solution t)
          (advectingLowHighVelocityBand highGrade)) *
        Real.sqrt (velocityL1SquareMassOn
          (openPeriodicVelocityFourierMode solution t)
          (advectingLowHighVelocityBand highGrade)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc
    _ ≤ (rotatedLowPinStokesCoefficient highGrade *
          (calibration.fullTurn * 3)) *
        (((dyadicRadius (level + 1) : ℝ) *
          openPeriodicVelocityL1MassOn solution t
            (frequencyDyadicGradeSlice (level + 1))) *
          (Real.sqrt (velocityL1SquareMassOn
              (openPeriodicVelocityFourierMode solution t)
              (advectingLowHighVelocityBand highGrade)) *
            Real.sqrt (velocityL1SquareMassOn
              (openPeriodicVelocityFourierMode solution t)
              (advectingLowHighVelocityBand highGrade)))) := by
      simpa [openPeriodicVelocityL1MassOn, mul_assoc] using hbase
    _ ≤ (rotatedLowPinStokesCoefficient highGrade *
          (calibration.fullTurn * 3)) *
        ((calibratedLowVelocityGradeKernel level *
          (3 * ‖openVelocityWeightedH3State solution t‖)) *
          (Real.sqrt (velocityL1SquareMassOn
              (openPeriodicVelocityFourierMode solution t)
              (advectingLowHighVelocityBand highGrade)) *
            Real.sqrt (velocityL1SquareMassOn
              (openPeriodicVelocityFourierMode solution t)
              (advectingLowHighVelocityBand highGrade)))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hlow hhigh) hcoefficient
    _ = _ := by ring

theorem finiteOpenAdvectingLowThirdGradeRatioPopulationAt_positiveLow_le_kernel
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius level highGrade : ℕ) :
    finiteAdvectingLowThirdGradeRatioPopulationAt calibration radius
        (level + 1) highGrade (openPeriodicVelocityFourierMode solution t) ≤
      (rotatedLowPinStokesCoefficient highGrade *
          (calibration.fullTurn * 3)) *
        (calibratedLowVelocityGradeKernel level *
          (3 * ‖openVelocityWeightedH3State solution t‖)) *
        (Real.sqrt (velocityL1SquareMassOn
            (openPeriodicVelocityFourierMode solution t)
            (advectingLowHighVelocityBand highGrade)) *
          Real.sqrt (velocityL1SquareMassOn
            (openPeriodicVelocityFourierMode solution t)
            (advectingLowHighVelocityBand highGrade))) := by
  have hbase := finiteAdvectingLowThirdGradeRatioPopulationAt_le_cauchyBand
    calibration radius (level + 1) highGrade
      (openPeriodicVelocityFourierMode solution t)
  rw [rotatedLowPinGradeCoefficient_eq_lowRadius] at hbase
  have hlow := radius_mul_openPeriodicVelocityL1MassOn_gradeSucc_le_kernel
    solution t level
  have hcoefficient :
      0 ≤ rotatedLowPinStokesCoefficient highGrade *
        (calibration.fullTurn * 3) :=
    mul_nonneg (rotatedLowPinStokesCoefficient_nonneg highGrade)
      (mul_nonneg (fullTurn_nonneg_from_arcRadial calibration) (by norm_num))
  have hhigh : 0 ≤
      Real.sqrt (velocityL1SquareMassOn
          (openPeriodicVelocityFourierMode solution t)
          (advectingLowHighVelocityBand highGrade)) *
        Real.sqrt (velocityL1SquareMassOn
          (openPeriodicVelocityFourierMode solution t)
          (advectingLowHighVelocityBand highGrade)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc
    _ ≤ (rotatedLowPinStokesCoefficient highGrade *
          (calibration.fullTurn * 3)) *
        (((dyadicRadius (level + 1) : ℝ) *
          openPeriodicVelocityL1MassOn solution t
            (frequencyDyadicGradeSlice (level + 1))) *
          (Real.sqrt (velocityL1SquareMassOn
              (openPeriodicVelocityFourierMode solution t)
              (advectingLowHighVelocityBand highGrade)) *
            Real.sqrt (velocityL1SquareMassOn
              (openPeriodicVelocityFourierMode solution t)
              (advectingLowHighVelocityBand highGrade)))) := by
      simpa [openPeriodicVelocityL1MassOn, mul_assoc] using hbase
    _ ≤ (rotatedLowPinStokesCoefficient highGrade *
          (calibration.fullTurn * 3)) *
        ((calibratedLowVelocityGradeKernel level *
          (3 * ‖openVelocityWeightedH3State solution t‖)) *
          (Real.sqrt (velocityL1SquareMassOn
              (openPeriodicVelocityFourierMode solution t)
              (advectingLowHighVelocityBand highGrade)) *
            Real.sqrt (velocityL1SquareMassOn
              (openPeriodicVelocityFourierMode solution t)
              (advectingLowHighVelocityBand highGrade)))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hlow hhigh) hcoefficient
    _ = _ := by ring

/-! The next two theorems compose the summable low-grade kernel with the native high-band
payment.  Their right sides have no high-grade parameter. -/

theorem finiteOpenAdvectingLowSecondGradeRatioPopulationAt_positiveLow_le_uniformH3Kernel
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius level highGrade : ℕ)
    (hunique : level + 1 < highGrade) :
    finiteAdvectingLowSecondGradeRatioPopulationAt calibration radius
        (level + 1) highGrade (openPeriodicVelocityFourierMode solution t) ≤
      (calibration.fullTurn * 3) *
        (calibratedLowVelocityGradeKernel level *
          (3 * ‖openVelocityWeightedH3State solution t‖)) *
        (9 * rotatedHighBandH3Calibration *
          ‖openVelocityWeightedH3State solution t‖ ^ 2) := by
  let mass := velocityL1SquareMassOn
    (openPeriodicVelocityFourierMode solution t)
    (advectingLowHighVelocityBand highGrade)
  have hbase :=
    finiteOpenAdvectingLowSecondGradeRatioPopulationAt_positiveLow_le_kernel
      calibration solution t radius level highGrade
  have hmass : 0 ≤ mass :=
    velocityL1SquareMassOn_nonneg _ _
  have hsqrt : Real.sqrt mass * Real.sqrt mass = mass := by
    rw [← sq, Real.sq_sqrt hmass]
  have hhigh :=
    rotatedLowPinStokesCoefficient_mul_velocityL1SquareMassOn_highBand_le_nativeH3
      solution t highGrade (by omega)
  have hfront : 0 ≤
      (calibration.fullTurn * 3) *
        (calibratedLowVelocityGradeKernel level *
          (3 * ‖openVelocityWeightedH3State solution t‖)) := by
    exact mul_nonneg
      (mul_nonneg (fullTurn_nonneg_from_arcRadial calibration) (by norm_num))
      (mul_nonneg (calibratedLowVelocityGradeKernel_nonneg level)
        (mul_nonneg (by norm_num) (norm_nonneg _)))
  calc
    _ ≤ (rotatedLowPinStokesCoefficient highGrade *
          (calibration.fullTurn * 3)) *
        (calibratedLowVelocityGradeKernel level *
          (3 * ‖openVelocityWeightedH3State solution t‖)) *
        (Real.sqrt mass * Real.sqrt mass) := by
      simpa [mass] using hbase
    _ = (calibration.fullTurn * 3) *
        (calibratedLowVelocityGradeKernel level *
          (3 * ‖openVelocityWeightedH3State solution t‖)) *
        (rotatedLowPinStokesCoefficient highGrade * mass) := by
      rw [hsqrt]
      ring
    _ ≤ (calibration.fullTurn * 3) *
        (calibratedLowVelocityGradeKernel level *
          (3 * ‖openVelocityWeightedH3State solution t‖)) *
        (9 * rotatedHighBandH3Calibration *
          ‖openVelocityWeightedH3State solution t‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hhigh hfront

theorem finiteOpenAdvectingLowThirdGradeRatioPopulationAt_positiveLow_le_uniformH3Kernel
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius level highGrade : ℕ)
    (hunique : level + 1 < highGrade) :
    finiteAdvectingLowThirdGradeRatioPopulationAt calibration radius
        (level + 1) highGrade (openPeriodicVelocityFourierMode solution t) ≤
      (calibration.fullTurn * 3) *
        (calibratedLowVelocityGradeKernel level *
          (3 * ‖openVelocityWeightedH3State solution t‖)) *
        (9 * rotatedHighBandH3Calibration *
          ‖openVelocityWeightedH3State solution t‖ ^ 2) := by
  let mass := velocityL1SquareMassOn
    (openPeriodicVelocityFourierMode solution t)
    (advectingLowHighVelocityBand highGrade)
  have hbase :=
    finiteOpenAdvectingLowThirdGradeRatioPopulationAt_positiveLow_le_kernel
      calibration solution t radius level highGrade
  have hmass : 0 ≤ mass :=
    velocityL1SquareMassOn_nonneg _ _
  have hsqrt : Real.sqrt mass * Real.sqrt mass = mass := by
    rw [← sq, Real.sq_sqrt hmass]
  have hhigh :=
    rotatedLowPinStokesCoefficient_mul_velocityL1SquareMassOn_highBand_le_nativeH3
      solution t highGrade (by omega)
  have hfront : 0 ≤
      (calibration.fullTurn * 3) *
        (calibratedLowVelocityGradeKernel level *
          (3 * ‖openVelocityWeightedH3State solution t‖)) := by
    exact mul_nonneg
      (mul_nonneg (fullTurn_nonneg_from_arcRadial calibration) (by norm_num))
      (mul_nonneg (calibratedLowVelocityGradeKernel_nonneg level)
        (mul_nonneg (by norm_num) (norm_nonneg _)))
  calc
    _ ≤ (rotatedLowPinStokesCoefficient highGrade *
          (calibration.fullTurn * 3)) *
        (calibratedLowVelocityGradeKernel level *
          (3 * ‖openVelocityWeightedH3State solution t‖)) *
        (Real.sqrt mass * Real.sqrt mass) := by
      simpa [mass] using hbase
    _ = (calibration.fullTurn * 3) *
        (calibratedLowVelocityGradeKernel level *
          (3 * ‖openVelocityWeightedH3State solution t‖)) *
        (rotatedLowPinStokesCoefficient highGrade * mass) := by
      rw [hsqrt]
      ring
    _ ≤ (calibration.fullTurn * 3) *
        (calibratedLowVelocityGradeKernel level *
          (3 * ‖openVelocityWeightedH3State solution t‖)) *
        (9 * rotatedHighBandH3Calibration *
          ‖openVelocityWeightedH3State solution t‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hhigh hfront

/-- Grade zero is not forced through a nonexistent predecessor shell.  Its finite low-frequency
mass remains explicit while the high-band convolution is still controlled. -/
theorem finiteOpenAdvectingLowSecondGradeRatioPopulationAt_gradeZero_le
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius highGrade : ℕ) :
    finiteAdvectingLowSecondGradeRatioPopulationAt calibration radius 0 highGrade
        (openPeriodicVelocityFourierMode solution t) ≤
      rotatedLowPinGradeCoefficient calibration 0 highGrade *
        (openPeriodicVelocityL1MassOn solution t (frequencyDyadicGradeSlice 0) *
          (Real.sqrt (velocityL1SquareMassOn
              (openPeriodicVelocityFourierMode solution t)
              (advectingLowHighVelocityBand highGrade)) *
            Real.sqrt (velocityL1SquareMassOn
              (openPeriodicVelocityFourierMode solution t)
              (advectingLowHighVelocityBand highGrade)))) := by
  simpa [openPeriodicVelocityL1MassOn] using
    (finiteAdvectingLowSecondGradeRatioPopulationAt_le_cauchyBand calibration
      radius 0 highGrade (openPeriodicVelocityFourierMode solution t))

theorem finiteOpenAdvectingLowThirdGradeRatioPopulationAt_gradeZero_le
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius highGrade : ℕ) :
    finiteAdvectingLowThirdGradeRatioPopulationAt calibration radius 0 highGrade
        (openPeriodicVelocityFourierMode solution t) ≤
      rotatedLowPinGradeCoefficient calibration 0 highGrade *
        (openPeriodicVelocityL1MassOn solution t (frequencyDyadicGradeSlice 0) *
          (Real.sqrt (velocityL1SquareMassOn
              (openPeriodicVelocityFourierMode solution t)
              (advectingLowHighVelocityBand highGrade)) *
            Real.sqrt (velocityL1SquareMassOn
              (openPeriodicVelocityFourierMode solution t)
              (advectingLowHighVelocityBand highGrade)))) := by
  simpa [openPeriodicVelocityL1MassOn] using
    (finiteAdvectingLowThirdGradeRatioPopulationAt_le_cauchyBand calibration
      radius 0 highGrade (openPeriodicVelocityFourierMode solution t))

/-- The initial low-frequency fibre remains explicit, while its actual positive high band is
paid uniformly in the native `H3` chart. -/
theorem finiteOpenAdvectingLowSecondGradeRatioPopulationAt_gradeZero_le_uniformH3
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius highGrade : ℕ) (hpositive : 0 < highGrade) :
    finiteAdvectingLowSecondGradeRatioPopulationAt calibration radius 0 highGrade
        (openPeriodicVelocityFourierMode solution t) ≤
      (calibration.fullTurn * 3) *
        openPeriodicVelocityL1MassOn solution t (frequencyDyadicGradeSlice 0) *
        (9 * rotatedHighBandH3Calibration *
          ‖openVelocityWeightedH3State solution t‖ ^ 2) := by
  let mass := velocityL1SquareMassOn
    (openPeriodicVelocityFourierMode solution t)
    (advectingLowHighVelocityBand highGrade)
  have hbase := finiteOpenAdvectingLowSecondGradeRatioPopulationAt_gradeZero_le
    calibration solution t radius highGrade
  rw [rotatedLowPinGradeCoefficient_eq_lowRadius] at hbase
  have hradiusZero : (dyadicRadius 0 : ℝ) = 1 := by norm_num [dyadicRadius]
  rw [hradiusZero, mul_one] at hbase
  have hmass : 0 ≤ mass := velocityL1SquareMassOn_nonneg _ _
  have hsqrt : Real.sqrt mass * Real.sqrt mass = mass := by
    rw [← sq, Real.sq_sqrt hmass]
  have hhigh :=
    rotatedLowPinStokesCoefficient_mul_velocityL1SquareMassOn_highBand_le_nativeH3
      solution t highGrade hpositive
  have hfront : 0 ≤
      (calibration.fullTurn * 3) *
        openPeriodicVelocityL1MassOn solution t (frequencyDyadicGradeSlice 0) :=
    mul_nonneg
      (mul_nonneg (fullTurn_nonneg_from_arcRadial calibration) (by norm_num))
      (openPeriodicVelocityL1MassOn_nonneg solution t _)
  calc
    _ ≤ (rotatedLowPinStokesCoefficient highGrade *
          (calibration.fullTurn * 3)) *
        (openPeriodicVelocityL1MassOn solution t (frequencyDyadicGradeSlice 0) *
          (Real.sqrt mass * Real.sqrt mass)) := by
      simpa [mass, mul_assoc] using hbase
    _ = (calibration.fullTurn * 3) *
        openPeriodicVelocityL1MassOn solution t (frequencyDyadicGradeSlice 0) *
        (rotatedLowPinStokesCoefficient highGrade * mass) := by
      rw [hsqrt]
      ring
    _ ≤ (calibration.fullTurn * 3) *
        openPeriodicVelocityL1MassOn solution t (frequencyDyadicGradeSlice 0) *
        (9 * rotatedHighBandH3Calibration *
          ‖openVelocityWeightedH3State solution t‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hhigh hfront

theorem finiteOpenAdvectingLowThirdGradeRatioPopulationAt_gradeZero_le_uniformH3
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius highGrade : ℕ) (hpositive : 0 < highGrade) :
    finiteAdvectingLowThirdGradeRatioPopulationAt calibration radius 0 highGrade
        (openPeriodicVelocityFourierMode solution t) ≤
      (calibration.fullTurn * 3) *
        openPeriodicVelocityL1MassOn solution t (frequencyDyadicGradeSlice 0) *
        (9 * rotatedHighBandH3Calibration *
          ‖openVelocityWeightedH3State solution t‖ ^ 2) := by
  let mass := velocityL1SquareMassOn
    (openPeriodicVelocityFourierMode solution t)
    (advectingLowHighVelocityBand highGrade)
  have hbase := finiteOpenAdvectingLowThirdGradeRatioPopulationAt_gradeZero_le
    calibration solution t radius highGrade
  rw [rotatedLowPinGradeCoefficient_eq_lowRadius] at hbase
  have hradiusZero : (dyadicRadius 0 : ℝ) = 1 := by norm_num [dyadicRadius]
  rw [hradiusZero, mul_one] at hbase
  have hmass : 0 ≤ mass := velocityL1SquareMassOn_nonneg _ _
  have hsqrt : Real.sqrt mass * Real.sqrt mass = mass := by
    rw [← sq, Real.sq_sqrt hmass]
  have hhigh :=
    rotatedLowPinStokesCoefficient_mul_velocityL1SquareMassOn_highBand_le_nativeH3
      solution t highGrade hpositive
  have hfront : 0 ≤
      (calibration.fullTurn * 3) *
        openPeriodicVelocityL1MassOn solution t (frequencyDyadicGradeSlice 0) :=
    mul_nonneg
      (mul_nonneg (fullTurn_nonneg_from_arcRadial calibration) (by norm_num))
      (openPeriodicVelocityL1MassOn_nonneg solution t _)
  calc
    _ ≤ (rotatedLowPinStokesCoefficient highGrade *
          (calibration.fullTurn * 3)) *
        (openPeriodicVelocityL1MassOn solution t (frequencyDyadicGradeSlice 0) *
          (Real.sqrt mass * Real.sqrt mass)) := by
      simpa [mass, mul_assoc] using hbase
    _ = (calibration.fullTurn * 3) *
        openPeriodicVelocityL1MassOn solution t (frequencyDyadicGradeSlice 0) *
        (rotatedLowPinStokesCoefficient highGrade * mass) := by
      rw [hsqrt]
      ring
    _ ≤ (calibration.fullTurn * 3) *
        openPeriodicVelocityL1MassOn solution t (frequencyDyadicGradeSlice 0) *
        (9 * rotatedHighBandH3Calibration *
          ‖openVelocityWeightedH3State solution t‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hhigh hfront

section Audit

#print axioms sum_velocityL1_mul_receiver_le_sqrt_masses
#print axioms completeAdvectingLowVelocityModeProductMass_eq_rows
#print axioms norm_lowHighCompletedStokesCoefficient_le
#print axioms completeAdvectingLowSecondGradeRatioPopulation_le_cauchyBand
#print axioms completeAdvectingLowThirdGradeRatioPopulation_le_cauchyBand
#print axioms finiteAdvectingLowSecondGradeRatioPopulationAt_le_cauchyBand
#print axioms finiteAdvectingLowThirdGradeRatioPopulationAt_le_cauchyBand
#print axioms finiteAdvectingLowSecondGradeRatioPopulation_eq_sum_gradeFibres
#print axioms finiteAdvectingLowThirdGradeRatioPopulation_eq_sum_gradeFibres
#print axioms finiteAdvectingLowSecondGradeRatioPopulation_le_sum_gradeCauchyBands
#print axioms finiteAdvectingLowThirdGradeRatioPopulation_le_sum_gradeCauchyBands
#print axioms finiteOpenAdvectingLowSecondGradeRatioPopulationAt_positiveLow_le_kernel
#print axioms finiteOpenAdvectingLowThirdGradeRatioPopulationAt_positiveLow_le_kernel
#print axioms rotatedLowPinStokesCoefficient_mul_velocityL1SquareMassOn_highBand_le_nativeH3
#print axioms finiteOpenAdvectingLowSecondGradeRatioPopulationAt_positiveLow_le_uniformH3Kernel
#print axioms finiteOpenAdvectingLowThirdGradeRatioPopulationAt_positiveLow_le_uniformH3Kernel
#print axioms finiteOpenAdvectingLowSecondGradeRatioPopulationAt_gradeZero_le_uniformH3
#print axioms finiteOpenAdvectingLowThirdGradeRatioPopulationAt_gradeZero_le_uniformH3

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2RotatedMajorantBound
