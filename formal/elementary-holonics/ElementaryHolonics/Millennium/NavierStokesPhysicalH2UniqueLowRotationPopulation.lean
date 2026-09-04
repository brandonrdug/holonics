import ElementaryHolonics.Millennium.NavierStokesPhysicalH2CyclicLowPinReorientation
import ElementaryHolonics.Millennium.NavierStokesPhysicalH2VelocityGradeLeverBound
import ElementaryHolonics.Millennium.NavierStokesCalibratedTriadicFaceBound
import ElementaryHolonics.Millennium.NavierStokesH2AdvectingLowGradeFaceMass

/-!
# Finite unique-low rotation population for the physical H2 velocity swing

**[proved-derived; formal-checked]** The common three-pin cube is partitioned exactly into its
three unique-low orientations and the comparable-scale residue.  Cyclic rotation carries the
whole addressed occurrence -- all three frequency pins, their velocity modes, and the oriented
physical face -- into one advecting-low chart.  The three unique-low currents therefore join as
one signed three-rotation orbit before any norm is taken; the orbit is not declared to vanish and
its three faces are not identified.

On that chart, divergence reorients the two high/low multiplier legs onto faces differentiating
at the least pin.  Consequently all three legs expose the actual low/high dyadic grade ratio,
while the comparable-scale population remains a separate finite residue.  This file stops at the
finite cube boundary.  It makes no infinite-exhaustion, time, absorption, or continuation claim.
The separately completed cube-exhaustion owner now identifies the limit of the finite signed
current with the complete physical `H2` current.  Passing this bound to a useful infinite
majorant still requires convergence or uniform control of the three sector majorants and the
comparable residue; convergence of the signed left side alone does not supply that estimate or an
absorption law.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2UniqueLowRotationPopulation

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCalibratedTriadicFaceBound
open Soma.Holonics.Millennium.NavierStokesCompleteDyadicTriadSectorPartition
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesH2AdvectingLowGradeFaceMass
open Soma.Holonics.Millennium.NavierStokesH2AdvectingLowGradeLeverBound
open Soma.Holonics.Millennium.NavierStokesH2TriadMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPhysicalH2CyclicLowPinReorientation
open Soma.Holonics.Millennium.NavierStokesPhysicalH2CyclicSectorSwing
open Soma.Holonics.Millennium.NavierStokesPhysicalH2CurlMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityGradeLeverBound
open Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityTriadJoin
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.Turn

/-! ## Cyclic transport of complete addresses -/

/-- One cyclic rotation of a complete transport occurrence. -/
def completeTransportRotate (address : CompleteTransportAddress) :
    CompleteTransportAddress :=
  (address.2, completeTransportReceiver address)

/-- Two cyclic rotations of a complete transport occurrence. -/
def completeTransportRotateTwice (address : CompleteTransportAddress) :
    CompleteTransportAddress :=
  completeTransportRotate (completeTransportRotate address)

@[simp]
theorem completeTransportRotate_first (address : CompleteTransportAddress) :
    (completeTransportRotate address).1 = address.2 := rfl

@[simp]
theorem completeTransportRotate_second (address : CompleteTransportAddress) :
    (completeTransportRotate address).2 = completeTransportReceiver address := rfl

@[simp]
theorem completeTransportReceiver_rotate (address : CompleteTransportAddress) :
    completeTransportReceiver (completeTransportRotate address) = address.1 := by
  funext coordinate
  simp [completeTransportRotate, completeTransportReceiver]
  omega

@[simp]
theorem completeTransportRotate_three (address : CompleteTransportAddress) :
    completeTransportRotate
        (completeTransportRotate (completeTransportRotate address)) = address := by
  apply Prod.ext
  · change completeTransportReceiver (completeTransportRotate address) = address.1
    exact completeTransportReceiver_rotate address
  · change completeTransportReceiver
      (completeTransportRotate (completeTransportRotate address)) = address.2
    rw [completeTransportReceiver_rotate]
    rfl

/-- Rotation is an exact equivalence, with two rotations as its inverse. -/
def completeTransportRotateEquiv :
    CompleteTransportAddress ≃ CompleteTransportAddress where
  toFun := completeTransportRotate
  invFun := completeTransportRotateTwice
  left_inv := by
    intro address
    exact completeTransportRotate_three address
  right_inv := by
    intro address
    unfold completeTransportRotateTwice
    exact completeTransportRotate_three address

@[simp]
theorem completeTransportTriad_rotate (address : CompleteTransportAddress) :
    completeTransportTriad (completeTransportRotate address) =
      (completeTransportTriad address).rotate := by
  cases address with
  | mk advecting transported =>
      unfold completeTransportRotate completeTransportTriad
        AddressedClosedFourierTriad.rotate
      rw [AddressedClosedFourierTriad.mk.injEq]
      refine ⟨rfl, rfl, ?_⟩
      funext coordinate
      change -transported coordinate -
          (-advecting coordinate - transported coordinate) = advecting coordinate
      omega

@[simp]
theorem completeTransportTriad_rotateTwice (address : CompleteTransportAddress) :
    completeTransportTriad (completeTransportRotateTwice address) =
      (completeTransportTriad address).rotate.rotate := by
  unfold completeTransportRotateTwice
  simp

@[simp]
theorem completeTransportRotateTwice_first (address : CompleteTransportAddress) :
    (completeTransportRotateTwice address).1 = completeTransportReceiver address := rfl

@[simp]
theorem completeTransportRotateTwice_second (address : CompleteTransportAddress) :
    (completeTransportRotateTwice address).2 = address.1 := by
  exact completeTransportReceiver_rotate address

@[simp]
theorem completeTransportReceiver_rotateTwice (address : CompleteTransportAddress) :
    completeTransportReceiver (completeTransportRotateTwice address) = address.2 := by
  unfold completeTransportRotateTwice
  rw [completeTransportReceiver_rotate]
  rfl

/-- The common three-pin cube is cyclically invariant. -/
theorem completeTransportRotate_mem_physicalH2VelocityTriadAperture_iff
    (radius : ℕ) (address : CompleteTransportAddress) :
    completeTransportRotate address ∈ physicalH2VelocityTriadAperture radius ↔
      address ∈ physicalH2VelocityTriadAperture radius := by
  rw [mem_physicalH2VelocityTriadAperture_iff,
    mem_physicalH2VelocityTriadAperture_iff]
  simp only [completeTransportRotate_first, completeTransportRotate_second,
    completeTransportReceiver_rotate]
  tauto

theorem completeTransportRotateTwice_mem_physicalH2VelocityTriadAperture_iff
    (radius : ℕ) (address : CompleteTransportAddress) :
    completeTransportRotateTwice address ∈ physicalH2VelocityTriadAperture radius ↔
      address ∈ physicalH2VelocityTriadAperture radius := by
  unfold completeTransportRotateTwice
  rw [completeTransportRotate_mem_physicalH2VelocityTriadAperture_iff,
    completeTransportRotate_mem_physicalH2VelocityTriadAperture_iff]

/-! ## Four exact finite sectors -/

def finitePhysicalH2AdvectingLowAperture (radius : ℕ) :
    Finset CompleteTransportAddress := by
  classical
  exact (physicalH2VelocityTriadAperture radius).filter fun address ↦
    AdvectingLowSector (completeTransportTriad address)

def finitePhysicalH2TransportedLowAperture (radius : ℕ) :
    Finset CompleteTransportAddress := by
  classical
  exact (physicalH2VelocityTriadAperture radius).filter fun address ↦
    TransportedLowSector (completeTransportTriad address)

def finitePhysicalH2ReceiverLowAperture (radius : ℕ) :
    Finset CompleteTransportAddress := by
  classical
  exact (physicalH2VelocityTriadAperture radius).filter fun address ↦
    ReceiverLowSector (completeTransportTriad address)

def finitePhysicalH2ComparableAperture (radius : ℕ) :
    Finset CompleteTransportAddress := by
  classical
  exact (physicalH2VelocityTriadAperture radius).filter fun address ↦
    ComparableSector (completeTransportTriad address)

def finitePhysicalH2AdvectingLowCurrent
    (radius : ℕ) (velocityMode : SpatialFrequency → ComplexVector) : ℂ :=
  ∑ address ∈ finitePhysicalH2AdvectingLowAperture radius,
    physicalH2VelocityExchangedTriadFace velocityMode address

def finitePhysicalH2TransportedLowCurrent
    (radius : ℕ) (velocityMode : SpatialFrequency → ComplexVector) : ℂ :=
  ∑ address ∈ finitePhysicalH2TransportedLowAperture radius,
    physicalH2VelocityExchangedTriadFace velocityMode address

def finitePhysicalH2ReceiverLowCurrent
    (radius : ℕ) (velocityMode : SpatialFrequency → ComplexVector) : ℂ :=
  ∑ address ∈ finitePhysicalH2ReceiverLowAperture radius,
    physicalH2VelocityExchangedTriadFace velocityMode address

def finitePhysicalH2ComparableCurrent
    (radius : ℕ) (velocityMode : SpatialFrequency → ComplexVector) : ℂ :=
  ∑ address ∈ finitePhysicalH2ComparableAperture radius,
    physicalH2VelocityExchangedTriadFace velocityMode address

/-- The finite current splits into its four signed sector currents before any norm receiver. -/
theorem finitePhysicalH2VelocityExchangedTriadCurrent_eq_fourSectors
    (radius : ℕ) (velocityMode : SpatialFrequency → ComplexVector) :
    finitePhysicalH2VelocityExchangedTriadCurrent radius velocityMode =
      finitePhysicalH2AdvectingLowCurrent radius velocityMode +
        finitePhysicalH2TransportedLowCurrent radius velocityMode +
        finitePhysicalH2ReceiverLowCurrent radius velocityMode +
        finitePhysicalH2ComparableCurrent radius velocityMode := by
  classical
  unfold finitePhysicalH2VelocityExchangedTriadCurrent
    finitePhysicalH2AdvectingLowCurrent
    finitePhysicalH2TransportedLowCurrent
    finitePhysicalH2ReceiverLowCurrent
    finitePhysicalH2ComparableCurrent
    finitePhysicalH2AdvectingLowAperture
    finitePhysicalH2TransportedLowAperture
    finitePhysicalH2ReceiverLowAperture
    finitePhysicalH2ComparableAperture
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro address _haddress
  rcases triadSector_exhaustive (completeTransportTriad address) with
      hadvecting | htransported | hreceiver | hcomparable
  · simp [hadvecting, advectingLow_not_transportedLow hadvecting,
      advectingLow_not_receiverLow hadvecting,
      advectingLow_not_comparable hadvecting]
  · have hnotAdvecting :
        ¬AdvectingLowSector (completeTransportTriad address) :=
      fun hadvecting ↦ advectingLow_not_transportedLow hadvecting htransported
    have hnotReceiver := transportedLow_not_receiverLow htransported
    have hnotComparable := transportedLow_not_comparable htransported
    simp [hnotAdvecting, htransported, hnotReceiver, hnotComparable]
  · have hnotAdvecting :
        ¬AdvectingLowSector (completeTransportTriad address) :=
      fun hadvecting ↦ advectingLow_not_receiverLow hadvecting hreceiver
    have hnotTransported :
        ¬TransportedLowSector (completeTransportTriad address) :=
      fun htransported ↦ transportedLow_not_receiverLow htransported hreceiver
    have hnotComparable := receiverLow_not_comparable hreceiver
    simp [hnotAdvecting, hnotTransported, hreceiver, hnotComparable]
  · rcases hcomparable with ⟨hnotAdvecting, hnotTransported, hnotReceiver⟩
    have hcomparable : ComparableSector (completeTransportTriad address) :=
      ⟨hnotAdvecting, hnotTransported, hnotReceiver⟩
    simp [hnotAdvecting, hnotTransported, hnotReceiver, hcomparable]

/-! ## Exact rotation into one advecting-low chart -/

theorem completeTransportRotate_mem_advectingLowAperture_iff_transportedLow
    (radius : ℕ) (address : CompleteTransportAddress) :
    completeTransportRotate address ∈ finitePhysicalH2AdvectingLowAperture radius ↔
      address ∈ finitePhysicalH2TransportedLowAperture radius := by
  simp only [finitePhysicalH2AdvectingLowAperture,
    finitePhysicalH2TransportedLowAperture, Finset.mem_filter,
    completeTransportRotate_mem_physicalH2VelocityTriadAperture_iff,
    completeTransportTriad_rotate]
  rw [advectingLowSector_rotate_iff_transportedLowSector]

theorem completeTransportRotateTwice_mem_advectingLowAperture_iff_receiverLow
    (radius : ℕ) (address : CompleteTransportAddress) :
    completeTransportRotateTwice address ∈ finitePhysicalH2AdvectingLowAperture radius ↔
      address ∈ finitePhysicalH2ReceiverLowAperture radius := by
  simp only [finitePhysicalH2AdvectingLowAperture,
    finitePhysicalH2ReceiverLowAperture, Finset.mem_filter,
    completeTransportRotateTwice_mem_physicalH2VelocityTriadAperture_iff,
    completeTransportTriad_rotateTwice]
  rw [advectingLowSector_rotate_iff_transportedLowSector,
    transportedLowSector_rotate_iff_receiverLowSector]

/-- Transported-low occurrences become advecting-low occurrences after one rotation, but their
original oriented physical faces become the two-rotation face in that chart. -/
theorem finitePhysicalH2TransportedLowCurrent_eq_rotatedAdvectingLow
    (radius : ℕ) (velocityMode : SpatialFrequency → ComplexVector) :
    finitePhysicalH2TransportedLowCurrent radius velocityMode =
      ∑ address ∈ finitePhysicalH2AdvectingLowAperture radius,
        physicalH2VelocityExchangedTriadFace velocityMode
          (completeTransportRotateTwice address) := by
  classical
  unfold finitePhysicalH2TransportedLowCurrent
  apply Finset.sum_bij (fun address _haddress ↦ completeTransportRotate address)
  · intro address haddress
    exact (completeTransportRotate_mem_advectingLowAperture_iff_transportedLow
      radius address).mpr haddress
  · intro left _hleft right _hright hequal
    exact completeTransportRotateEquiv.injective hequal
  · intro address haddress
    refine ⟨completeTransportRotateTwice address, ?_, ?_⟩
    · apply (completeTransportRotate_mem_advectingLowAperture_iff_transportedLow
        radius (completeTransportRotateTwice address)).mp
      simpa [completeTransportRotateTwice] using haddress
    · simpa [completeTransportRotateTwice] using
        (completeTransportRotate_three address)
  · intro address _haddress
    congr 1
    symm
    exact completeTransportRotate_three address

/-- Receiver-low occurrences become advecting-low occurrences after two rotations, retaining the
one-rotation physical face in the common chart. -/
theorem finitePhysicalH2ReceiverLowCurrent_eq_rotatedAdvectingLow
    (radius : ℕ) (velocityMode : SpatialFrequency → ComplexVector) :
    finitePhysicalH2ReceiverLowCurrent radius velocityMode =
      ∑ address ∈ finitePhysicalH2AdvectingLowAperture radius,
        physicalH2VelocityExchangedTriadFace velocityMode
          (completeTransportRotate address) := by
  classical
  unfold finitePhysicalH2ReceiverLowCurrent
  apply Finset.sum_bij (fun address _haddress ↦ completeTransportRotateTwice address)
  · intro address haddress
    exact (completeTransportRotateTwice_mem_advectingLowAperture_iff_receiverLow
      radius address).mpr haddress
  · intro left _hleft right _hright hequal
    exact completeTransportRotateEquiv.symm.injective hequal
  · intro address haddress
    refine ⟨completeTransportRotate address, ?_, ?_⟩
    · apply (completeTransportRotateTwice_mem_advectingLowAperture_iff_receiverLow
        radius (completeTransportRotate address)).mp
      simpa [completeTransportRotateTwice] using haddress
    · simpa [completeTransportRotateTwice] using
        (completeTransportRotate_three address)
  · intro address _haddress
    congr 1
    symm
    simpa [completeTransportRotateTwice] using
      (completeTransportRotate_three address)

/-- The three unique-low sector currents form the literal three-face cyclic swing on one
advecting-low occurrence population. -/
theorem finitePhysicalH2UniqueLowCurrents_eq_cyclicAdvectingLow
    (radius : ℕ) (velocityMode : SpatialFrequency → ComplexVector) :
    finitePhysicalH2AdvectingLowCurrent radius velocityMode +
        finitePhysicalH2TransportedLowCurrent radius velocityMode +
        finitePhysicalH2ReceiverLowCurrent radius velocityMode =
      ∑ address ∈ finitePhysicalH2AdvectingLowAperture radius,
        cyclicPhysicalH2ExchangedTriadTransfer (completeTransportTriad address)
          (velocityMode address.1)
          (velocityMode address.2)
          (velocityMode (completeTransportReceiver address)) := by
  rw [finitePhysicalH2TransportedLowCurrent_eq_rotatedAdvectingLow,
    finitePhysicalH2ReceiverLowCurrent_eq_rotatedAdvectingLow]
  unfold finitePhysicalH2AdvectingLowCurrent
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro address _haddress
  unfold physicalH2VelocityExchangedTriadFace
    cyclicPhysicalH2ExchangedTriadTransfer
  simp only [completeTransportTriad_rotate, completeTransportTriad_rotateTwice,
    completeTransportRotate_first, completeTransportRotate_second,
    completeTransportReceiver_rotate, completeTransportRotateTwice_first,
    completeTransportRotateTwice_second, completeTransportReceiver_rotateTwice]
  ring

/-- Exact finite signed population identity: the three unique-low orientations form a cyclic
orbit and the comparable-scale current remains explicit. -/
theorem finitePhysicalH2VelocityExchangedTriadCurrent_eq_cyclicUniqueLow_add_comparable
    (radius : ℕ) (velocityMode : SpatialFrequency → ComplexVector) :
    finitePhysicalH2VelocityExchangedTriadCurrent radius velocityMode =
      (∑ address ∈ finitePhysicalH2AdvectingLowAperture radius,
        cyclicPhysicalH2ExchangedTriadTransfer (completeTransportTriad address)
          (velocityMode address.1)
          (velocityMode address.2)
          (velocityMode (completeTransportReceiver address))) +
        finitePhysicalH2ComparableCurrent radius velocityMode := by
  rw [finitePhysicalH2VelocityExchangedTriadCurrent_eq_fourSectors,
    finitePhysicalH2UniqueLowCurrents_eq_cyclicAdvectingLow]

/-! ## Signed least-pin reorientation before norms -/

/-- The literal three-rotation orbit after divergence has moved both high/low derivative
occurrences onto the first (least-grade) pin. -/
def firstPinReorientedPhysicalH2OrbitFace
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) : ℂ :=
  let triad := completeTransportTriad address
  (((torusStokesEigenvalue triad.transported -
      torusStokesEigenvalue triad.receiver) *
    (1 + torusStokesEigenvalue triad.transported +
      torusStokesEigenvalue triad.receiver) : ℝ) : ℂ) *
      triadicEnergyFace triad.advecting triad.transported
        (velocityMode triad.advecting) (velocityMode triad.transported)
        (velocityMode triad.receiver) -
  (((torusStokesEigenvalue triad.receiver -
      torusStokesEigenvalue triad.advecting) *
    (1 + torusStokesEigenvalue triad.receiver +
      torusStokesEigenvalue triad.advecting) : ℝ) : ℂ) *
      triadicEnergyFace triad.transported triad.advecting
        (velocityMode triad.transported) (velocityMode triad.advecting)
        (velocityMode triad.receiver) +
  (((torusStokesEigenvalue triad.advecting -
      torusStokesEigenvalue triad.transported) *
    (1 + torusStokesEigenvalue triad.advecting +
      torusStokesEigenvalue triad.transported) : ℝ) : ℂ) *
      triadicEnergyFace triad.receiver triad.advecting
        (velocityMode triad.receiver) (velocityMode triad.advecting)
        (velocityMode triad.transported)

/-- Pointwise the full cyclic orbit is exactly its least-pin reorientation.  No face equality or
cyclic cancellation is used. -/
theorem cyclicPhysicalH2VelocityOrbit_eq_firstPinReoriented
    (radius : ℕ) (velocityMode : SpatialFrequency → ComplexVector)
    (hdivergence : ∀ frequency ∈ frequencyCube radius,
      complexDot (complexFrequencyVector frequency) (velocityMode frequency) = 0)
    (address : CompleteTransportAddress)
    (haddress : address ∈ physicalH2VelocityTriadAperture radius) :
    cyclicPhysicalH2ExchangedTriadTransfer (completeTransportTriad address)
        (velocityMode address.1)
        (velocityMode address.2)
        (velocityMode (completeTransportReceiver address)) =
      firstPinReorientedPhysicalH2OrbitFace velocityMode address := by
  have hpins :=
    (mem_physicalH2VelocityTriadAperture_iff radius address).mp haddress
  exact cyclicPhysicalH2ExchangedTriadTransfer_eq_reoriented_firstPin
    (completeTransportTriad address)
    (velocityMode address.1)
    (velocityMode address.2)
    (velocityMode (completeTransportReceiver address))
    (hdivergence address.1 hpins.1)
    (hdivergence address.2 hpins.2.1)
    (hdivergence (completeTransportReceiver address) hpins.2.2)

/-- The finite current retains the signed least-pin-reoriented unique-low orbit plus the
comparable-scale residue. -/
theorem finitePhysicalH2VelocityExchangedTriadCurrent_eq_reorientedUniqueLow_add_comparable
    (radius : ℕ) (velocityMode : SpatialFrequency → ComplexVector)
    (hdivergence : ∀ frequency ∈ frequencyCube radius,
      complexDot (complexFrequencyVector frequency) (velocityMode frequency) = 0) :
    finitePhysicalH2VelocityExchangedTriadCurrent radius velocityMode =
      (∑ address ∈ finitePhysicalH2AdvectingLowAperture radius,
        firstPinReorientedPhysicalH2OrbitFace velocityMode address) +
        finitePhysicalH2ComparableCurrent radius velocityMode := by
  classical
  rw [finitePhysicalH2VelocityExchangedTriadCurrent_eq_cyclicUniqueLow_add_comparable]
  congr 1
  apply Finset.sum_congr rfl
  intro address haddress
  exact cyclicPhysicalH2VelocityOrbit_eq_firstPinReoriented radius velocityMode
    hdivergence address (Finset.mem_filter.mp haddress).1

/-! ## Three actual grade-ratio face populations -/

/-- The low-grade cube radius is exactly the low/high grade ratio times the chosen high radius. -/
theorem lowGradeRadius_eq_gradeRatio_mul_highRadius
    (lowGrade highGrade : ℕ) :
    (dyadicRadius lowGrade : ℝ) =
      dyadicGradeLengthRatio lowGrade highGrade *
        (dyadicRadius highGrade : ℝ) := by
  unfold dyadicGradeLengthRatio
  have hhigh : (dyadicRadius highGrade : ℝ) ≠ 0 := by
    unfold dyadicRadius
    positivity
  field_simp

/-- In an advecting-low chart, every derivative at the first pin carries the explicit least-grade
ratio relative to the common high aperture. -/
theorem frequencyL1_advecting_le_three_mul_gradeRatio_mul_highRadius
    (triad : AddressedClosedFourierTriad) :
    frequencyL1 triad.advecting ≤
      3 * dyadicGradeLengthRatio (advectingGrade triad)
          (advectingLowHighGrade triad) *
        (dyadicRadius (advectingLowHighGrade triad) : ℝ) := by
  calc
    frequencyL1 triad.advecting ≤
        3 * (dyadicRadius (advectingGrade triad) : ℝ) :=
      frequencyL1_le_three_mul_cubeRadius
        (frequencyDyadicGrade_mem triad.advecting)
    _ = 3 * dyadicGradeLengthRatio (advectingGrade triad)
          (advectingLowHighGrade triad) *
        (dyadicRadius (advectingLowHighGrade triad) : ℝ) := by
      rw [lowGradeRadius_eq_gradeRatio_mul_highRadius]
      ring

/-- The high/high first orbit leg, with the completed velocity multiplier lever retained exactly. -/
def advectingLowPrimaryGradeRatioFace
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) : ℝ :=
  let triad := completeTransportTriad address
  (primitiveTorusStokesScale *
    (6 * dyadicGradeLengthRatio (advectingGrade triad)
        (advectingLowHighGrade triad) *
      (dyadicRadius (advectingLowHighGrade triad) : ℝ) ^ 2) *
    (1 + torusStokesEigenvalue triad.transported +
      torusStokesEigenvalue triad.receiver)) *
    ‖triadicEnergyFace triad.advecting triad.transported
      (velocityMode triad.advecting) (velocityMode triad.transported)
      (velocityMode triad.receiver)‖

/-- The second orbit leg after exact exchange onto the least derivative pin.  Its own multiplier
and face orientation are retained. -/
def advectingLowSecondGradeRatioFace
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) : ℝ :=
  let triad := completeTransportTriad address
  ‖(((torusStokesEigenvalue triad.receiver -
      torusStokesEigenvalue triad.advecting) *
    (1 + torusStokesEigenvalue triad.receiver +
      torusStokesEigenvalue triad.advecting) : ℝ) : ℂ)‖ *
    (calibration.fullTurn *
      (3 * dyadicGradeLengthRatio (advectingGrade triad)
          (advectingLowHighGrade triad) *
        (dyadicRadius (advectingLowHighGrade triad) : ℝ)) *
      complexVectorL1 (velocityMode triad.transported) *
      complexVectorL1 (velocityMode triad.advecting) *
      complexVectorL1 (velocityMode triad.receiver))

/-- The third orbit leg already differentiates at the least pin; its receiver-first orientation
and actual multiplier remain visible. -/
def advectingLowThirdGradeRatioFace
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) : ℝ :=
  let triad := completeTransportTriad address
  ‖(((torusStokesEigenvalue triad.advecting -
      torusStokesEigenvalue triad.transported) *
    (1 + torusStokesEigenvalue triad.advecting +
      torusStokesEigenvalue triad.transported) : ℝ) : ℂ)‖ *
    (calibration.fullTurn *
      (3 * dyadicGradeLengthRatio (advectingGrade triad)
          (advectingLowHighGrade triad) *
        (dyadicRadius (advectingLowHighGrade triad) : ℝ)) *
      complexVectorL1 (velocityMode triad.receiver) *
      complexVectorL1 (velocityMode triad.advecting) *
      complexVectorL1 (velocityMode triad.transported))

/-- The first oriented leg is controlled by the completed physical `H2` least-grade lever. -/
theorem norm_firstReorientedLeg_le_primaryGradeRatioFace
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress)
    (hdivergence :
      complexDot (complexFrequencyVector address.1) (velocityMode address.1) = 0)
    (hsector : AdvectingLowSector (completeTransportTriad address)) :
    ‖(((torusStokesEigenvalue address.2 -
          torusStokesEigenvalue (completeTransportReceiver address)) *
        (1 + torusStokesEigenvalue address.2 +
          torusStokesEigenvalue (completeTransportReceiver address)) : ℝ) : ℂ) *
        triadicEnergyFace address.1 address.2
          (velocityMode address.1) (velocityMode address.2)
          (velocityMode (completeTransportReceiver address))‖ ≤
      advectingLowPrimaryGradeRatioFace velocityMode address := by
  have hbound :=
    norm_physicalH2VelocityExchangedTriadFace_le_advectingLowGradeRatio
      velocityMode address hdivergence hsector
  rw [physicalH2VelocityExchangedTriadFace,
    physicalH2ExchangedTriadTransfer_eq_factorized
      (completeTransportTriad address)
      (velocityMode address.1) (velocityMode address.2)
      (velocityMode (completeTransportReceiver address)) hdivergence] at hbound
  simpa [advectingLowPrimaryGradeRatioFace, completeTransportTriad] using hbound

/-- After exact exchange, the second leg is differentiated at the least pin and therefore carries
the same explicit dyadic grade ratio, without changing its mode orientation. -/
theorem norm_secondReorientedLeg_le_secondGradeRatioFace
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (hcircle : calibration.IsEuclideanCircle)
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) :
    ‖(((torusStokesEigenvalue (completeTransportReceiver address) -
          torusStokesEigenvalue address.1) *
        (1 + torusStokesEigenvalue (completeTransportReceiver address) +
          torusStokesEigenvalue address.1) : ℝ) : ℂ) *
        triadicEnergyFace address.2 address.1
          (velocityMode address.2) (velocityMode address.1)
          (velocityMode (completeTransportReceiver address))‖ ≤
      advectingLowSecondGradeRatioFace calibration velocityMode address := by
  have hface := norm_triadicEnergyFace_le_of_calibration calibration hcircle
    address.2 address.1 (velocityMode address.2) (velocityMode address.1)
    (velocityMode (completeTransportReceiver address))
  have hfrequency :=
    frequencyL1_advecting_le_three_mul_gradeRatio_mul_highRadius
      (completeTransportTriad address)
  have hturn : 0 ≤ calibration.fullTurn :=
    fullTurn_nonneg_from_arcRadial calibration
  have htransported : 0 ≤ complexVectorL1 (velocityMode address.2) :=
    complexVectorL1_nonneg _
  have hadvecting : 0 ≤ complexVectorL1 (velocityMode address.1) :=
    complexVectorL1_nonneg _
  have hreceiver :
      0 ≤ complexVectorL1 (velocityMode (completeTransportReceiver address)) :=
    complexVectorL1_nonneg _
  have hfrequency' : frequencyL1 address.1 ≤
      3 * dyadicGradeLengthRatio
          (advectingGrade (completeTransportTriad address))
          (advectingLowHighGrade (completeTransportTriad address)) *
        (dyadicRadius
          (advectingLowHighGrade (completeTransportTriad address)) : ℝ) := by
    simpa [completeTransportTriad] using hfrequency
  unfold advectingLowSecondGradeRatioFace
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    ‖triadicEnergyFace address.2 address.1
        (velocityMode address.2) (velocityMode address.1)
        (velocityMode (completeTransportReceiver address))‖ ≤
      calibration.fullTurn * frequencyL1 address.1 *
        complexVectorL1 (velocityMode address.2) *
        complexVectorL1 (velocityMode address.1) *
        complexVectorL1 (velocityMode (completeTransportReceiver address)) := hface
    _ ≤ calibration.fullTurn *
        (3 * dyadicGradeLengthRatio
          (advectingGrade (completeTransportTriad address))
          (advectingLowHighGrade (completeTransportTriad address)) *
          (dyadicRadius
            (advectingLowHighGrade (completeTransportTriad address)) : ℝ)) *
        complexVectorL1 (velocityMode address.2) *
        complexVectorL1 (velocityMode address.1) *
        complexVectorL1 (velocityMode (completeTransportReceiver address)) := by
      gcongr

/-- The third leg already differentiates at the least pin, so it carries the grade ratio with its
receiver-first mode orientation unchanged. -/
theorem norm_thirdReorientedLeg_le_thirdGradeRatioFace
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (hcircle : calibration.IsEuclideanCircle)
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) :
    ‖(((torusStokesEigenvalue address.1 - torusStokesEigenvalue address.2) *
        (1 + torusStokesEigenvalue address.1 +
          torusStokesEigenvalue address.2) : ℝ) : ℂ) *
        triadicEnergyFace (completeTransportReceiver address) address.1
          (velocityMode (completeTransportReceiver address))
          (velocityMode address.1) (velocityMode address.2)‖ ≤
      advectingLowThirdGradeRatioFace calibration velocityMode address := by
  have hface := norm_triadicEnergyFace_le_of_calibration calibration hcircle
    (completeTransportReceiver address) address.1
    (velocityMode (completeTransportReceiver address))
    (velocityMode address.1) (velocityMode address.2)
  have hfrequency :=
    frequencyL1_advecting_le_three_mul_gradeRatio_mul_highRadius
      (completeTransportTriad address)
  have hturn : 0 ≤ calibration.fullTurn :=
    fullTurn_nonneg_from_arcRadial calibration
  have hreceiver :
      0 ≤ complexVectorL1 (velocityMode (completeTransportReceiver address)) :=
    complexVectorL1_nonneg _
  have hadvecting : 0 ≤ complexVectorL1 (velocityMode address.1) :=
    complexVectorL1_nonneg _
  have htransported : 0 ≤ complexVectorL1 (velocityMode address.2) :=
    complexVectorL1_nonneg _
  have hfrequency' : frequencyL1 address.1 ≤
      3 * dyadicGradeLengthRatio
          (advectingGrade (completeTransportTriad address))
          (advectingLowHighGrade (completeTransportTriad address)) *
        (dyadicRadius
          (advectingLowHighGrade (completeTransportTriad address)) : ℝ) := by
    simpa [completeTransportTriad] using hfrequency
  unfold advectingLowThirdGradeRatioFace
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    ‖triadicEnergyFace (completeTransportReceiver address) address.1
        (velocityMode (completeTransportReceiver address))
        (velocityMode address.1) (velocityMode address.2)‖ ≤
      calibration.fullTurn * frequencyL1 address.1 *
        complexVectorL1 (velocityMode (completeTransportReceiver address)) *
        complexVectorL1 (velocityMode address.1) *
        complexVectorL1 (velocityMode address.2) := hface
    _ ≤ calibration.fullTurn *
        (3 * dyadicGradeLengthRatio
          (advectingGrade (completeTransportTriad address))
          (advectingLowHighGrade (completeTransportTriad address)) *
          (dyadicRadius
            (advectingLowHighGrade (completeTransportTriad address)) : ℝ)) *
        complexVectorL1 (velocityMode (completeTransportReceiver address)) *
        complexVectorL1 (velocityMode address.1) *
        complexVectorL1 (velocityMode address.2) := by
      gcongr

/-- Each least-pin-reoriented orbit is bounded by three distinct actual grade-ratio face
populations.  The rotated faces are not equated and no cancellation is asserted. -/
theorem norm_firstPinReorientedPhysicalH2OrbitFace_le_threeGradeRatioFaces
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (hcircle : calibration.IsEuclideanCircle)
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress)
    (hdivergence :
      complexDot (complexFrequencyVector address.1) (velocityMode address.1) = 0)
    (hsector : AdvectingLowSector (completeTransportTriad address)) :
    ‖firstPinReorientedPhysicalH2OrbitFace velocityMode address‖ ≤
      advectingLowPrimaryGradeRatioFace velocityMode address +
        advectingLowSecondGradeRatioFace calibration velocityMode address +
        advectingLowThirdGradeRatioFace calibration velocityMode address := by
  rw [show firstPinReorientedPhysicalH2OrbitFace velocityMode address =
      (((torusStokesEigenvalue address.2 -
          torusStokesEigenvalue (completeTransportReceiver address)) *
        (1 + torusStokesEigenvalue address.2 +
          torusStokesEigenvalue (completeTransportReceiver address)) : ℝ) : ℂ) *
          triadicEnergyFace address.1 address.2
            (velocityMode address.1) (velocityMode address.2)
            (velocityMode (completeTransportReceiver address)) -
      (((torusStokesEigenvalue (completeTransportReceiver address) -
          torusStokesEigenvalue address.1) *
        (1 + torusStokesEigenvalue (completeTransportReceiver address) +
          torusStokesEigenvalue address.1) : ℝ) : ℂ) *
          triadicEnergyFace address.2 address.1
            (velocityMode address.2) (velocityMode address.1)
            (velocityMode (completeTransportReceiver address)) +
      (((torusStokesEigenvalue address.1 - torusStokesEigenvalue address.2) *
        (1 + torusStokesEigenvalue address.1 +
          torusStokesEigenvalue address.2) : ℝ) : ℂ) *
          triadicEnergyFace (completeTransportReceiver address) address.1
            (velocityMode (completeTransportReceiver address))
            (velocityMode address.1) (velocityMode address.2) by
        rfl]
  calc
    ‖_ - _ + _‖ ≤ ‖_ - _‖ + ‖_‖ := norm_add_le _ _
    _ ≤ (‖_‖ + ‖_‖) + ‖_‖ := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ advectingLowPrimaryGradeRatioFace velocityMode address +
          advectingLowSecondGradeRatioFace calibration velocityMode address +
          advectingLowThirdGradeRatioFace calibration velocityMode address :=
      add_le_add
        (add_le_add
          (norm_firstReorientedLeg_le_primaryGradeRatioFace velocityMode address
            hdivergence hsector)
          (norm_secondReorientedLeg_le_secondGradeRatioFace calibration hcircle
            velocityMode address))
        (norm_thirdReorientedLeg_le_thirdGradeRatioFace calibration hcircle
          velocityMode address)

/-- Finite mass of the completed high/high first leg on the actual advecting-low population. -/
def finiteAdvectingLowPrimaryGradeRatioPopulation
    (radius : ℕ) (velocityMode : SpatialFrequency → ComplexVector) : ℝ :=
  ∑ address ∈ finitePhysicalH2AdvectingLowAperture radius,
    advectingLowPrimaryGradeRatioFace velocityMode address

/-- Finite mass of the exchanged second leg after its derivative is transported onto the least
pin. -/
def finiteAdvectingLowSecondGradeRatioPopulation
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (radius : ℕ) (velocityMode : SpatialFrequency → ComplexVector) : ℝ :=
  ∑ address ∈ finitePhysicalH2AdvectingLowAperture radius,
    advectingLowSecondGradeRatioFace calibration velocityMode address

/-- Finite mass of the third, receiver-first leg, which already differentiates at the least pin. -/
def finiteAdvectingLowThirdGradeRatioPopulation
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (radius : ℕ) (velocityMode : SpatialFrequency → ComplexVector) : ℝ :=
  ∑ address ∈ finitePhysicalH2AdvectingLowAperture radius,
    advectingLowThirdGradeRatioFace calibration velocityMode address

/-- **Finite unique-low rotation bound.**  The norm of the literal completed current is bounded
by three separate advecting-low grade-ratio populations plus the norm of the untouched comparable
residue.  This is the strongest unconditional conclusion of the finite cube, cyclic rotation,
divergence reorientation, and calibrated face estimates alone. -/
theorem norm_finitePhysicalH2VelocityExchangedTriadCurrent_le_threeGradeRatioPopulations_add_comparable
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (hcircle : calibration.IsEuclideanCircle)
    (radius : ℕ) (velocityMode : SpatialFrequency → ComplexVector)
    (hdivergence : ∀ frequency ∈ frequencyCube radius,
      complexDot (complexFrequencyVector frequency) (velocityMode frequency) = 0) :
    ‖finitePhysicalH2VelocityExchangedTriadCurrent radius velocityMode‖ ≤
      finiteAdvectingLowPrimaryGradeRatioPopulation radius velocityMode +
        finiteAdvectingLowSecondGradeRatioPopulation calibration radius velocityMode +
        finiteAdvectingLowThirdGradeRatioPopulation calibration radius velocityMode +
        ‖finitePhysicalH2ComparableCurrent radius velocityMode‖ := by
  classical
  rw [finitePhysicalH2VelocityExchangedTriadCurrent_eq_reorientedUniqueLow_add_comparable
    radius velocityMode hdivergence]
  calc
    ‖(∑ address ∈ finitePhysicalH2AdvectingLowAperture radius,
          firstPinReorientedPhysicalH2OrbitFace velocityMode address) +
        finitePhysicalH2ComparableCurrent radius velocityMode‖ ≤
      ‖∑ address ∈ finitePhysicalH2AdvectingLowAperture radius,
          firstPinReorientedPhysicalH2OrbitFace velocityMode address‖ +
        ‖finitePhysicalH2ComparableCurrent radius velocityMode‖ :=
      norm_add_le _ _
    _ ≤ (∑ address ∈ finitePhysicalH2AdvectingLowAperture radius,
          ‖firstPinReorientedPhysicalH2OrbitFace velocityMode address‖) +
        ‖finitePhysicalH2ComparableCurrent radius velocityMode‖ :=
      add_le_add (norm_sum_le _ _) le_rfl
    _ ≤ (∑ address ∈ finitePhysicalH2AdvectingLowAperture radius,
          (advectingLowPrimaryGradeRatioFace velocityMode address +
            advectingLowSecondGradeRatioFace calibration velocityMode address +
            advectingLowThirdGradeRatioFace calibration velocityMode address)) +
        ‖finitePhysicalH2ComparableCurrent radius velocityMode‖ := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro address haddress
        have hmembership := Finset.mem_filter.mp haddress
        exact norm_firstPinReorientedPhysicalH2OrbitFace_le_threeGradeRatioFaces
          calibration hcircle velocityMode address
          (hdivergence address.1
            ((mem_physicalH2VelocityTriadAperture_iff radius address).mp
              hmembership.1).1)
          hmembership.2
      · rfl
    _ = finiteAdvectingLowPrimaryGradeRatioPopulation radius velocityMode +
        finiteAdvectingLowSecondGradeRatioPopulation calibration radius velocityMode +
        finiteAdvectingLowThirdGradeRatioPopulation calibration radius velocityMode +
        ‖finitePhysicalH2ComparableCurrent radius velocityMode‖ := by
      unfold finiteAdvectingLowPrimaryGradeRatioPopulation
        finiteAdvectingLowSecondGradeRatioPopulation
        finiteAdvectingLowThirdGradeRatioPopulation
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

/-- Literal open-solution specialization.  The solution carrier supplies divergence freedom, but
the theorem remains at the finite cube boundary and retains the comparable residue. -/
theorem norm_finiteOpenPhysicalH2VelocityExchangedTriadCurrent_le_threeGradeRatioPopulations_add_comparable
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (hcircle : calibration.IsEuclideanCircle)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius : ℕ) :
    ‖finiteOpenPhysicalH2VelocityExchangedTriadCurrent solution t radius‖ ≤
      finiteAdvectingLowPrimaryGradeRatioPopulation radius
          (openPeriodicVelocityFourierMode solution t) +
        finiteAdvectingLowSecondGradeRatioPopulation calibration radius
          (openPeriodicVelocityFourierMode solution t) +
        finiteAdvectingLowThirdGradeRatioPopulation calibration radius
          (openPeriodicVelocityFourierMode solution t) +
        ‖finitePhysicalH2ComparableCurrent radius
          (openPeriodicVelocityFourierMode solution t)‖ := by
  exact
    norm_finitePhysicalH2VelocityExchangedTriadCurrent_le_threeGradeRatioPopulations_add_comparable
      calibration hcircle radius (openPeriodicVelocityFourierMode solution t)
      (fun frequency _hfrequency ↦
        openPeriodicVelocityFourierMode_divergenceFree solution t frequency)

section Audit

#print axioms finitePhysicalH2VelocityExchangedTriadCurrent_eq_fourSectors
#print axioms finitePhysicalH2UniqueLowCurrents_eq_cyclicAdvectingLow
#print axioms finitePhysicalH2VelocityExchangedTriadCurrent_eq_reorientedUniqueLow_add_comparable
#print axioms norm_firstPinReorientedPhysicalH2OrbitFace_le_threeGradeRatioFaces
#print axioms norm_finitePhysicalH2VelocityExchangedTriadCurrent_le_threeGradeRatioPopulations_add_comparable
#print axioms norm_finiteOpenPhysicalH2VelocityExchangedTriadCurrent_le_threeGradeRatioPopulations_add_comparable

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2UniqueLowRotationPopulation
