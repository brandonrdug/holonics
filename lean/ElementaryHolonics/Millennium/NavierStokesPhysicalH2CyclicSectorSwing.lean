import ElementaryHolonics.Millennium.NavierStokesCompleteDyadicTriadSectorPartition

/-!
# The physical H2 cyclic sector swing

**[proved-derived; formal-checked]**  The three cyclic choices of advecting pin do not in
general cancel after the completed physical `H2` multiplier is attached.  What they retain before
any norm receiver is an exact cyclic coboundary: each pin multiplier is paired with the returned
difference of the two adjacent oriented triadic faces.  Adding one common multiplier coordinate
to every pin disappears from this coboundary exactly.

For the physical multiplier, the coboundary separates into the same cyclic boundary applied to
the order-one Stokes coordinate and to its square.  This is the strongest unconditional cyclic
identity supplied by closed-triad incidence and divergence freedom alone; no equality between the
three distinct oriented faces is assumed.

The dyadic receiver is rotated at the same signed level.  Each of the three unique-low sectors is
equivalent to one advecting-low chart: zero rotations for advecting-low, one rotation for
transported-low, and two rotations for receiver-low.  The comparable sector is rotation
invariant and remains an explicit residue.  No terminal absorption or continuation estimate is
asserted.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2CyclicSectorSwing

open Soma.Holonics.Millennium.NavierStokesCompleteDyadicTriadSectorPartition
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesH2TriadMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesPhysicalH2CurlMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicTriadFluxCancellation
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## Three oriented faces and their cyclic multiplier boundary -/

/-- The face with the original advecting pin. -/
def cyclicFirstTriadicFace
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector) : ℂ :=
  triadicEnergyFace triad.advecting triad.transported
    advectingMode transportedMode receiverMode

/-- The face after one cyclic rotation of both pins and modes. -/
def cyclicSecondTriadicFace
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector) : ℂ :=
  triadicEnergyFace triad.transported triad.receiver
    transportedMode receiverMode advectingMode

/-- The face after two cyclic rotations of both pins and modes. -/
def cyclicThirdTriadicFace
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector) : ℂ :=
  triadicEnergyFace triad.receiver triad.advecting
    receiverMode advectingMode transportedMode

/-- The exact cyclic boundary seen by a multiplier on the three frequency pins.  Each coefficient
is attached to the returned difference of its two adjacent oriented faces. -/
def cyclicMultiplierCoboundary
    (multiplier : SpatialFrequency → ℂ)
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector) : ℂ :=
  multiplier triad.advecting *
      (cyclicThirdTriadicFace triad advectingMode transportedMode receiverMode -
        cyclicSecondTriadicFace triad advectingMode transportedMode receiverMode) +
    multiplier triad.transported *
      (cyclicFirstTriadicFace triad advectingMode transportedMode receiverMode -
        cyclicThirdTriadicFace triad advectingMode transportedMode receiverMode) +
    multiplier triad.receiver *
      (cyclicSecondTriadicFace triad advectingMode transportedMode receiverMode -
        cyclicFirstTriadicFace triad advectingMode transportedMode receiverMode)

/-- The sum of the three rotated exchanged transfers for an arbitrary frequency multiplier. -/
def cyclicWeightedExchangedTriadTransfer
    (multiplier : SpatialFrequency → ℂ)
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector) : ℂ :=
  weightedExchangedTriadTransfer multiplier triad
      advectingMode transportedMode receiverMode +
    weightedExchangedTriadTransfer multiplier triad.rotate
      transportedMode receiverMode advectingMode +
    weightedExchangedTriadTransfer multiplier triad.rotate.rotate
      receiverMode advectingMode transportedMode

/-- **Exact cyclic coboundary identity.**  Divergence freedom at all three pins turns the three
rotated exchanged pairs into one multiplier coboundary without taking norms. -/
theorem cyclicWeightedExchangedTriadTransfer_eq_coboundary
    (multiplier : SpatialFrequency → ℂ)
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hadvecting :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0)
    (htransported :
      complexDot (complexFrequencyVector triad.transported) transportedMode = 0)
    (hreceiver :
      complexDot (complexFrequencyVector triad.receiver) receiverMode = 0) :
    cyclicWeightedExchangedTriadTransfer multiplier triad
        advectingMode transportedMode receiverMode =
      cyclicMultiplierCoboundary multiplier triad
        advectingMode transportedMode receiverMode := by
  unfold cyclicWeightedExchangedTriadTransfer
  rw [weightedExchangedTriadTransfer_eq_difference_mul multiplier triad
      advectingMode transportedMode receiverMode hadvecting,
    weightedExchangedTriadTransfer_eq_difference_mul multiplier triad.rotate
      transportedMode receiverMode advectingMode htransported,
    weightedExchangedTriadTransfer_eq_difference_mul multiplier triad.rotate.rotate
      receiverMode advectingMode transportedMode hreceiver]
  simp only [AddressedClosedFourierTriad.rotate_advecting,
    AddressedClosedFourierTriad.rotate_transported,
    AddressedClosedFourierTriad.rotate_receiver]
  unfold cyclicMultiplierCoboundary cyclicFirstTriadicFace
    cyclicSecondTriadicFace cyclicThirdTriadicFace
  ring

/-- A common multiplier coordinate has zero cyclic boundary.  This records the exact common-part
cancellation independently of any physical multiplier choice. -/
theorem cyclicMultiplierCoboundary_add_common
    (multiplier : SpatialFrequency → ℂ) (common : ℂ)
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector) :
    cyclicMultiplierCoboundary (fun frequency ↦ multiplier frequency + common) triad
        advectingMode transportedMode receiverMode =
      cyclicMultiplierCoboundary multiplier triad
        advectingMode transportedMode receiverMode := by
  unfold cyclicMultiplierCoboundary
  ring

/-! ## The completed physical H2 cyclic swing -/

/-- The literal sum of the three cyclically rotated completed physical `H2` transfers. -/
def cyclicPhysicalH2ExchangedTriadTransfer
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector) : ℂ :=
  physicalH2ExchangedTriadTransfer triad
      advectingMode transportedMode receiverMode +
    physicalH2ExchangedTriadTransfer triad.rotate
      transportedMode receiverMode advectingMode +
    physicalH2ExchangedTriadTransfer triad.rotate.rotate
      receiverMode advectingMode transportedMode

/-- The completed physical cyclic swing is exactly the coboundary of the completed physical
multiplier.  It is not asserted to vanish. -/
theorem cyclicPhysicalH2ExchangedTriadTransfer_eq_coboundary
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hadvecting :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0)
    (htransported :
      complexDot (complexFrequencyVector triad.transported) transportedMode = 0)
    (hreceiver :
      complexDot (complexFrequencyVector triad.receiver) receiverMode = 0) :
    cyclicPhysicalH2ExchangedTriadTransfer triad
        advectingMode transportedMode receiverMode =
      cyclicMultiplierCoboundary physicalH2CurlEnergyMultiplier triad
        advectingMode transportedMode receiverMode := by
  exact cyclicWeightedExchangedTriadTransfer_eq_coboundary
    physicalH2CurlEnergyMultiplier triad
      advectingMode transportedMode receiverMode
      hadvecting htransported hreceiver

/-- The physical coboundary splits exactly into its order-one and order-two Stokes-coordinate
boundaries.  The shared cyclic incidence is retained rather than estimating the two pieces
separately. -/
theorem cyclicPhysicalH2ExchangedTriadTransfer_eq_orderOne_add_orderTwo
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hadvecting :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0)
    (htransported :
      complexDot (complexFrequencyVector triad.transported) transportedMode = 0)
    (hreceiver :
      complexDot (complexFrequencyVector triad.receiver) receiverMode = 0) :
    cyclicPhysicalH2ExchangedTriadTransfer triad
        advectingMode transportedMode receiverMode =
      cyclicMultiplierCoboundary
          (fun frequency ↦ (torusStokesEigenvalue frequency : ℂ)) triad
          advectingMode transportedMode receiverMode +
        cyclicMultiplierCoboundary
          (fun frequency ↦ ((torusStokesEigenvalue frequency ^ 2 : ℝ) : ℂ)) triad
          advectingMode transportedMode receiverMode := by
  rw [cyclicPhysicalH2ExchangedTriadTransfer_eq_coboundary triad
      advectingMode transportedMode receiverMode hadvecting htransported hreceiver]
  unfold cyclicMultiplierCoboundary physicalH2CurlEnergyMultiplier
  push_cast
  ring

/-- The three rotated completed transfers retain the explicit local pantographic factors.  This
form is useful when the least-grade pin is rotated into the advecting chart before norms. -/
theorem cyclicPhysicalH2ExchangedTriadTransfer_eq_three_factorized_swings
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hadvecting :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0)
    (htransported :
      complexDot (complexFrequencyVector triad.transported) transportedMode = 0)
    (hreceiver :
      complexDot (complexFrequencyVector triad.receiver) receiverMode = 0) :
    cyclicPhysicalH2ExchangedTriadTransfer triad
        advectingMode transportedMode receiverMode =
      (((torusStokesEigenvalue triad.transported -
          torusStokesEigenvalue triad.receiver) *
        (1 + torusStokesEigenvalue triad.transported +
          torusStokesEigenvalue triad.receiver) : ℝ) : ℂ) *
          cyclicFirstTriadicFace triad advectingMode transportedMode receiverMode +
      (((torusStokesEigenvalue triad.receiver -
          torusStokesEigenvalue triad.advecting) *
        (1 + torusStokesEigenvalue triad.receiver +
          torusStokesEigenvalue triad.advecting) : ℝ) : ℂ) *
          cyclicSecondTriadicFace triad advectingMode transportedMode receiverMode +
      (((torusStokesEigenvalue triad.advecting -
          torusStokesEigenvalue triad.transported) *
        (1 + torusStokesEigenvalue triad.advecting +
          torusStokesEigenvalue triad.transported) : ℝ) : ℂ) *
          cyclicThirdTriadicFace triad advectingMode transportedMode receiverMode := by
  unfold cyclicPhysicalH2ExchangedTriadTransfer
  rw [physicalH2ExchangedTriadTransfer_eq_factorized triad
      advectingMode transportedMode receiverMode hadvecting,
    physicalH2ExchangedTriadTransfer_eq_factorized triad.rotate
      transportedMode receiverMode advectingMode htransported,
    physicalH2ExchangedTriadTransfer_eq_factorized triad.rotate.rotate
      receiverMode advectingMode transportedMode hreceiver]
  simp only [AddressedClosedFourierTriad.rotate_advecting,
    AddressedClosedFourierTriad.rotate_transported,
    AddressedClosedFourierTriad.rotate_receiver]
  rfl

/-! ## A firing counterexample to blanket cyclic cancellation -/

/-- A closed frequency triangle used to separate the three cyclic faces. -/
def cyclicNoncancellationTriad : AddressedClosedFourierTriad where
  advecting := ![1, 0, 0]
  transported := ![0, 1, 0]
  receiver := ![-1, -1, 0]
  closed := by
    ext coordinate
    fin_cases coordinate <;> norm_num

/-- Divergence-free mode at the first pin of `cyclicNoncancellationTriad`. -/
def cyclicNoncancellationAdvectingMode : ComplexVector := ![0, 1, 0]

/-- Divergence-free mode at the second pin of `cyclicNoncancellationTriad`. -/
def cyclicNoncancellationTransportedMode : ComplexVector := ![1, 0, 1]

/-- Divergence-free mode at the third pin of `cyclicNoncancellationTriad`. -/
def cyclicNoncancellationReceiverMode : ComplexVector := ![1, -1, 1]

theorem cyclicNoncancellation_advecting_divergence :
    complexDot
      (complexFrequencyVector cyclicNoncancellationTriad.advecting)
      cyclicNoncancellationAdvectingMode = 0 := by
  simp [cyclicNoncancellationTriad, cyclicNoncancellationAdvectingMode,
    complexDot, complexFrequencyVector, dotProduct, Fin.sum_univ_succ]

theorem cyclicNoncancellation_transported_divergence :
    complexDot
      (complexFrequencyVector cyclicNoncancellationTriad.transported)
      cyclicNoncancellationTransportedMode = 0 := by
  simp [cyclicNoncancellationTriad, cyclicNoncancellationTransportedMode,
    complexDot, complexFrequencyVector, dotProduct, Fin.sum_univ_succ]

theorem cyclicNoncancellation_receiver_divergence :
    complexDot
      (complexFrequencyVector cyclicNoncancellationTriad.receiver)
      cyclicNoncancellationReceiverMode = 0 := by
  simp [cyclicNoncancellationTriad, cyclicNoncancellationReceiverMode,
    complexDot, complexFrequencyVector, dotProduct, Fin.sum_univ_succ]

/-- The first oriented face is twice the second in the separating configuration. -/
theorem cyclicNoncancellation_firstFace_eq_two_mul_secondFace :
    cyclicFirstTriadicFace cyclicNoncancellationTriad
        cyclicNoncancellationAdvectingMode cyclicNoncancellationTransportedMode
        cyclicNoncancellationReceiverMode =
      2 * cyclicSecondTriadicFace cyclicNoncancellationTriad
        cyclicNoncancellationAdvectingMode cyclicNoncancellationTransportedMode
        cyclicNoncancellationReceiverMode := by
  simp [cyclicFirstTriadicFace, cyclicSecondTriadicFace, triadicEnergyFace,
    complexAdvectiveInteraction, cyclicNoncancellationTriad,
    cyclicNoncancellationAdvectingMode, cyclicNoncancellationTransportedMode,
    cyclicNoncancellationReceiverMode, complexDot, complexFrequencyVector, dotProduct,
    Fin.sum_univ_succ]
  ring

/-- The third oriented face vanishes in the separating configuration. -/
theorem cyclicNoncancellation_thirdFace_eq_zero :
    cyclicThirdTriadicFace cyclicNoncancellationTriad
      cyclicNoncancellationAdvectingMode cyclicNoncancellationTransportedMode
      cyclicNoncancellationReceiverMode = 0 := by
  simp [cyclicThirdTriadicFace, triadicEnergyFace, complexAdvectiveInteraction,
    cyclicNoncancellationTriad, cyclicNoncancellationAdvectingMode,
    cyclicNoncancellationTransportedMode, cyclicNoncancellationReceiverMode,
    complexDot, complexFrequencyVector, dotProduct, Fin.sum_univ_succ]

/-- The surviving second face is nonzero.  Its derivative-turn factor is discharged through the
already-founded coordinate-multiplier kernel theorem rather than by introducing a numerical
circle coordinate here. -/
theorem cyclicNoncancellation_secondFace_ne_zero :
    cyclicSecondTriadicFace cyclicNoncancellationTriad
      cyclicNoncancellationAdvectingMode cyclicNoncancellationTransportedMode
      cyclicNoncancellationReceiverMode ≠ 0 := by
  intro hzero
  have hfirstFrequency :
      firstFrequency cyclicNoncancellationTriad.advecting ≠ 0 := by
    simp [firstFrequency, cyclicNoncancellationTriad]
  have hmultiplier := mt
    (firstCoordinateMultiplier_eq_zero_iff
      cyclicNoncancellationTriad.advecting).mp hfirstFrequency
  apply hmultiplier
  simpa [cyclicSecondTriadicFace, triadicEnergyFace, complexAdvectiveInteraction,
    cyclicNoncancellationTriad, cyclicNoncancellationAdvectingMode,
    cyclicNoncancellationTransportedMode, cyclicNoncancellationReceiverMode,
    complexDot, complexFrequencyVector, dotProduct, Fin.sum_univ_succ,
    firstFrequency] using hzero

/-- The exact value of the cyclic physical swing in the separating configuration. -/
theorem cyclicNoncancellation_physicalSwing_eq :
    cyclicPhysicalH2ExchangedTriadTransfer cyclicNoncancellationTriad
        cyclicNoncancellationAdvectingMode cyclicNoncancellationTransportedMode
        cyclicNoncancellationReceiverMode =
      -((primitiveTorusStokesScale + 3 * primitiveTorusStokesScale ^ 2 : ℝ) : ℂ) *
        cyclicSecondTriadicFace cyclicNoncancellationTriad
          cyclicNoncancellationAdvectingMode cyclicNoncancellationTransportedMode
          cyclicNoncancellationReceiverMode := by
  rw [cyclicPhysicalH2ExchangedTriadTransfer_eq_three_factorized_swings
    cyclicNoncancellationTriad cyclicNoncancellationAdvectingMode
    cyclicNoncancellationTransportedMode cyclicNoncancellationReceiverMode
    cyclicNoncancellation_advecting_divergence
    cyclicNoncancellation_transported_divergence
    cyclicNoncancellation_receiver_divergence]
  rw [cyclicNoncancellation_firstFace_eq_two_mul_secondFace,
    cyclicNoncancellation_thirdFace_eq_zero]
  simp only [mul_zero, add_zero]
  rw [torusStokesEigenvalue_eq_primitiveScale_mul_frequencySquared,
    torusStokesEigenvalue_eq_primitiveScale_mul_frequencySquared,
    torusStokesEigenvalue_eq_primitiveScale_mul_frequencySquared]
  simp [frequencySquared, cyclicNoncancellationTriad, Fin.sum_univ_succ]
  ring

/-- **Firing counterexample.**  Closed-triad incidence and divergence freedom do not make the
three rotated completed physical `H2` transfers sum to zero. -/
theorem cyclicNoncancellation_physicalSwing_ne_zero :
    cyclicPhysicalH2ExchangedTriadTransfer cyclicNoncancellationTriad
      cyclicNoncancellationAdvectingMode cyclicNoncancellationTransportedMode
      cyclicNoncancellationReceiverMode ≠ 0 := by
  rw [cyclicNoncancellation_physicalSwing_eq]
  apply mul_ne_zero
  · apply neg_ne_zero.mpr
    exact Complex.ofReal_ne_zero.mpr (by
      have hscale := primitiveTorusStokesScale_pos
      positivity)
  · exact cyclicNoncancellation_secondFace_ne_zero

/-! ## Rotation into the advecting-low chart -/

@[simp]
theorem rotate_three (triad : AddressedClosedFourierTriad) :
    triad.rotate.rotate.rotate = triad := by
  cases triad
  rfl

@[simp]
theorem advectingGrade_rotate (triad : AddressedClosedFourierTriad) :
    advectingGrade triad.rotate = transportedGrade triad := rfl

@[simp]
theorem transportedGrade_rotate (triad : AddressedClosedFourierTriad) :
    transportedGrade triad.rotate = receiverGrade triad := rfl

@[simp]
theorem receiverGrade_rotate (triad : AddressedClosedFourierTriad) :
    receiverGrade triad.rotate = advectingGrade triad := rfl

theorem advectingLowSector_rotate_iff_transportedLowSector
    (triad : AddressedClosedFourierTriad) :
    AdvectingLowSector triad.rotate ↔ TransportedLowSector triad := by
  unfold AdvectingLowSector TransportedLowSector
  simp only [advectingGrade_rotate, transportedGrade_rotate, receiverGrade_rotate]
  constructor <;> rintro ⟨hleft, hright⟩ <;> exact ⟨hright, hleft⟩

theorem transportedLowSector_rotate_iff_receiverLowSector
    (triad : AddressedClosedFourierTriad) :
    TransportedLowSector triad.rotate ↔ ReceiverLowSector triad := by
  unfold TransportedLowSector ReceiverLowSector
  simp only [advectingGrade_rotate, transportedGrade_rotate, receiverGrade_rotate]
  constructor <;> rintro ⟨hleft, hright⟩ <;> exact ⟨hright, hleft⟩

theorem receiverLowSector_rotate_iff_advectingLowSector
    (triad : AddressedClosedFourierTriad) :
    ReceiverLowSector triad.rotate ↔ AdvectingLowSector triad := by
  unfold ReceiverLowSector AdvectingLowSector
  simp only [advectingGrade_rotate, transportedGrade_rotate, receiverGrade_rotate]

/-- One rotation sends the transported-low population into the advecting-low chart. -/
theorem transportedLowSector_iff_rotate_advectingLowSector
    (triad : AddressedClosedFourierTriad) :
    TransportedLowSector triad ↔ AdvectingLowSector triad.rotate :=
  (advectingLowSector_rotate_iff_transportedLowSector triad).symm

/-- Two rotations send the receiver-low population into the advecting-low chart. -/
theorem receiverLowSector_iff_rotate_rotate_advectingLowSector
    (triad : AddressedClosedFourierTriad) :
    ReceiverLowSector triad ↔ AdvectingLowSector triad.rotate.rotate := by
  rw [advectingLowSector_rotate_iff_transportedLowSector,
    transportedLowSector_rotate_iff_receiverLowSector]

/-- The comparable-scale residue is invariant under cyclic rotation. -/
theorem comparableSector_rotate_iff (triad : AddressedClosedFourierTriad) :
    ComparableSector triad.rotate ↔ ComparableSector triad := by
  unfold ComparableSector
  rw [advectingLowSector_rotate_iff_transportedLowSector,
    transportedLowSector_rotate_iff_receiverLowSector,
    receiverLowSector_rotate_iff_advectingLowSector]
  aesop

/-- Address-preserving reindexing of the transported-low population into an advecting-low
population. -/
def transportedLowRotateEquivAdvectingLow :
    {triad : AddressedClosedFourierTriad // TransportedLowSector triad} ≃
      {triad : AddressedClosedFourierTriad // AdvectingLowSector triad} where
  toFun := fun triad ↦
    ⟨triad.1.rotate,
      (transportedLowSector_iff_rotate_advectingLowSector triad.1).mp triad.2⟩
  invFun := fun triad ↦
    ⟨triad.1.rotate.rotate, by
      apply (transportedLowSector_iff_rotate_advectingLowSector
        triad.1.rotate.rotate).mpr
      simpa using triad.2⟩
  left_inv := by
    intro triad
    apply Subtype.ext
    exact rotate_three triad.1
  right_inv := by
    intro triad
    apply Subtype.ext
    exact rotate_three triad.1

/-- Address-preserving reindexing of the receiver-low population into an advecting-low
population. -/
def receiverLowRotateEquivAdvectingLow :
    {triad : AddressedClosedFourierTriad // ReceiverLowSector triad} ≃
      {triad : AddressedClosedFourierTriad // AdvectingLowSector triad} where
  toFun := fun triad ↦
    ⟨triad.1.rotate.rotate,
      (receiverLowSector_iff_rotate_rotate_advectingLowSector triad.1).mp triad.2⟩
  invFun := fun triad ↦
    ⟨triad.1.rotate, by
      apply (receiverLowSector_iff_rotate_rotate_advectingLowSector triad.1.rotate).mpr
      simpa using triad.2⟩
  left_inv := by
    intro triad
    apply Subtype.ext
    exact rotate_three triad.1
  right_inv := by
    intro triad
    apply Subtype.ext
    exact rotate_three triad.1

section Audit

#print axioms cyclicWeightedExchangedTriadTransfer_eq_coboundary
#print axioms cyclicMultiplierCoboundary_add_common
#print axioms cyclicPhysicalH2ExchangedTriadTransfer_eq_coboundary
#print axioms cyclicPhysicalH2ExchangedTriadTransfer_eq_orderOne_add_orderTwo
#print axioms cyclicPhysicalH2ExchangedTriadTransfer_eq_three_factorized_swings
#print axioms cyclicNoncancellation_physicalSwing_ne_zero
#print axioms transportedLowRotateEquivAdvectingLow
#print axioms receiverLowRotateEquivAdvectingLow
#print axioms comparableSector_rotate_iff

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2CyclicSectorSwing
