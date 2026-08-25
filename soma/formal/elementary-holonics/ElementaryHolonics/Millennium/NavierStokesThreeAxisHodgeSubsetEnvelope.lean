import ElementaryHolonics.Millennium.NavierStokesThreeAxisHodgeDyadicMass
import ElementaryHolonics.Millennium.NavierStokesThreeAxisScalarSubsetVariation

/-!
# All-positive three-axis Hodge subset envelopes

The two-axis Hodge estimates do not control a difference which meets all three coordinates.
This owner begins the missing ladder with the exact `(1,1,1)` product return.  Its eight raw
Leibniz faces reduce to seven because three differences annihilate the quadratic numerator.

**[proved-derived]** On a controlled `2 × 2 × 2` successor window, a genuine Hodge entry has the
envelope

`3 B² E111 + 3 (2B+1) E11 + 6 E1`,

and hence is at most `(226 * 10^6) / R³` on dyadic scales `s ≥ 3`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeSubsetEnvelope

open Soma.Holonics.HigherDifferenceTransport
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeKernelDifference
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeLocalizedVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeHigherMixedVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeLowerMixedVariation
open Soma.Holonics.Millennium.NavierStokesSmoothHodgeJacobianBand
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeEnvelopeScaling
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeSupportStencil
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesReciprocalDifferenceRecurrence
open Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeScaleDescent
open Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeDyadicMass
open Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeProductMass

/-- One first-order allocation face.  Each allocation is zero or one; the complementary order
meets the reciprocal at the exactly transported stencil point. -/
def hodge111AllocationFace
    (firstAllocation secondAllocation thirdAllocation : Fin 2)
    (left right : SpatialFrequency → ℂ) (frequency : SpatialFrequency) : ℂ :=
  threeAxisMixedForwardDifference 0 1 2
      firstAllocation.val secondAllocation.val thirdAllocation.val left frequency *
    threeAxisMixedForwardDifference 0 1 2
      (1 - firstAllocation.val) (1 - secondAllocation.val) (1 - thirdAllocation.val) right
      (threeAxisStencilPoint 0 1 2 frequency
        firstAllocation.val secondAllocation.val thirdAllocation.val)

/-- The eight chronological allocations of three successive first-order product differences. -/
def hodge111AllocationReturn
    (left right : SpatialFrequency → ℂ) (frequency : SpatialFrequency) : ℂ :=
  ledgerSum (productLedger coordinateTransport [0, 1, 2] left right) frequency

/-- Exact shifted Leibniz law for the `(1,1,1)` word. -/
theorem threeAxisMixedForwardDifference_one_one_one_mul_eq_allocationReturn
    (left right : SpatialFrequency → ℂ) (frequency : SpatialFrequency) :
    threeAxisMixedForwardDifference 0 1 2 1 1 1
        (fun current ↦ left current * right current) frequency =
      hodge111AllocationReturn left right frequency := by
  rw [← differenceWord_eq_threeAxisMixedForwardDifference 0 1 2 1 1 1]
  change differenceWord coordinateTransport [0, 1, 2]
      (fun current ↦ left current * right current) frequency = _
  exact congrFun
    (differenceWord_mul_eq_ledgerSum coordinateTransport [0, 1, 2] left right)
    frequency

/-! ## The two remaining all-positive occurrence ledgers -/

/-- The complete chronological population for the `(1,1,2)` product difference.  The repeated
third-axis occurrences remain distinct until an explicit interchange quotient is applied. -/
def hodge112OccurrenceLedger
    (left right : SpatialFrequency → ℂ) :
    List (ProductFace (Fin 3) SpatialFrequency ℂ) :=
  productLedger coordinateTransport [0, 1, 2, 2] left right

/-- Sum the complete sixteen-occurrence `(1,1,2)` ledger without condensing the two third-axis
histories into binomial weights. -/
def hodge112OccurrenceReturn
    (left right : SpatialFrequency → ℂ) (frequency : SpatialFrequency) : ℂ :=
  ledgerSum (hodge112OccurrenceLedger left right) frequency

/-- The complete chronological population for the `(1,2,2)` product difference. -/
def hodge122OccurrenceLedger
    (left right : SpatialFrequency → ℂ) :
    List (ProductFace (Fin 3) SpatialFrequency ℂ) :=
  productLedger coordinateTransport [0, 1, 1, 2, 2] left right

/-- Sum the complete thirty-two-occurrence `(1,2,2)` ledger before any commuting quotient. -/
def hodge122OccurrenceReturn
    (left right : SpatialFrequency → ℂ) (frequency : SpatialFrequency) : ℂ :=
  ledgerSum (hodge122OccurrenceLedger left right) frequency

/-- Four addressed differences return all sixteen binary shifted-Leibniz histories. -/
theorem hodge112OccurrenceLedger_length
    (left right : SpatialFrequency → ℂ) :
    (hodge112OccurrenceLedger left right).length = 16 := by
  simpa [hodge112OccurrenceLedger] using
    (productLedger_length coordinateTransport [0, 1, 2, 2] left right)

/-- Five addressed differences return all thirty-two binary shifted-Leibniz histories. -/
theorem hodge122OccurrenceLedger_length
    (left right : SpatialFrequency → ℂ) :
    (hodge122OccurrenceLedger left right).length = 32 := by
  simpa [hodge122OccurrenceLedger] using
    (productLedger_length coordinateTransport [0, 1, 1, 2, 2] left right)

/-- Exact `(1,1,2)` shifted-Leibniz law with every occurrence lineage retained. -/
theorem threeAxisMixedForwardDifference_one_one_two_mul_eq_occurrenceReturn
    (left right : SpatialFrequency → ℂ) (frequency : SpatialFrequency) :
    threeAxisMixedForwardDifference 0 1 2 1 1 2
        (fun current ↦ left current * right current) frequency =
      hodge112OccurrenceReturn left right frequency := by
  rw [← differenceWord_eq_threeAxisMixedForwardDifference 0 1 2 1 1 2]
  change differenceWord coordinateTransport [0, 1, 2, 2]
      (fun current ↦ left current * right current) frequency = _
  exact congrFun
    (differenceWord_mul_eq_ledgerSum coordinateTransport [0, 1, 2, 2] left right)
    frequency

/-- Exact `(1,2,2)` shifted-Leibniz law with every occurrence lineage retained. -/
theorem threeAxisMixedForwardDifference_one_two_two_mul_eq_occurrenceReturn
    (left right : SpatialFrequency → ℂ) (frequency : SpatialFrequency) :
    threeAxisMixedForwardDifference 0 1 2 1 2 2
        (fun current ↦ left current * right current) frequency =
      hodge122OccurrenceReturn left right frequency := by
  rw [← differenceWord_eq_threeAxisMixedForwardDifference 0 1 2 1 2 2]
  change differenceWord coordinateTransport [0, 1, 1, 2, 2]
      (fun current ↦ left current * right current) frequency = _
  exact congrFun
    (differenceWord_mul_eq_ledgerSum coordinateTransport [0, 1, 1, 2, 2] left right)
    frequency

/-! ## The anisotropic commuting receivers -/

/-- The commuting allocation addresses for the `(1,1,2)` word.  The first two axes remember
order zero or one and the repeated third axis remembers order zero, one, or two. -/
abbrev Hodge112Allocation := Fin 2 × Fin 2 × Fin 3

/-- The commuting allocation addresses for the `(1,2,2)` word. -/
abbrev Hodge122Allocation := Fin 2 × Fin 3 × Fin 3

/-- A single product hand, read as left-factor order zero or one. -/
def firstOrderLeftAllocation (hand : ProductHand) : Fin 2 := by
  refine ⟨hand.leftOrder, ?_⟩
  cases hand <;> decide

/-- Quotient a chronological `(1,1,2)` face only by the exact commuting order seen on each
axis.  The source face itself remains in `hodge112OccurrenceLedger`; this is its receiver shadow. -/
def hodge112AllocationReceiver
    (face : ProductFace (Fin 3) SpatialFrequency ℂ) : Hodge112Allocation :=
  (firstOrderLeftAllocation (face.handAt 0),
    firstOrderLeftAllocation (face.handAt 1),
    pairedLeftOrder (face.handAt 2) (face.handAt 3))

/-- Quotient a chronological `(1,2,2)` face by the corresponding three-axis left orders. -/
def hodge122AllocationReceiver
    (face : ProductFace (Fin 3) SpatialFrequency ℂ) : Hodge122Allocation :=
  (firstOrderLeftAllocation (face.handAt 0),
    pairedLeftOrder (face.handAt 1) (face.handAt 2),
    pairedLeftOrder (face.handAt 3) (face.handAt 4))

/-- The receiver-address ledger for all sixteen `(1,1,2)` occurrences.  Repeated addresses retain
their multiplicity in this list. -/
def hodge112AllocationAddressLedger
    (left right : SpatialFrequency → ℂ) : List Hodge112Allocation :=
  (hodge112OccurrenceLedger left right).map hodge112AllocationReceiver

/-- The receiver-address ledger for all thirty-two `(1,2,2)` occurrences. -/
def hodge122AllocationAddressLedger
    (left right : SpatialFrequency → ℂ) : List Hodge122Allocation :=
  (hodge122OccurrenceLedger left right).map hodge122AllocationReceiver

/-- The anisotropic `(1,1,2)` commuting receiver has exactly twelve possible faces. -/
theorem hodge112Allocation_card : Fintype.card Hodge112Allocation = 12 := by
  decide

/-- The anisotropic `(1,2,2)` commuting receiver has exactly eighteen possible faces. -/
theorem hodge122Allocation_card : Fintype.card Hodge122Allocation = 18 := by
  decide

/-- Condensation changes addresses, not the sixteen-source occurrence population. -/
theorem hodge112AllocationAddressLedger_length
    (left right : SpatialFrequency → ℂ) :
    (hodge112AllocationAddressLedger left right).length = 16 := by
  simp [hodge112AllocationAddressLedger, hodge112OccurrenceLedger_length]

/-- Condensation changes addresses, not the thirty-two-source occurrence population. -/
theorem hodge122AllocationAddressLedger_length
    (left right : SpatialFrequency → ℂ) :
    (hodge122AllocationAddressLedger left right).length = 32 := by
  simp [hodge122AllocationAddressLedger, hodge122OccurrenceLedger_length]

/-! ## Exact receiver-preserving binomial grouping -/

/-- One third-axis allocation slice before the remaining first/second-axis product faces are
expanded. -/
def stagedThirdSecondOrderSlice
    (firstOrder secondOrder : ℕ) (thirdAllocation : Fin 3)
    (left right : SpatialFrequency → ℂ) (frequency : SpatialFrequency) : ℂ :=
  (secondOrderBinomialWeight thirdAllocation : ℂ) *
    mixedForwardDifference 0 1 firstOrder secondOrder
      (fun current ↦
        (fwdDiff (coordinateStep 2))^[thirdAllocation.val] left current *
          (fwdDiff (coordinateStep 2))^[2 - thirdAllocation.val] right
            (current + thirdAllocation.val • coordinateStep 2)) frequency

/-- The three exact binomial slices returned by the repeated third-axis difference. -/
def stagedThirdSecondOrderReturn
    (firstOrder secondOrder : ℕ)
    (left right : SpatialFrequency → ℂ) (frequency : SpatialFrequency) : ℂ :=
  stagedThirdSecondOrderSlice firstOrder secondOrder 2 left right frequency +
    stagedThirdSecondOrderSlice firstOrder secondOrder 1 left right frequency +
      stagedThirdSecondOrderSlice firstOrder secondOrder 0 left right frequency

/-- A second difference on the third axis groups its four occurrence histories into the exact
binomial multiplicities `1,2,1`, after which arbitrary first/second-axis differences distribute
over the three returned slices. -/
theorem threeAxisMixedForwardDifference_mul_eq_stagedThirdSecondOrderReturn
    (firstOrder secondOrder : ℕ)
    (left right : SpatialFrequency → ℂ) (frequency : SpatialFrequency) :
    threeAxisMixedForwardDifference 0 1 2 firstOrder secondOrder 2
        (fun current ↦ left current * right current) frequency =
      stagedThirdSecondOrderReturn firstOrder secondOrder left right frequency := by
  let thirdStep := coordinateStep 2
  let firstTerm : SpatialFrequency → ℂ := fun current ↦
    (fwdDiff thirdStep)^[2] left current * right (current + thirdStep + thirdStep)
  let middleTerm : SpatialFrequency → ℂ := fun current ↦
    fwdDiff thirdStep left current * fwdDiff thirdStep right (current + thirdStep)
  let lastTerm : SpatialFrequency → ℂ := fun current ↦
    left current * (fwdDiff thirdStep)^[2] right current
  have hthirdProduct :
      (fwdDiff thirdStep)^[2] (fun current ↦ left current * right current) =
        firstTerm + (2 : ℂ) • middleTerm + lastTerm := by
    funext current
    simpa [firstTerm, middleTerm, lastTerm, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, mul_assoc] using
        fwdDiff_iter_two_mul_eq thirdStep left right current
  unfold threeAxisMixedForwardDifference
  rw [hthirdProduct, fwdDiff_iter_add, fwdDiff_iter_add,
    fwdDiff_iter_add, fwdDiff_iter_const_smul, fwdDiff_iter_add,
    fwdDiff_iter_const_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change
    mixedForwardDifference 0 1 firstOrder secondOrder firstTerm frequency +
        2 * mixedForwardDifference 0 1 firstOrder secondOrder middleTerm frequency +
      mixedForwardDifference 0 1 firstOrder secondOrder lastTerm frequency = _
  unfold stagedThirdSecondOrderReturn stagedThirdSecondOrderSlice
  simp [secondOrderBinomialWeight, firstTerm, middleTerm, lastTerm, thirdStep,
    Function.iterate_zero_apply, two_smul, add_assoc]

/-- The four commuting product faces for one first difference on each of two axes. -/
def twoAxisFourFaceReturn
    (first second : Fin 3) (left right : SpatialFrequency → ℂ)
    (frequency : SpatialFrequency) : ℂ :=
  mixedForwardDifference first second 1 1 left frequency *
        right (frequency + coordinateStep second + coordinateStep first) +
    mixedForwardDifference first second 0 1 left frequency *
        mixedForwardDifference first second 1 0 right
          (frequency + coordinateStep second) +
    mixedForwardDifference first second 1 0 left frequency *
        mixedForwardDifference first second 0 1 right
          (frequency + coordinateStep first) +
    left frequency * mixedForwardDifference first second 1 1 right frequency

theorem mixedForwardDifference_one_one_mul_eq_fourFaceReturn
    (first second : Fin 3) (left right : SpatialFrequency → ℂ)
    (frequency : SpatialFrequency) :
    mixedForwardDifference first second 1 1
        (fun current ↦ left current * right current) frequency =
      twoAxisFourFaceReturn first second left right frequency := by
  simpa [twoAxisFourFaceReturn] using
    mixedForwardDifference_one_one_mul_eq first second left right frequency

/-- The six commuting product faces for first-axis order one and second-axis order two. -/
def twoAxisSixFaceReturn
    (first second : Fin 3) (left right : SpatialFrequency → ℂ)
    (frequency : SpatialFrequency) : ℂ :=
  mixedForwardDifference first second 1 2 left frequency *
        right (frequency + coordinateStep second + coordinateStep second +
          coordinateStep first) +
    2 * mixedForwardDifference first second 1 1 left frequency *
        mixedForwardDifference first second 0 1 right
          (frequency + coordinateStep second + coordinateStep first) +
    mixedForwardDifference first second 1 0 left frequency *
        mixedForwardDifference first second 0 2 right
          (frequency + coordinateStep first) +
    mixedForwardDifference first second 0 2 left frequency *
        mixedForwardDifference first second 1 0 right
          (frequency + coordinateStep second + coordinateStep second) +
    2 * mixedForwardDifference first second 0 1 left frequency *
        mixedForwardDifference first second 1 1 right
          (frequency + coordinateStep second) +
    left frequency * mixedForwardDifference first second 1 2 right frequency

theorem mixedForwardDifference_one_two_mul_eq_sixFaceReturn
    (first second : Fin 3) (left right : SpatialFrequency → ℂ)
    (frequency : SpatialFrequency) :
    mixedForwardDifference first second 1 2
        (fun current ↦ left current * right current) frequency =
      twoAxisSixFaceReturn first second left right frequency := by
  simpa [twoAxisSixFaceReturn] using
    mixedForwardDifference_one_two_mul_eq first second left right frequency

/-- One of the three staged `(1,1,2)` slices, now expanded into four commuting allocation
faces. -/
def stagedHodge112FourFaceReturn
    (thirdAllocation : Fin 3)
    (left right : SpatialFrequency → ℂ) (frequency : SpatialFrequency) : ℂ :=
  (secondOrderBinomialWeight thirdAllocation : ℂ) *
    twoAxisFourFaceReturn 0 1
      ((fwdDiff (coordinateStep 2))^[thirdAllocation.val] left)
      (fun current ↦
        (fwdDiff (coordinateStep 2))^[2 - thirdAllocation.val] right
          (current + thirdAllocation.val • coordinateStep 2)) frequency

/-- The twelve-face `(1,1,2)` commuting allocation return. -/
def stagedHodge112AllocationReturn
    (left right : SpatialFrequency → ℂ) (frequency : SpatialFrequency) : ℂ :=
  stagedHodge112FourFaceReturn 2 left right frequency +
    stagedHodge112FourFaceReturn 1 left right frequency +
      stagedHodge112FourFaceReturn 0 left right frequency

/-- One of the three staged `(1,2,2)` slices, expanded into six commuting allocation faces. -/
def stagedHodge122SixFaceReturn
    (thirdAllocation : Fin 3)
    (left right : SpatialFrequency → ℂ) (frequency : SpatialFrequency) : ℂ :=
  (secondOrderBinomialWeight thirdAllocation : ℂ) *
    twoAxisSixFaceReturn 0 1
      ((fwdDiff (coordinateStep 2))^[thirdAllocation.val] left)
      (fun current ↦
        (fwdDiff (coordinateStep 2))^[2 - thirdAllocation.val] right
          (current + thirdAllocation.val • coordinateStep 2)) frequency

/-- The eighteen-face `(1,2,2)` commuting allocation return. -/
def stagedHodge122AllocationReturn
    (left right : SpatialFrequency → ℂ) (frequency : SpatialFrequency) : ℂ :=
  stagedHodge122SixFaceReturn 2 left right frequency +
    stagedHodge122SixFaceReturn 1 left right frequency +
      stagedHodge122SixFaceReturn 0 left right frequency

theorem stagedThirdSecondOrderSlice_one_one_eq_fourFaceReturn
    (thirdAllocation : Fin 3) (left right : SpatialFrequency → ℂ)
    (frequency : SpatialFrequency) :
    stagedThirdSecondOrderSlice 1 1 thirdAllocation left right frequency =
      stagedHodge112FourFaceReturn thirdAllocation left right frequency := by
  unfold stagedThirdSecondOrderSlice stagedHodge112FourFaceReturn
  rw [mixedForwardDifference_one_one_mul_eq_fourFaceReturn]

theorem stagedThirdSecondOrderSlice_one_two_eq_sixFaceReturn
    (thirdAllocation : Fin 3) (left right : SpatialFrequency → ℂ)
    (frequency : SpatialFrequency) :
    stagedThirdSecondOrderSlice 1 2 thirdAllocation left right frequency =
      stagedHodge122SixFaceReturn thirdAllocation left right frequency := by
  unfold stagedThirdSecondOrderSlice stagedHodge122SixFaceReturn
  rw [mixedForwardDifference_one_two_mul_eq_sixFaceReturn]

/-- The `(1,1,2)` product difference factors through the exact twelve-face commuting receiver. -/
theorem threeAxisMixedForwardDifference_one_one_two_mul_eq_stagedAllocationReturn
    (left right : SpatialFrequency → ℂ) (frequency : SpatialFrequency) :
    threeAxisMixedForwardDifference 0 1 2 1 1 2
        (fun current ↦ left current * right current) frequency =
      stagedHodge112AllocationReturn left right frequency := by
  rw [threeAxisMixedForwardDifference_mul_eq_stagedThirdSecondOrderReturn]
  unfold stagedThirdSecondOrderReturn stagedHodge112AllocationReturn
  rw [stagedThirdSecondOrderSlice_one_one_eq_fourFaceReturn,
    stagedThirdSecondOrderSlice_one_one_eq_fourFaceReturn,
    stagedThirdSecondOrderSlice_one_one_eq_fourFaceReturn]

/-- The `(1,2,2)` product difference factors through the exact eighteen-face commuting receiver. -/
theorem threeAxisMixedForwardDifference_one_two_two_mul_eq_stagedAllocationReturn
    (left right : SpatialFrequency → ℂ) (frequency : SpatialFrequency) :
    threeAxisMixedForwardDifference 0 1 2 1 2 2
        (fun current ↦ left current * right current) frequency =
      stagedHodge122AllocationReturn left right frequency := by
  rw [threeAxisMixedForwardDifference_mul_eq_stagedThirdSecondOrderReturn]
  unfold stagedThirdSecondOrderReturn stagedHodge122AllocationReturn
  rw [stagedThirdSecondOrderSlice_one_two_eq_sixFaceReturn,
    stagedThirdSecondOrderSlice_one_two_eq_sixFaceReturn,
    stagedThirdSecondOrderSlice_one_two_eq_sixFaceReturn]

/-- The sixteen chronological occurrences and twelve commuting faces have the same scalar
return. -/
theorem hodge112OccurrenceReturn_eq_stagedAllocationReturn
    (left right : SpatialFrequency → ℂ) (frequency : SpatialFrequency) :
    hodge112OccurrenceReturn left right frequency =
      stagedHodge112AllocationReturn left right frequency := by
  rw [← threeAxisMixedForwardDifference_one_one_two_mul_eq_occurrenceReturn,
    threeAxisMixedForwardDifference_one_one_two_mul_eq_stagedAllocationReturn]

/-- The thirty-two chronological occurrences and eighteen commuting faces have the same scalar
return. -/
theorem hodge122OccurrenceReturn_eq_stagedAllocationReturn
    (left right : SpatialFrequency → ℂ) (frequency : SpatialFrequency) :
    hodge122OccurrenceReturn left right frequency =
      stagedHodge122AllocationReturn left right frequency := by
  rw [← threeAxisMixedForwardDifference_one_two_two_mul_eq_occurrenceReturn,
    threeAxisMixedForwardDifference_one_two_two_mul_eq_stagedAllocationReturn]

/-- The actual `(1,1,2)` Hodge entry is exactly its twelve-face numerator/reciprocal return. -/
theorem hodgeJacobianMultiplierEntry_threeAxisMixedForwardDifference_one_one_two_eq
    (frequency : SpatialFrequency) (component coordinate input : Fin 3) :
    threeAxisMixedForwardDifference 0 1 2 1 1 2
        (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
        frequency =
      stagedHodge112AllocationReturn
        (fun current ↦ hodgeJacobianRatioNumerator current component coordinate input)
        hodgeReciprocal frequency := by
  rw [show (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input) =
      fun current ↦ hodgeJacobianRatioNumerator current component coordinate input *
        hodgeReciprocal current by
    funext current
    rw [hodgeJacobianMultiplierEntry_eq_ratio]
    simp [hodgeJacobianRatioNumerator, hodgeReciprocal, hodgeCrossBasisFactor,
      div_eq_mul_inv]]
  exact threeAxisMixedForwardDifference_one_one_two_mul_eq_stagedAllocationReturn _ _ _

/-- The actual `(1,2,2)` Hodge entry is exactly its eighteen-face numerator/reciprocal return. -/
theorem hodgeJacobianMultiplierEntry_threeAxisMixedForwardDifference_one_two_two_eq
    (frequency : SpatialFrequency) (component coordinate input : Fin 3) :
    threeAxisMixedForwardDifference 0 1 2 1 2 2
        (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
        frequency =
      stagedHodge122AllocationReturn
        (fun current ↦ hodgeJacobianRatioNumerator current component coordinate input)
        hodgeReciprocal frequency := by
  rw [show (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input) =
      fun current ↦ hodgeJacobianRatioNumerator current component coordinate input *
        hodgeReciprocal current by
    funext current
    rw [hodgeJacobianMultiplierEntry_eq_ratio]
    simp [hodgeJacobianRatioNumerator, hodgeReciprocal, hodgeCrossBasisFactor,
      div_eq_mul_inv]]
  exact threeAxisMixedForwardDifference_one_two_two_mul_eq_stagedAllocationReturn _ _ _

/-- The actual `(1,1,1)` Hodge-entry envelope. -/
def hodgeJacobianEntryThreeAxis111Envelope (lower bound : ℝ) : ℝ :=
  3 * bound ^ 2 * hodgeReciprocal111Envelope lower bound +
    3 * (2 * bound + 1) * hodgeReciprocalMixedOneOneEnvelope lower bound +
      6 * hodgeReciprocalFirstEnvelope lower bound

/-- The allocation ledger for a `(1,1,2)` Hodge entry after the quadratic numerator has killed
every allocation of numerator order at least three. -/
def hodgeJacobianEntryThreeAxis112Envelope (lower bound : ℝ) : ℝ :=
  3 * bound ^ 2 * hodgeReciprocal112Envelope lower bound +
    2 * (2 * bound + 1) * hodgeReciprocal111Envelope lower bound +
      2 * (2 * bound + 1) * hodgeReciprocalMixedOneTwoEnvelope lower bound +
        2 * hodgeReciprocalSecondEnvelope lower bound +
          10 * hodgeReciprocalMixedOneOneEnvelope lower bound

/-- The allocation ledger for a `(1,2,2)` Hodge entry after quadratic annihilation. -/
def hodgeJacobianEntryThreeAxis122Envelope (lower bound : ℝ) : ℝ :=
  3 * bound ^ 2 * hodgeReciprocal122Envelope lower bound +
    (2 * bound + 1) * hodgeReciprocalMixedTwoTwoEnvelope lower bound +
      4 * (2 * bound + 1) * hodgeReciprocal112Envelope lower bound +
        12 * hodgeReciprocalMixedOneTwoEnvelope lower bound +
          8 * hodgeReciprocal111Envelope lower bound

set_option maxHeartbeats 800000 in
/-- A controlled first-order cube supplies the seven surviving product faces. -/
theorem norm_hodgeJacobianMultiplierEntry_threeAxisMixedForwardDifference_one_one_one_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (frequency : SpatialFrequency) (component coordinate input : Fin 3)
    (hstencil : ThreeAxisStencilControlled lower bound 0 1 2 frequency 1 1 1) :
    ‖threeAxisMixedForwardDifference 0 1 2 1 1 1
      (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
      frequency‖ ≤ hodgeJacobianEntryThreeAxis111Envelope lower bound := by
  let numerator := fun current ↦
    hodgeJacobianRatioNumerator current component coordinate input
  let reciprocal := hodgeReciprocal
  have hentry :
      (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input) =
        fun current ↦ numerator current * reciprocal current := by
    funext current
    rw [hodgeJacobianMultiplierEntry_eq_ratio]
    simp [numerator, reciprocal, hodgeJacobianRatioNumerator, hodgeReciprocal,
      hodgeCrossBasisFactor, div_eq_mul_inv]
  have hcoordinates : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound := by
    simpa using (hstencil 0 (by omega) 0 (by omega) 0 (by omega)).2
  have hn000 : ‖numerator frequency‖ ≤ 3 * bound ^ 2 :=
    (norm_hodgeJacobianRatioNumerator_le_frequencySquared
      frequency component coordinate input).trans
        (frequencySquared_le_three_mul_sq hbound frequency hcoordinates)
  have hn100 : ‖threeAxisMixedForwardDifference 0 1 2 1 0 0 numerator frequency‖ ≤
      2 * bound + 1 := by
    simpa [threeAxisMixedForwardDifference, mixedForwardDifference, numerator] using
      norm_hodgeJacobianRatioNumerator_mixedForwardDifference_one_zero_le
        hbound 0 1 frequency hcoordinates component coordinate input
  have hn010 : ‖threeAxisMixedForwardDifference 0 1 2 0 1 0 numerator frequency‖ ≤
      2 * bound + 1 := by
    simpa [threeAxisMixedForwardDifference, mixedForwardDifference, numerator] using
      norm_hodgeJacobianRatioNumerator_mixedForwardDifference_zero_one_le
        hbound 0 1 frequency hcoordinates component coordinate input
  have hn001 : ‖threeAxisMixedForwardDifference 0 1 2 0 0 1 numerator frequency‖ ≤
      2 * bound + 1 := by
    simpa [threeAxisMixedForwardDifference, mixedForwardDifference, numerator,
      Function.iterate_one] using
      norm_hodgeJacobianRatioNumerator_mixedForwardDifference_one_zero_le
        hbound 2 0 frequency hcoordinates component coordinate input
  have hn110 : ‖threeAxisMixedForwardDifference 0 1 2 1 1 0 numerator frequency‖ ≤ 2 := by
    simpa [threeAxisMixedForwardDifference, mixedForwardDifference, numerator] using
      norm_hodgeJacobianRatioNumerator_mixedForwardDifference_one_one_le_two
        0 1 frequency component coordinate input
  have hn101 : ‖threeAxisMixedForwardDifference 0 1 2 1 0 1 numerator frequency‖ ≤ 2 := by
    simpa [threeAxisMixedForwardDifference, mixedForwardDifference, numerator,
      Function.iterate_one] using
      norm_hodgeJacobianRatioNumerator_mixedForwardDifference_one_one_le_two
        0 2 frequency component coordinate input
  have hn011 : ‖threeAxisMixedForwardDifference 0 1 2 0 1 1 numerator frequency‖ ≤ 2 := by
    simpa [threeAxisMixedForwardDifference, mixedForwardDifference, numerator,
      Function.iterate_one] using
      norm_hodgeJacobianRatioNumerator_mixedForwardDifference_one_one_le_two
        1 2 frequency component coordinate input
  have hn111 : threeAxisMixedForwardDifference 0 1 2 1 1 1 numerator frequency = 0 := by
    have hzero := congrFun
      (hodgeJacobianRatioNumerator_allocation_eq_zero_of_three_le
        (1 : Fin 3) (1 : Fin 3) (1 : Fin 3) component coordinate input (by norm_num))
      frequency
    simpa [threeAxisMixedForwardDifference, numerator] using hzero
  have hr111 : ‖threeAxisMixedForwardDifference 0 1 2 1 1 1 reciprocal frequency‖ ≤
      hodgeReciprocal111Envelope lower bound := by
    have hraw := norm_hodgeReciprocal_oneEach_le_of_controlled
      hlower hbound frequency hstencil
    rw [show oneEachAxisWord =
      List.replicate 1 0 ++ List.replicate 1 1 ++ List.replicate 1 2 by rfl,
      differenceWord_eq_threeAxisMixedForwardDifference] at hraw
    simpa [reciprocal] using hraw
  have hr011 : ‖threeAxisMixedForwardDifference 0 1 2 0 1 1 reciprocal
      (threeAxisStencilPoint 0 1 2 frequency 1 0 0)‖ ≤
      hodgeReciprocalMixedOneOneEnvelope lower bound := by
    have hraw := norm_hodgeReciprocal_mixedForwardDifference_one_one_le_of_controlled
      hlower hbound 1 2 (by decide)
      (threeAxisStencilPoint 0 1 2 frequency 1 0 0)
      (hstencil.secondThird (firstOffset := 1) (by omega))
    simpa [threeAxisMixedForwardDifference, mixedForwardDifference, reciprocal] using hraw
  have hr101 : ‖threeAxisMixedForwardDifference 0 1 2 1 0 1 reciprocal
      (threeAxisStencilPoint 0 1 2 frequency 0 1 0)‖ ≤
      hodgeReciprocalMixedOneOneEnvelope lower bound := by
    have hraw := norm_hodgeReciprocal_mixedForwardDifference_one_one_le_of_controlled
      hlower hbound 0 2 (by decide)
      (threeAxisStencilPoint 0 1 2 frequency 0 1 0)
      (hstencil.firstThird (secondOffset := 1) (by omega))
    simpa [threeAxisMixedForwardDifference, mixedForwardDifference, reciprocal] using hraw
  have hr110 : ‖threeAxisMixedForwardDifference 0 1 2 1 1 0 reciprocal
      (threeAxisStencilPoint 0 1 2 frequency 0 0 1)‖ ≤
      hodgeReciprocalMixedOneOneEnvelope lower bound := by
    have hraw := norm_hodgeReciprocal_mixedForwardDifference_one_one_le_of_controlled
      hlower hbound 0 1 (by decide)
      (threeAxisStencilPoint 0 1 2 frequency 0 0 1)
      (hstencil.firstSecond (thirdOffset := 1) (by omega))
    simpa [threeAxisMixedForwardDifference, mixedForwardDifference, reciprocal] using hraw
  have hr001 : ‖threeAxisMixedForwardDifference 0 1 2 0 0 1 reciprocal
      (threeAxisStencilPoint 0 1 2 frequency 1 1 0)‖ ≤
      hodgeReciprocalFirstEnvelope lower bound := by
    have hsub := hstencil.rebase
      (firstOffset := 1) (secondOffset := 1) (thirdOffset := 0)
      (firstOrder := 0) (secondOrder := 0) (thirdOrder := 1)
      (by omega) (by omega) (by omega)
    have hraw := norm_hodgeReciprocal_mixedForwardDifference_zero_one_le
      hlower hbound 0 2 (threeAxisStencilPoint 0 1 2 frequency 1 1 0)
      (by simpa [threeAxisStencilPoint] using
        (hsub.firstThird (secondOffset := 0) (by omega)))
    simpa [threeAxisMixedForwardDifference, mixedForwardDifference, reciprocal] using hraw
  have hr010 : ‖threeAxisMixedForwardDifference 0 1 2 0 1 0 reciprocal
      (threeAxisStencilPoint 0 1 2 frequency 1 0 1)‖ ≤
      hodgeReciprocalFirstEnvelope lower bound := by
    have hsub := hstencil.rebase
      (firstOffset := 1) (secondOffset := 0) (thirdOffset := 1)
      (firstOrder := 0) (secondOrder := 1) (thirdOrder := 0)
      (by omega) (by omega) (by omega)
    have hraw := norm_hodgeReciprocal_mixedForwardDifference_zero_one_le
      hlower hbound 0 1 (threeAxisStencilPoint 0 1 2 frequency 1 0 1)
      (by simpa [threeAxisStencilPoint] using
        (hsub.firstSecond (thirdOffset := 0) (by omega)))
    simpa [threeAxisMixedForwardDifference, mixedForwardDifference, reciprocal] using hraw
  have hr100 : ‖threeAxisMixedForwardDifference 0 1 2 1 0 0 reciprocal
      (threeAxisStencilPoint 0 1 2 frequency 0 1 1)‖ ≤
      hodgeReciprocalFirstEnvelope lower bound := by
    have hsub := hstencil.rebase
      (firstOffset := 0) (secondOffset := 1) (thirdOffset := 1)
      (firstOrder := 1) (secondOrder := 0) (thirdOrder := 0)
      (by omega) (by omega) (by omega)
    have hraw := norm_hodgeReciprocal_mixedForwardDifference_one_zero_le
      hlower hbound 0 1 (threeAxisStencilPoint 0 1 2 frequency 0 1 1)
      (by simpa [threeAxisStencilPoint] using
        (hsub.firstSecond (thirdOffset := 0) (by omega)))
    simpa [threeAxisMixedForwardDifference, mixedForwardDifference, reciprocal] using hraw
  let a := numerator frequency *
    threeAxisMixedForwardDifference 0 1 2 1 1 1 reciprocal frequency
  let b := threeAxisMixedForwardDifference 0 1 2 1 0 0 numerator frequency *
    threeAxisMixedForwardDifference 0 1 2 0 1 1 reciprocal
      (threeAxisStencilPoint 0 1 2 frequency 1 0 0)
  let c := threeAxisMixedForwardDifference 0 1 2 0 1 0 numerator frequency *
    threeAxisMixedForwardDifference 0 1 2 1 0 1 reciprocal
      (threeAxisStencilPoint 0 1 2 frequency 0 1 0)
  let d := threeAxisMixedForwardDifference 0 1 2 0 0 1 numerator frequency *
    threeAxisMixedForwardDifference 0 1 2 1 1 0 reciprocal
      (threeAxisStencilPoint 0 1 2 frequency 0 0 1)
  let e := threeAxisMixedForwardDifference 0 1 2 1 1 0 numerator frequency *
    threeAxisMixedForwardDifference 0 1 2 0 0 1 reciprocal
      (threeAxisStencilPoint 0 1 2 frequency 1 1 0)
  let f := threeAxisMixedForwardDifference 0 1 2 1 0 1 numerator frequency *
    threeAxisMixedForwardDifference 0 1 2 0 1 0 reciprocal
      (threeAxisStencilPoint 0 1 2 frequency 1 0 1)
  let g := threeAxisMixedForwardDifference 0 1 2 0 1 1 numerator frequency *
    threeAxisMixedForwardDifference 0 1 2 1 0 0 reciprocal
      (threeAxisStencilPoint 0 1 2 frequency 0 1 1)
  let h := threeAxisMixedForwardDifference 0 1 2 1 1 1 numerator frequency *
    reciprocal (threeAxisStencilPoint 0 1 2 frequency 1 1 1)
  have ha : ‖a‖ ≤ 3 * bound ^ 2 * hodgeReciprocal111Envelope lower bound := by
    dsimp [a]
    rw [norm_mul]
    exact mul_le_mul hn000 (by simpa [threeAxisStencilPoint] using hr111)
      (norm_nonneg _) (by positivity)
  have hb : ‖b‖ ≤ (2 * bound + 1) * hodgeReciprocalMixedOneOneEnvelope lower bound := by
    dsimp [b]
    rw [norm_mul]
    exact mul_le_mul hn100 hr011 (norm_nonneg _) (by positivity)
  have hc : ‖c‖ ≤ (2 * bound + 1) * hodgeReciprocalMixedOneOneEnvelope lower bound := by
    dsimp [c]
    rw [norm_mul]
    exact mul_le_mul hn010 hr101 (norm_nonneg _) (by positivity)
  have hd : ‖d‖ ≤ (2 * bound + 1) * hodgeReciprocalMixedOneOneEnvelope lower bound := by
    dsimp [d]
    rw [norm_mul]
    exact mul_le_mul hn001 hr110 (norm_nonneg _) (by positivity)
  have he : ‖e‖ ≤ 2 * hodgeReciprocalFirstEnvelope lower bound := by
    dsimp [e]
    rw [norm_mul]
    exact mul_le_mul hn110 hr001 (norm_nonneg _) (by positivity)
  have hf : ‖f‖ ≤ 2 * hodgeReciprocalFirstEnvelope lower bound := by
    dsimp [f]
    rw [norm_mul]
    exact mul_le_mul hn101 hr010 (norm_nonneg _) (by positivity)
  have hg : ‖g‖ ≤ 2 * hodgeReciprocalFirstEnvelope lower bound := by
    dsimp [g]
    rw [norm_mul]
    exact mul_le_mul hn011 hr100 (norm_nonneg _) (by positivity)
  have hh : ‖h‖ ≤ 0 := by
    simp [h, hn111]
  rw [hentry, threeAxisMixedForwardDifference_one_one_one_mul_eq_allocationReturn]
  have hreturn : hodge111AllocationReturn numerator reciprocal frequency =
      a + b + c + d + e + f + g + h := by
    rw [← threeAxisMixedForwardDifference_one_one_one_mul_eq_allocationReturn]
    simp [a, b, c, d, e, f, g, h, threeAxisMixedForwardDifference,
      fwdDiff, threeAxisStencilPoint]
    ring
  rw [hreturn]
  have htriangle := norm_add_nine_le a b c d e f g h 0
  simp only [norm_zero, add_zero] at htriangle
  rw [show a + b + c + d + e + f + g + h =
    a + (b + (c + (d + (e + (f + (g + h)))))) by ring]
  refine htriangle.trans ?_
  unfold hodgeJacobianEntryThreeAxis111Envelope
  linarith

/-! ## Dyadic scaling -/

/-- The missing genuinely three-axis first-order entry has inverse-cubic radial scale. -/
theorem hodgeJacobianEntryThreeAxis111Envelope_dyadic_le
    (scale : ℕ) (hscale : 3 ≤ scale) :
    hodgeJacobianEntryThreeAxis111Envelope
      (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) ≤
      (226 * 10 ^ 6) / (dyadicRadius scale : ℝ) ^ 3 := by
  let radius : ℝ := dyadicRadius scale
  let lower := dyadicHodgeControlledLower scale
  let bound := dyadicHodgeControlledBound scale
  let e111 := hodgeReciprocal111Envelope lower bound
  let e11 := hodgeReciprocalMixedOneOneEnvelope lower bound
  let e1 := hodgeReciprocalFirstEnvelope lower bound
  have hradius : 0 < radius := by
    dsimp [radius]
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  have hboundSq : bound ^ 2 ≤ 25 * radius ^ 2 := by
    simpa [bound, radius] using dyadicHodgeControlledBound_sq_le scale hscale
  have hlinear : 2 * bound + 1 ≤ 11 * radius := by
    simpa [bound, radius] using two_mul_bound_add_one_le_eleven_mul_radius scale hscale
  have hlower : 0 < lower := by
    simpa [lower] using dyadicHodgeControlledLower_pos scale hscale
  have h111 : e111 ≤ (3 * 10 ^ 6) / radius ^ 5 := by
    norm_num
    simpa [e111, lower, bound, radius] using
      hodgeReciprocal111Envelope_dyadic_le scale hscale
  have h11 : e11 ≤ 15500 / radius ^ 4 := by
    simpa [e11, lower, bound, radius] using
      hodgeReciprocalMixedOneOneEnvelope_dyadic_le scale hscale
  have h1 : e1 ≤ 176 / radius ^ 3 := by
    simpa [e1, lower, bound, radius] using
      hodgeReciprocalFirstEnvelope_dyadic_le scale hscale
  have h111Nonneg : 0 ≤ e111 := by
    dsimp [e111, lower, bound]
    unfold hodgeReciprocal111Envelope hodgeReciprocalMixedOneOneEnvelope
      dyadicHodgeControlledLower dyadicHodgeControlledBound
    positivity
  have h11Nonneg : 0 ≤ e11 := by
    dsimp [e11, lower, bound]
    unfold hodgeReciprocalMixedOneOneEnvelope
      dyadicHodgeControlledLower dyadicHodgeControlledBound
    positivity
  have hterm111 : 3 * bound ^ 2 * e111 ≤
      3 * (25 * radius ^ 2) * ((3 * 10 ^ 6) / radius ^ 5) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hboundSq (by norm_num)) h111
      h111Nonneg (by positivity)
  have hterm11 : 3 * (2 * bound + 1) * e11 ≤
      3 * (11 * radius) * (15500 / radius ^ 4) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hlinear (by norm_num)) h11
      h11Nonneg (by positivity)
  have hterm1 : 6 * e1 ≤ 6 * (176 / radius ^ 3) :=
    mul_le_mul_of_nonneg_left h1 (by norm_num)
  unfold hodgeJacobianEntryThreeAxis111Envelope
  change 3 * bound ^ 2 * e111 + 3 * (2 * bound + 1) * e11 + 6 * e1 ≤ _
  calc
    _ ≤ 3 * (25 * radius ^ 2) * ((3 * 10 ^ 6) / radius ^ 5) +
          3 * (11 * radius) * (15500 / radius ^ 4) +
            6 * (176 / radius ^ 3) :=
      add_le_add (add_le_add hterm111 hterm11) hterm1
    _ ≤ (226 * 10 ^ 6) / radius ^ 3 := by
      field_simp [hradius.ne']
      norm_num

/-- The exact `(1,1,2)` allocation ledger has inverse-fourth radial scale. -/
theorem hodgeJacobianEntryThreeAxis112Envelope_dyadic_le
    (scale : ℕ) (hscale : 3 ≤ scale) :
    hodgeJacobianEntryThreeAxis112Envelope
      (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) ≤
      (46 * 10 ^ 9) / (dyadicRadius scale : ℝ) ^ 4 := by
  let radius : ℝ := dyadicRadius scale
  let lower := dyadicHodgeControlledLower scale
  let bound := dyadicHodgeControlledBound scale
  let e112 := hodgeReciprocal112Envelope lower bound
  let e111 := hodgeReciprocal111Envelope lower bound
  let e12 := hodgeReciprocalMixedOneTwoEnvelope lower bound
  let e2 := hodgeReciprocalSecondEnvelope lower bound
  let e11 := hodgeReciprocalMixedOneOneEnvelope lower bound
  have hradius : 0 < radius := by
    dsimp [radius]
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  have hboundSq : bound ^ 2 ≤ 25 * radius ^ 2 := by
    simpa [bound, radius] using dyadicHodgeControlledBound_sq_le scale hscale
  have hlinear : 2 * bound + 1 ≤ 11 * radius := by
    simpa [bound, radius] using two_mul_bound_add_one_le_eleven_mul_radius scale hscale
  have h112 : e112 ≤ (6 * 10 ^ 8) / radius ^ 6 := by
    norm_num
    simpa [e112, lower, bound, radius] using
      hodgeReciprocal112Envelope_dyadic_le scale hscale
  have h111 : e111 ≤ (3 * 10 ^ 6) / radius ^ 5 := by
    norm_num
    simpa [e111, lower, bound, radius] using
      hodgeReciprocal111Envelope_dyadic_le scale hscale
  have h12 : e12 ≤ (22 * 10 ^ 5) / radius ^ 5 := by
    norm_num
    simpa [e12, lower, bound, radius] using
      hodgeReciprocalMixedOneTwoEnvelope_dyadic_le scale hscale
  have h2 : e2 ≤ 17000 / radius ^ 4 := by
    simpa [e2, lower, bound, radius] using
      hodgeReciprocalSecondEnvelope_dyadic_le scale hscale
  have h11 : e11 ≤ 15500 / radius ^ 4 := by
    simpa [e11, lower, bound, radius] using
      hodgeReciprocalMixedOneOneEnvelope_dyadic_le scale hscale
  have h112Nonneg : 0 ≤ e112 := by
    dsimp [e112, lower, bound]
    unfold hodgeReciprocal112Envelope hodgeReciprocal111Envelope
      hodgeReciprocalMixedOneTwoEnvelope hodgeReciprocalMixedOneOneEnvelope
      hodgeReciprocalValueEnvelope hodgeReciprocalFirstEnvelope
      hodgeReciprocalSecondEnvelope dyadicHodgeControlledLower dyadicHodgeControlledBound
    positivity
  have h111Nonneg : 0 ≤ e111 := by
    dsimp [e111, lower, bound]
    unfold hodgeReciprocal111Envelope hodgeReciprocalMixedOneOneEnvelope
      dyadicHodgeControlledLower dyadicHodgeControlledBound
    positivity
  have h12Nonneg : 0 ≤ e12 := by
    dsimp [e12, lower, bound]
    unfold hodgeReciprocalMixedOneTwoEnvelope hodgeReciprocalValueEnvelope
      hodgeReciprocalFirstEnvelope hodgeReciprocalSecondEnvelope
      dyadicHodgeControlledLower dyadicHodgeControlledBound
    positivity
  have hterm112 : 3 * bound ^ 2 * e112 ≤
      3 * (25 * radius ^ 2) * ((6 * 10 ^ 8) / radius ^ 6) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hboundSq (by norm_num)) h112
      h112Nonneg (by positivity)
  have hterm111 : 2 * (2 * bound + 1) * e111 ≤
      2 * (11 * radius) * ((3 * 10 ^ 6) / radius ^ 5) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hlinear (by norm_num)) h111
      h111Nonneg (by positivity)
  have hterm12 : 2 * (2 * bound + 1) * e12 ≤
      2 * (11 * radius) * ((22 * 10 ^ 5) / radius ^ 5) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hlinear (by norm_num)) h12
      h12Nonneg (by positivity)
  have hterm2 : 2 * e2 ≤ 2 * (17000 / radius ^ 4) :=
    mul_le_mul_of_nonneg_left h2 (by norm_num)
  have hterm11 : 10 * e11 ≤ 10 * (15500 / radius ^ 4) :=
    mul_le_mul_of_nonneg_left h11 (by norm_num)
  unfold hodgeJacobianEntryThreeAxis112Envelope
  change 3 * bound ^ 2 * e112 + 2 * (2 * bound + 1) * e111 +
    2 * (2 * bound + 1) * e12 + 2 * e2 + 10 * e11 ≤ _
  calc
    _ ≤ 3 * (25 * radius ^ 2) * ((6 * 10 ^ 8) / radius ^ 6) +
        2 * (11 * radius) * ((3 * 10 ^ 6) / radius ^ 5) +
          2 * (11 * radius) * ((22 * 10 ^ 5) / radius ^ 5) +
            2 * (17000 / radius ^ 4) + 10 * (15500 / radius ^ 4) := by
      exact add_le_add (add_le_add (add_le_add (add_le_add hterm112 hterm111)
        hterm12) hterm2) hterm11
    _ ≤ (46 * 10 ^ 9) / radius ^ 4 := by
      field_simp [hradius.ne']
      norm_num

/-- The exact `(1,2,2)` allocation ledger has inverse-fifth radial scale. -/
theorem hodgeJacobianEntryThreeAxis122Envelope_dyadic_le
    (scale : ℕ) (hscale : 3 ≤ scale) :
    hodgeJacobianEntryThreeAxis122Envelope
      (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) ≤
      (12 * 10 ^ 12) / (dyadicRadius scale : ℝ) ^ 5 := by
  let radius : ℝ := dyadicRadius scale
  let lower := dyadicHodgeControlledLower scale
  let bound := dyadicHodgeControlledBound scale
  let e122 := hodgeReciprocal122Envelope lower bound
  let e22 := hodgeReciprocalMixedTwoTwoEnvelope lower bound
  let e112 := hodgeReciprocal112Envelope lower bound
  let e12 := hodgeReciprocalMixedOneTwoEnvelope lower bound
  let e111 := hodgeReciprocal111Envelope lower bound
  have hradius : 0 < radius := by
    dsimp [radius]
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  have hboundSq : bound ^ 2 ≤ 25 * radius ^ 2 := by
    simpa [bound, radius] using dyadicHodgeControlledBound_sq_le scale hscale
  have hlinear : 2 * bound + 1 ≤ 11 * radius := by
    simpa [bound, radius] using two_mul_bound_add_one_le_eleven_mul_radius scale hscale
  have h122 : e122 ≤ (15 * 10 ^ 10) / radius ^ 7 := by
    norm_num
    simpa [e122, lower, bound, radius] using
      hodgeReciprocal122Envelope_dyadic_le scale hscale
  have h22 : e22 ≤ (42 * 10 ^ 7) / radius ^ 6 := by
    norm_num
    simpa [e22, lower, bound, radius] using
      hodgeReciprocalMixedTwoTwoEnvelope_dyadic_le scale hscale
  have h112 : e112 ≤ (6 * 10 ^ 8) / radius ^ 6 := by
    norm_num
    simpa [e112, lower, bound, radius] using
      hodgeReciprocal112Envelope_dyadic_le scale hscale
  have h12 : e12 ≤ (22 * 10 ^ 5) / radius ^ 5 := by
    norm_num
    simpa [e12, lower, bound, radius] using
      hodgeReciprocalMixedOneTwoEnvelope_dyadic_le scale hscale
  have h111 : e111 ≤ (3 * 10 ^ 6) / radius ^ 5 := by
    norm_num
    simpa [e111, lower, bound, radius] using
      hodgeReciprocal111Envelope_dyadic_le scale hscale
  have h122Nonneg : 0 ≤ e122 := by
    dsimp [e122, lower, bound]
    unfold hodgeReciprocal122Envelope hodgeReciprocal112Envelope
      hodgeReciprocal111Envelope hodgeReciprocalMixedTwoTwoEnvelope
      hodgeReciprocalMixedOneTwoEnvelope hodgeReciprocalMixedOneOneEnvelope
      hodgeReciprocalValueEnvelope hodgeReciprocalFirstEnvelope
      hodgeReciprocalSecondEnvelope dyadicHodgeControlledLower dyadicHodgeControlledBound
    positivity
  have h22Nonneg : 0 ≤ e22 := by
    dsimp [e22, lower, bound]
    unfold hodgeReciprocalMixedTwoTwoEnvelope hodgeReciprocalValueEnvelope
      hodgeReciprocalFirstEnvelope hodgeReciprocalSecondEnvelope
      dyadicHodgeControlledLower dyadicHodgeControlledBound
    positivity
  have h112Nonneg : 0 ≤ e112 := by
    dsimp [e112, lower, bound]
    unfold hodgeReciprocal112Envelope hodgeReciprocal111Envelope
      hodgeReciprocalMixedOneTwoEnvelope hodgeReciprocalMixedOneOneEnvelope
      hodgeReciprocalValueEnvelope hodgeReciprocalFirstEnvelope
      hodgeReciprocalSecondEnvelope dyadicHodgeControlledLower dyadicHodgeControlledBound
    positivity
  have hterm122 : 3 * bound ^ 2 * e122 ≤
      3 * (25 * radius ^ 2) * ((15 * 10 ^ 10) / radius ^ 7) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hboundSq (by norm_num)) h122
      h122Nonneg (by positivity)
  have hterm22 : (2 * bound + 1) * e22 ≤
      (11 * radius) * ((42 * 10 ^ 7) / radius ^ 6) :=
    mul_le_mul hlinear h22 h22Nonneg (by positivity)
  have hterm112 : 4 * (2 * bound + 1) * e112 ≤
      4 * (11 * radius) * ((6 * 10 ^ 8) / radius ^ 6) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hlinear (by norm_num)) h112
      h112Nonneg (by positivity)
  have hterm12 : 12 * e12 ≤ 12 * ((22 * 10 ^ 5) / radius ^ 5) :=
    mul_le_mul_of_nonneg_left h12 (by norm_num)
  have hterm111 : 8 * e111 ≤ 8 * ((3 * 10 ^ 6) / radius ^ 5) :=
    mul_le_mul_of_nonneg_left h111 (by norm_num)
  unfold hodgeJacobianEntryThreeAxis122Envelope
  change 3 * bound ^ 2 * e122 + (2 * bound + 1) * e22 +
    4 * (2 * bound + 1) * e112 + 12 * e12 + 8 * e111 ≤ _
  calc
    _ ≤ 3 * (25 * radius ^ 2) * ((15 * 10 ^ 10) / radius ^ 7) +
        (11 * radius) * ((42 * 10 ^ 7) / radius ^ 6) +
          4 * (11 * radius) * ((6 * 10 ^ 8) / radius ^ 6) +
            12 * ((22 * 10 ^ 5) / radius ^ 5) +
              8 * ((3 * 10 ^ 6) / radius ^ 5) := by
      exact add_le_add (add_le_add (add_le_add (add_le_add hterm122 hterm22)
        hterm112) hterm12) hterm111
    _ ≤ (12 * 10 ^ 12) / radius ^ 5 := by
      field_simp [hradius.ne']
      norm_num

section Audit

#print axioms threeAxisMixedForwardDifference_one_one_one_mul_eq_allocationReturn
#print axioms hodge112OccurrenceLedger_length
#print axioms hodge122OccurrenceLedger_length
#print axioms threeAxisMixedForwardDifference_one_one_two_mul_eq_occurrenceReturn
#print axioms threeAxisMixedForwardDifference_one_two_two_mul_eq_occurrenceReturn
#print axioms hodge112Allocation_card
#print axioms hodge122Allocation_card
#print axioms hodge112AllocationAddressLedger_length
#print axioms hodge122AllocationAddressLedger_length
#print axioms threeAxisMixedForwardDifference_one_one_two_mul_eq_stagedAllocationReturn
#print axioms threeAxisMixedForwardDifference_one_two_two_mul_eq_stagedAllocationReturn
#print axioms hodge112OccurrenceReturn_eq_stagedAllocationReturn
#print axioms hodge122OccurrenceReturn_eq_stagedAllocationReturn
#print axioms hodgeJacobianMultiplierEntry_threeAxisMixedForwardDifference_one_one_two_eq
#print axioms hodgeJacobianMultiplierEntry_threeAxisMixedForwardDifference_one_two_two_eq
#print axioms norm_hodgeJacobianMultiplierEntry_threeAxisMixedForwardDifference_one_one_one_le
#print axioms hodgeJacobianEntryThreeAxis111Envelope_dyadic_le
#print axioms hodgeJacobianEntryThreeAxis112Envelope_dyadic_le
#print axioms hodgeJacobianEntryThreeAxis122Envelope_dyadic_le

end Audit

end Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeSubsetEnvelope
