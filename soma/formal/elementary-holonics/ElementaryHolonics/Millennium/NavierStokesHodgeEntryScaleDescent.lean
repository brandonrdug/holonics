import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeThreeAxisOneFace

/-!
# Strict scale descent for the Hodge entry itself

**[proved-derived]** The quadratic-denominator recurrence is not confined to its reciprocal.  If
an addressed word annihilates the numerator of a quotient section, the complete shifted product
ledger forces the same strict predecessor recurrence for the quotient.  Applied to a genuine
Hodge-Jacobian entry, this lifts the checked `11` and `111` faces to the missing `112` face without
introducing an analytic hypothesis.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesHodgeEntryScaleDescent

open Soma.Holonics.HigherDifferenceTransport
open Soma.Holonics.HigherDifferenceScaleDescent
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesSmoothHodgeJacobianBand
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeKernelDifference
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeLocalizedVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeHigherMixedVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeLowerMixedVariation
open Soma.Holonics.Millennium.NavierStokesReciprocalDifferenceRecurrence
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeEnvelopeScaling
open Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeScaleDescent
open Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeProductMass
open Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeSubsetEnvelope

/-- Exact returned recurrence for any right section whose product with the denominator is
annihilated by the addressed word. -/
theorem differenceWord_right_recurrence_of_product_zero
    (word : List (Fin 3)) (right : SpatialFrequency → ℂ) (frequency : SpatialFrequency)
    (hzero : differenceWord coordinateTransport word
      (fun current ↦ (frequencySquared current : ℂ) * right current) frequency = 0) :
    (frequencySquared frequency : ℂ) *
        differenceWord coordinateTransport word right frequency =
      -ledgerSum (reciprocalRemainderLedger coordinateTransport word
        (fun current ↦ (frequencySquared current : ℂ)) right) frequency := by
  have hexpanded := differenceWord_mul_eq_principal_add_remainder
    coordinateTransport word (fun current ↦ (frequencySquared current : ℂ)) right frequency
  have hsum :
      (frequencySquared frequency : ℂ) *
          differenceWord coordinateTransport word right frequency +
        ledgerSum (reciprocalRemainderLedger coordinateTransport word
          (fun current ↦ (frequencySquared current : ℂ)) right) frequency = 0 :=
    hexpanded.symm.trans hzero
  calc
    (frequencySquared frequency : ℂ) *
        differenceWord coordinateTransport word right frequency =
      (frequencySquared frequency : ℂ) *
          differenceWord coordinateTransport word right frequency +
        ledgerSum (reciprocalRemainderLedger coordinateTransport word
          (fun current ↦ (frequencySquared current : ℂ)) right) frequency -
        ledgerSum (reciprocalRemainderLedger coordinateTransport word
          (fun current ↦ (frequencySquared current : ℂ)) right) frequency := by ring
    _ = 0 - ledgerSum (reciprocalRemainderLedger coordinateTransport word
        (fun current ↦ (frequencySquared current : ℂ)) right) frequency := by rw [hsum]
    _ = -ledgerSum (reciprocalRemainderLedger coordinateTransport word
        (fun current ↦ (frequencySquared current : ℂ)) right) frequency := by ring

/-- Division by the positive quadratic aperture for an arbitrary right section. -/
theorem norm_differenceWord_right_le_div_of_frequencySquared_recurrence
    {lower envelope : ℝ} (hlower : 0 < lower)
    (word : List (Fin 3)) (right : SpatialFrequency → ℂ)
    (frequency : SpatialFrequency) (returned : ℂ)
    (hfrequency : lower ≤ frequencySquared frequency)
    (hrecurrence : (frequencySquared frequency : ℂ) *
      differenceWord coordinateTransport word right frequency = -returned)
    (hreturn : ‖returned‖ ≤ envelope) :
    ‖differenceWord coordinateTransport word right frequency‖ ≤ envelope / lower := by
  have hfrequencyPositive : 0 < frequencySquared frequency := hlower.trans_le hfrequency
  have hdenominatorNorm : ‖(frequencySquared frequency : ℂ)‖ =
      frequencySquared frequency := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hfrequencyPositive]
  rw [le_div_iff₀ hlower]
  calc
    ‖differenceWord coordinateTransport word right frequency‖ * lower ≤
        ‖differenceWord coordinateTransport word right frequency‖ *
          frequencySquared frequency :=
      mul_le_mul_of_nonneg_left hfrequency (norm_nonneg _)
    _ = ‖(frequencySquared frequency : ℂ) *
          differenceWord coordinateTransport word right frequency‖ := by
      rw [norm_mul, hdenominatorNorm]
      ring
    _ = ‖returned‖ := by rw [hrecurrence, norm_neg]
    _ ≤ envelope := hreturn

/-- The quotient-section grouped return for the `112` word. -/
def hodgeEntry112GroupedActiveReturn
    (doubled : Fin 3) (right : SpatialFrequency → ℂ)
    (frequency : SpatialFrequency) : ℂ :=
  (∑ axis : Fin 3,
    (oneOneTwoFirstMultiplicity doubled axis : ℂ) *
      differenceWord coordinateTransport [axis]
          (fun current ↦ (frequencySquared current : ℂ)) frequency *
        differenceWord coordinateTransport (oneOneTwoRemoveOne doubled axis) right
          (coordinateTransport axis frequency)) +
    differenceWord coordinateTransport [doubled, doubled]
        (fun current ↦ (frequencySquared current : ℂ)) frequency *
      differenceWord coordinateTransport (oneEachAxisRemoveOne doubled) right
        (coordinateTransport doubled (coordinateTransport doubled frequency))

set_option maxHeartbeats 800000 in
/-- The complete nonprincipal product ledger of a `112` quotient section condenses to its five
active denominator occurrences. -/
theorem hodgeEntry112_remainderLedgerSum_eq_groupedReturn
    (doubled : Fin 3) (right : SpatialFrequency → ℂ) (frequency : SpatialFrequency) :
    ledgerSum (reciprocalRemainderLedger coordinateTransport (oneOneTwoWord doubled)
        (fun current ↦ (frequencySquared current : ℂ)) right) frequency =
      hodgeEntry112GroupedActiveReturn doubled right frequency := by
  fin_cases doubled <;>
    simp [oneOneTwoWord, reciprocalRemainderLedger, principalFace, expandFace,
      rightBranch, leftBranch, ledgerSum, ProductFace.value,
      hodgeEntry112GroupedActiveReturn, oneOneTwoRemoveOne,
      oneOneTwoFirstMultiplicity, oneEachAxisRemoveOne, Fin.sum_univ_succ,
      difference_shift_of_interchange coordinateTransport coordinateTransport_interchange,
      difference, shift, coordinateTransport, coordinateStep, frequencySquared] <;> ring

/-- Every `112` word annihilates the quadratic Hodge numerator. -/
theorem differenceWord_hodgeJacobianRatioNumerator_oneOneTwo_eq_zero
    (doubled : Fin 3) (frequency : SpatialFrequency)
    (component coordinate input : Fin 3) :
    differenceWord coordinateTransport (oneOneTwoWord doubled)
      (fun current ↦ hodgeJacobianRatioNumerator current component coordinate input)
      frequency = 0 := by
  fin_cases doubled
  · have hzero := congrFun
      (hodgeJacobianRatioNumerator_allocation_eq_zero_of_three_le
        (2 : Fin 3) (1 : Fin 3) (1 : Fin 3) component coordinate input (by norm_num))
      frequency
    have hword := congrFun
      (differenceWord_eq_threeAxisMixedForwardDifference 0 1 2 2 1 1
        (fun current ↦ hodgeJacobianRatioNumerator current component coordinate input)) frequency
    simpa [oneOneTwoWord] using hword.trans hzero
  · have hzero := congrFun
      (hodgeJacobianRatioNumerator_allocation_eq_zero_of_three_le
        (1 : Fin 3) (2 : Fin 3) (1 : Fin 3) component coordinate input (by norm_num))
      frequency
    have hword := congrFun
      (differenceWord_eq_threeAxisMixedForwardDifference 0 1 2 1 2 1
        (fun current ↦ hodgeJacobianRatioNumerator current component coordinate input)) frequency
    simpa [oneOneTwoWord] using hword.trans hzero
  · have hzero := congrFun
      (hodgeJacobianRatioNumerator_allocation_eq_zero_of_three_le
        (1 : Fin 3) (1 : Fin 3) (2 : Fin 3) component coordinate input (by norm_num))
      frequency
    have hword := congrFun
      (differenceWord_eq_threeAxisMixedForwardDifference 0 1 2 1 1 2
        (fun current ↦ hodgeJacobianRatioNumerator current component coordinate input)) frequency
    simpa [oneOneTwoWord] using hword.trans hzero

/-- The genuine Hodge entry obeys the exact five-occurrence `112` predecessor recurrence. -/
theorem hodgeJacobianMultiplierEntry_oneOneTwo_groupedRecurrence
    (doubled : Fin 3) (frequency : SpatialFrequency)
    (component coordinate input : Fin 3) :
    (frequencySquared frequency : ℂ) *
        differenceWord coordinateTransport (oneOneTwoWord doubled)
          (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
          frequency =
      -hodgeEntry112GroupedActiveReturn doubled
        (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
        frequency := by
  let entry := fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input
  have hproduct :
      (fun current ↦ (frequencySquared current : ℂ) * entry current) =
        fun current ↦ hodgeJacobianRatioNumerator current component coordinate input := by
    funext current
    by_cases hcurrent : current = 0
    · subst current
      simp [entry, hodgeJacobianMultiplierEntry_eq_ratio,
        hodgeJacobianRatioNumerator, hodgeCrossBasisFactor]
    · have hsquare : ((frequencySquared current : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (frequencySquared_pos hcurrent).ne'
      simp only [entry, hodgeJacobianMultiplierEntry_eq_ratio,
        hodgeJacobianRatioNumerator, hodgeCrossBasisFactor]
      field_simp
  have hzero : differenceWord coordinateTransport (oneOneTwoWord doubled)
      (fun current ↦ (frequencySquared current : ℂ) * entry current) frequency = 0 := by
    rw [hproduct]
    exact differenceWord_hodgeJacobianRatioNumerator_oneOneTwo_eq_zero
      doubled frequency component coordinate input
  have hrecurrence := differenceWord_right_recurrence_of_product_zero
    (oneOneTwoWord doubled) entry frequency hzero
  rw [hodgeEntry112_remainderLedgerSum_eq_groupedReturn] at hrecurrence
  exact hrecurrence

/-- The controlled Hodge `11` face in addressed-word coordinates. -/
theorem norm_hodgeJacobianMultiplierEntry_pairWord_one_one_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (first second : Fin 3) (haxes : first ≠ second) (frequency : SpatialFrequency)
    (component coordinate input : Fin 3)
    (hstencil : TwoAxisStencilControlled lower bound first second frequency 1 1) :
    ‖differenceWord coordinateTransport [first, second]
      (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
      frequency‖ ≤ hodgeJacobianEntryMixedOneOneEnvelope lower bound := by
  rw [show [first, second] =
      List.replicate 1 first ++ List.replicate 1 second by simp,
    differenceWord_eq_mixedForwardDifference]
  exact norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_one_one_le
    hlower hbound first second haxes frequency component coordinate input hstencil

/-- The controlled Hodge `12` face in addressed-word coordinates. -/
theorem norm_hodgeJacobianMultiplierEntry_pairWord_one_two_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (first second : Fin 3) (haxes : first ≠ second) (frequency : SpatialFrequency)
    (component coordinate input : Fin 3)
    (hstencil : TwoAxisStencilControlled lower bound first second frequency 1 2) :
    ‖differenceWord coordinateTransport [first, second, second]
      (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
      frequency‖ ≤ hodgeJacobianEntryMixedOneTwoEnvelope lower bound := by
  rw [show [first, second, second] =
      List.replicate 1 first ++ List.replicate 2 second by simp,
    differenceWord_eq_mixedForwardDifference]
  exact norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_one_two_le
    hlower hbound first second haxes frequency component coordinate input hstencil

/-- The transposed controlled Hodge `21` face in addressed-word coordinates. -/
theorem norm_hodgeJacobianMultiplierEntry_pairWord_two_one_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (first second : Fin 3) (haxes : first ≠ second) (frequency : SpatialFrequency)
    (component coordinate input : Fin 3)
    (hstencil : TwoAxisStencilControlled lower bound first second frequency 2 1) :
    ‖differenceWord coordinateTransport [first, first, second]
      (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
      frequency‖ ≤ hodgeJacobianEntryMixedOneTwoEnvelope lower bound := by
  rw [show [first, first, second] =
      List.replicate 2 first ++ List.replicate 1 second by simp,
    differenceWord_eq_mixedForwardDifference]
  exact norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_two_one_le
    hlower hbound first second haxes frequency component coordinate input hstencil

/-- The controlled Hodge `111` face in addressed-word coordinates. -/
theorem norm_hodgeJacobianMultiplierEntry_oneEach_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (frequency : SpatialFrequency) (component coordinate input : Fin 3)
    (hstencil : ThreeAxisStencilControlled lower bound 0 1 2 frequency 1 1 1) :
    ‖differenceWord coordinateTransport oneEachAxisWord
      (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
      frequency‖ ≤ hodgeJacobianEntryThreeAxis111Envelope lower bound := by
  rw [show oneEachAxisWord =
      List.replicate 1 0 ++ List.replicate 1 1 ++ List.replicate 1 2 by rfl,
    differenceWord_eq_threeAxisMixedForwardDifference]
  exact norm_hodgeJacobianMultiplierEntry_threeAxisMixedForwardDifference_one_one_one_le
    hlower hbound frequency component coordinate input hstencil

/-- Heterogeneous Hodge-entry predecessors of an addressed `112` face. -/
structure HodgeEntry112LowerOrderEnvelope
    (doubled : Fin 3) (right : SpatialFrequency → ℂ) (frequency : SpatialFrequency)
    (oneOneOneBound oneTwoBound oneOneBound : ℝ) : Prop where
  first : ∀ axis : Fin 3,
    ‖differenceWord coordinateTransport (oneOneTwoRemoveOne doubled axis) right
      (coordinateTransport axis frequency)‖ ≤
        if axis = doubled then oneOneOneBound else oneTwoBound
  second :
    ‖differenceWord coordinateTransport (oneEachAxisRemoveOne doubled) right
      (coordinateTransport doubled (coordinateTransport doubled frequency))‖ ≤ oneOneBound

/-- The five active Hodge-entry predecessor occurrences return the exact `2+2+1` envelope. -/
theorem norm_hodgeEntry112GroupedActiveReturn_le
    {bound oneOneOneBound oneTwoBound oneOneBound : ℝ}
    (hbound : 0 ≤ bound) (doubled : Fin 3) (right : SpatialFrequency → ℂ)
    (frequency : SpatialFrequency)
    (hcoordinates : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound)
    (hlower : HodgeEntry112LowerOrderEnvelope doubled right frequency
      oneOneOneBound oneTwoBound oneOneBound) :
    ‖hodgeEntry112GroupedActiveReturn doubled right frequency‖ ≤
      2 * (2 * bound + 1) * oneOneOneBound +
        2 * (2 * bound + 1) * oneTwoBound + 2 * oneOneBound := by
  unfold hodgeEntry112GroupedActiveReturn
  calc
    ‖(∑ axis : Fin 3,
          (oneOneTwoFirstMultiplicity doubled axis : ℂ) *
            differenceWord coordinateTransport [axis]
                (fun current ↦ (frequencySquared current : ℂ)) frequency *
              differenceWord coordinateTransport (oneOneTwoRemoveOne doubled axis) right
                (coordinateTransport axis frequency)) +
        differenceWord coordinateTransport [doubled, doubled]
            (fun current ↦ (frequencySquared current : ℂ)) frequency *
          differenceWord coordinateTransport (oneEachAxisRemoveOne doubled) right
            (coordinateTransport doubled (coordinateTransport doubled frequency))‖ ≤
      ‖∑ axis : Fin 3,
          (oneOneTwoFirstMultiplicity doubled axis : ℂ) *
            differenceWord coordinateTransport [axis]
                (fun current ↦ (frequencySquared current : ℂ)) frequency *
              differenceWord coordinateTransport (oneOneTwoRemoveOne doubled axis) right
                (coordinateTransport axis frequency)‖ +
        ‖differenceWord coordinateTransport [doubled, doubled]
            (fun current ↦ (frequencySquared current : ℂ)) frequency *
          differenceWord coordinateTransport (oneEachAxisRemoveOne doubled) right
            (coordinateTransport doubled (coordinateTransport doubled frequency))‖ :=
      norm_add_le _ _
    _ ≤ (∑ axis : Fin 3,
          (oneOneTwoFirstMultiplicity doubled axis : ℝ) * (2 * bound + 1) *
            (if axis = doubled then oneOneOneBound else oneTwoBound)) +
        2 * oneOneBound := by
      apply add_le_add
      · refine (norm_sum_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro axis _
        simp only [norm_mul, Complex.norm_natCast]
        have hdenominator := norm_hodgeDenominator_singleDifference_le
          hbound axis frequency hcoordinates
        have hpredecessor := hlower.first axis
        have hmultiplicity : 0 ≤ (oneOneTwoFirstMultiplicity doubled axis : ℝ) := by
          positivity
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hdenominator hmultiplicity)
          hpredecessor (norm_nonneg _) (by positivity)
      · rw [norm_mul, norm_hodgeDenominator_sameAxis_secondDifference]
        exact mul_le_mul_of_nonneg_left hlower.second (by norm_num)
    _ = 2 * (2 * bound + 1) * oneOneOneBound +
        2 * (2 * bound + 1) * oneTwoBound + 2 * oneOneBound := by
      fin_cases doubled <;>
        rw [Fin.sum_univ_succ, Fin.sum_univ_two] <;>
        simp [oneOneTwoFirstMultiplicity] <;> ring

/-- The recursive Hodge-entry envelope at the `112` stage. -/
def hodgeJacobianEntryThreeAxis112DescentEnvelope (lower bound : ℝ) : ℝ :=
  (2 * (2 * bound + 1) * hodgeJacobianEntryThreeAxis111Envelope lower bound +
      2 * (2 * bound + 1) * hodgeJacobianEntryMixedOneTwoEnvelope lower bound +
      2 * hodgeJacobianEntryMixedOneOneEnvelope lower bound) / lower

/-- A controlled Hodge entry with any addressed `112` order descends to its checked `111`, `12`,
and `11` predecessor faces. -/
theorem norm_hodgeJacobianMultiplierEntry_oneOneTwo_le_of_controlled
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (doubled : Fin 3) (frequency : SpatialFrequency)
    (component coordinate input : Fin 3)
    (hstencil : ThreeAxisStencilControlled lower bound 0 1 2 frequency
      (oneOneTwoAxisOrder doubled 0) (oneOneTwoAxisOrder doubled 1)
        (oneOneTwoAxisOrder doubled 2)) :
    ‖differenceWord coordinateTransport (oneOneTwoWord doubled)
      (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
      frequency‖ ≤ hodgeJacobianEntryThreeAxis112DescentEnvelope lower bound := by
  let entry := fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input
  have hcoordinates : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound := by
    simpa using (hstencil 0 (by simp [oneOneTwoAxisOrder])
      0 (by simp [oneOneTwoAxisOrder]) 0 (by simp [oneOneTwoAxisOrder])).2
  have hfrequency : lower ≤ frequencySquared frequency := by
    simpa using (hstencil 0 (by simp [oneOneTwoAxisOrder])
      0 (by simp [oneOneTwoAxisOrder]) 0 (by simp [oneOneTwoAxisOrder])).1
  have hlowerOrders : HodgeEntry112LowerOrderEnvelope doubled entry frequency
      (hodgeJacobianEntryThreeAxis111Envelope lower bound)
      (hodgeJacobianEntryMixedOneTwoEnvelope lower bound)
      (hodgeJacobianEntryMixedOneOneEnvelope lower bound) := by
    fin_cases doubled
    · have hstencil' : ThreeAxisStencilControlled lower bound 0 1 2 frequency 2 1 1 := by
        simpa [oneOneTwoAxisOrder] using hstencil
      refine ⟨?_, ?_⟩
      · intro axis
        fin_cases axis
        · have hsub := hstencil'.rebase
              (firstOffset := 1) (secondOffset := 0) (thirdOffset := 0)
              (firstOrder := 1) (secondOrder := 1) (thirdOrder := 1)
              (by omega) (by omega) (by omega)
          have hraw := norm_hodgeJacobianMultiplierEntry_oneEach_le
            hlower hbound (threeAxisStencilPoint 0 1 2 frequency 1 0 0)
            component coordinate input hsub
          simpa [entry, oneOneTwoRemoveOne, oneEachAxisWord, threeAxisStencilPoint,
            coordinateTransport] using hraw
        · have hraw := norm_hodgeJacobianMultiplierEntry_pairWord_two_one_le
            hlower hbound 0 2 (by decide)
            (threeAxisStencilPoint 0 1 2 frequency 0 1 0)
            component coordinate input
            (hstencil'.firstThird (secondOffset := 1) (by omega))
          simpa [entry, oneOneTwoRemoveOne, threeAxisStencilPoint,
            coordinateTransport] using hraw
        · have hraw := norm_hodgeJacobianMultiplierEntry_pairWord_two_one_le
            hlower hbound 0 1 (by decide)
            (threeAxisStencilPoint 0 1 2 frequency 0 0 1)
            component coordinate input
            (hstencil'.firstSecond (thirdOffset := 1) (by omega))
          simpa [entry, oneOneTwoRemoveOne, threeAxisStencilPoint,
            coordinateTransport] using hraw
      · have hraw := norm_hodgeJacobianMultiplierEntry_pairWord_one_one_le
          hlower hbound 1 2 (by decide)
          (threeAxisStencilPoint 0 1 2 frequency 2 0 0)
          component coordinate input
          (hstencil'.secondThird (firstOffset := 2) (by omega))
        have hbase : threeAxisStencilPoint 0 1 2 frequency 2 0 0 =
            coordinateTransport 0 (coordinateTransport 0 frequency) := by
          simp only [threeAxisStencilPoint, coordinateTransport, zero_nsmul, add_zero]
          rw [two_nsmul]
          abel
        rw [hbase] at hraw
        simpa [entry, oneEachAxisRemoveOne] using hraw
    · have hstencil' : ThreeAxisStencilControlled lower bound 0 1 2 frequency 1 2 1 := by
        simpa [oneOneTwoAxisOrder] using hstencil
      refine ⟨?_, ?_⟩
      · intro axis
        fin_cases axis
        · have hraw := norm_hodgeJacobianMultiplierEntry_pairWord_two_one_le
            hlower hbound 1 2 (by decide)
            (threeAxisStencilPoint 0 1 2 frequency 1 0 0)
            component coordinate input
            (hstencil'.secondThird (firstOffset := 1) (by omega))
          simpa [entry, oneOneTwoRemoveOne, threeAxisStencilPoint,
            coordinateTransport] using hraw
        · have hsub := hstencil'.rebase
              (firstOffset := 0) (secondOffset := 1) (thirdOffset := 0)
              (firstOrder := 1) (secondOrder := 1) (thirdOrder := 1)
              (by omega) (by omega) (by omega)
          have hraw := norm_hodgeJacobianMultiplierEntry_oneEach_le
            hlower hbound (threeAxisStencilPoint 0 1 2 frequency 0 1 0)
            component coordinate input hsub
          simpa [entry, oneOneTwoRemoveOne, oneEachAxisWord, threeAxisStencilPoint,
            coordinateTransport] using hraw
        · have hraw := norm_hodgeJacobianMultiplierEntry_pairWord_one_two_le
            hlower hbound 0 1 (by decide)
            (threeAxisStencilPoint 0 1 2 frequency 0 0 1)
            component coordinate input
            (hstencil'.firstSecond (thirdOffset := 1) (by omega))
          simpa [entry, oneOneTwoRemoveOne, threeAxisStencilPoint,
            coordinateTransport] using hraw
      · have hraw := norm_hodgeJacobianMultiplierEntry_pairWord_one_one_le
          hlower hbound 0 2 (by decide)
          (threeAxisStencilPoint 0 1 2 frequency 0 2 0)
          component coordinate input
          (hstencil'.firstThird (secondOffset := 2) (by omega))
        have hbase : threeAxisStencilPoint 0 1 2 frequency 0 2 0 =
            coordinateTransport 1 (coordinateTransport 1 frequency) := by
          simp only [threeAxisStencilPoint, coordinateTransport, zero_nsmul, add_zero]
          rw [two_nsmul]
          abel
        rw [hbase] at hraw
        simpa [entry, oneEachAxisRemoveOne] using hraw
    · have hstencil' : ThreeAxisStencilControlled lower bound 0 1 2 frequency 1 1 2 := by
        simpa [oneOneTwoAxisOrder] using hstencil
      refine ⟨?_, ?_⟩
      · intro axis
        fin_cases axis
        · have hraw := norm_hodgeJacobianMultiplierEntry_pairWord_one_two_le
            hlower hbound 1 2 (by decide)
            (threeAxisStencilPoint 0 1 2 frequency 1 0 0)
            component coordinate input
            (hstencil'.secondThird (firstOffset := 1) (by omega))
          simpa [entry, oneOneTwoRemoveOne, threeAxisStencilPoint,
            coordinateTransport] using hraw
        · have hraw := norm_hodgeJacobianMultiplierEntry_pairWord_one_two_le
            hlower hbound 0 2 (by decide)
            (threeAxisStencilPoint 0 1 2 frequency 0 1 0)
            component coordinate input
            (hstencil'.firstThird (secondOffset := 1) (by omega))
          simpa [entry, oneOneTwoRemoveOne, threeAxisStencilPoint,
            coordinateTransport] using hraw
        · have hsub := hstencil'.rebase
              (firstOffset := 0) (secondOffset := 0) (thirdOffset := 1)
              (firstOrder := 1) (secondOrder := 1) (thirdOrder := 1)
              (by omega) (by omega) (by omega)
          have hraw := norm_hodgeJacobianMultiplierEntry_oneEach_le
            hlower hbound (threeAxisStencilPoint 0 1 2 frequency 0 0 1)
            component coordinate input hsub
          simpa [entry, oneOneTwoRemoveOne, oneEachAxisWord, threeAxisStencilPoint,
            coordinateTransport] using hraw
      · have hraw := norm_hodgeJacobianMultiplierEntry_pairWord_one_one_le
          hlower hbound 0 1 (by decide)
          (threeAxisStencilPoint 0 1 2 frequency 0 0 2)
          component coordinate input
          (hstencil'.firstSecond (thirdOffset := 2) (by omega))
        have hbase : threeAxisStencilPoint 0 1 2 frequency 0 0 2 =
            coordinateTransport 2 (coordinateTransport 2 frequency) := by
          simp only [threeAxisStencilPoint, coordinateTransport, zero_nsmul, add_zero]
          rw [two_nsmul]
          abel
        rw [hbase] at hraw
        simpa [entry, oneEachAxisRemoveOne] using hraw
  have hgrouped := norm_hodgeEntry112GroupedActiveReturn_le hbound doubled entry frequency
    hcoordinates hlowerOrders
  unfold hodgeJacobianEntryThreeAxis112DescentEnvelope
  exact norm_differenceWord_right_le_div_of_frequencySquared_recurrence
    hlower (oneOneTwoWord doubled) entry frequency
    (hodgeEntry112GroupedActiveReturn doubled entry frequency) hfrequency
    (hodgeJacobianMultiplierEntry_oneOneTwo_groupedRecurrence
      doubled frequency component coordinate input) hgrouped

/-- **[proved-derived]** The strict `112` Hodge-entry descent has exact inverse-fourth dyadic
scale.  The numerator `8626400000` is the sum of the three proved predecessor contributions, and
the final factor four is the exact controlled-aperture reciprocal bound. -/
theorem hodgeJacobianEntryThreeAxis112DescentEnvelope_dyadic_le
    (scale : ℕ) (hscale : 3 ≤ scale) :
    hodgeJacobianEntryThreeAxis112DescentEnvelope
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) ≤
      34505600000 / (dyadicRadius scale : ℝ) ^ 4 := by
  let radius : ℝ := dyadicRadius scale
  let lower := dyadicHodgeControlledLower scale
  let bound := dyadicHodgeControlledBound scale
  let e111 := hodgeJacobianEntryThreeAxis111Envelope lower bound
  let e12 := hodgeJacobianEntryMixedOneTwoEnvelope lower bound
  let e11 := hodgeJacobianEntryMixedOneOneEnvelope lower bound
  have hradius : 0 < radius := by
    dsimp [radius]
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  have hlower : 0 < lower := by
    simpa [lower] using dyadicHodgeControlledLower_pos scale hscale
  have hlinear : 2 * bound + 1 ≤ 11 * radius := by
    simpa [bound, radius] using
      two_mul_bound_add_one_le_eleven_mul_radius scale hscale
  have hboundNonneg : 0 ≤ bound := by
    dsimp [bound]
    unfold dyadicHodgeControlledBound
    positivity
  have h111 : e111 ≤ 226000000 / radius ^ 3 := by
    have hsource := hodgeJacobianEntryThreeAxis111Envelope_dyadic_le scale hscale
    norm_num at hsource
    simpa [e111, lower, bound, radius] using hsource
  have h12 : e12 ≤ 166000000 / radius ^ 3 := by
    simpa [e12, lower, bound, radius] using
      hodgeJacobianEntryMixedOneTwoEnvelope_dyadic_le scale hscale
  have h11 : e11 ≤ 1200000 / radius ^ 2 := by
    simpa [e11, lower, bound, radius] using
      hodgeJacobianEntryMixedOneOneEnvelope_dyadic_le scale hscale
  have he111 : 0 ≤ e111 := by
    dsimp [e111, lower, bound]
    unfold hodgeJacobianEntryThreeAxis111Envelope hodgeReciprocal111Envelope
      hodgeReciprocalMixedOneOneEnvelope hodgeReciprocalFirstEnvelope
      dyadicHodgeControlledLower dyadicHodgeControlledBound
    positivity
  have he12 : 0 ≤ e12 := by
    dsimp [e12, lower, bound]
    unfold hodgeJacobianEntryMixedOneTwoEnvelope hodgeReciprocalMixedOneTwoEnvelope
      hodgeReciprocalMixedOneOneEnvelope hodgeReciprocalValueEnvelope
      hodgeReciprocalFirstEnvelope hodgeReciprocalSecondEnvelope
      dyadicHodgeControlledLower dyadicHodgeControlledBound
    positivity
  have he11 : 0 ≤ e11 := by
    dsimp [e11, lower, bound]
    unfold hodgeJacobianEntryMixedOneOneEnvelope hodgeReciprocalMixedOneOneEnvelope
      hodgeReciprocalValueEnvelope hodgeReciprocalFirstEnvelope
      dyadicHodgeControlledLower dyadicHodgeControlledBound
    positivity
  have hterm111 : 2 * (2 * bound + 1) * e111 ≤
      2 * (11 * radius) * (226000000 / radius ^ 3) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hlinear (by norm_num)) h111
      he111 (by positivity)
  have hterm12 : 2 * (2 * bound + 1) * e12 ≤
      2 * (11 * radius) * (166000000 / radius ^ 3) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hlinear (by norm_num)) h12
      he12 (by positivity)
  have hterm11 : 2 * e11 ≤ 2 * (1200000 / radius ^ 2) :=
    mul_le_mul_of_nonneg_left h11 (by norm_num)
  have hnumerator :
      2 * (2 * bound + 1) * e111 + 2 * (2 * bound + 1) * e12 + 2 * e11 ≤
        8626400000 / radius ^ 2 := by
    calc
      _ ≤ 2 * (11 * radius) * (226000000 / radius ^ 3) +
          2 * (11 * radius) * (166000000 / radius ^ 3) +
          2 * (1200000 / radius ^ 2) :=
        add_le_add (add_le_add hterm111 hterm12) hterm11
      _ = 8626400000 / radius ^ 2 := by
        field_simp [hradius.ne']
        norm_num
  have hinverse : 1 / lower ≤ 4 / radius ^ 2 := by
    simpa [lower, radius] using one_div_dyadicHodgeControlledLower_le scale hscale
  unfold hodgeJacobianEntryThreeAxis112DescentEnvelope
  change (2 * (2 * bound + 1) * e111 + 2 * (2 * bound + 1) * e12 + 2 * e11) /
      lower ≤ _
  rw [div_eq_mul_inv, show lower⁻¹ = 1 / lower by simp]
  calc
    _ ≤ (8626400000 / radius ^ 2) * (4 / radius ^ 2) := by
      exact mul_le_mul hnumerator hinverse (by positivity) (by positivity)
    _ = 34505600000 / radius ^ 4 := by
      field_simp [hradius.ne']
      norm_num

/-! ### The `122` entry edge -/

/-- The quotient-section grouped return for the `122` word.  The translated receiver of every
predecessor occurrence is retained. -/
def hodgeEntry122GroupedActiveReturn
    (single : Fin 3) (right : SpatialFrequency → ℂ)
    (frequency : SpatialFrequency) : ℂ :=
  (∑ axis : Fin 3,
    (oneTwoTwoFirstMultiplicity single axis : ℂ) *
      differenceWord coordinateTransport [axis]
          (fun current ↦ (frequencySquared current : ℂ)) frequency *
        differenceWord coordinateTransport (oneTwoTwoRemoveOne single axis) right
          (coordinateTransport axis frequency)) +
    ∑ axis : Fin 3, if axis = single then 0 else
      differenceWord coordinateTransport [axis, axis]
          (fun current ↦ (frequencySquared current : ℂ)) frequency *
        differenceWord coordinateTransport (oneTwoTwoRemoveTwo single axis) right
          (coordinateTransport axis (coordinateTransport axis frequency))

set_option maxHeartbeats 1200000 in
/-- The complete nonprincipal product ledger of a `122` quotient section condenses to its seven
active denominator occurrences with multiplicities `1,2,2,1,1`. -/
theorem hodgeEntry122_remainderLedgerSum_eq_groupedReturn
    (single : Fin 3) (right : SpatialFrequency → ℂ) (frequency : SpatialFrequency) :
    ledgerSum (reciprocalRemainderLedger coordinateTransport (oneTwoTwoWord single)
        (fun current ↦ (frequencySquared current : ℂ)) right) frequency =
      hodgeEntry122GroupedActiveReturn single right frequency := by
  fin_cases single <;>
    simp [oneTwoTwoWord, reciprocalRemainderLedger, principalFace, expandFace,
      rightBranch, leftBranch, ledgerSum, ProductFace.value,
      hodgeEntry122GroupedActiveReturn, oneTwoTwoRemoveOne, oneTwoTwoRemoveTwo,
      oneTwoTwoFirstMultiplicity, Fin.sum_univ_succ,
      difference_shift_of_interchange coordinateTransport coordinateTransport_interchange,
      difference, shift, coordinateTransport, coordinateStep, frequencySquared] <;> ring

/-- Every `122` word annihilates the quadratic Hodge numerator. -/
theorem differenceWord_hodgeJacobianRatioNumerator_oneTwoTwo_eq_zero
    (single : Fin 3) (frequency : SpatialFrequency)
    (component coordinate input : Fin 3) :
    differenceWord coordinateTransport (oneTwoTwoWord single)
      (fun current ↦ hodgeJacobianRatioNumerator current component coordinate input)
      frequency = 0 := by
  fin_cases single
  · have hzero := congrFun
      (hodgeJacobianRatioNumerator_allocation_eq_zero_of_three_le
        (1 : Fin 3) (2 : Fin 3) (2 : Fin 3) component coordinate input (by norm_num))
      frequency
    have hword := congrFun
      (differenceWord_eq_threeAxisMixedForwardDifference 0 1 2 1 2 2
        (fun current ↦ hodgeJacobianRatioNumerator current component coordinate input)) frequency
    simpa [oneTwoTwoWord] using hword.trans hzero
  · have hzero := congrFun
      (hodgeJacobianRatioNumerator_allocation_eq_zero_of_three_le
        (2 : Fin 3) (1 : Fin 3) (2 : Fin 3) component coordinate input (by norm_num))
      frequency
    have hword := congrFun
      (differenceWord_eq_threeAxisMixedForwardDifference 0 1 2 2 1 2
        (fun current ↦ hodgeJacobianRatioNumerator current component coordinate input)) frequency
    simpa [oneTwoTwoWord] using hword.trans hzero
  · have hzero := congrFun
      (hodgeJacobianRatioNumerator_allocation_eq_zero_of_three_le
        (2 : Fin 3) (2 : Fin 3) (1 : Fin 3) component coordinate input (by norm_num))
      frequency
    have hword := congrFun
      (differenceWord_eq_threeAxisMixedForwardDifference 0 1 2 2 2 1
        (fun current ↦ hodgeJacobianRatioNumerator current component coordinate input)) frequency
    simpa [oneTwoTwoWord] using hword.trans hzero

/-- The genuine Hodge entry obeys the exact seven-occurrence `122` predecessor recurrence. -/
theorem hodgeJacobianMultiplierEntry_oneTwoTwo_groupedRecurrence
    (single : Fin 3) (frequency : SpatialFrequency)
    (component coordinate input : Fin 3) :
    (frequencySquared frequency : ℂ) *
        differenceWord coordinateTransport (oneTwoTwoWord single)
          (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
          frequency =
      -hodgeEntry122GroupedActiveReturn single
        (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
        frequency := by
  let entry := fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input
  have hproduct :
      (fun current ↦ (frequencySquared current : ℂ) * entry current) =
        fun current ↦ hodgeJacobianRatioNumerator current component coordinate input := by
    funext current
    by_cases hcurrent : current = 0
    · subst current
      simp [entry, hodgeJacobianMultiplierEntry_eq_ratio,
        hodgeJacobianRatioNumerator, hodgeCrossBasisFactor]
    · have hsquare : ((frequencySquared current : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (frequencySquared_pos hcurrent).ne'
      simp only [entry, hodgeJacobianMultiplierEntry_eq_ratio,
        hodgeJacobianRatioNumerator, hodgeCrossBasisFactor]
      field_simp
  have hzero : differenceWord coordinateTransport (oneTwoTwoWord single)
      (fun current ↦ (frequencySquared current : ℂ) * entry current) frequency = 0 := by
    rw [hproduct]
    exact differenceWord_hodgeJacobianRatioNumerator_oneTwoTwo_eq_zero
      single frequency component coordinate input
  have hrecurrence := differenceWord_right_recurrence_of_product_zero
    (oneTwoTwoWord single) entry frequency hzero
  rw [hodgeEntry122_remainderLedgerSum_eq_groupedReturn] at hrecurrence
  exact hrecurrence

/-- The controlled Hodge `22` face in addressed-word coordinates. -/
theorem norm_hodgeJacobianMultiplierEntry_pairWord_two_two_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (first second : Fin 3) (haxes : first ≠ second) (frequency : SpatialFrequency)
    (component coordinate input : Fin 3)
    (hstencil : TwoAxisStencilControlled lower bound first second frequency 2 2) :
    ‖differenceWord coordinateTransport [first, first, second, second]
      (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
      frequency‖ ≤ hodgeJacobianEntryMixedTwoTwoEnvelope lower bound := by
  rw [show [first, first, second, second] =
      List.replicate 2 first ++ List.replicate 2 second by simp,
    differenceWord_eq_mixedForwardDifference]
  exact norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_two_two_le
    hlower hbound first second haxes frequency component coordinate input hstencil

/-- Heterogeneous Hodge-entry predecessors of an addressed `122` face. -/
structure HodgeEntry122LowerOrderEnvelope
    (single : Fin 3) (right : SpatialFrequency → ℂ) (frequency : SpatialFrequency)
    (twoTwoBound oneOneTwoBound oneTwoBound : ℝ) : Prop where
  first : ∀ axis : Fin 3,
    ‖differenceWord coordinateTransport (oneTwoTwoRemoveOne single axis) right
      (coordinateTransport axis frequency)‖ ≤
        if axis = single then twoTwoBound else oneOneTwoBound
  second : ∀ axis : Fin 3, axis ≠ single →
    ‖differenceWord coordinateTransport (oneTwoTwoRemoveTwo single axis) right
      (coordinateTransport axis (coordinateTransport axis frequency))‖ ≤ oneTwoBound

/-- The seven active Hodge-entry predecessor occurrences return the exact `1+4+2` envelope. -/
theorem norm_hodgeEntry122GroupedActiveReturn_le
    {bound twoTwoBound oneOneTwoBound oneTwoBound : ℝ}
    (hbound : 0 ≤ bound) (single : Fin 3) (right : SpatialFrequency → ℂ)
    (frequency : SpatialFrequency)
    (hcoordinates : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound)
    (hlower : HodgeEntry122LowerOrderEnvelope single right frequency
      twoTwoBound oneOneTwoBound oneTwoBound) :
    ‖hodgeEntry122GroupedActiveReturn single right frequency‖ ≤
      (2 * bound + 1) * twoTwoBound +
        4 * (2 * bound + 1) * oneOneTwoBound + 4 * oneTwoBound := by
  unfold hodgeEntry122GroupedActiveReturn
  calc
    ‖(∑ axis : Fin 3,
          (oneTwoTwoFirstMultiplicity single axis : ℂ) *
            differenceWord coordinateTransport [axis]
                (fun current ↦ (frequencySquared current : ℂ)) frequency *
              differenceWord coordinateTransport (oneTwoTwoRemoveOne single axis) right
                (coordinateTransport axis frequency)) +
        ∑ axis : Fin 3, if axis = single then 0 else
          differenceWord coordinateTransport [axis, axis]
              (fun current ↦ (frequencySquared current : ℂ)) frequency *
            differenceWord coordinateTransport (oneTwoTwoRemoveTwo single axis) right
              (coordinateTransport axis (coordinateTransport axis frequency))‖ ≤
      ‖∑ axis : Fin 3,
          (oneTwoTwoFirstMultiplicity single axis : ℂ) *
            differenceWord coordinateTransport [axis]
                (fun current ↦ (frequencySquared current : ℂ)) frequency *
              differenceWord coordinateTransport (oneTwoTwoRemoveOne single axis) right
                (coordinateTransport axis frequency)‖ +
        ‖∑ axis : Fin 3, if axis = single then 0 else
          differenceWord coordinateTransport [axis, axis]
              (fun current ↦ (frequencySquared current : ℂ)) frequency *
            differenceWord coordinateTransport (oneTwoTwoRemoveTwo single axis) right
              (coordinateTransport axis (coordinateTransport axis frequency))‖ :=
      norm_add_le _ _
    _ ≤ (∑ axis : Fin 3,
          (oneTwoTwoFirstMultiplicity single axis : ℝ) * (2 * bound + 1) *
            (if axis = single then twoTwoBound else oneOneTwoBound)) +
        ∑ axis : Fin 3, if axis = single then 0 else 2 * oneTwoBound := by
      apply add_le_add
      · refine (norm_sum_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro axis _
        simp only [norm_mul, Complex.norm_natCast]
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left
            (norm_hodgeDenominator_singleDifference_le
              hbound axis frequency hcoordinates) (by positivity))
          (hlower.first axis) (norm_nonneg _) (by positivity)
      · refine (norm_sum_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro axis _
        split_ifs with haxis
        · simp
        · rw [norm_mul, norm_hodgeDenominator_sameAxis_secondDifference]
          exact mul_le_mul_of_nonneg_left (hlower.second axis haxis) (by norm_num)
    _ = (2 * bound + 1) * twoTwoBound +
        4 * (2 * bound + 1) * oneOneTwoBound + 4 * oneTwoBound := by
      fin_cases single <;>
        simp only [Fin.sum_univ_succ] <;>
        simp [oneTwoTwoFirstMultiplicity] <;> ring

/-- The recursive Hodge-entry envelope at the `122` stage. -/
def hodgeJacobianEntryThreeAxis122DescentEnvelope (lower bound : ℝ) : ℝ :=
  ((2 * bound + 1) * hodgeJacobianEntryMixedTwoTwoEnvelope lower bound +
      4 * (2 * bound + 1) * hodgeJacobianEntryThreeAxis112DescentEnvelope lower bound +
      4 * hodgeJacobianEntryMixedOneTwoEnvelope lower bound) / lower

/-- A controlled Hodge entry with any addressed `122` order descends to its checked `22`, `112`,
and `12` predecessor faces. -/
theorem norm_hodgeJacobianMultiplierEntry_oneTwoTwo_le_of_controlled
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (single : Fin 3) (frequency : SpatialFrequency)
    (component coordinate input : Fin 3)
    (hstencil : ThreeAxisStencilControlled lower bound 0 1 2 frequency
      (oneTwoTwoAxisOrder single 0) (oneTwoTwoAxisOrder single 1)
        (oneTwoTwoAxisOrder single 2)) :
    ‖differenceWord coordinateTransport (oneTwoTwoWord single)
      (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
      frequency‖ ≤ hodgeJacobianEntryThreeAxis122DescentEnvelope lower bound := by
  let entry := fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input
  have hcoordinates : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound := by
    simpa using (hstencil 0 (by simp [oneTwoTwoAxisOrder])
      0 (by simp [oneTwoTwoAxisOrder]) 0 (by simp [oneTwoTwoAxisOrder])).2
  have hfrequency : lower ≤ frequencySquared frequency := by
    simpa using (hstencil 0 (by simp [oneTwoTwoAxisOrder])
      0 (by simp [oneTwoTwoAxisOrder]) 0 (by simp [oneTwoTwoAxisOrder])).1
  have hlowerOrders : HodgeEntry122LowerOrderEnvelope single entry frequency
      (hodgeJacobianEntryMixedTwoTwoEnvelope lower bound)
      (hodgeJacobianEntryThreeAxis112DescentEnvelope lower bound)
      (hodgeJacobianEntryMixedOneTwoEnvelope lower bound) := by
    fin_cases single
    · have hstencil' : ThreeAxisStencilControlled lower bound 0 1 2 frequency 1 2 2 := by
        simpa [oneTwoTwoAxisOrder] using hstencil
      refine ⟨?_, ?_⟩
      · intro axis
        fin_cases axis
        · have hraw := norm_hodgeJacobianMultiplierEntry_pairWord_two_two_le
            hlower hbound 1 2 (by decide)
            (threeAxisStencilPoint 0 1 2 frequency 1 0 0)
            component coordinate input
            (hstencil'.secondThird (firstOffset := 1) (by omega))
          simpa [entry, oneTwoTwoRemoveOne, threeAxisStencilPoint,
            coordinateTransport] using hraw
        · have hsub := hstencil'.rebase
              (firstOffset := 0) (secondOffset := 1) (thirdOffset := 0)
              (firstOrder := 1) (secondOrder := 1) (thirdOrder := 2)
              (by omega) (by omega) (by omega)
          have hraw := norm_hodgeJacobianMultiplierEntry_oneOneTwo_le_of_controlled
            hlower hbound 2 (threeAxisStencilPoint 0 1 2 frequency 0 1 0)
            component coordinate input hsub
          simpa [entry, oneTwoTwoRemoveOne, threeAxisStencilPoint,
            coordinateTransport] using hraw
        · have hsub := hstencil'.rebase
              (firstOffset := 0) (secondOffset := 0) (thirdOffset := 1)
              (firstOrder := 1) (secondOrder := 2) (thirdOrder := 1)
              (by omega) (by omega) (by omega)
          have hraw := norm_hodgeJacobianMultiplierEntry_oneOneTwo_le_of_controlled
            hlower hbound 1 (threeAxisStencilPoint 0 1 2 frequency 0 0 1)
            component coordinate input hsub
          simpa [entry, oneTwoTwoRemoveOne, threeAxisStencilPoint,
            coordinateTransport] using hraw
      · intro axis haxis
        fin_cases axis
        · simp at haxis
        · have hraw := norm_hodgeJacobianMultiplierEntry_pairWord_one_two_le
            hlower hbound 0 2 (by decide)
            (threeAxisStencilPoint 0 1 2 frequency 0 2 0)
            component coordinate input
            (hstencil'.firstThird (secondOffset := 2) (by omega))
          have hbase : threeAxisStencilPoint 0 1 2 frequency 0 2 0 =
              coordinateTransport 1 (coordinateTransport 1 frequency) := by
            simp only [threeAxisStencilPoint, coordinateTransport, zero_nsmul, add_zero]
            rw [two_nsmul]
            abel
          rw [hbase] at hraw
          simpa [entry, oneTwoTwoRemoveTwo] using hraw
        · have hraw := norm_hodgeJacobianMultiplierEntry_pairWord_one_two_le
            hlower hbound 0 1 (by decide)
            (threeAxisStencilPoint 0 1 2 frequency 0 0 2)
            component coordinate input
            (hstencil'.firstSecond (thirdOffset := 2) (by omega))
          have hbase : threeAxisStencilPoint 0 1 2 frequency 0 0 2 =
              coordinateTransport 2 (coordinateTransport 2 frequency) := by
            simp only [threeAxisStencilPoint, coordinateTransport, zero_nsmul, add_zero]
            rw [two_nsmul]
            abel
          rw [hbase] at hraw
          simpa [entry, oneTwoTwoRemoveTwo] using hraw
    · have hstencil' : ThreeAxisStencilControlled lower bound 0 1 2 frequency 2 1 2 := by
        simpa [oneTwoTwoAxisOrder] using hstencil
      refine ⟨?_, ?_⟩
      · intro axis
        fin_cases axis
        · have hsub := hstencil'.rebase
              (firstOffset := 1) (secondOffset := 0) (thirdOffset := 0)
              (firstOrder := 1) (secondOrder := 1) (thirdOrder := 2)
              (by omega) (by omega) (by omega)
          have hraw := norm_hodgeJacobianMultiplierEntry_oneOneTwo_le_of_controlled
            hlower hbound 2 (threeAxisStencilPoint 0 1 2 frequency 1 0 0)
            component coordinate input hsub
          simpa [entry, oneTwoTwoRemoveOne, threeAxisStencilPoint,
            coordinateTransport] using hraw
        · have hraw := norm_hodgeJacobianMultiplierEntry_pairWord_two_two_le
            hlower hbound 0 2 (by decide)
            (threeAxisStencilPoint 0 1 2 frequency 0 1 0)
            component coordinate input
            (hstencil'.firstThird (secondOffset := 1) (by omega))
          simpa [entry, oneTwoTwoRemoveOne, threeAxisStencilPoint,
            coordinateTransport] using hraw
        · have hsub := hstencil'.rebase
              (firstOffset := 0) (secondOffset := 0) (thirdOffset := 1)
              (firstOrder := 2) (secondOrder := 1) (thirdOrder := 1)
              (by omega) (by omega) (by omega)
          have hraw := norm_hodgeJacobianMultiplierEntry_oneOneTwo_le_of_controlled
            hlower hbound 0 (threeAxisStencilPoint 0 1 2 frequency 0 0 1)
            component coordinate input hsub
          simpa [entry, oneTwoTwoRemoveOne, threeAxisStencilPoint,
            coordinateTransport] using hraw
      · intro axis haxis
        fin_cases axis
        · have hraw := norm_hodgeJacobianMultiplierEntry_pairWord_one_two_le
            hlower hbound 1 2 (by decide)
            (threeAxisStencilPoint 0 1 2 frequency 2 0 0)
            component coordinate input
            (hstencil'.secondThird (firstOffset := 2) (by omega))
          have hbase : threeAxisStencilPoint 0 1 2 frequency 2 0 0 =
              coordinateTransport 0 (coordinateTransport 0 frequency) := by
            simp only [threeAxisStencilPoint, coordinateTransport, zero_nsmul, add_zero]
            rw [two_nsmul]
            abel
          rw [hbase] at hraw
          simpa [entry, oneTwoTwoRemoveTwo] using hraw
        · simp at haxis
        · have hraw := norm_hodgeJacobianMultiplierEntry_pairWord_two_one_le
            hlower hbound 0 1 (by decide)
            (threeAxisStencilPoint 0 1 2 frequency 0 0 2)
            component coordinate input
            (hstencil'.firstSecond (thirdOffset := 2) (by omega))
          have hbase : threeAxisStencilPoint 0 1 2 frequency 0 0 2 =
              coordinateTransport 2 (coordinateTransport 2 frequency) := by
            simp only [threeAxisStencilPoint, coordinateTransport, zero_nsmul, add_zero]
            rw [two_nsmul]
            abel
          rw [hbase] at hraw
          simpa [entry, oneTwoTwoRemoveTwo] using hraw
    · have hstencil' : ThreeAxisStencilControlled lower bound 0 1 2 frequency 2 2 1 := by
        simpa [oneTwoTwoAxisOrder] using hstencil
      refine ⟨?_, ?_⟩
      · intro axis
        fin_cases axis
        · have hsub := hstencil'.rebase
              (firstOffset := 1) (secondOffset := 0) (thirdOffset := 0)
              (firstOrder := 1) (secondOrder := 2) (thirdOrder := 1)
              (by omega) (by omega) (by omega)
          have hraw := norm_hodgeJacobianMultiplierEntry_oneOneTwo_le_of_controlled
            hlower hbound 1 (threeAxisStencilPoint 0 1 2 frequency 1 0 0)
            component coordinate input hsub
          simpa [entry, oneTwoTwoRemoveOne, threeAxisStencilPoint,
            coordinateTransport] using hraw
        · have hsub := hstencil'.rebase
              (firstOffset := 0) (secondOffset := 1) (thirdOffset := 0)
              (firstOrder := 2) (secondOrder := 1) (thirdOrder := 1)
              (by omega) (by omega) (by omega)
          have hraw := norm_hodgeJacobianMultiplierEntry_oneOneTwo_le_of_controlled
            hlower hbound 0 (threeAxisStencilPoint 0 1 2 frequency 0 1 0)
            component coordinate input hsub
          simpa [entry, oneTwoTwoRemoveOne, threeAxisStencilPoint,
            coordinateTransport] using hraw
        · have hraw := norm_hodgeJacobianMultiplierEntry_pairWord_two_two_le
            hlower hbound 0 1 (by decide)
            (threeAxisStencilPoint 0 1 2 frequency 0 0 1)
            component coordinate input
            (hstencil'.firstSecond (thirdOffset := 1) (by omega))
          simpa [entry, oneTwoTwoRemoveOne, threeAxisStencilPoint,
            coordinateTransport] using hraw
      · intro axis haxis
        fin_cases axis
        · have hraw := norm_hodgeJacobianMultiplierEntry_pairWord_two_one_le
            hlower hbound 1 2 (by decide)
            (threeAxisStencilPoint 0 1 2 frequency 2 0 0)
            component coordinate input
            (hstencil'.secondThird (firstOffset := 2) (by omega))
          have hbase : threeAxisStencilPoint 0 1 2 frequency 2 0 0 =
              coordinateTransport 0 (coordinateTransport 0 frequency) := by
            simp only [threeAxisStencilPoint, coordinateTransport, zero_nsmul, add_zero]
            rw [two_nsmul]
            abel
          rw [hbase] at hraw
          simpa [entry, oneTwoTwoRemoveTwo] using hraw
        · have hraw := norm_hodgeJacobianMultiplierEntry_pairWord_two_one_le
            hlower hbound 0 2 (by decide)
            (threeAxisStencilPoint 0 1 2 frequency 0 2 0)
            component coordinate input
            (hstencil'.firstThird (secondOffset := 2) (by omega))
          have hbase : threeAxisStencilPoint 0 1 2 frequency 0 2 0 =
              coordinateTransport 1 (coordinateTransport 1 frequency) := by
            simp only [threeAxisStencilPoint, coordinateTransport, zero_nsmul, add_zero]
            rw [two_nsmul]
            abel
          rw [hbase] at hraw
          simpa [entry, oneTwoTwoRemoveTwo] using hraw
        · simp at haxis
  have hgrouped := norm_hodgeEntry122GroupedActiveReturn_le hbound single entry frequency
    hcoordinates hlowerOrders
  unfold hodgeJacobianEntryThreeAxis122DescentEnvelope
  exact norm_differenceWord_right_le_div_of_frequencySquared_recurrence
    hlower (oneTwoTwoWord single) entry frequency
    (hodgeEntry122GroupedActiveReturn single entry frequency) hfrequency
    (hodgeJacobianMultiplierEntry_oneTwoTwo_groupedRecurrence
      single frequency component coordinate input) hgrouped

/-- **[proved-derived]** The strict `122` Hodge-entry descent has exact inverse-fifth dyadic
scale.  The numerator `1870910400000` is the exact `22 + 4·112 + 4·12` predecessor ledger; the
controlled aperture contributes the final factor four. -/
theorem hodgeJacobianEntryThreeAxis122DescentEnvelope_dyadic_le
    (scale : ℕ) (hscale : 3 ≤ scale) :
    hodgeJacobianEntryThreeAxis122DescentEnvelope
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) ≤
      7483641600000 / (dyadicRadius scale : ℝ) ^ 5 := by
  let radius : ℝ := dyadicRadius scale
  let lower := dyadicHodgeControlledLower scale
  let bound := dyadicHodgeControlledBound scale
  let e22 := hodgeJacobianEntryMixedTwoTwoEnvelope lower bound
  let e112 := hodgeJacobianEntryThreeAxis112DescentEnvelope lower bound
  let e12 := hodgeJacobianEntryMixedOneTwoEnvelope lower bound
  have hradius : 0 < radius := by
    dsimp [radius]
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  have hlower : 0 < lower := by
    simpa [lower] using dyadicHodgeControlledLower_pos scale hscale
  have hlinear : 2 * bound + 1 ≤ 11 * radius := by
    simpa [bound, radius] using
      two_mul_bound_add_one_le_eleven_mul_radius scale hscale
  have hboundNonneg : 0 ≤ bound := by
    dsimp [bound]
    unfold dyadicHodgeControlledBound
    positivity
  have h22 : e22 ≤ 32000000000 / radius ^ 4 := by
    simpa [e22, lower, bound, radius] using
      hodgeJacobianEntryMixedTwoTwoEnvelope_dyadic_le scale hscale
  have h112 : e112 ≤ 34505600000 / radius ^ 4 := by
    simpa [e112, lower, bound, radius] using
      hodgeJacobianEntryThreeAxis112DescentEnvelope_dyadic_le scale hscale
  have h12 : e12 ≤ 166000000 / radius ^ 3 := by
    simpa [e12, lower, bound, radius] using
      hodgeJacobianEntryMixedOneTwoEnvelope_dyadic_le scale hscale
  have he22 : 0 ≤ e22 := by
    dsimp [e22, lower, bound]
    unfold hodgeJacobianEntryMixedTwoTwoEnvelope hodgeReciprocalMixedTwoTwoEnvelope
      hodgeReciprocalMixedOneTwoEnvelope hodgeReciprocalMixedOneOneEnvelope
      hodgeReciprocalValueEnvelope hodgeReciprocalFirstEnvelope
      hodgeReciprocalSecondEnvelope dyadicHodgeControlledLower dyadicHodgeControlledBound
    positivity
  have he112 : 0 ≤ e112 := by
    dsimp [e112, lower, bound]
    unfold hodgeJacobianEntryThreeAxis112DescentEnvelope
      hodgeJacobianEntryThreeAxis111Envelope hodgeJacobianEntryMixedOneTwoEnvelope
      hodgeJacobianEntryMixedOneOneEnvelope hodgeReciprocal111Envelope
      hodgeReciprocalMixedOneTwoEnvelope hodgeReciprocalMixedOneOneEnvelope
      hodgeReciprocalValueEnvelope hodgeReciprocalFirstEnvelope
      hodgeReciprocalSecondEnvelope dyadicHodgeControlledLower dyadicHodgeControlledBound
    positivity
  have he12 : 0 ≤ e12 := by
    dsimp [e12, lower, bound]
    unfold hodgeJacobianEntryMixedOneTwoEnvelope hodgeReciprocalMixedOneTwoEnvelope
      hodgeReciprocalMixedOneOneEnvelope hodgeReciprocalValueEnvelope
      hodgeReciprocalFirstEnvelope hodgeReciprocalSecondEnvelope
      dyadicHodgeControlledLower dyadicHodgeControlledBound
    positivity
  have hterm22 : (2 * bound + 1) * e22 ≤
      (11 * radius) * (32000000000 / radius ^ 4) :=
    mul_le_mul hlinear h22 he22 (by positivity)
  have hterm112 : 4 * (2 * bound + 1) * e112 ≤
      4 * (11 * radius) * (34505600000 / radius ^ 4) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hlinear (by norm_num)) h112
      he112 (by positivity)
  have hterm12 : 4 * e12 ≤ 4 * (166000000 / radius ^ 3) :=
    mul_le_mul_of_nonneg_left h12 (by norm_num)
  have hnumerator :
      (2 * bound + 1) * e22 + 4 * (2 * bound + 1) * e112 + 4 * e12 ≤
        1870910400000 / radius ^ 3 := by
    calc
      _ ≤ (11 * radius) * (32000000000 / radius ^ 4) +
          4 * (11 * radius) * (34505600000 / radius ^ 4) +
          4 * (166000000 / radius ^ 3) :=
        add_le_add (add_le_add hterm22 hterm112) hterm12
      _ = 1870910400000 / radius ^ 3 := by
        field_simp [hradius.ne']
        norm_num
  have hinverse : 1 / lower ≤ 4 / radius ^ 2 := by
    simpa [lower, radius] using one_div_dyadicHodgeControlledLower_le scale hscale
  unfold hodgeJacobianEntryThreeAxis122DescentEnvelope
  change ((2 * bound + 1) * e22 + 4 * (2 * bound + 1) * e112 + 4 * e12) /
      lower ≤ _
  rw [div_eq_mul_inv, show lower⁻¹ = 1 / lower by simp]
  calc
    _ ≤ (1870910400000 / radius ^ 3) * (1 / lower) := by
      exact mul_le_mul_of_nonneg_right hnumerator (by positivity)
    _ ≤ (1870910400000 / radius ^ 3) * (4 / radius ^ 2) := by
      exact mul_le_mul_of_nonneg_left hinverse (by positivity)
    _ = 7483641600000 / radius ^ 5 := by
      field_simp [hradius.ne']
      norm_num

section Audit

#print axioms differenceWord_right_recurrence_of_product_zero
#print axioms hodgeJacobianMultiplierEntry_oneOneTwo_groupedRecurrence
#print axioms norm_hodgeJacobianMultiplierEntry_oneOneTwo_le_of_controlled
#print axioms hodgeJacobianEntryThreeAxis112DescentEnvelope_dyadic_le
#print axioms hodgeJacobianMultiplierEntry_oneTwoTwo_groupedRecurrence
#print axioms norm_hodgeJacobianMultiplierEntry_oneTwoTwo_le_of_controlled
#print axioms hodgeJacobianEntryThreeAxis122DescentEnvelope_dyadic_le

end Audit

end Soma.Holonics.Millennium.NavierStokesHodgeEntryScaleDescent
