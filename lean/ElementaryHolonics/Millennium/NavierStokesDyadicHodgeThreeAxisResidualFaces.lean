import ElementaryHolonics.Millennium.NavierStokesHodgeEntryScaleDescent

/-!
# The six strict residual dyadic Hodge allocation faces

**[proved-derived]** The remaining scalar addresses are the three permutations of `110` and
`100`.  Their complementary Hodge words are the three axis-addressed `112` and `122` words.
This owner composes the strict Hodge-entry descent with the exact scalar chart, caused support
stencil, tensor Fubini mass, and allocation multiplicities.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisResidualFaces

open Soma.Holonics.HigherDifferenceTransport
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesSmoothHodgeJacobianBand
open Soma.Holonics.Millennium.NavierStokesReciprocalDifferenceRecurrence
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeKernelVariation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeSupportStencil
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeProductFaces
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeEnvelopeScaling
open Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeScaleDescent
open Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeProductMass
open Soma.Holonics.Millennium.NavierStokesThreeAxisScalarSubsetVariation
open Soma.Holonics.Millennium.NavierStokesThreeAxisDyadicHodgeSupportStencil
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisAllocation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisScalarChart
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisCornerMass
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisOtherTwoSlices
open Soma.Holonics.Millennium.NavierStokesHodgeEntryScaleDescent

/-- The scalar allocation complementary to an addressed Hodge `112` word. -/
def oneOneTwoScalarAllocation (doubled axis : Fin 3) : Fin 3 :=
  if axis = doubled then 0 else 1

/-- The scalar allocation complementary to an addressed Hodge `122` word. -/
def oneTwoTwoScalarAllocation (single axis : Fin 3) : Fin 3 :=
  if axis = single then 1 else 0

/-- The `110` scalar hand and `112` Hodge hand partition two differences in every axis. -/
theorem oneOneTwoScalarAllocation_complement
    (doubled axis : Fin 3) :
    2 - (oneOneTwoScalarAllocation doubled axis).val = oneOneTwoAxisOrder doubled axis := by
  fin_cases doubled <;> fin_cases axis <;>
    simp [oneOneTwoScalarAllocation, oneOneTwoAxisOrder]

/-- The `100` scalar hand and `122` Hodge hand partition two differences in every axis. -/
theorem oneTwoTwoScalarAllocation_complement
    (single axis : Fin 3) :
    2 - (oneTwoTwoScalarAllocation single axis).val = oneTwoTwoAxisOrder single axis := by
  fin_cases single <;> fin_cases axis <;>
    simp [oneTwoTwoScalarAllocation, oneTwoTwoAxisOrder]

/-! ## Common-chart residue removal -/

/-- Before the complementary first-axis offset, the scalar hand is exactly zero on the global
backward-padded chart. -/
theorem threeAxisMixedForwardDifference_directDyadicScalar_backwardPadded_eq_zero_of_first_lt
    (scale firstOrder secondOrder thirdOrder firstIndex secondIndex thirdIndex : ℕ)
    (hfirstOrder : firstOrder ≤ 2) (hsecondOrder : secondOrder ≤ 2)
    (hthirdOrder : thirdOrder ≤ 2) (hfirstIndex : firstIndex < 2 - firstOrder) :
    threeAxisMixedForwardDifference 0 1 2 firstOrder secondOrder thirdOrder
      (directDyadicScalarCoefficient scale)
      (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
        firstIndex secondIndex thirdIndex) = 0 := by
  rw [threeAxisMixedForwardDifference_backwardPadded_eq_natural]
  interval_cases firstOrder
  · have hzero : ∀ currentSecond currentThird,
        directDyadicScalarCoefficient scale
          (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
            firstIndex currentSecond currentThird) = 0 := by
      intro currentSecond currentThird
      exact directDyadicScalarCoefficient_threeAxisBackwardPadded_eq_zero_of_first_lt_two
        scale firstIndex currentSecond currentThird hfirstIndex
    interval_cases secondOrder <;> interval_cases thirdOrder <;>
      simp [fwdDiff, hzero]
  · have hzero0 : ∀ currentSecond currentThird,
        directDyadicScalarCoefficient scale
          (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
            firstIndex currentSecond currentThird) = 0 := by
      intro currentSecond currentThird
      exact directDyadicScalarCoefficient_threeAxisBackwardPadded_eq_zero_of_first_lt_two
        scale firstIndex currentSecond currentThird (by omega)
    have hzero1 : ∀ currentSecond currentThird,
        directDyadicScalarCoefficient scale
          (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
            (firstIndex + 1) currentSecond currentThird) = 0 := by
      intro currentSecond currentThird
      exact directDyadicScalarCoefficient_threeAxisBackwardPadded_eq_zero_of_first_lt_two
        scale (firstIndex + 1) currentSecond currentThird (by omega)
    interval_cases secondOrder <;> interval_cases thirdOrder <;>
      simp [fwdDiff, hzero0, hzero1]
  · omega

/-- Before the complementary second-axis offset, the scalar hand is exactly zero on the global
backward-padded chart. -/
theorem threeAxisMixedForwardDifference_directDyadicScalar_backwardPadded_eq_zero_of_second_lt
    (scale firstOrder secondOrder thirdOrder firstIndex secondIndex thirdIndex : ℕ)
    (hfirstOrder : firstOrder ≤ 2) (hsecondOrder : secondOrder ≤ 2)
    (hthirdOrder : thirdOrder ≤ 2) (hsecondIndex : secondIndex < 2 - secondOrder) :
    threeAxisMixedForwardDifference 0 1 2 firstOrder secondOrder thirdOrder
      (directDyadicScalarCoefficient scale)
      (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
        firstIndex secondIndex thirdIndex) = 0 := by
  rw [threeAxisMixedForwardDifference_backwardPadded_eq_natural]
  interval_cases secondOrder
  · have hzero : ∀ currentFirst currentThird,
        directDyadicScalarCoefficient scale
          (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
            currentFirst secondIndex currentThird) = 0 := by
      intro currentFirst currentThird
      exact directDyadicScalarCoefficient_threeAxisBackwardPadded_eq_zero_of_second_lt_two
        scale currentFirst secondIndex currentThird hsecondIndex
    interval_cases firstOrder <;> interval_cases thirdOrder <;>
      simp [fwdDiff, hzero]
  · have hzero0 : ∀ currentFirst currentThird,
        directDyadicScalarCoefficient scale
          (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
            currentFirst secondIndex currentThird) = 0 := by
      intro currentFirst currentThird
      exact directDyadicScalarCoefficient_threeAxisBackwardPadded_eq_zero_of_second_lt_two
        scale currentFirst secondIndex currentThird (by omega)
    have hzero1 : ∀ currentFirst currentThird,
        directDyadicScalarCoefficient scale
          (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
            currentFirst (secondIndex + 1) currentThird) = 0 := by
      intro currentFirst currentThird
      exact directDyadicScalarCoefficient_threeAxisBackwardPadded_eq_zero_of_second_lt_two
        scale currentFirst (secondIndex + 1) currentThird (by omega)
    interval_cases firstOrder <;> interval_cases thirdOrder <;>
      simp [fwdDiff, hzero0, hzero1]
  · omega

/-- Before the complementary third-axis offset, the scalar hand is exactly zero on the global
backward-padded chart. -/
theorem threeAxisMixedForwardDifference_directDyadicScalar_backwardPadded_eq_zero_of_third_lt
    (scale firstOrder secondOrder thirdOrder firstIndex secondIndex thirdIndex : ℕ)
    (hfirstOrder : firstOrder ≤ 2) (hsecondOrder : secondOrder ≤ 2)
    (hthirdOrder : thirdOrder ≤ 2) (hthirdIndex : thirdIndex < 2 - thirdOrder) :
    threeAxisMixedForwardDifference 0 1 2 firstOrder secondOrder thirdOrder
      (directDyadicScalarCoefficient scale)
      (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
        firstIndex secondIndex thirdIndex) = 0 := by
  rw [threeAxisMixedForwardDifference_backwardPadded_eq_natural]
  interval_cases thirdOrder
  · have hzero : ∀ currentFirst currentSecond,
        directDyadicScalarCoefficient scale
          (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
            currentFirst currentSecond thirdIndex) = 0 := by
      intro currentFirst currentSecond
      exact directDyadicScalarCoefficient_threeAxisBackwardPadded_eq_zero_of_third_lt_two
        scale currentFirst currentSecond thirdIndex hthirdIndex
    interval_cases firstOrder <;> interval_cases secondOrder <;>
      simp [fwdDiff, hzero]
  · have hzero0 : ∀ currentFirst currentSecond,
        directDyadicScalarCoefficient scale
          (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
            currentFirst currentSecond thirdIndex) = 0 := by
      intro currentFirst currentSecond
      exact directDyadicScalarCoefficient_threeAxisBackwardPadded_eq_zero_of_third_lt_two
        scale currentFirst currentSecond thirdIndex (by omega)
    have hzero1 : ∀ currentFirst currentSecond,
        directDyadicScalarCoefficient scale
          (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
            currentFirst currentSecond (thirdIndex + 1)) = 0 := by
      intro currentFirst currentSecond
      exact directDyadicScalarCoefficient_threeAxisBackwardPadded_eq_zero_of_third_lt_two
        scale currentFirst currentSecond (thirdIndex + 1) (by omega)
    interval_cases firstOrder <;> interval_cases secondOrder <;>
      simp [fwdDiff, hzero0, hzero1]
  · omega

/-- Unweighted global mass of one scalar/Hodge allocation face on the common doubly padded
population. -/
def dyadicHodgeThreeAxisGlobalProductFaceMass
    (scale firstOrder secondOrder thirdOrder : ℕ)
    (component coordinate input : Fin 3) : ℝ :=
  ∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
    ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
      ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ‖dyadicHodgeThreeAxisGlobalProductFace scale firstOrder secondOrder thirdOrder
          component coordinate input firstIndex secondIndex thirdIndex‖

/-- **[proved-derived]** Every admitted scalar/Hodge face loses exactly its three complementary
left residues and no others: its common global mass equals its natural translated mass. -/
theorem dyadicHodgeThreeAxisGlobalProductFaceMass_eq_natural
    (scale firstOrder secondOrder thirdOrder : ℕ)
    (component coordinate input : Fin 3)
    (hfirstOrder : firstOrder ≤ 2) (hsecondOrder : secondOrder ≤ 2)
    (hthirdOrder : thirdOrder ≤ 2) :
    dyadicHodgeThreeAxisGlobalProductFaceMass scale firstOrder secondOrder thirdOrder
        component coordinate input =
      dyadicHodgeThreeAxisNaturalProductFaceMass scale firstOrder secondOrder thirdOrder
        component coordinate input := by
  unfold dyadicHodgeThreeAxisGlobalProductFaceMass
    dyadicHodgeThreeAxisNaturalProductFaceMass
  nth_rewrite 1 [show dyadicHodgeApertureCount scale + 2 =
    (2 - firstOrder) + (dyadicHodgeApertureCount scale + firstOrder) by omega]
  nth_rewrite 1 [show dyadicHodgeApertureCount scale + 2 =
    (2 - secondOrder) + (dyadicHodgeApertureCount scale + secondOrder) by omega]
  nth_rewrite 1 [show dyadicHodgeApertureCount scale + 2 =
    (2 - thirdOrder) + (dyadicHodgeApertureCount scale + thirdOrder) by omega]
  apply sum_range_threeAxis_shift_of_prefix_zero
  · intro firstIndex hfirstIndex secondIndex _ thirdIndex _
    have hzero :=
      threeAxisMixedForwardDifference_directDyadicScalar_backwardPadded_eq_zero_of_first_lt
        scale firstOrder secondOrder thirdOrder firstIndex secondIndex thirdIndex
        hfirstOrder hsecondOrder hthirdOrder hfirstIndex
    rw [show dyadicHodgeThreeAxisGlobalProductFace scale firstOrder secondOrder thirdOrder
      component coordinate input firstIndex secondIndex thirdIndex = 0 by
      simp [dyadicHodgeThreeAxisGlobalProductFace, hzero]]
    simp
  · intro firstIndex _ secondIndex hsecondIndex thirdIndex _
    have hzero :=
      threeAxisMixedForwardDifference_directDyadicScalar_backwardPadded_eq_zero_of_second_lt
        scale firstOrder secondOrder thirdOrder
        ((2 - firstOrder) + firstIndex) secondIndex thirdIndex
        hfirstOrder hsecondOrder hthirdOrder hsecondIndex
    rw [show dyadicHodgeThreeAxisGlobalProductFace scale firstOrder secondOrder thirdOrder
      component coordinate input ((2 - firstOrder) + firstIndex) secondIndex thirdIndex = 0 by
      simp [dyadicHodgeThreeAxisGlobalProductFace, hzero]]
    simp
  · intro firstIndex _ secondIndex _ thirdIndex hthirdIndex
    have hzero :=
      threeAxisMixedForwardDifference_directDyadicScalar_backwardPadded_eq_zero_of_third_lt
        scale firstOrder secondOrder thirdOrder
        ((2 - firstOrder) + firstIndex) ((2 - secondOrder) + secondIndex) thirdIndex
        hfirstOrder hsecondOrder hthirdOrder hthirdIndex
    rw [show dyadicHodgeThreeAxisGlobalProductFace scale firstOrder secondOrder thirdOrder
      component coordinate input ((2 - firstOrder) + firstIndex)
        ((2 - secondOrder) + secondIndex) thirdIndex = 0 by
      simp [dyadicHodgeThreeAxisGlobalProductFace, hzero]]
    simp
  · intro firstIndex _ secondIndex _ thirdIndex _
    simpa [Nat.add_comm] using congrArg norm
      (dyadicHodgeThreeAxisGlobalProductFace_add_offsets_eq_subset
        scale firstOrder secondOrder thirdOrder component coordinate input
          firstIndex secondIndex thirdIndex)

/-- Every actual allocation face on the common global chart is its exact occurrence multiplicity
times the corresponding unweighted global product face. -/
theorem directDyadicHodgeThreeAxisAllocationFace_eq_weightedGlobalProductFace
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstAllocation secondAllocation thirdAllocation : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) :
    directDyadicHodgeThreeAxisAllocationFace scale component coordinate input
        firstAllocation secondAllocation thirdAllocation
        (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
          firstIndex secondIndex thirdIndex) =
      ((secondOrderBinomialWeight firstAllocation *
          secondOrderBinomialWeight secondAllocation *
          secondOrderBinomialWeight thirdAllocation : ℕ) : ℂ) *
        dyadicHodgeThreeAxisGlobalProductFace scale
          firstAllocation.val secondAllocation.val thirdAllocation.val
          component coordinate input firstIndex secondIndex thirdIndex := by
  simp [directDyadicHodgeThreeAxisAllocationFace, threeAxisHodgeAllocationFace,
    dyadicHodgeThreeAxisGlobalProductFace]
  ring

/-- Common-chart mass of one actual weighted allocation face. -/
def directDyadicHodgeThreeAxisGlobalAllocationFaceMass
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstAllocation secondAllocation thirdAllocation : Fin 3) : ℝ :=
  ∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
    ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
      ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ‖directDyadicHodgeThreeAxisAllocationFace scale component coordinate input
          firstAllocation secondAllocation thirdAllocation
          (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
            firstIndex secondIndex thirdIndex)‖

/-- **[proved-derived]** Every one of the 27 actual face masses reindexes exactly from the common
global allocation population to its natural translated population. -/
theorem directDyadicHodgeThreeAxisGlobalAllocationFaceMass_eq_natural
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstAllocation secondAllocation thirdAllocation : Fin 3) :
    directDyadicHodgeThreeAxisGlobalAllocationFaceMass scale component coordinate input
        firstAllocation secondAllocation thirdAllocation =
      directDyadicHodgeThreeAxisNaturalAllocationFaceMass scale component coordinate input
        firstAllocation secondAllocation thirdAllocation := by
  have hglobal := dyadicHodgeThreeAxisGlobalProductFaceMass_eq_natural
    scale firstAllocation.val secondAllocation.val thirdAllocation.val
      component coordinate input (by omega) (by omega) (by omega)
  simp only [directDyadicHodgeThreeAxisGlobalAllocationFaceMass,
    directDyadicHodgeThreeAxisAllocationFace_eq_weightedGlobalProductFace,
    norm_mul, Complex.norm_natCast,
    directDyadicHodgeThreeAxisNaturalAllocationFaceMass_eq_weighted]
  have hweighted := congrArg
    (fun mass : ℝ ↦
      (secondOrderBinomialWeight firstAllocation *
          secondOrderBinomialWeight secondAllocation *
          secondOrderBinomialWeight thirdAllocation : ℕ) * mass) hglobal
  unfold dyadicHodgeThreeAxisGlobalProductFaceMass at hweighted
  simpa only [Finset.mul_sum] using hweighted

/-- The addressed-word `112` theorem in the three-axis mixed-difference chart used by the
allocation owner. -/
theorem norm_hodgeJacobianMultiplierEntry_threeAxis_oneOneTwo_le_of_controlled
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (doubled : Fin 3) (frequency : SpatialFrequency)
    (component coordinate input : Fin 3)
    (hstencil : ThreeAxisStencilControlled lower bound 0 1 2 frequency
      (oneOneTwoAxisOrder doubled 0) (oneOneTwoAxisOrder doubled 1)
        (oneOneTwoAxisOrder doubled 2)) :
    ‖threeAxisMixedForwardDifference 0 1 2
      (oneOneTwoAxisOrder doubled 0) (oneOneTwoAxisOrder doubled 1)
        (oneOneTwoAxisOrder doubled 2)
      (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
      frequency‖ ≤ hodgeJacobianEntryThreeAxis112DescentEnvelope lower bound := by
  rw [← differenceWord_eq_threeAxisMixedForwardDifference]
  have hraw := norm_hodgeJacobianMultiplierEntry_oneOneTwo_le_of_controlled
    hlower hbound doubled frequency component coordinate input hstencil
  fin_cases doubled <;>
    simpa [oneOneTwoWord, oneOneTwoAxisOrder] using hraw

/-- The addressed-word `122` theorem in the three-axis mixed-difference chart used by the
allocation owner. -/
theorem norm_hodgeJacobianMultiplierEntry_threeAxis_oneTwoTwo_le_of_controlled
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (single : Fin 3) (frequency : SpatialFrequency)
    (component coordinate input : Fin 3)
    (hstencil : ThreeAxisStencilControlled lower bound 0 1 2 frequency
      (oneTwoTwoAxisOrder single 0) (oneTwoTwoAxisOrder single 1)
        (oneTwoTwoAxisOrder single 2)) :
    ‖threeAxisMixedForwardDifference 0 1 2
      (oneTwoTwoAxisOrder single 0) (oneTwoTwoAxisOrder single 1)
        (oneTwoTwoAxisOrder single 2)
      (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
      frequency‖ ≤ hodgeJacobianEntryThreeAxis122DescentEnvelope lower bound := by
  rw [← differenceWord_eq_threeAxisMixedForwardDifference]
  have hraw := norm_hodgeJacobianMultiplierEntry_oneTwoTwo_le_of_controlled
    hlower hbound single frequency component coordinate input hstencil
  fin_cases single <;>
    simpa [oneTwoTwoWord, oneTwoTwoAxisOrder] using hraw

/-- Pointwise product control for any of the three scalar-`110` / Hodge-`112` faces. -/
theorem norm_dyadicHodgeThreeAxisSubsetProductFace_residual112_le
    (scale : ℕ) (doubled : Fin 3) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) (hscale : 3 ≤ scale)
    (hfirstIndex : firstIndex < dyadicHodgeApertureCount scale +
      (oneOneTwoScalarAllocation doubled 0).val)
    (hsecondIndex : secondIndex < dyadicHodgeApertureCount scale +
      (oneOneTwoScalarAllocation doubled 1).val)
    (hthirdIndex : thirdIndex < dyadicHodgeApertureCount scale +
      (oneOneTwoScalarAllocation doubled 2).val) :
    ‖dyadicHodgeThreeAxisSubsetProductFace scale
        (oneOneTwoScalarAllocation doubled 0).val
        (oneOneTwoScalarAllocation doubled 1).val
        (oneOneTwoScalarAllocation doubled 2).val
        component coordinate input firstIndex secondIndex thirdIndex‖ ≤
      ‖dyadicTensorBandThreeAxisVariation scale
        (oneOneTwoScalarAllocation doubled 0).val
        (oneOneTwoScalarAllocation doubled 1).val
        (oneOneTwoScalarAllocation doubled 2).val
        firstIndex secondIndex thirdIndex‖ *
        (34505600000 / (dyadicRadius scale : ℝ) ^ 4) := by
  let firstOrder := (oneOneTwoScalarAllocation doubled 0).val
  let secondOrder := (oneOneTwoScalarAllocation doubled 1).val
  let thirdOrder := (oneOneTwoScalarAllocation doubled 2).val
  let frequency := dyadicHodgeThreeAxisSubsetPaddedFrequency scale
    firstOrder secondOrder thirdOrder firstIndex secondIndex thirdIndex
  have hfirstOrder : firstOrder ≤ 2 := by
    fin_cases doubled <;> simp [firstOrder, oneOneTwoScalarAllocation]
  have hsecondOrder : secondOrder ≤ 2 := by
    fin_cases doubled <;> simp [secondOrder, oneOneTwoScalarAllocation]
  have hthirdOrder : thirdOrder ≤ 2 := by
    fin_cases doubled <;> simp [thirdOrder, oneOneTwoScalarAllocation]
  have hscalar :=
    threeAxisMixedForwardDifference_directDyadicScalarCoefficient_subsetPadded_eq
      scale firstOrder secondOrder thirdOrder firstIndex secondIndex thirdIndex
      hfirstOrder hsecondOrder hthirdOrder hfirstIndex hsecondIndex hthirdIndex
  change ‖threeAxisMixedForwardDifference 0 1 2 firstOrder secondOrder thirdOrder
      (directDyadicScalarCoefficient scale) frequency *
    threeAxisMixedForwardDifference 0 1 2 (2 - firstOrder) (2 - secondOrder)
      (2 - thirdOrder)
      (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
      (threeAxisStencilPoint 0 1 2 frequency firstOrder secondOrder thirdOrder)‖ ≤ _
  change threeAxisMixedForwardDifference 0 1 2 firstOrder secondOrder thirdOrder
      (directDyadicScalarCoefficient scale) frequency = _ at hscalar
  rw [hscalar, norm_mul]
  by_cases hzero : dyadicTensorBandThreeAxisVariation scale
      firstOrder secondOrder thirdOrder firstIndex secondIndex thirdIndex = 0
  · have hzero' : dyadicTensorBandThreeAxisVariation scale
        (oneOneTwoScalarAllocation doubled 0).val
        (oneOneTwoScalarAllocation doubled 1).val
        (oneOneTwoScalarAllocation doubled 2).val
        firstIndex secondIndex thirdIndex = 0 := by
      simpa [firstOrder, secondOrder, thirdOrder] using hzero
    simp [hzero, hzero']
  · have hglobal : threeAxisMixedForwardDifference 0 1 2
        firstOrder secondOrder thirdOrder
        (directDyadicScalarCoefficient scale) frequency ≠ 0 := by
      rw [hscalar]
      exact hzero
    have hstencil :=
      directDyadicScalar_threeAxis_support_controls_complementaryHodgeStencil
        scale firstOrder secondOrder thirdOrder
        (dyadicHodgeInnerCutoff_ge_three_of_scale_ge_three scale hscale)
        hfirstOrder hsecondOrder hthirdOrder frequency hglobal
    have hstencil' : ThreeAxisStencilControlled
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale)
        0 1 2 (threeAxisStencilPoint 0 1 2 frequency firstOrder secondOrder thirdOrder)
        (oneOneTwoAxisOrder doubled 0) (oneOneTwoAxisOrder doubled 1)
          (oneOneTwoAxisOrder doubled 2) := by
      simpa [dyadicHodgeControlledLower, dyadicHodgeControlledBound, firstOrder,
        secondOrder, thirdOrder, oneOneTwoScalarAllocation_complement] using hstencil
    have hlower := dyadicHodgeControlledLower_pos scale hscale
    have hbound : 0 ≤ dyadicHodgeControlledBound scale := by
      unfold dyadicHodgeControlledBound
      positivity
    gcongr
    have hraw := norm_hodgeJacobianMultiplierEntry_threeAxis_oneOneTwo_le_of_controlled
      hlower hbound doubled
      (threeAxisStencilPoint 0 1 2 frequency firstOrder secondOrder thirdOrder)
      component coordinate input hstencil'
    have hscaleBound := hodgeJacobianEntryThreeAxis112DescentEnvelope_dyadic_le scale hscale
    simpa [firstOrder, secondOrder, thirdOrder,
      oneOneTwoScalarAllocation_complement] using hraw.trans hscaleBound

/-- Pointwise product control for any of the three scalar-`100` / Hodge-`122` faces. -/
theorem norm_dyadicHodgeThreeAxisSubsetProductFace_residual122_le
    (scale : ℕ) (single : Fin 3) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) (hscale : 3 ≤ scale)
    (hfirstIndex : firstIndex < dyadicHodgeApertureCount scale +
      (oneTwoTwoScalarAllocation single 0).val)
    (hsecondIndex : secondIndex < dyadicHodgeApertureCount scale +
      (oneTwoTwoScalarAllocation single 1).val)
    (hthirdIndex : thirdIndex < dyadicHodgeApertureCount scale +
      (oneTwoTwoScalarAllocation single 2).val) :
    ‖dyadicHodgeThreeAxisSubsetProductFace scale
        (oneTwoTwoScalarAllocation single 0).val
        (oneTwoTwoScalarAllocation single 1).val
        (oneTwoTwoScalarAllocation single 2).val
        component coordinate input firstIndex secondIndex thirdIndex‖ ≤
      ‖dyadicTensorBandThreeAxisVariation scale
        (oneTwoTwoScalarAllocation single 0).val
        (oneTwoTwoScalarAllocation single 1).val
        (oneTwoTwoScalarAllocation single 2).val
        firstIndex secondIndex thirdIndex‖ *
        (7483641600000 / (dyadicRadius scale : ℝ) ^ 5) := by
  let firstOrder := (oneTwoTwoScalarAllocation single 0).val
  let secondOrder := (oneTwoTwoScalarAllocation single 1).val
  let thirdOrder := (oneTwoTwoScalarAllocation single 2).val
  let frequency := dyadicHodgeThreeAxisSubsetPaddedFrequency scale
    firstOrder secondOrder thirdOrder firstIndex secondIndex thirdIndex
  have hfirstOrder : firstOrder ≤ 2 := by
    fin_cases single <;> simp [firstOrder, oneTwoTwoScalarAllocation]
  have hsecondOrder : secondOrder ≤ 2 := by
    fin_cases single <;> simp [secondOrder, oneTwoTwoScalarAllocation]
  have hthirdOrder : thirdOrder ≤ 2 := by
    fin_cases single <;> simp [thirdOrder, oneTwoTwoScalarAllocation]
  have hscalar :=
    threeAxisMixedForwardDifference_directDyadicScalarCoefficient_subsetPadded_eq
      scale firstOrder secondOrder thirdOrder firstIndex secondIndex thirdIndex
      hfirstOrder hsecondOrder hthirdOrder hfirstIndex hsecondIndex hthirdIndex
  change ‖threeAxisMixedForwardDifference 0 1 2 firstOrder secondOrder thirdOrder
      (directDyadicScalarCoefficient scale) frequency *
    threeAxisMixedForwardDifference 0 1 2 (2 - firstOrder) (2 - secondOrder)
      (2 - thirdOrder)
      (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
      (threeAxisStencilPoint 0 1 2 frequency firstOrder secondOrder thirdOrder)‖ ≤ _
  change threeAxisMixedForwardDifference 0 1 2 firstOrder secondOrder thirdOrder
      (directDyadicScalarCoefficient scale) frequency = _ at hscalar
  rw [hscalar, norm_mul]
  by_cases hzero : dyadicTensorBandThreeAxisVariation scale
      firstOrder secondOrder thirdOrder firstIndex secondIndex thirdIndex = 0
  · have hzero' : dyadicTensorBandThreeAxisVariation scale
        (oneTwoTwoScalarAllocation single 0).val
        (oneTwoTwoScalarAllocation single 1).val
        (oneTwoTwoScalarAllocation single 2).val
        firstIndex secondIndex thirdIndex = 0 := by
      simpa [firstOrder, secondOrder, thirdOrder] using hzero
    simp [hzero, hzero']
  · have hglobal : threeAxisMixedForwardDifference 0 1 2
        firstOrder secondOrder thirdOrder
        (directDyadicScalarCoefficient scale) frequency ≠ 0 := by
      rw [hscalar]
      exact hzero
    have hstencil :=
      directDyadicScalar_threeAxis_support_controls_complementaryHodgeStencil
        scale firstOrder secondOrder thirdOrder
        (dyadicHodgeInnerCutoff_ge_three_of_scale_ge_three scale hscale)
        hfirstOrder hsecondOrder hthirdOrder frequency hglobal
    have hstencil' : ThreeAxisStencilControlled
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale)
        0 1 2 (threeAxisStencilPoint 0 1 2 frequency firstOrder secondOrder thirdOrder)
        (oneTwoTwoAxisOrder single 0) (oneTwoTwoAxisOrder single 1)
          (oneTwoTwoAxisOrder single 2) := by
      simpa [dyadicHodgeControlledLower, dyadicHodgeControlledBound, firstOrder,
        secondOrder, thirdOrder, oneTwoTwoScalarAllocation_complement] using hstencil
    have hlower := dyadicHodgeControlledLower_pos scale hscale
    have hbound : 0 ≤ dyadicHodgeControlledBound scale := by
      unfold dyadicHodgeControlledBound
      positivity
    gcongr
    have hraw := norm_hodgeJacobianMultiplierEntry_threeAxis_oneTwoTwo_le_of_controlled
      hlower hbound single
      (threeAxisStencilPoint 0 1 2 frequency firstOrder secondOrder thirdOrder)
      component coordinate input hstencil'
    have hscaleBound := hodgeJacobianEntryThreeAxis122DescentEnvelope_dyadic_le scale hscale
    simpa [firstOrder, secondOrder, thirdOrder,
      oneTwoTwoScalarAllocation_complement] using hraw.trans hscaleBound

/-- Each unweighted scalar-`110` / Hodge-`112` face has exact inverse-cubic mass numerator
`256 * 34505600000`. -/
theorem dyadicHodgeThreeAxisNaturalProductFaceMass_residual112_le
    (scale : ℕ) (doubled : Fin 3) (component coordinate input : Fin 3)
    (hscale : 3 ≤ scale) :
    dyadicHodgeThreeAxisNaturalProductFaceMass scale
        (oneOneTwoScalarAllocation doubled 0).val
        (oneOneTwoScalarAllocation doubled 1).val
        (oneOneTwoScalarAllocation doubled 2).val
        component coordinate input ≤
      8833433600000 / (dyadicRadius scale : ℝ) ^ 3 := by
  have hpoint := dyadicHodgeThreeAxisNaturalProductFaceMass_le_envelopes_of_pointwise
    scale (oneOneTwoScalarAllocation doubled 0).val
      (oneOneTwoScalarAllocation doubled 1).val
      (oneOneTwoScalarAllocation doubled 2).val
      component coordinate input
      (34505600000 / (dyadicRadius scale : ℝ) ^ 4) (by positivity)
      (fun firstIndex secondIndex thirdIndex hfirstIndex hsecondIndex hthirdIndex ↦
        norm_dyadicHodgeThreeAxisSubsetProductFace_residual112_le
          scale doubled component coordinate input firstIndex secondIndex thirdIndex hscale
            hfirstIndex hsecondIndex hthirdIndex)
  calc
    _ ≤ (nextProfileVariationEnvelope scale (oneOneTwoScalarAllocation doubled 0).val *
          nextProfileVariationEnvelope scale (oneOneTwoScalarAllocation doubled 1).val *
          nextProfileVariationEnvelope scale (oneOneTwoScalarAllocation doubled 2).val +
        baseProfileVariationEnvelope scale (oneOneTwoScalarAllocation doubled 0).val *
          baseProfileVariationEnvelope scale (oneOneTwoScalarAllocation doubled 1).val *
          baseProfileVariationEnvelope scale (oneOneTwoScalarAllocation doubled 2).val) *
        (34505600000 / (dyadicRadius scale : ℝ) ^ 4) := hpoint
    _ = 8833433600000 / (dyadicRadius scale : ℝ) ^ 3 := by
      have hradius : (dyadicRadius scale : ℝ) ≠ 0 := by
        norm_num [dyadicRadius]
      fin_cases doubled <;>
        simp [oneOneTwoScalarAllocation, nextProfileVariationEnvelope,
          baseProfileVariationEnvelope] <;>
        field_simp [hradius] <;> norm_num

/-- Each unweighted scalar-`100` / Hodge-`122` face has exact inverse-cubic mass numerator
`512 * 7483641600000`. -/
theorem dyadicHodgeThreeAxisNaturalProductFaceMass_residual122_le
    (scale : ℕ) (single : Fin 3) (component coordinate input : Fin 3)
    (hscale : 3 ≤ scale) :
    dyadicHodgeThreeAxisNaturalProductFaceMass scale
        (oneTwoTwoScalarAllocation single 0).val
        (oneTwoTwoScalarAllocation single 1).val
        (oneTwoTwoScalarAllocation single 2).val
        component coordinate input ≤
      3831624499200000 / (dyadicRadius scale : ℝ) ^ 3 := by
  have hpoint := dyadicHodgeThreeAxisNaturalProductFaceMass_le_envelopes_of_pointwise
    scale (oneTwoTwoScalarAllocation single 0).val
      (oneTwoTwoScalarAllocation single 1).val
      (oneTwoTwoScalarAllocation single 2).val
      component coordinate input
      (7483641600000 / (dyadicRadius scale : ℝ) ^ 5) (by positivity)
      (fun firstIndex secondIndex thirdIndex hfirstIndex hsecondIndex hthirdIndex ↦
        norm_dyadicHodgeThreeAxisSubsetProductFace_residual122_le
          scale single component coordinate input firstIndex secondIndex thirdIndex hscale
            hfirstIndex hsecondIndex hthirdIndex)
  calc
    _ ≤ (nextProfileVariationEnvelope scale (oneTwoTwoScalarAllocation single 0).val *
          nextProfileVariationEnvelope scale (oneTwoTwoScalarAllocation single 1).val *
          nextProfileVariationEnvelope scale (oneTwoTwoScalarAllocation single 2).val +
        baseProfileVariationEnvelope scale (oneTwoTwoScalarAllocation single 0).val *
          baseProfileVariationEnvelope scale (oneTwoTwoScalarAllocation single 1).val *
          baseProfileVariationEnvelope scale (oneTwoTwoScalarAllocation single 2).val) *
        (7483641600000 / (dyadicRadius scale : ℝ) ^ 5) := hpoint
    _ = 3831624499200000 / (dyadicRadius scale : ℝ) ^ 3 := by
      have hradius : (dyadicRadius scale : ℝ) ≠ 0 := by
        norm_num [dyadicRadius]
      fin_cases single <;>
        simp [oneTwoTwoScalarAllocation, nextProfileVariationEnvelope,
          baseProfileVariationEnvelope] <;>
        field_simp [hradius] <;> norm_num

/-- Each actual scalar-`110` / Hodge-`112` allocation face retains multiplicity four. -/
theorem directDyadicHodgeThreeAxisNaturalAllocationFaceMass_residual112_le
    (scale : ℕ) (doubled : Fin 3) (component coordinate input : Fin 3)
    (hscale : 3 ≤ scale) :
    directDyadicHodgeThreeAxisNaturalAllocationFaceMass scale component coordinate input
        (oneOneTwoScalarAllocation doubled 0)
        (oneOneTwoScalarAllocation doubled 1)
        (oneOneTwoScalarAllocation doubled 2) ≤
      35333734400000 / (dyadicRadius scale : ℝ) ^ 3 := by
  rw [directDyadicHodgeThreeAxisNaturalAllocationFaceMass_eq_weighted]
  have hface := dyadicHodgeThreeAxisNaturalProductFaceMass_residual112_le
    scale doubled component coordinate input hscale
  have hweight : secondOrderBinomialWeight (oneOneTwoScalarAllocation doubled 0) *
      secondOrderBinomialWeight (oneOneTwoScalarAllocation doubled 1) *
        secondOrderBinomialWeight (oneOneTwoScalarAllocation doubled 2) = 4 := by
    fin_cases doubled <;>
      simp [oneOneTwoScalarAllocation, secondOrderBinomialWeight]
  rw [hweight]
  calc
    (4 : ℝ) * dyadicHodgeThreeAxisNaturalProductFaceMass scale
        (oneOneTwoScalarAllocation doubled 0).val
        (oneOneTwoScalarAllocation doubled 1).val
        (oneOneTwoScalarAllocation doubled 2).val component coordinate input ≤
      4 * (8833433600000 / (dyadicRadius scale : ℝ) ^ 3) := by gcongr
    _ = 35333734400000 / (dyadicRadius scale : ℝ) ^ 3 := by ring

/-- Each actual scalar-`100` / Hodge-`122` allocation face retains multiplicity two. -/
theorem directDyadicHodgeThreeAxisNaturalAllocationFaceMass_residual122_le
    (scale : ℕ) (single : Fin 3) (component coordinate input : Fin 3)
    (hscale : 3 ≤ scale) :
    directDyadicHodgeThreeAxisNaturalAllocationFaceMass scale component coordinate input
        (oneTwoTwoScalarAllocation single 0)
        (oneTwoTwoScalarAllocation single 1)
        (oneTwoTwoScalarAllocation single 2) ≤
      7663248998400000 / (dyadicRadius scale : ℝ) ^ 3 := by
  rw [directDyadicHodgeThreeAxisNaturalAllocationFaceMass_eq_weighted]
  have hface := dyadicHodgeThreeAxisNaturalProductFaceMass_residual122_le
    scale single component coordinate input hscale
  have hweight : secondOrderBinomialWeight (oneTwoTwoScalarAllocation single 0) *
      secondOrderBinomialWeight (oneTwoTwoScalarAllocation single 1) *
        secondOrderBinomialWeight (oneTwoTwoScalarAllocation single 2) = 2 := by
    fin_cases single <;>
      simp [oneTwoTwoScalarAllocation, secondOrderBinomialWeight]
  rw [hweight]
  calc
    (2 : ℝ) * dyadicHodgeThreeAxisNaturalProductFaceMass scale
        (oneTwoTwoScalarAllocation single 0).val
        (oneTwoTwoScalarAllocation single 1).val
        (oneTwoTwoScalarAllocation single 2).val component coordinate input ≤
      2 * (3831624499200000 / (dyadicRadius scale : ℝ) ^ 3) := by gcongr
    _ = 7663248998400000 / (dyadicRadius scale : ℝ) ^ 3 := by ring

/-- The finite mass of the six strict residual allocation faces, with their axis lineage. -/
def directDyadicHodgeThreeAxisStrictResidualAllocationMass
    (scale : ℕ) (component coordinate input : Fin 3) : ℝ :=
  (∑ doubled : Fin 3,
    directDyadicHodgeThreeAxisNaturalAllocationFaceMass scale component coordinate input
      (oneOneTwoScalarAllocation doubled 0)
      (oneOneTwoScalarAllocation doubled 1)
      (oneOneTwoScalarAllocation doubled 2)) +
    ∑ single : Fin 3,
      directDyadicHodgeThreeAxisNaturalAllocationFaceMass scale component coordinate input
        (oneTwoTwoScalarAllocation single 0)
        (oneTwoTwoScalarAllocation single 1)
        (oneTwoTwoScalarAllocation single 2)

/-- **[proved-derived]** The six actual strict residual faces have exact combined inverse-cubic
numerator `3*35333734400000 + 3*7663248998400000`. -/
theorem directDyadicHodgeThreeAxisStrictResidualAllocationMass_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    directDyadicHodgeThreeAxisStrictResidualAllocationMass scale component coordinate input ≤
      23095748198400000 / (dyadicRadius scale : ℝ) ^ 3 := by
  unfold directDyadicHodgeThreeAxisStrictResidualAllocationMass
  calc
    _ ≤ (∑ _doubled : Fin 3,
          35333734400000 / (dyadicRadius scale : ℝ) ^ 3) +
        ∑ _single : Fin 3,
          7663248998400000 / (dyadicRadius scale : ℝ) ^ 3 := by
      apply add_le_add
      · gcongr with doubled
        exact directDyadicHodgeThreeAxisNaturalAllocationFaceMass_residual112_le
          scale doubled component coordinate input hscale
      · gcongr with single
        exact directDyadicHodgeThreeAxisNaturalAllocationFaceMass_residual122_le
          scale single component coordinate input hscale
    _ = 23095748198400000 / (dyadicRadius scale : ℝ) ^ 3 := by
      simp
      ring

section Audit

#print axioms oneOneTwoScalarAllocation_complement
#print axioms threeAxisMixedForwardDifference_directDyadicScalar_backwardPadded_eq_zero_of_first_lt
#print axioms dyadicHodgeThreeAxisGlobalProductFaceMass_eq_natural
#print axioms directDyadicHodgeThreeAxisGlobalAllocationFaceMass_eq_natural
#print axioms norm_hodgeJacobianMultiplierEntry_threeAxis_oneOneTwo_le_of_controlled
#print axioms norm_dyadicHodgeThreeAxisSubsetProductFace_residual112_le
#print axioms norm_dyadicHodgeThreeAxisSubsetProductFace_residual122_le
#print axioms dyadicHodgeThreeAxisNaturalProductFaceMass_residual112_le
#print axioms dyadicHodgeThreeAxisNaturalProductFaceMass_residual122_le
#print axioms directDyadicHodgeThreeAxisStrictResidualAllocationMass_le

end Audit

end Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisResidualFaces
