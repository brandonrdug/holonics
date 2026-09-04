import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeThreeAxisThirdTwoSlice

/-!
# The two remaining scalar-order-two Hodge allocation slabs

**[proved-derived]** The first completed nine-face slab is not special to the displayed third
coordinate.  This owner extracts the two-axis Hodge stencil in an arbitrary coordinate plane,
then composes that law with the shared scalar chart.  It returns the slabs whose scalar first or
second order is two, while retaining the exact three-axis allocation multiplicities.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisOtherTwoSlices

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesSmoothHodgeJacobianBand
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeHigherMixedVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeLowerMixedVariation
open Soma.Holonics.Millennium.NavierStokesReciprocalDifferenceRecurrence
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeKernelVariation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeSupportStencil
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeProductFaces
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeTwoAxisMass
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeEnvelopeScaling
open Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeScaleDescent
open Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeProductMass
open Soma.Holonics.Millennium.NavierStokesThreeAxisScalarSubsetVariation
open Soma.Holonics.Millennium.NavierStokesThreeAxisDyadicHodgeSupportStencil
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisAllocation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisScalarChart
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisCornerMass
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisThirdTwoSlice

/-- A controlled Hodge stencil in any genuine coordinate plane obeys the two-axis complementary
face bound selected by the two scalar allocation orders. -/
theorem norm_complementaryHodge_twoAxis_of_stencil_le
    (scale firstOrder secondOrder : ℕ) (first second : Fin 3)
    (component coordinate input : Fin 3) (frequency : SpatialFrequency)
    (hscale : 3 ≤ scale) (hfirstOrder : firstOrder ≤ 2)
    (hsecondOrder : secondOrder ≤ 2) (haxes : first ≠ second)
    (hstencil : TwoAxisStencilControlled
      (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale)
      first second frequency (2 - firstOrder) (2 - secondOrder)) :
    ‖mixedForwardDifference first second (2 - firstOrder) (2 - secondOrder)
      (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
      frequency‖ ≤ dyadicHodgeComplementaryFaceBound scale firstOrder secondOrder := by
  have hlower := dyadicHodgeControlledLower_pos scale hscale
  have hbound : 0 ≤ dyadicHodgeControlledBound scale := by
    unfold dyadicHodgeControlledBound
    positivity
  interval_cases firstOrder <;> interval_cases secondOrder
  · have hraw := norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_two_two_le
      hlower hbound first second haxes frequency component coordinate input hstencil
    simpa [dyadicHodgeComplementaryFaceBound] using
      hraw.trans (hodgeJacobianEntryMixedTwoTwoEnvelope_dyadic_le scale hscale)
  · have hraw := norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_two_one_le
      hlower hbound first second haxes frequency component coordinate input hstencil
    simpa [dyadicHodgeComplementaryFaceBound] using
      hraw.trans (hodgeJacobianEntryMixedOneTwoEnvelope_dyadic_le scale hscale)
  · have hraw := norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_two_zero_le
      hlower hbound first second frequency component coordinate input hstencil
    simpa [dyadicHodgeComplementaryFaceBound] using
      hraw.trans (hodgeJacobianEntrySecondEnvelope_dyadic_le scale hscale)
  · have hraw := norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_one_two_le
      hlower hbound first second haxes frequency component coordinate input hstencil
    simpa [dyadicHodgeComplementaryFaceBound] using
      hraw.trans (hodgeJacobianEntryMixedOneTwoEnvelope_dyadic_le scale hscale)
  · have hraw := norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_one_one_le
      hlower hbound first second haxes frequency component coordinate input hstencil
    simpa [dyadicHodgeComplementaryFaceBound] using
      hraw.trans (hodgeJacobianEntryMixedOneOneEnvelope_dyadic_le scale hscale)
  · have hraw := norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_one_zero_le
      hlower hbound first second frequency component coordinate input hstencil
    simpa [dyadicHodgeComplementaryFaceBound] using
      hraw.trans (hodgeJacobianEntryFirstEnvelope_dyadic_le scale hscale)
  · have hraw := norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_zero_two_le
      hlower hbound first second frequency component coordinate input hstencil
    simpa [dyadicHodgeComplementaryFaceBound] using
      hraw.trans (hodgeJacobianEntrySecondEnvelope_dyadic_le scale hscale)
  · have hraw := norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_zero_one_le
      hlower hbound first second frequency component coordinate input hstencil
    simpa [dyadicHodgeComplementaryFaceBound] using
      hraw.trans (hodgeJacobianEntryFirstEnvelope_dyadic_le scale hscale)
  · simpa [dyadicHodgeComplementaryFaceBound, mixedForwardDifference] using
      norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_zero_zero_le_one
        first second frequency component coordinate input

/-- Pointwise control when the scalar first-axis order is two. -/
theorem norm_dyadicHodgeThreeAxisSubsetProductFace_first_two_le
    (scale secondOrder thirdOrder : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) (hscale : 3 ≤ scale)
    (hsecondOrder : secondOrder ≤ 2) (hthirdOrder : thirdOrder ≤ 2)
    (hfirstIndex : firstIndex < dyadicHodgeApertureCount scale + 2)
    (hsecondIndex : secondIndex < dyadicHodgeApertureCount scale + secondOrder)
    (hthirdIndex : thirdIndex < dyadicHodgeApertureCount scale + thirdOrder) :
    ‖dyadicHodgeThreeAxisSubsetProductFace scale 2 secondOrder thirdOrder
        component coordinate input firstIndex secondIndex thirdIndex‖ ≤
      ‖dyadicTensorBandThreeAxisVariation scale 2 secondOrder thirdOrder
        firstIndex secondIndex thirdIndex‖ *
        dyadicHodgeComplementaryFaceBound scale secondOrder thirdOrder := by
  let frequency := dyadicHodgeThreeAxisSubsetPaddedFrequency scale
    2 secondOrder thirdOrder firstIndex secondIndex thirdIndex
  have hscalar :=
    threeAxisMixedForwardDifference_directDyadicScalarCoefficient_subsetPadded_eq
      scale 2 secondOrder thirdOrder firstIndex secondIndex thirdIndex
      (by omega) hsecondOrder hthirdOrder hfirstIndex hsecondIndex hthirdIndex
  change ‖threeAxisMixedForwardDifference 0 1 2 2 secondOrder thirdOrder
      (directDyadicScalarCoefficient scale) frequency *
    threeAxisMixedForwardDifference 0 1 2 0 (2 - secondOrder) (2 - thirdOrder)
      (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
      (threeAxisStencilPoint 0 1 2 frequency 2 secondOrder thirdOrder)‖ ≤ _
  change threeAxisMixedForwardDifference 0 1 2 2 secondOrder thirdOrder
      (directDyadicScalarCoefficient scale) frequency = _ at hscalar
  rw [hscalar, norm_mul]
  by_cases hzero : dyadicTensorBandThreeAxisVariation scale 2 secondOrder thirdOrder
      firstIndex secondIndex thirdIndex = 0
  · simp [hzero]
  · have hglobal : threeAxisMixedForwardDifference 0 1 2 2 secondOrder thirdOrder
        (directDyadicScalarCoefficient scale) frequency ≠ 0 := by
      rw [hscalar]
      exact hzero
    have hstencil : ThreeAxisStencilControlled
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale)
        0 1 2 (threeAxisStencilPoint 0 1 2 frequency 2 secondOrder thirdOrder)
        0 (2 - secondOrder) (2 - thirdOrder) := by
      simpa [dyadicHodgeControlledLower, dyadicHodgeControlledBound] using
        (directDyadicScalar_threeAxis_support_controls_complementaryHodgeStencil
          scale 2 secondOrder thirdOrder
          (dyadicHodgeInnerCutoff_ge_three_of_scale_ge_three scale hscale)
          (by omega) hsecondOrder hthirdOrder frequency hglobal)
    have htwo : TwoAxisStencilControlled
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale)
        1 2 (threeAxisStencilPoint 0 1 2 frequency 2 secondOrder thirdOrder)
        (2 - secondOrder) (2 - thirdOrder) := by
      simpa [threeAxisStencilPoint] using hstencil.secondThird (firstOffset := 0) (by omega)
    gcongr
    change ‖mixedForwardDifference 1 2 (2 - secondOrder) (2 - thirdOrder)
      (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
      (threeAxisStencilPoint 0 1 2 frequency 2 secondOrder thirdOrder)‖ ≤ _
    exact norm_complementaryHodge_twoAxis_of_stencil_le scale secondOrder thirdOrder
      1 2 component coordinate input
      (threeAxisStencilPoint 0 1 2 frequency 2 secondOrder thirdOrder)
      hscale hsecondOrder hthirdOrder (by decide) htwo

/-- Pointwise control when the scalar second-axis order is two. -/
theorem norm_dyadicHodgeThreeAxisSubsetProductFace_second_two_le
    (scale firstOrder thirdOrder : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) (hscale : 3 ≤ scale)
    (hfirstOrder : firstOrder ≤ 2) (hthirdOrder : thirdOrder ≤ 2)
    (hfirstIndex : firstIndex < dyadicHodgeApertureCount scale + firstOrder)
    (hsecondIndex : secondIndex < dyadicHodgeApertureCount scale + 2)
    (hthirdIndex : thirdIndex < dyadicHodgeApertureCount scale + thirdOrder) :
    ‖dyadicHodgeThreeAxisSubsetProductFace scale firstOrder 2 thirdOrder
        component coordinate input firstIndex secondIndex thirdIndex‖ ≤
      ‖dyadicTensorBandThreeAxisVariation scale firstOrder 2 thirdOrder
        firstIndex secondIndex thirdIndex‖ *
        dyadicHodgeComplementaryFaceBound scale firstOrder thirdOrder := by
  let frequency := dyadicHodgeThreeAxisSubsetPaddedFrequency scale
    firstOrder 2 thirdOrder firstIndex secondIndex thirdIndex
  have hscalar :=
    threeAxisMixedForwardDifference_directDyadicScalarCoefficient_subsetPadded_eq
      scale firstOrder 2 thirdOrder firstIndex secondIndex thirdIndex
      hfirstOrder (by omega) hthirdOrder hfirstIndex hsecondIndex hthirdIndex
  change ‖threeAxisMixedForwardDifference 0 1 2 firstOrder 2 thirdOrder
      (directDyadicScalarCoefficient scale) frequency *
    threeAxisMixedForwardDifference 0 1 2 (2 - firstOrder) 0 (2 - thirdOrder)
      (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
      (threeAxisStencilPoint 0 1 2 frequency firstOrder 2 thirdOrder)‖ ≤ _
  change threeAxisMixedForwardDifference 0 1 2 firstOrder 2 thirdOrder
      (directDyadicScalarCoefficient scale) frequency = _ at hscalar
  rw [hscalar, norm_mul]
  by_cases hzero : dyadicTensorBandThreeAxisVariation scale firstOrder 2 thirdOrder
      firstIndex secondIndex thirdIndex = 0
  · simp [hzero]
  · have hglobal : threeAxisMixedForwardDifference 0 1 2 firstOrder 2 thirdOrder
        (directDyadicScalarCoefficient scale) frequency ≠ 0 := by
      rw [hscalar]
      exact hzero
    have hstencil : ThreeAxisStencilControlled
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale)
        0 1 2 (threeAxisStencilPoint 0 1 2 frequency firstOrder 2 thirdOrder)
        (2 - firstOrder) 0 (2 - thirdOrder) := by
      simpa [dyadicHodgeControlledLower, dyadicHodgeControlledBound] using
        (directDyadicScalar_threeAxis_support_controls_complementaryHodgeStencil
          scale firstOrder 2 thirdOrder
          (dyadicHodgeInnerCutoff_ge_three_of_scale_ge_three scale hscale)
          hfirstOrder (by omega) hthirdOrder frequency hglobal)
    have htwo : TwoAxisStencilControlled
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale)
        0 2 (threeAxisStencilPoint 0 1 2 frequency firstOrder 2 thirdOrder)
        (2 - firstOrder) (2 - thirdOrder) := by
      simpa [threeAxisStencilPoint] using hstencil.firstThird (secondOffset := 0) (by omega)
    gcongr
    change ‖mixedForwardDifference 0 2 (2 - firstOrder) (2 - thirdOrder)
      (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
      (threeAxisStencilPoint 0 1 2 frequency firstOrder 2 thirdOrder)‖ ≤ _
    exact norm_complementaryHodge_twoAxis_of_stencil_le scale firstOrder thirdOrder
      0 2 component coordinate input
      (threeAxisStencilPoint 0 1 2 frequency firstOrder 2 thirdOrder)
      hscale hfirstOrder hthirdOrder (by decide) htwo

/-- Natural unweighted mass of any one of the 27 scalar/Hodge product faces. -/
def dyadicHodgeThreeAxisNaturalProductFaceMass
    (scale firstOrder secondOrder thirdOrder : ℕ)
    (component coordinate input : Fin 3) : ℝ :=
  ∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + firstOrder),
    ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + secondOrder),
      ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale + thirdOrder),
        ‖dyadicHodgeThreeAxisSubsetProductFace scale firstOrder secondOrder thirdOrder
          component coordinate input firstIndex secondIndex thirdIndex‖

/-- A pointwise face bound factors exactly through the scalar tensor Fubini population. -/
theorem dyadicHodgeThreeAxisNaturalProductFaceMass_le_envelopes_of_pointwise
    (scale firstOrder secondOrder thirdOrder : ℕ)
    (component coordinate input : Fin 3) (hodgeBound : ℝ) (hhodgeBound : 0 ≤ hodgeBound)
    (hpoint : ∀ firstIndex secondIndex thirdIndex,
      firstIndex < dyadicHodgeApertureCount scale + firstOrder →
      secondIndex < dyadicHodgeApertureCount scale + secondOrder →
      thirdIndex < dyadicHodgeApertureCount scale + thirdOrder →
      ‖dyadicHodgeThreeAxisSubsetProductFace scale firstOrder secondOrder thirdOrder
          component coordinate input firstIndex secondIndex thirdIndex‖ ≤
        ‖dyadicTensorBandThreeAxisVariation scale firstOrder secondOrder thirdOrder
          firstIndex secondIndex thirdIndex‖ * hodgeBound) :
    dyadicHodgeThreeAxisNaturalProductFaceMass scale firstOrder secondOrder thirdOrder
        component coordinate input ≤
      (nextProfileVariationEnvelope scale firstOrder *
          nextProfileVariationEnvelope scale secondOrder *
          nextProfileVariationEnvelope scale thirdOrder +
        baseProfileVariationEnvelope scale firstOrder *
          baseProfileVariationEnvelope scale secondOrder *
          baseProfileVariationEnvelope scale thirdOrder) * hodgeBound := by
  unfold dyadicHodgeThreeAxisNaturalProductFaceMass
  calc
    _ ≤ ∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + firstOrder),
        ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + secondOrder),
          ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale + thirdOrder),
            ‖dyadicTensorBandThreeAxisVariation scale firstOrder secondOrder thirdOrder
              firstIndex secondIndex thirdIndex‖ * hodgeBound := by
      gcongr with firstIndex hfirst secondIndex hsecond thirdIndex hthird
      exact hpoint firstIndex secondIndex thirdIndex
        (Finset.mem_range.mp hfirst) (Finset.mem_range.mp hsecond)
        (Finset.mem_range.mp hthird)
    _ = (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + firstOrder),
        ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + secondOrder),
          ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale + thirdOrder),
            ‖dyadicTensorBandThreeAxisVariation scale firstOrder secondOrder thirdOrder
              firstIndex secondIndex thirdIndex‖) * hodgeBound := by
      simp only [Finset.sum_mul]
    _ ≤ (nextProfileVariationEnvelope scale firstOrder *
          nextProfileVariationEnvelope scale secondOrder *
          nextProfileVariationEnvelope scale thirdOrder +
        baseProfileVariationEnvelope scale firstOrder *
          baseProfileVariationEnvelope scale secondOrder *
          baseProfileVariationEnvelope scale thirdOrder) * hodgeBound := by
      exact mul_le_mul_of_nonneg_right
        (sum_norm_dyadicTensorBandThreeAxisVariation_le_envelopes
          scale firstOrder secondOrder thirdOrder) hhodgeBound

/-- Natural mass bound for every face in the scalar-first-order-two slab. -/
theorem dyadicHodgeThreeAxisNaturalProductFaceMass_first_two_le_envelopes
    (scale secondOrder thirdOrder : ℕ) (component coordinate input : Fin 3)
    (hscale : 3 ≤ scale) (hsecondOrder : secondOrder ≤ 2)
    (hthirdOrder : thirdOrder ≤ 2) :
    dyadicHodgeThreeAxisNaturalProductFaceMass scale 2 secondOrder thirdOrder
        component coordinate input ≤
      (nextProfileVariationEnvelope scale 2 *
          nextProfileVariationEnvelope scale secondOrder *
          nextProfileVariationEnvelope scale thirdOrder +
        baseProfileVariationEnvelope scale 2 *
          baseProfileVariationEnvelope scale secondOrder *
          baseProfileVariationEnvelope scale thirdOrder) *
        dyadicHodgeComplementaryFaceBound scale secondOrder thirdOrder := by
  apply dyadicHodgeThreeAxisNaturalProductFaceMass_le_envelopes_of_pointwise
  · interval_cases secondOrder <;> interval_cases thirdOrder <;>
      simp [dyadicHodgeComplementaryFaceBound] <;> positivity
  · intro firstIndex secondIndex thirdIndex hfirstIndex hsecondIndex hthirdIndex
    exact norm_dyadicHodgeThreeAxisSubsetProductFace_first_two_le
      scale secondOrder thirdOrder component coordinate input
      firstIndex secondIndex thirdIndex hscale hsecondOrder hthirdOrder
      hfirstIndex hsecondIndex hthirdIndex

/-- Natural mass bound for every face in the scalar-second-order-two slab. -/
theorem dyadicHodgeThreeAxisNaturalProductFaceMass_second_two_le_envelopes
    (scale firstOrder thirdOrder : ℕ) (component coordinate input : Fin 3)
    (hscale : 3 ≤ scale) (hfirstOrder : firstOrder ≤ 2)
    (hthirdOrder : thirdOrder ≤ 2) :
    dyadicHodgeThreeAxisNaturalProductFaceMass scale firstOrder 2 thirdOrder
        component coordinate input ≤
      (nextProfileVariationEnvelope scale firstOrder *
          nextProfileVariationEnvelope scale 2 *
          nextProfileVariationEnvelope scale thirdOrder +
        baseProfileVariationEnvelope scale firstOrder *
          baseProfileVariationEnvelope scale 2 *
          baseProfileVariationEnvelope scale thirdOrder) *
        dyadicHodgeComplementaryFaceBound scale firstOrder thirdOrder := by
  apply dyadicHodgeThreeAxisNaturalProductFaceMass_le_envelopes_of_pointwise
  · interval_cases firstOrder <;> interval_cases thirdOrder <;>
      simp [dyadicHodgeComplementaryFaceBound] <;> positivity
  · intro firstIndex secondIndex thirdIndex hfirstIndex hsecondIndex hthirdIndex
    exact norm_dyadicHodgeThreeAxisSubsetProductFace_second_two_le
      scale firstOrder thirdOrder component coordinate input
      firstIndex secondIndex thirdIndex hscale hfirstOrder hthirdOrder
      hfirstIndex hsecondIndex hthirdIndex

/-- The same exact inverse-cubic radial table controls the first-order-two slab. -/
theorem dyadicHodgeThreeAxisFirstTwoEnvelope_le_radial
    (scale secondOrder thirdOrder : ℕ) (hsecondOrder : secondOrder ≤ 2)
    (hthirdOrder : thirdOrder ≤ 2) :
    (nextProfileVariationEnvelope scale 2 *
          nextProfileVariationEnvelope scale secondOrder *
          nextProfileVariationEnvelope scale thirdOrder +
        baseProfileVariationEnvelope scale 2 *
          baseProfileVariationEnvelope scale secondOrder *
          baseProfileVariationEnvelope scale thirdOrder) *
        dyadicHodgeComplementaryFaceBound scale secondOrder thirdOrder ≤
      dyadicHodgeThirdTwoFaceRadialConstant secondOrder thirdOrder /
        (dyadicRadius scale : ℝ) ^ 3 := by
  simpa only [mul_comm, mul_left_comm, mul_assoc] using
    dyadicHodgeThreeAxisThirdTwoEnvelope_le_radial
      scale secondOrder thirdOrder hsecondOrder hthirdOrder

/-- The same exact inverse-cubic radial table controls the second-order-two slab. -/
theorem dyadicHodgeThreeAxisSecondTwoEnvelope_le_radial
    (scale firstOrder thirdOrder : ℕ) (hfirstOrder : firstOrder ≤ 2)
    (hthirdOrder : thirdOrder ≤ 2) :
    (nextProfileVariationEnvelope scale firstOrder *
          nextProfileVariationEnvelope scale 2 *
          nextProfileVariationEnvelope scale thirdOrder +
        baseProfileVariationEnvelope scale firstOrder *
          baseProfileVariationEnvelope scale 2 *
          baseProfileVariationEnvelope scale thirdOrder) *
        dyadicHodgeComplementaryFaceBound scale firstOrder thirdOrder ≤
      dyadicHodgeThirdTwoFaceRadialConstant firstOrder thirdOrder /
        (dyadicRadius scale : ℝ) ^ 3 := by
  simpa only [mul_comm, mul_left_comm, mul_assoc] using
    dyadicHodgeThreeAxisThirdTwoEnvelope_le_radial
      scale firstOrder thirdOrder hfirstOrder hthirdOrder

/-- Uniform inverse-cubic bound for each natural face in the first-order-two slab. -/
theorem dyadicHodgeThreeAxisNaturalProductFaceMass_first_two_le_radial
    (scale secondOrder thirdOrder : ℕ) (component coordinate input : Fin 3)
    (hscale : 3 ≤ scale) (hsecondOrder : secondOrder ≤ 2)
    (hthirdOrder : thirdOrder ≤ 2) :
    dyadicHodgeThreeAxisNaturalProductFaceMass scale 2 secondOrder thirdOrder
        component coordinate input ≤
      dyadicHodgeThirdTwoFaceRadialConstant secondOrder thirdOrder /
        (dyadicRadius scale : ℝ) ^ 3 :=
  (dyadicHodgeThreeAxisNaturalProductFaceMass_first_two_le_envelopes
    scale secondOrder thirdOrder component coordinate input
      hscale hsecondOrder hthirdOrder).trans
    (dyadicHodgeThreeAxisFirstTwoEnvelope_le_radial
      scale secondOrder thirdOrder hsecondOrder hthirdOrder)

/-- Uniform inverse-cubic bound for each natural face in the second-order-two slab. -/
theorem dyadicHodgeThreeAxisNaturalProductFaceMass_second_two_le_radial
    (scale firstOrder thirdOrder : ℕ) (component coordinate input : Fin 3)
    (hscale : 3 ≤ scale) (hfirstOrder : firstOrder ≤ 2)
    (hthirdOrder : thirdOrder ≤ 2) :
    dyadicHodgeThreeAxisNaturalProductFaceMass scale firstOrder 2 thirdOrder
        component coordinate input ≤
      dyadicHodgeThirdTwoFaceRadialConstant firstOrder thirdOrder /
        (dyadicRadius scale : ℝ) ^ 3 :=
  (dyadicHodgeThreeAxisNaturalProductFaceMass_second_two_le_envelopes
    scale firstOrder thirdOrder component coordinate input
      hscale hfirstOrder hthirdOrder).trans
    (dyadicHodgeThreeAxisSecondTwoEnvelope_le_radial
      scale firstOrder thirdOrder hfirstOrder hthirdOrder)

/-- Every actual allocation value on its natural padded address is exactly its three binomial
weights times the corresponding unweighted natural product face. -/
theorem directDyadicHodgeThreeAxisAllocationFace_eq_weightedNaturalProductFace
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstAllocation secondAllocation thirdAllocation : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) :
    directDyadicHodgeThreeAxisAllocationFace scale component coordinate input
        firstAllocation secondAllocation thirdAllocation
        (dyadicHodgeThreeAxisSubsetPaddedFrequency scale
          firstAllocation.val secondAllocation.val thirdAllocation.val
          firstIndex secondIndex thirdIndex) =
      ((secondOrderBinomialWeight firstAllocation *
          secondOrderBinomialWeight secondAllocation *
          secondOrderBinomialWeight thirdAllocation : ℕ) : ℂ) *
        dyadicHodgeThreeAxisSubsetProductFace scale
          firstAllocation.val secondAllocation.val thirdAllocation.val
          component coordinate input firstIndex secondIndex thirdIndex := by
  simp [directDyadicHodgeThreeAxisAllocationFace, threeAxisHodgeAllocationFace,
    dyadicHodgeThreeAxisSubsetProductFace]
  ring

/-- Natural finite mass of any actual weighted allocation face. -/
def directDyadicHodgeThreeAxisNaturalAllocationFaceMass
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstAllocation secondAllocation thirdAllocation : Fin 3) : ℝ :=
  ∑ firstIndex ∈ Finset.range
      (dyadicHodgeApertureCount scale + firstAllocation.val),
    ∑ secondIndex ∈ Finset.range
        (dyadicHodgeApertureCount scale + secondAllocation.val),
      ∑ thirdIndex ∈ Finset.range
          (dyadicHodgeApertureCount scale + thirdAllocation.val),
        ‖directDyadicHodgeThreeAxisAllocationFace scale component coordinate input
          firstAllocation secondAllocation thirdAllocation
          (dyadicHodgeThreeAxisSubsetPaddedFrequency scale
            firstAllocation.val secondAllocation.val thirdAllocation.val
            firstIndex secondIndex thirdIndex)‖

/-- The exact three-axis occurrence multiplicity factors out of every actual face mass. -/
theorem directDyadicHodgeThreeAxisNaturalAllocationFaceMass_eq_weighted
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstAllocation secondAllocation thirdAllocation : Fin 3) :
    directDyadicHodgeThreeAxisNaturalAllocationFaceMass scale component coordinate input
        firstAllocation secondAllocation thirdAllocation =
      (secondOrderBinomialWeight firstAllocation *
          secondOrderBinomialWeight secondAllocation *
          secondOrderBinomialWeight thirdAllocation : ℕ) *
        dyadicHodgeThreeAxisNaturalProductFaceMass scale
          firstAllocation.val secondAllocation.val thirdAllocation.val
          component coordinate input := by
  simp only [directDyadicHodgeThreeAxisNaturalAllocationFaceMass,
    dyadicHodgeThreeAxisNaturalProductFaceMass,
    directDyadicHodgeThreeAxisAllocationFace_eq_weightedNaturalProductFace,
    norm_mul, Complex.norm_natCast, Finset.mul_sum]

/-- Uniform inverse-cubic bound for every actual face in the first-order-two slab. -/
theorem directDyadicHodgeThreeAxisNaturalAllocationFaceMass_first_two_le_radial
    (scale : ℕ) (component coordinate input : Fin 3)
    (secondAllocation thirdAllocation : Fin 3) (hscale : 3 ≤ scale) :
    directDyadicHodgeThreeAxisNaturalAllocationFaceMass scale component coordinate input
        (2 : Fin 3) secondAllocation thirdAllocation ≤
      (secondOrderBinomialWeight secondAllocation *
          secondOrderBinomialWeight thirdAllocation : ℕ) *
        (dyadicHodgeThirdTwoFaceRadialConstant
            secondAllocation.val thirdAllocation.val /
          (dyadicRadius scale : ℝ) ^ 3) := by
  rw [directDyadicHodgeThreeAxisNaturalAllocationFaceMass_eq_weighted]
  have hface := dyadicHodgeThreeAxisNaturalProductFaceMass_first_two_le_radial
    scale secondAllocation.val thirdAllocation.val component coordinate input
      hscale (by omega) (by omega)
  have hweight : 0 ≤ ((secondOrderBinomialWeight secondAllocation *
      secondOrderBinomialWeight thirdAllocation : ℕ) : ℝ) := by positivity
  simpa [secondOrderBinomialWeight] using
    mul_le_mul_of_nonneg_left hface hweight

/-- Uniform inverse-cubic bound for every actual face in the second-order-two slab. -/
theorem directDyadicHodgeThreeAxisNaturalAllocationFaceMass_second_two_le_radial
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstAllocation thirdAllocation : Fin 3) (hscale : 3 ≤ scale) :
    directDyadicHodgeThreeAxisNaturalAllocationFaceMass scale component coordinate input
        firstAllocation (2 : Fin 3) thirdAllocation ≤
      (secondOrderBinomialWeight firstAllocation *
          secondOrderBinomialWeight thirdAllocation : ℕ) *
        (dyadicHodgeThirdTwoFaceRadialConstant
            firstAllocation.val thirdAllocation.val /
          (dyadicRadius scale : ℝ) ^ 3) := by
  rw [directDyadicHodgeThreeAxisNaturalAllocationFaceMass_eq_weighted]
  have hface := dyadicHodgeThreeAxisNaturalProductFaceMass_second_two_le_radial
    scale firstAllocation.val thirdAllocation.val component coordinate input
      hscale (by omega) (by omega)
  have hweight : 0 ≤ ((secondOrderBinomialWeight firstAllocation *
      secondOrderBinomialWeight thirdAllocation : ℕ) : ℝ) := by positivity
  simpa [secondOrderBinomialWeight] using
    mul_le_mul_of_nonneg_left hface hweight

/-- Complete actual scalar-first-order-two slab. -/
def directDyadicHodgeThreeAxisFirstTwoAllocationSlabMass
    (scale : ℕ) (component coordinate input : Fin 3) : ℝ :=
  ∑ secondAllocation : Fin 3, ∑ thirdAllocation : Fin 3,
    directDyadicHodgeThreeAxisNaturalAllocationFaceMass scale component coordinate input
      (2 : Fin 3) secondAllocation thirdAllocation

/-- Complete actual scalar-second-order-two slab. -/
def directDyadicHodgeThreeAxisSecondTwoAllocationSlabMass
    (scale : ℕ) (component coordinate input : Fin 3) : ℝ :=
  ∑ firstAllocation : Fin 3, ∑ thirdAllocation : Fin 3,
    directDyadicHodgeThreeAxisNaturalAllocationFaceMass scale component coordinate input
      firstAllocation (2 : Fin 3) thirdAllocation

/-- **[proved-derived]** The first-order-two slab returns the same exact inverse-cubic numerator
as the already closed third-order-two slab. -/
theorem directDyadicHodgeThreeAxisFirstTwoAllocationSlabMass_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    directDyadicHodgeThreeAxisFirstTwoAllocationSlabMass scale component coordinate input ≤
      12416369280072 / (dyadicRadius scale : ℝ) ^ 3 := by
  unfold directDyadicHodgeThreeAxisFirstTwoAllocationSlabMass
  calc
    _ ≤ ∑ secondAllocation : Fin 3, ∑ thirdAllocation : Fin 3,
        (secondOrderBinomialWeight secondAllocation *
            secondOrderBinomialWeight thirdAllocation : ℕ) *
          (dyadicHodgeThirdTwoFaceRadialConstant
              secondAllocation.val thirdAllocation.val /
            (dyadicRadius scale : ℝ) ^ 3) := by
      gcongr with secondAllocation _ thirdAllocation _
      exact directDyadicHodgeThreeAxisNaturalAllocationFaceMass_first_two_le_radial
        scale component coordinate input secondAllocation thirdAllocation hscale
    _ = 12416369280072 / (dyadicRadius scale : ℝ) ^ 3 := by
      simp [Fin.sum_univ_succ, secondOrderBinomialWeight,
        dyadicHodgeThirdTwoFaceRadialConstant]
      ring

/-- **[proved-derived]** The second-order-two slab returns the same exact inverse-cubic numerator
as the other two coordinate slabs. -/
theorem directDyadicHodgeThreeAxisSecondTwoAllocationSlabMass_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    directDyadicHodgeThreeAxisSecondTwoAllocationSlabMass scale component coordinate input ≤
      12416369280072 / (dyadicRadius scale : ℝ) ^ 3 := by
  unfold directDyadicHodgeThreeAxisSecondTwoAllocationSlabMass
  calc
    _ ≤ ∑ firstAllocation : Fin 3, ∑ thirdAllocation : Fin 3,
        (secondOrderBinomialWeight firstAllocation *
            secondOrderBinomialWeight thirdAllocation : ℕ) *
          (dyadicHodgeThirdTwoFaceRadialConstant
              firstAllocation.val thirdAllocation.val /
            (dyadicRadius scale : ℝ) ^ 3) := by
      gcongr with firstAllocation _ thirdAllocation _
      exact directDyadicHodgeThreeAxisNaturalAllocationFaceMass_second_two_le_radial
        scale component coordinate input firstAllocation thirdAllocation hscale
    _ = 12416369280072 / (dyadicRadius scale : ℝ) ^ 3 := by
      simp [Fin.sum_univ_succ, secondOrderBinomialWeight,
        dyadicHodgeThirdTwoFaceRadialConstant]
      ring

section Audit

#print axioms norm_complementaryHodge_twoAxis_of_stencil_le
#print axioms norm_dyadicHodgeThreeAxisSubsetProductFace_first_two_le
#print axioms norm_dyadicHodgeThreeAxisSubsetProductFace_second_two_le
#print axioms dyadicHodgeThreeAxisNaturalProductFaceMass_le_envelopes_of_pointwise
#print axioms dyadicHodgeThreeAxisNaturalProductFaceMass_first_two_le_radial
#print axioms dyadicHodgeThreeAxisNaturalProductFaceMass_second_two_le_radial
#print axioms directDyadicHodgeThreeAxisNaturalAllocationFaceMass_eq_weighted
#print axioms directDyadicHodgeThreeAxisFirstTwoAllocationSlabMass_le
#print axioms directDyadicHodgeThreeAxisSecondTwoAllocationSlabMass_le

end Audit

end Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisOtherTwoSlices
