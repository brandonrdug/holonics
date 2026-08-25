import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeThreeAxisCornerMass

/-!
# The nine faces whose scalar third-axis order is two

**[proved-derived]** When the scalar hand receives both third-axis differences, the complementary
Hodge hand has third order zero.  The complete three-axis support pin then descends to the genuine
first/second Hodge stencil, so all nine allocation faces are controlled by the already-derived
two-axis Hodge envelopes.  The scalar side uses the all-orders three-axis chart theorem.

Every returned mass has the common inverse-cubic radial scale.  The allocation multiplicities are
retained separately and no face is estimated by mode count.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisThirdTwoSlice

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

/-- A controlled three-axis stencil with third order zero returns the exact complementary
first/second Hodge bound selected by the scalar allocation. -/
theorem norm_complementaryHodge_firstSecond_of_threeAxisStencil_le
    (scale firstOrder secondOrder : ℕ)
    (component coordinate input : Fin 3) (frequency : SpatialFrequency)
    (hscale : 3 ≤ scale) (hfirstOrder : firstOrder ≤ 2)
    (hsecondOrder : secondOrder ≤ 2)
    (hstencil : ThreeAxisStencilControlled
      (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale)
      0 1 2 frequency (2 - firstOrder) (2 - secondOrder) 0) :
    ‖threeAxisMixedForwardDifference 0 1 2
      (2 - firstOrder) (2 - secondOrder) 0
      (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
      frequency‖ ≤ dyadicHodgeComplementaryFaceBound scale firstOrder secondOrder := by
  have hlower := dyadicHodgeControlledLower_pos scale hscale
  have hbound : 0 ≤ dyadicHodgeControlledBound scale := by
    unfold dyadicHodgeControlledBound
    positivity
  interval_cases firstOrder <;> interval_cases secondOrder
  · have htwo : TwoAxisStencilControlled
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale)
        0 1 frequency 2 2 := by
      simpa [threeAxisStencilPoint] using hstencil.firstSecond (thirdOffset := 0) (by omega)
    have hraw := norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_two_two_le
      hlower hbound 0 1 (by decide) frequency component coordinate input htwo
    simpa [dyadicHodgeComplementaryFaceBound, threeAxisMixedForwardDifference,
      mixedForwardDifference] using
        hraw.trans (hodgeJacobianEntryMixedTwoTwoEnvelope_dyadic_le scale hscale)
  · have htwo : TwoAxisStencilControlled
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale)
        0 1 frequency 2 1 := by
      simpa [threeAxisStencilPoint] using hstencil.firstSecond (thirdOffset := 0) (by omega)
    have hraw := norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_two_one_le
      hlower hbound 0 1 (by decide) frequency component coordinate input htwo
    simpa [dyadicHodgeComplementaryFaceBound, threeAxisMixedForwardDifference,
      mixedForwardDifference] using
        hraw.trans (hodgeJacobianEntryMixedOneTwoEnvelope_dyadic_le scale hscale)
  · have htwo : TwoAxisStencilControlled
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale)
        0 1 frequency 2 0 := by
      simpa [threeAxisStencilPoint] using hstencil.firstSecond (thirdOffset := 0) (by omega)
    have hraw := norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_two_zero_le
      hlower hbound 0 1 frequency component coordinate input htwo
    simpa [dyadicHodgeComplementaryFaceBound, threeAxisMixedForwardDifference,
      mixedForwardDifference] using
        hraw.trans (hodgeJacobianEntrySecondEnvelope_dyadic_le scale hscale)
  · have htwo : TwoAxisStencilControlled
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale)
        0 1 frequency 1 2 := by
      simpa [threeAxisStencilPoint] using hstencil.firstSecond (thirdOffset := 0) (by omega)
    have hraw := norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_one_two_le
      hlower hbound 0 1 (by decide) frequency component coordinate input htwo
    simpa [dyadicHodgeComplementaryFaceBound, threeAxisMixedForwardDifference,
      mixedForwardDifference] using
        hraw.trans (hodgeJacobianEntryMixedOneTwoEnvelope_dyadic_le scale hscale)
  · have htwo : TwoAxisStencilControlled
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale)
        0 1 frequency 1 1 := by
      simpa [threeAxisStencilPoint] using hstencil.firstSecond (thirdOffset := 0) (by omega)
    have hraw := norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_one_one_le
      hlower hbound 0 1 (by decide) frequency component coordinate input htwo
    simpa [dyadicHodgeComplementaryFaceBound, threeAxisMixedForwardDifference,
      mixedForwardDifference] using
        hraw.trans (hodgeJacobianEntryMixedOneOneEnvelope_dyadic_le scale hscale)
  · have htwo : TwoAxisStencilControlled
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale)
        0 1 frequency 1 0 := by
      simpa [threeAxisStencilPoint] using hstencil.firstSecond (thirdOffset := 0) (by omega)
    have hraw := norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_one_zero_le
      hlower hbound 0 1 frequency component coordinate input htwo
    simpa [dyadicHodgeComplementaryFaceBound, threeAxisMixedForwardDifference,
      mixedForwardDifference] using
        hraw.trans (hodgeJacobianEntryFirstEnvelope_dyadic_le scale hscale)
  · have htwo : TwoAxisStencilControlled
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale)
        0 1 frequency 0 2 := by
      simpa [threeAxisStencilPoint] using hstencil.firstSecond (thirdOffset := 0) (by omega)
    have hraw := norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_zero_two_le
      hlower hbound 0 1 frequency component coordinate input htwo
    simpa [dyadicHodgeComplementaryFaceBound, threeAxisMixedForwardDifference,
      mixedForwardDifference] using
        hraw.trans (hodgeJacobianEntrySecondEnvelope_dyadic_le scale hscale)
  · have htwo : TwoAxisStencilControlled
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale)
        0 1 frequency 0 1 := by
      simpa [threeAxisStencilPoint] using hstencil.firstSecond (thirdOffset := 0) (by omega)
    have hraw := norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_zero_one_le
      hlower hbound 0 1 frequency component coordinate input htwo
    simpa [dyadicHodgeComplementaryFaceBound, threeAxisMixedForwardDifference,
      mixedForwardDifference] using
        hraw.trans (hodgeJacobianEntryFirstEnvelope_dyadic_le scale hscale)
  · simpa [dyadicHodgeComplementaryFaceBound, threeAxisMixedForwardDifference,
      mixedForwardDifference, threeAxisStencilPoint] using
        norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_zero_zero_le_one
          0 1 frequency component coordinate input

/-- Pointwise control of every natural product face in the scalar-third-order-two slab. -/
theorem norm_dyadicHodgeThreeAxisSubsetProductFace_third_two_le
    (scale firstOrder secondOrder : ℕ)
    (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) (hscale : 3 ≤ scale)
    (hfirstOrder : firstOrder ≤ 2) (hsecondOrder : secondOrder ≤ 2)
    (hfirstIndex : firstIndex < dyadicHodgeApertureCount scale + firstOrder)
    (hsecondIndex : secondIndex < dyadicHodgeApertureCount scale + secondOrder)
    (hthirdIndex : thirdIndex < dyadicHodgeApertureCount scale + 2) :
    ‖dyadicHodgeThreeAxisSubsetProductFace scale firstOrder secondOrder 2
        component coordinate input firstIndex secondIndex thirdIndex‖ ≤
      ‖dyadicTensorBandThreeAxisVariation scale firstOrder secondOrder 2
        firstIndex secondIndex thirdIndex‖ *
        dyadicHodgeComplementaryFaceBound scale firstOrder secondOrder := by
  let frequency := dyadicHodgeThreeAxisSubsetPaddedFrequency scale
    firstOrder secondOrder 2 firstIndex secondIndex thirdIndex
  have hscalar :=
    threeAxisMixedForwardDifference_directDyadicScalarCoefficient_subsetPadded_eq
      scale firstOrder secondOrder 2 firstIndex secondIndex thirdIndex
      hfirstOrder hsecondOrder (by omega) hfirstIndex hsecondIndex hthirdIndex
  change ‖threeAxisMixedForwardDifference 0 1 2 firstOrder secondOrder 2
      (directDyadicScalarCoefficient scale) frequency *
    threeAxisMixedForwardDifference 0 1 2 (2 - firstOrder) (2 - secondOrder) 0
      (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
      (threeAxisStencilPoint 0 1 2 frequency firstOrder secondOrder 2)‖ ≤ _
  change threeAxisMixedForwardDifference 0 1 2 firstOrder secondOrder 2
      (directDyadicScalarCoefficient scale) frequency = _ at hscalar
  rw [hscalar, norm_mul]
  by_cases hzero : dyadicTensorBandThreeAxisVariation scale firstOrder secondOrder 2
      firstIndex secondIndex thirdIndex = 0
  · simp [hzero]
  · have hglobal : threeAxisMixedForwardDifference 0 1 2 firstOrder secondOrder 2
        (directDyadicScalarCoefficient scale) frequency ≠ 0 := by
      rw [hscalar]
      exact hzero
    have hstencil : ThreeAxisStencilControlled
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale)
        0 1 2 (threeAxisStencilPoint 0 1 2 frequency firstOrder secondOrder 2)
        (2 - firstOrder) (2 - secondOrder) 0 := by
      simpa [dyadicHodgeControlledLower, dyadicHodgeControlledBound] using
        (directDyadicScalar_threeAxis_support_controls_complementaryHodgeStencil
          scale firstOrder secondOrder 2
          (dyadicHodgeInnerCutoff_ge_three_of_scale_ge_three scale hscale)
          hfirstOrder hsecondOrder (by omega) frequency hglobal)
    gcongr
    exact norm_complementaryHodge_firstSecond_of_threeAxisStencil_le
      scale firstOrder secondOrder component coordinate input
      (threeAxisStencilPoint 0 1 2 frequency firstOrder secondOrder 2)
      hscale hfirstOrder hsecondOrder hstencil

/-- Natural unweighted mass of one face in the third-order-two slab. -/
def dyadicHodgeThreeAxisThirdTwoSubsetProductFaceMass
    (scale firstOrder secondOrder : ℕ)
    (component coordinate input : Fin 3) : ℝ :=
  ∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + firstOrder),
    ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + secondOrder),
      ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ‖dyadicHodgeThreeAxisSubsetProductFace scale firstOrder secondOrder 2
          component coordinate input firstIndex secondIndex thirdIndex‖

/-- Exact Fubini/Hodge majorant for every one of the nine faces. -/
theorem dyadicHodgeThreeAxisThirdTwoSubsetProductFaceMass_le_envelopes
    (scale firstOrder secondOrder : ℕ)
    (component coordinate input : Fin 3) (hscale : 3 ≤ scale)
    (hfirstOrder : firstOrder ≤ 2) (hsecondOrder : secondOrder ≤ 2) :
    dyadicHodgeThreeAxisThirdTwoSubsetProductFaceMass scale firstOrder secondOrder
        component coordinate input ≤
      (nextProfileVariationEnvelope scale firstOrder *
          nextProfileVariationEnvelope scale secondOrder *
          nextProfileVariationEnvelope scale 2 +
        baseProfileVariationEnvelope scale firstOrder *
          baseProfileVariationEnvelope scale secondOrder *
          baseProfileVariationEnvelope scale 2) *
        dyadicHodgeComplementaryFaceBound scale firstOrder secondOrder := by
  unfold dyadicHodgeThreeAxisThirdTwoSubsetProductFaceMass
  calc
    _ ≤ ∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + firstOrder),
        ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + secondOrder),
          ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
            ‖dyadicTensorBandThreeAxisVariation scale firstOrder secondOrder 2
              firstIndex secondIndex thirdIndex‖ *
              dyadicHodgeComplementaryFaceBound scale firstOrder secondOrder := by
      gcongr with firstIndex hfirst secondIndex hsecond thirdIndex hthird
      exact norm_dyadicHodgeThreeAxisSubsetProductFace_third_two_le
        scale firstOrder secondOrder component coordinate input
        firstIndex secondIndex thirdIndex hscale hfirstOrder hsecondOrder
        (Finset.mem_range.mp hfirst) (Finset.mem_range.mp hsecond)
        (Finset.mem_range.mp hthird)
    _ = (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + firstOrder),
        ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + secondOrder),
          ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
            ‖dyadicTensorBandThreeAxisVariation scale firstOrder secondOrder 2
              firstIndex secondIndex thirdIndex‖) *
          dyadicHodgeComplementaryFaceBound scale firstOrder secondOrder := by
      simp only [Finset.sum_mul]
    _ ≤ (nextProfileVariationEnvelope scale firstOrder *
          nextProfileVariationEnvelope scale secondOrder *
          nextProfileVariationEnvelope scale 2 +
        baseProfileVariationEnvelope scale firstOrder *
          baseProfileVariationEnvelope scale secondOrder *
          baseProfileVariationEnvelope scale 2) *
          dyadicHodgeComplementaryFaceBound scale firstOrder secondOrder := by
      apply mul_le_mul_of_nonneg_right
      · exact sum_norm_dyadicTensorBandThreeAxisVariation_le_envelopes
          scale firstOrder secondOrder 2
      · interval_cases firstOrder <;> interval_cases secondOrder <;>
          simp [dyadicHodgeComplementaryFaceBound] <;> positivity

/-- Exact inverse-cubic numerator for each unweighted face, ordered lexicographically by the two
scalar allocation orders. -/
def dyadicHodgeThirdTwoFaceRadialConstant
    (firstOrder secondOrder : ℕ) : ℝ :=
  match firstOrder, secondOrder with
  | 0, 0 => 12288000000000
  | 0, 1 => 31872000000
  | 0, 2 => 208000000
  | 1, 0 => 31872000000
  | 1, 1 => 115200000
  | 1, 2 => 1120000
  | 2, 0 => 208000000
  | 2, 1 => 1120000
  | 2, 2 => 72
  | _, _ => 0

/-- Every envelope product in the slab has the same inverse-cubic radial scale. -/
theorem dyadicHodgeThreeAxisThirdTwoEnvelope_le_radial
    (scale firstOrder secondOrder : ℕ) (hfirstOrder : firstOrder ≤ 2)
    (hsecondOrder : secondOrder ≤ 2) :
    (nextProfileVariationEnvelope scale firstOrder *
          nextProfileVariationEnvelope scale secondOrder *
          nextProfileVariationEnvelope scale 2 +
        baseProfileVariationEnvelope scale firstOrder *
          baseProfileVariationEnvelope scale secondOrder *
          baseProfileVariationEnvelope scale 2) *
        dyadicHodgeComplementaryFaceBound scale firstOrder secondOrder ≤
      dyadicHodgeThirdTwoFaceRadialConstant firstOrder secondOrder /
        (dyadicRadius scale : ℝ) ^ 3 := by
  have hradius : 0 < (dyadicRadius scale : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  interval_cases firstOrder <;> interval_cases secondOrder <;>
    simp only [nextProfileVariationEnvelope, baseProfileVariationEnvelope,
      dyadicHodgeComplementaryFaceBound, dyadicHodgeThirdTwoFaceRadialConstant] <;>
    field_simp [hradius.ne'] <;>
    norm_num

/-- Uniform inverse-cubic bound for all nine unweighted natural product faces. -/
theorem dyadicHodgeThreeAxisThirdTwoSubsetProductFaceMass_le_radial
    (scale firstOrder secondOrder : ℕ)
    (component coordinate input : Fin 3) (hscale : 3 ≤ scale)
    (hfirstOrder : firstOrder ≤ 2) (hsecondOrder : secondOrder ≤ 2) :
    dyadicHodgeThreeAxisThirdTwoSubsetProductFaceMass scale firstOrder secondOrder
        component coordinate input ≤
      dyadicHodgeThirdTwoFaceRadialConstant firstOrder secondOrder /
        (dyadicRadius scale : ℝ) ^ 3 :=
  (dyadicHodgeThreeAxisThirdTwoSubsetProductFaceMass_le_envelopes
    scale firstOrder secondOrder component coordinate input
      hscale hfirstOrder hsecondOrder).trans
    (dyadicHodgeThreeAxisThirdTwoEnvelope_le_radial
      scale firstOrder secondOrder hfirstOrder hsecondOrder)

/-- The actual allocation face at natural address is its exact binomial weight times the
unweighted subset product face. -/
theorem directDyadicHodgeThreeAxisAllocationFace_third_two_eq_subsetProductFace
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstAllocation secondAllocation : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) :
    directDyadicHodgeThreeAxisAllocationFace scale component coordinate input
        firstAllocation secondAllocation (2 : Fin 3)
        (dyadicHodgeThreeAxisSubsetPaddedFrequency scale
          firstAllocation.val secondAllocation.val 2
          firstIndex secondIndex thirdIndex) =
      ((secondOrderBinomialWeight firstAllocation *
          secondOrderBinomialWeight secondAllocation : ℕ) : ℂ) *
        dyadicHodgeThreeAxisSubsetProductFace scale
          firstAllocation.val secondAllocation.val 2
          component coordinate input firstIndex secondIndex thirdIndex := by
  simp [directDyadicHodgeThreeAxisAllocationFace, threeAxisHodgeAllocationFace,
    dyadicHodgeThreeAxisSubsetProductFace, secondOrderBinomialWeight]
  ring

/-- Natural mass of one actual weighted allocation face in the slab. -/
def directDyadicHodgeThreeAxisThirdTwoAllocationFaceMass
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstAllocation secondAllocation : Fin 3) : ℝ :=
  ∑ firstIndex ∈ Finset.range
      (dyadicHodgeApertureCount scale + firstAllocation.val),
    ∑ secondIndex ∈ Finset.range
        (dyadicHodgeApertureCount scale + secondAllocation.val),
      ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ‖directDyadicHodgeThreeAxisAllocationFace scale component coordinate input
          firstAllocation secondAllocation (2 : Fin 3)
          (dyadicHodgeThreeAxisSubsetPaddedFrequency scale
            firstAllocation.val secondAllocation.val 2
            firstIndex secondIndex thirdIndex)‖

/-- The actual weighted face mass is exactly its retained occurrence multiplicity times the
unweighted product mass. -/
theorem directDyadicHodgeThreeAxisThirdTwoAllocationFaceMass_eq_weighted
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstAllocation secondAllocation : Fin 3) :
    directDyadicHodgeThreeAxisThirdTwoAllocationFaceMass scale component coordinate input
        firstAllocation secondAllocation =
      (secondOrderBinomialWeight firstAllocation *
          secondOrderBinomialWeight secondAllocation : ℕ) *
        dyadicHodgeThreeAxisThirdTwoSubsetProductFaceMass scale
          firstAllocation.val secondAllocation.val component coordinate input := by
  simp only [directDyadicHodgeThreeAxisThirdTwoAllocationFaceMass,
    dyadicHodgeThreeAxisThirdTwoSubsetProductFaceMass,
    directDyadicHodgeThreeAxisAllocationFace_third_two_eq_subsetProductFace,
    norm_mul, Complex.norm_natCast, Finset.mul_sum]

/-- Uniform inverse-cubic bound for each of the nine actual weighted allocation faces. -/
theorem directDyadicHodgeThreeAxisThirdTwoAllocationFaceMass_le_radial
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstAllocation secondAllocation : Fin 3) (hscale : 3 ≤ scale) :
    directDyadicHodgeThreeAxisThirdTwoAllocationFaceMass scale component coordinate input
        firstAllocation secondAllocation ≤
      (secondOrderBinomialWeight firstAllocation *
          secondOrderBinomialWeight secondAllocation : ℕ) *
        (dyadicHodgeThirdTwoFaceRadialConstant
          firstAllocation.val secondAllocation.val /
            (dyadicRadius scale : ℝ) ^ 3) := by
  rw [directDyadicHodgeThreeAxisThirdTwoAllocationFaceMass_eq_weighted]
  gcongr
  exact dyadicHodgeThreeAxisThirdTwoSubsetProductFaceMass_le_radial
    scale firstAllocation.val secondAllocation.val component coordinate input hscale
      (by omega) (by omega)

/-- The complete scalar-third-order-two slab, with all nine allocation multiplicities retained. -/
def directDyadicHodgeThreeAxisThirdTwoAllocationSlabMass
    (scale : ℕ) (component coordinate input : Fin 3) : ℝ :=
  ∑ firstAllocation : Fin 3, ∑ secondAllocation : Fin 3,
    directDyadicHodgeThreeAxisThirdTwoAllocationFaceMass scale component coordinate input
      firstAllocation secondAllocation

/-- **[proved-derived]** The complete nine-face slab has one exact inverse-cubic envelope.  This
is a uniform scale theorem for an actual population of the 27-face Hodge allocation, rather than
a list of disconnected pointwise estimates. -/
theorem directDyadicHodgeThreeAxisThirdTwoAllocationSlabMass_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    directDyadicHodgeThreeAxisThirdTwoAllocationSlabMass scale component coordinate input ≤
      12416369280072 / (dyadicRadius scale : ℝ) ^ 3 := by
  unfold directDyadicHodgeThreeAxisThirdTwoAllocationSlabMass
  calc
    _ ≤ ∑ firstAllocation : Fin 3, ∑ secondAllocation : Fin 3,
        (secondOrderBinomialWeight firstAllocation *
            secondOrderBinomialWeight secondAllocation : ℕ) *
          (dyadicHodgeThirdTwoFaceRadialConstant
              firstAllocation.val secondAllocation.val /
            (dyadicRadius scale : ℝ) ^ 3) := by
      gcongr with firstAllocation _ secondAllocation _
      exact directDyadicHodgeThreeAxisThirdTwoAllocationFaceMass_le_radial
        scale component coordinate input firstAllocation secondAllocation hscale
    _ = 12416369280072 / (dyadicRadius scale : ℝ) ^ 3 := by
      simp [Fin.sum_univ_succ, secondOrderBinomialWeight,
        dyadicHodgeThirdTwoFaceRadialConstant]
      ring

section Audit

#print axioms norm_complementaryHodge_firstSecond_of_threeAxisStencil_le
#print axioms norm_dyadicHodgeThreeAxisSubsetProductFace_third_two_le
#print axioms dyadicHodgeThreeAxisThirdTwoSubsetProductFaceMass_le_envelopes
#print axioms dyadicHodgeThreeAxisThirdTwoEnvelope_le_radial
#print axioms dyadicHodgeThreeAxisThirdTwoSubsetProductFaceMass_le_radial
#print axioms directDyadicHodgeThreeAxisThirdTwoAllocationFaceMass_eq_weighted
#print axioms directDyadicHodgeThreeAxisThirdTwoAllocationFaceMass_le_radial
#print axioms directDyadicHodgeThreeAxisThirdTwoAllocationSlabMass_le

end Audit

end Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisThirdTwoSlice
