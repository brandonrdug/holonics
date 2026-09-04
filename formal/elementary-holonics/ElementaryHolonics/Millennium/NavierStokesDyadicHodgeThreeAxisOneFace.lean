import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeThreeAxisOtherTwoSlices
import ElementaryHolonics.Millennium.NavierStokesThreeAxisHodgeSubsetEnvelope

/-!
# The central `(1,1,1)` dyadic Hodge allocation face

**[proved-derived]** The scalar and Hodge hands both receive one difference in each coordinate at
the central allocation address.  The scalar chart, complete support stencil, existing pointwise
three-axis `111` Hodge law, and generic weighted face-mass owner compose without a new hypothesis.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisOneFace

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesSmoothHodgeJacobianBand
open Soma.Holonics.Millennium.NavierStokesReciprocalDifferenceRecurrence
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeKernelVariation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeSupportStencil
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeEnvelopeScaling
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeProductFaces
open Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeScaleDescent
open Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeProductMass
open Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeSubsetEnvelope
open Soma.Holonics.Millennium.NavierStokesThreeAxisScalarSubsetVariation
open Soma.Holonics.Millennium.NavierStokesThreeAxisDyadicHodgeSupportStencil
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisAllocation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisScalarChart
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisCornerMass
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisOtherTwoSlices

/-- The actual Hodge hand at the central allocation address has exact inverse-cubic pointwise
control on every scalar-caused stencil. -/
theorem norm_dyadicHodgeThreeAxisSubsetProductFace_one_one_one_le
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) (hscale : 3 ≤ scale)
    (hfirstIndex : firstIndex < dyadicHodgeApertureCount scale + 1)
    (hsecondIndex : secondIndex < dyadicHodgeApertureCount scale + 1)
    (hthirdIndex : thirdIndex < dyadicHodgeApertureCount scale + 1) :
    ‖dyadicHodgeThreeAxisSubsetProductFace scale 1 1 1
        component coordinate input firstIndex secondIndex thirdIndex‖ ≤
      ‖dyadicTensorBandThreeAxisVariation scale 1 1 1
        firstIndex secondIndex thirdIndex‖ *
        ((226 * 10 ^ 6) / (dyadicRadius scale : ℝ) ^ 3) := by
  let frequency := dyadicHodgeThreeAxisSubsetPaddedFrequency scale
    1 1 1 firstIndex secondIndex thirdIndex
  have hscalar :=
    threeAxisMixedForwardDifference_directDyadicScalarCoefficient_subsetPadded_eq
      scale 1 1 1 firstIndex secondIndex thirdIndex
      (by omega) (by omega) (by omega) hfirstIndex hsecondIndex hthirdIndex
  change ‖threeAxisMixedForwardDifference 0 1 2 1 1 1
      (directDyadicScalarCoefficient scale) frequency *
    threeAxisMixedForwardDifference 0 1 2 1 1 1
      (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
      (threeAxisStencilPoint 0 1 2 frequency 1 1 1)‖ ≤ _
  change threeAxisMixedForwardDifference 0 1 2 1 1 1
      (directDyadicScalarCoefficient scale) frequency = _ at hscalar
  rw [hscalar, norm_mul]
  by_cases hzero : dyadicTensorBandThreeAxisVariation scale 1 1 1
      firstIndex secondIndex thirdIndex = 0
  · simp [hzero]
  · have hglobal : threeAxisMixedForwardDifference 0 1 2 1 1 1
        (directDyadicScalarCoefficient scale) frequency ≠ 0 := by
      rw [hscalar]
      exact hzero
    have hstencil : ThreeAxisStencilControlled
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale)
        0 1 2 (threeAxisStencilPoint 0 1 2 frequency 1 1 1) 1 1 1 := by
      simpa [dyadicHodgeControlledLower, dyadicHodgeControlledBound] using
        (directDyadicScalar_threeAxis_support_controls_complementaryHodgeStencil
          scale 1 1 1
          (dyadicHodgeInnerCutoff_ge_three_of_scale_ge_three scale hscale)
          (by omega) (by omega) (by omega) frequency hglobal)
    have hlower := dyadicHodgeControlledLower_pos scale hscale
    have hbound : 0 ≤ dyadicHodgeControlledBound scale := by
      unfold dyadicHodgeControlledBound
      positivity
    gcongr
    exact (norm_hodgeJacobianMultiplierEntry_threeAxisMixedForwardDifference_one_one_one_le
      hlower hbound (threeAxisStencilPoint 0 1 2 frequency 1 1 1)
      component coordinate input hstencil).trans
        (hodgeJacobianEntryThreeAxis111Envelope_dyadic_le scale hscale)

/-- The unweighted central natural face has the exact inverse-cubic numerator `128 * 226e6`. -/
theorem dyadicHodgeThreeAxisNaturalProductFaceMass_one_one_one_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    dyadicHodgeThreeAxisNaturalProductFaceMass scale 1 1 1
        component coordinate input ≤
      28928000000 / (dyadicRadius scale : ℝ) ^ 3 := by
  have hpoint := dyadicHodgeThreeAxisNaturalProductFaceMass_le_envelopes_of_pointwise
    scale 1 1 1 component coordinate input
      ((226 * 10 ^ 6) / (dyadicRadius scale : ℝ) ^ 3)
      (by positivity)
      (fun firstIndex secondIndex thirdIndex hfirstIndex hsecondIndex hthirdIndex ↦
        norm_dyadicHodgeThreeAxisSubsetProductFace_one_one_one_le
          scale component coordinate input firstIndex secondIndex thirdIndex hscale
            hfirstIndex hsecondIndex hthirdIndex)
  calc
    _ ≤ (nextProfileVariationEnvelope scale 1 *
          nextProfileVariationEnvelope scale 1 *
          nextProfileVariationEnvelope scale 1 +
        baseProfileVariationEnvelope scale 1 *
          baseProfileVariationEnvelope scale 1 *
          baseProfileVariationEnvelope scale 1) *
        ((226 * 10 ^ 6) / (dyadicRadius scale : ℝ) ^ 3) := hpoint
    _ = 28928000000 / (dyadicRadius scale : ℝ) ^ 3 := by
      simp [nextProfileVariationEnvelope, baseProfileVariationEnvelope]
      ring

/-- **[proved-derived]** The actual central allocation retains multiplicity eight and has exact
inverse-cubic numerator `8 * 128 * 226e6`. -/
theorem directDyadicHodgeThreeAxisNaturalAllocationFaceMass_one_one_one_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    directDyadicHodgeThreeAxisNaturalAllocationFaceMass scale component coordinate input
        (1 : Fin 3) (1 : Fin 3) (1 : Fin 3) ≤
      231424000000 / (dyadicRadius scale : ℝ) ^ 3 := by
  rw [directDyadicHodgeThreeAxisNaturalAllocationFaceMass_eq_weighted]
  have hface := dyadicHodgeThreeAxisNaturalProductFaceMass_one_one_one_le
    scale component coordinate input hscale
  change 8 * dyadicHodgeThreeAxisNaturalProductFaceMass scale 1 1 1
      component coordinate input ≤ _
  calc
    _ ≤ 8 * (28928000000 / (dyadicRadius scale : ℝ) ^ 3) := by gcongr
    _ = 231424000000 / (dyadicRadius scale : ℝ) ^ 3 := by ring

section Audit

#print axioms norm_dyadicHodgeThreeAxisSubsetProductFace_one_one_one_le
#print axioms dyadicHodgeThreeAxisNaturalProductFaceMass_one_one_one_le
#print axioms directDyadicHodgeThreeAxisNaturalAllocationFaceMass_one_one_one_le

end Audit

end Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisOneFace
