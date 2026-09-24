import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeEnvelopeScaling

/-!
# Complementary Hodge faces for the dyadic product rule

**[proved-derived]** Each nonzero scalar subset face controls the complementary rational Hodge
face at the exact shifted address used by the `2 × 2` Leibniz rule.  These are the nine pointwise
inputs whose scalar masses all produce an inverse-radius product mass.
-/

noncomputable section

namespace Soma.Holonics.Millennium.NavierStokesDyadicHodgeProductFaces

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesSmoothHodgeJacobianBand
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeHigherMixedVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeLowerMixedVariation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeSupportStencil
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeEnvelopeScaling

theorem dyadicHodgeInnerCutoff_ge_three_of_scale_ge_three
    (scale : ℕ) (hscale : 3 ≤ scale) :
    3 ≤ dyadicHodgeInnerCutoff scale := by
  unfold dyadicHodgeInnerCutoff
  have h := dyadicRadius_ge_eight_of_three_le scale hscale
  omega

theorem complementaryHodgeStencil_of_scalar_face_ne_zero
    (scale : ℕ) (hscale : 3 ≤ scale)
    (first second : Fin 3) (haxes : first ≠ second)
    (firstOrder secondOrder : ℕ)
    (hfirstOrder : firstOrder ≤ 2) (hsecondOrder : secondOrder ≤ 2)
    (frequency : SpatialFrequency)
    (hnonzero : mixedForwardDifference first second firstOrder secondOrder
      (directDyadicScalarCoefficient scale) frequency ≠ 0) :
    TwoAxisStencilControlled
      (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale)
      first second
      (twoAxisStencilPoint first second frequency firstOrder secondOrder)
      (2 - firstOrder) (2 - secondOrder) := by
  simpa [dyadicHodgeControlledLower, dyadicHodgeControlledBound] using
    directDyadicScalar_support_controls_complementaryHodgeStencil scale
      (dyadicHodgeInnerCutoff_ge_three_of_scale_ge_three scale hscale)
      first second haxes firstOrder secondOrder hfirstOrder hsecondOrder
      frequency hnonzero

theorem norm_complementaryHodge_two_two_le_of_scalar_zero_zero_ne_zero
    (scale : ℕ) (hscale : 3 ≤ scale)
    (first second : Fin 3) (haxes : first ≠ second)
    (frequency : SpatialFrequency) (component coordinate input : Fin 3)
    (hnonzero : mixedForwardDifference first second 0 0
      (directDyadicScalarCoefficient scale) frequency ≠ 0) :
    ‖mixedForwardDifference first second 2 2
      (fun current ↦ hodgeJacobianMultiplierEntry current
        component coordinate input) frequency‖ ≤
      32000000000 / (dyadicRadius scale : ℝ) ^ 4 := by
  have hstencil := complementaryHodgeStencil_of_scalar_face_ne_zero
    scale hscale first second haxes 0 0 (by omega) (by omega) frequency hnonzero
  have hraw := norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_two_two_le
    (lower := dyadicHodgeControlledLower scale)
    (bound := dyadicHodgeControlledBound scale)
    (dyadicHodgeControlledLower_pos scale hscale)
    (by unfold dyadicHodgeControlledBound; positivity)
    first second haxes frequency component coordinate input
    (by simpa [twoAxisStencilPoint] using hstencil)
  exact hraw.trans (hodgeJacobianEntryMixedTwoTwoEnvelope_dyadic_le scale hscale)

theorem norm_complementaryHodge_two_one_le_of_scalar_zero_one_ne_zero
    (scale : ℕ) (hscale : 3 ≤ scale)
    (first second : Fin 3) (haxes : first ≠ second)
    (frequency : SpatialFrequency) (component coordinate input : Fin 3)
    (hnonzero : mixedForwardDifference first second 0 1
      (directDyadicScalarCoefficient scale) frequency ≠ 0) :
    ‖mixedForwardDifference first second 2 1
      (fun current ↦ hodgeJacobianMultiplierEntry current
        component coordinate input)
      (twoAxisStencilPoint first second frequency 0 1)‖ ≤
      166000000 / (dyadicRadius scale : ℝ) ^ 3 := by
  have hstencil := complementaryHodgeStencil_of_scalar_face_ne_zero
    scale hscale first second haxes 0 1 (by omega) (by omega) frequency hnonzero
  have hraw := norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_two_one_le
    (dyadicHodgeControlledLower_pos scale hscale)
    (by unfold dyadicHodgeControlledBound; positivity)
    first second haxes (twoAxisStencilPoint first second frequency 0 1)
      component coordinate input hstencil
  exact hraw.trans (hodgeJacobianEntryMixedOneTwoEnvelope_dyadic_le scale hscale)

theorem norm_complementaryHodge_two_zero_le_of_scalar_zero_two_ne_zero
    (scale : ℕ) (hscale : 3 ≤ scale)
    (first second : Fin 3) (haxes : first ≠ second)
    (frequency : SpatialFrequency) (component coordinate input : Fin 3)
    (hnonzero : mixedForwardDifference first second 0 2
      (directDyadicScalarCoefficient scale) frequency ≠ 0) :
    ‖mixedForwardDifference first second 2 0
      (fun current ↦ hodgeJacobianMultiplierEntry current
        component coordinate input)
      (twoAxisStencilPoint first second frequency 0 2)‖ ≤
      1300000 / (dyadicRadius scale : ℝ) ^ 2 := by
  have hstencil := complementaryHodgeStencil_of_scalar_face_ne_zero
    scale hscale first second haxes 0 2 (by omega) (by omega) frequency hnonzero
  have hraw := norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_two_zero_le
    (dyadicHodgeControlledLower_pos scale hscale)
    (by unfold dyadicHodgeControlledBound; positivity)
    first second (twoAxisStencilPoint first second frequency 0 2)
      component coordinate input hstencil
  exact hraw.trans (hodgeJacobianEntrySecondEnvelope_dyadic_le scale hscale)

theorem norm_complementaryHodge_one_two_le_of_scalar_one_zero_ne_zero
    (scale : ℕ) (hscale : 3 ≤ scale)
    (first second : Fin 3) (haxes : first ≠ second)
    (frequency : SpatialFrequency) (component coordinate input : Fin 3)
    (hnonzero : mixedForwardDifference first second 1 0
      (directDyadicScalarCoefficient scale) frequency ≠ 0) :
    ‖mixedForwardDifference first second 1 2
      (fun current ↦ hodgeJacobianMultiplierEntry current
        component coordinate input)
      (twoAxisStencilPoint first second frequency 1 0)‖ ≤
      166000000 / (dyadicRadius scale : ℝ) ^ 3 := by
  have hstencil := complementaryHodgeStencil_of_scalar_face_ne_zero
    scale hscale first second haxes 1 0 (by omega) (by omega) frequency hnonzero
  have hraw := norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_one_two_le
    (dyadicHodgeControlledLower_pos scale hscale)
    (by unfold dyadicHodgeControlledBound; positivity)
    first second haxes (twoAxisStencilPoint first second frequency 1 0)
      component coordinate input hstencil
  exact hraw.trans (hodgeJacobianEntryMixedOneTwoEnvelope_dyadic_le scale hscale)

theorem norm_complementaryHodge_one_one_le_of_scalar_one_one_ne_zero
    (scale : ℕ) (hscale : 3 ≤ scale)
    (first second : Fin 3) (haxes : first ≠ second)
    (frequency : SpatialFrequency) (component coordinate input : Fin 3)
    (hnonzero : mixedForwardDifference first second 1 1
      (directDyadicScalarCoefficient scale) frequency ≠ 0) :
    ‖mixedForwardDifference first second 1 1
      (fun current ↦ hodgeJacobianMultiplierEntry current
        component coordinate input)
      (twoAxisStencilPoint first second frequency 1 1)‖ ≤
      1200000 / (dyadicRadius scale : ℝ) ^ 2 := by
  have hstencil := complementaryHodgeStencil_of_scalar_face_ne_zero
    scale hscale first second haxes 1 1 (by omega) (by omega) frequency hnonzero
  have hraw := norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_one_one_le
    (dyadicHodgeControlledLower_pos scale hscale)
    (by unfold dyadicHodgeControlledBound; positivity)
    first second haxes (twoAxisStencilPoint first second frequency 1 1)
      component coordinate input hstencil
  exact hraw.trans (hodgeJacobianEntryMixedOneOneEnvelope_dyadic_le scale hscale)

theorem norm_complementaryHodge_one_zero_le_of_scalar_one_two_ne_zero
    (scale : ℕ) (hscale : 3 ≤ scale)
    (first second : Fin 3) (haxes : first ≠ second)
    (frequency : SpatialFrequency) (component coordinate input : Fin 3)
    (hnonzero : mixedForwardDifference first second 1 2
      (directDyadicScalarCoefficient scale) frequency ≠ 0) :
    ‖mixedForwardDifference first second 1 0
      (fun current ↦ hodgeJacobianMultiplierEntry current
        component coordinate input)
      (twoAxisStencilPoint first second frequency 1 2)‖ ≤
      14000 / (dyadicRadius scale : ℝ) := by
  have hstencil := complementaryHodgeStencil_of_scalar_face_ne_zero
    scale hscale first second haxes 1 2 (by omega) (by omega) frequency hnonzero
  have hraw := norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_one_zero_le
    (dyadicHodgeControlledLower_pos scale hscale)
    (by unfold dyadicHodgeControlledBound; positivity)
    first second (twoAxisStencilPoint first second frequency 1 2)
      component coordinate input hstencil
  exact hraw.trans (hodgeJacobianEntryFirstEnvelope_dyadic_le scale hscale)

theorem norm_complementaryHodge_zero_two_le_of_scalar_two_zero_ne_zero
    (scale : ℕ) (hscale : 3 ≤ scale)
    (first second : Fin 3) (haxes : first ≠ second)
    (frequency : SpatialFrequency) (component coordinate input : Fin 3)
    (hnonzero : mixedForwardDifference first second 2 0
      (directDyadicScalarCoefficient scale) frequency ≠ 0) :
    ‖mixedForwardDifference first second 0 2
      (fun current ↦ hodgeJacobianMultiplierEntry current
        component coordinate input)
      (twoAxisStencilPoint first second frequency 2 0)‖ ≤
      1300000 / (dyadicRadius scale : ℝ) ^ 2 := by
  have hstencil := complementaryHodgeStencil_of_scalar_face_ne_zero
    scale hscale first second haxes 2 0 (by omega) (by omega) frequency hnonzero
  have hraw := norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_zero_two_le
    (dyadicHodgeControlledLower_pos scale hscale)
    (by unfold dyadicHodgeControlledBound; positivity)
    first second (twoAxisStencilPoint first second frequency 2 0)
      component coordinate input hstencil
  exact hraw.trans (hodgeJacobianEntrySecondEnvelope_dyadic_le scale hscale)

theorem norm_complementaryHodge_zero_one_le_of_scalar_two_one_ne_zero
    (scale : ℕ) (hscale : 3 ≤ scale)
    (first second : Fin 3) (haxes : first ≠ second)
    (frequency : SpatialFrequency) (component coordinate input : Fin 3)
    (hnonzero : mixedForwardDifference first second 2 1
      (directDyadicScalarCoefficient scale) frequency ≠ 0) :
    ‖mixedForwardDifference first second 0 1
      (fun current ↦ hodgeJacobianMultiplierEntry current
        component coordinate input)
      (twoAxisStencilPoint first second frequency 2 1)‖ ≤
      14000 / (dyadicRadius scale : ℝ) := by
  have hstencil := complementaryHodgeStencil_of_scalar_face_ne_zero
    scale hscale first second haxes 2 1 (by omega) (by omega) frequency hnonzero
  have hraw := norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_zero_one_le
    (dyadicHodgeControlledLower_pos scale hscale)
    (by unfold dyadicHodgeControlledBound; positivity)
    first second (twoAxisStencilPoint first second frequency 2 1)
      component coordinate input hstencil
  exact hraw.trans (hodgeJacobianEntryFirstEnvelope_dyadic_le scale hscale)

theorem norm_complementaryHodge_zero_zero_le_of_scalar_two_two_ne_zero
    (first second : Fin 3)
    (frequency : SpatialFrequency) (component coordinate input : Fin 3) :
    ‖mixedForwardDifference first second 0 0
      (fun current ↦ hodgeJacobianMultiplierEntry current
        component coordinate input)
      (twoAxisStencilPoint first second frequency 2 2)‖ ≤ 1 :=
  norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_zero_zero_le_one
    first second (twoAxisStencilPoint first second frequency 2 2)
      component coordinate input

section Audit

#print axioms norm_complementaryHodge_two_two_le_of_scalar_zero_zero_ne_zero
#print axioms norm_complementaryHodge_one_one_le_of_scalar_one_one_ne_zero
#print axioms norm_complementaryHodge_zero_zero_le_of_scalar_two_two_ne_zero

end Audit

end Soma.Holonics.Millennium.NavierStokesDyadicHodgeProductFaces
