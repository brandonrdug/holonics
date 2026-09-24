import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeThreeAxisScalarChart
import ElementaryHolonics.Millennium.NavierStokesThreeAxisDyadicHodgeSupportStencil
import ElementaryHolonics.Millennium.NavierStokesThreeAxisHodgeDyadicMass

/-!
# The zero-scalar / full-Hodge corner of the three-axis allocation

**[proved-derived]** This owner bounds the first source-specific face of the actual twenty-seven
face dyadic Hodge allocation.  The `(0,0,0)` scalar allocation leaves all six differences on the
Hodge multiplier.  Its nonzero scalar value therefore supplies the complete controlled Hodge
stencil, while its scalar population is the undifferentiated three-axis tensor-band mass.

The global doubly padded chart is reindexed exactly into the natural coefficient cube before the
bound is assembled.  No mode-count estimate and no arbitrary constant enlargement enters the
passage.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisCornerMass

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesSmoothHodgeJacobianBand
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeCoefficientVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeHigherMixedVariation
open Soma.Holonics.Millennium.NavierStokesReciprocalDifferenceRecurrence
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeKernelVariation
open Soma.Holonics.Millennium.NavierStokesDyadicTensorBandVariation
open Soma.Holonics.Millennium.NavierStokesDyadicTensorBandSubsetVariation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeSupportStencil
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeProductFaces
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeTwoAxisMass
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeEnvelopeScaling
open Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeScaleDescent
open Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeProductMass
open Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeDyadicMass
open Soma.Holonics.Millennium.NavierStokesThreeAxisScalarSubsetVariation
open Soma.Holonics.Millennium.NavierStokesThreeAxisDyadicHodgeSupportStencil
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisAllocation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisScalarChart

/-- The unweighted product face in the global doubly padded chart. -/
def dyadicHodgeThreeAxisGlobalProductFace
    (scale firstOrder secondOrder thirdOrder : ℕ)
    (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  let frequency := dyadicHodgeThreeAxisBackwardPaddedFrequency scale
    firstIndex secondIndex thirdIndex
  threeAxisMixedForwardDifference 0 1 2 firstOrder secondOrder thirdOrder
      (directDyadicScalarCoefficient scale) frequency *
    threeAxisMixedForwardDifference 0 1 2
      (2 - firstOrder) (2 - secondOrder) (2 - thirdOrder)
      (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
      (threeAxisStencilPoint 0 1 2 frequency firstOrder secondOrder thirdOrder)

/-- The same product face after its three exact left residues have been removed. -/
def dyadicHodgeThreeAxisSubsetProductFace
    (scale firstOrder secondOrder thirdOrder : ℕ)
    (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  let frequency := dyadicHodgeThreeAxisSubsetPaddedFrequency scale
    firstOrder secondOrder thirdOrder firstIndex secondIndex thirdIndex
  threeAxisMixedForwardDifference 0 1 2 firstOrder secondOrder thirdOrder
      (directDyadicScalarCoefficient scale) frequency *
    threeAxisMixedForwardDifference 0 1 2
      (2 - firstOrder) (2 - secondOrder) (2 - thirdOrder)
      (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
      (threeAxisStencilPoint 0 1 2 frequency firstOrder secondOrder thirdOrder)

/-- Adding each complementary offset identifies the global and natural product charts exactly. -/
theorem dyadicHodgeThreeAxisGlobalProductFace_add_offsets_eq_subset
    (scale firstOrder secondOrder thirdOrder : ℕ)
    (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) :
    dyadicHodgeThreeAxisGlobalProductFace scale firstOrder secondOrder thirdOrder
        component coordinate input
        (firstIndex + (2 - firstOrder))
        (secondIndex + (2 - secondOrder))
        (thirdIndex + (2 - thirdOrder)) =
      dyadicHodgeThreeAxisSubsetProductFace scale firstOrder secondOrder thirdOrder
        component coordinate input firstIndex secondIndex thirdIndex := by
  rfl

/-- At scalar order zero, the natural padded address is the actual finite aperture address. -/
theorem dyadicHodgeThreeAxisSubsetPaddedFrequency_zero_zero_zero_eq
    (scale firstIndex secondIndex thirdIndex : ℕ) :
    dyadicHodgeThreeAxisSubsetPaddedFrequency scale 0 0 0
        firstIndex secondIndex thirdIndex =
      dyadicHodgeApertureFrequency scale firstIndex secondIndex thirdIndex := by
  funext axis
  fin_cases axis <;>
    simp [dyadicHodgeThreeAxisSubsetPaddedFrequency,
      dyadicHodgeThreeAxisBackwardPaddedFrequency,
      dyadicHodgeApertureFrequency, centeredFrequency] <;>
    omega

/-- The natural scalar corner is exactly the undifferentiated three-axis tensor-band face. -/
theorem directDyadicScalarCoefficient_threeAxisSubsetPadded_zero_zero_zero_eq
    (scale firstIndex secondIndex thirdIndex : ℕ) :
    directDyadicScalarCoefficient scale
        (dyadicHodgeThreeAxisSubsetPaddedFrequency scale 0 0 0
          firstIndex secondIndex thirdIndex) =
      dyadicTensorBandThreeAxisVariation scale 0 0 0
        firstIndex secondIndex thirdIndex := by
  rw [dyadicHodgeThreeAxisSubsetPaddedFrequency_zero_zero_zero_eq]
  unfold directDyadicScalarCoefficient dyadicTensorBandThreeAxisVariation
    separatedDyadicProfileThreeAxisVariation
  rw [← dyadicTensorBandCubeCoefficient_eq_actual]
  rfl

/-- The first left residue of the scalar corner vanishes in the global chart. -/
theorem directDyadicScalarCoefficient_threeAxisBackwardPadded_eq_zero_of_first_lt_two
    (scale firstIndex secondIndex thirdIndex : ℕ) (hfirst : firstIndex < 2) :
    directDyadicScalarCoefficient scale
      (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
        firstIndex secondIndex thirdIndex) = 0 := by
  have houtside :
      dyadicHodgeThreeAxisBackwardPaddedFrequency scale
          firstIndex secondIndex thirdIndex ∉
        frequencyCube (dyadicHodgeOuterCutoff (scale + 1)) := by
    intro hmem
    have hcoordinate :=
      (mem_frequencyCube_iff (dyadicHodgeOuterCutoff (scale + 1)) _).mp hmem 0
    simp [dyadicHodgeThreeAxisBackwardPaddedFrequency,
      dyadicHodgeApertureRadius] at hcoordinate
    omega
  unfold directDyadicScalarCoefficient
  rw [dyadicHodgeBandWeight_eq_zero_of_not_mem_outer scale houtside]
  simp

/-- The second left residue of the scalar corner vanishes in the global chart. -/
theorem directDyadicScalarCoefficient_threeAxisBackwardPadded_eq_zero_of_second_lt_two
    (scale firstIndex secondIndex thirdIndex : ℕ) (hsecond : secondIndex < 2) :
    directDyadicScalarCoefficient scale
      (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
        firstIndex secondIndex thirdIndex) = 0 := by
  have houtside :
      dyadicHodgeThreeAxisBackwardPaddedFrequency scale
          firstIndex secondIndex thirdIndex ∉
        frequencyCube (dyadicHodgeOuterCutoff (scale + 1)) := by
    intro hmem
    have hcoordinate :=
      (mem_frequencyCube_iff (dyadicHodgeOuterCutoff (scale + 1)) _).mp hmem 1
    simp [dyadicHodgeThreeAxisBackwardPaddedFrequency,
      dyadicHodgeApertureRadius] at hcoordinate
    omega
  unfold directDyadicScalarCoefficient
  rw [dyadicHodgeBandWeight_eq_zero_of_not_mem_outer scale houtside]
  simp

/-- The third left residue of the scalar corner vanishes in the global chart. -/
theorem directDyadicScalarCoefficient_threeAxisBackwardPadded_eq_zero_of_third_lt_two
    (scale firstIndex secondIndex thirdIndex : ℕ) (hthird : thirdIndex < 2) :
    directDyadicScalarCoefficient scale
      (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
        firstIndex secondIndex thirdIndex) = 0 := by
  have houtside :
      dyadicHodgeThreeAxisBackwardPaddedFrequency scale
          firstIndex secondIndex thirdIndex ∉
        frequencyCube (dyadicHodgeOuterCutoff (scale + 1)) := by
    intro hmem
    have hcoordinate :=
      (mem_frequencyCube_iff (dyadicHodgeOuterCutoff (scale + 1)) _).mp hmem 2
    simp [dyadicHodgeThreeAxisBackwardPaddedFrequency,
      dyadicHodgeApertureRadius] at hcoordinate
    omega
  unfold directDyadicScalarCoefficient
  rw [dyadicHodgeBandWeight_eq_zero_of_not_mem_outer scale houtside]
  simp

/-- Exact finite translation of three nested populations after retaining every prefix residue. -/
theorem sum_range_threeAxis_shift_of_prefix_zero
    {α : Type*} [AddCommMonoid α]
    (firstOffset secondOffset thirdOffset firstCount secondCount thirdCount : ℕ)
    (global subset : ℕ → ℕ → ℕ → α)
    (hfirst : ∀ firstIndex < firstOffset,
      ∀ secondIndex < secondOffset + secondCount,
        ∀ thirdIndex < thirdOffset + thirdCount,
          global firstIndex secondIndex thirdIndex = 0)
    (hsecond : ∀ firstIndex < firstCount,
      ∀ secondIndex < secondOffset,
        ∀ thirdIndex < thirdOffset + thirdCount,
          global (firstOffset + firstIndex) secondIndex thirdIndex = 0)
    (hthird : ∀ firstIndex < firstCount,
      ∀ secondIndex < secondCount,
        ∀ thirdIndex < thirdOffset,
          global (firstOffset + firstIndex) (secondOffset + secondIndex) thirdIndex = 0)
    (hshift : ∀ firstIndex < firstCount,
      ∀ secondIndex < secondCount,
        ∀ thirdIndex < thirdCount,
          global (firstOffset + firstIndex) (secondOffset + secondIndex)
              (thirdOffset + thirdIndex) =
            subset firstIndex secondIndex thirdIndex) :
    (∑ firstIndex ∈ Finset.range (firstOffset + firstCount),
      ∑ secondIndex ∈ Finset.range (secondOffset + secondCount),
        ∑ thirdIndex ∈ Finset.range (thirdOffset + thirdCount),
          global firstIndex secondIndex thirdIndex) =
      ∑ firstIndex ∈ Finset.range firstCount,
        ∑ secondIndex ∈ Finset.range secondCount,
          ∑ thirdIndex ∈ Finset.range thirdCount,
            subset firstIndex secondIndex thirdIndex := by
  rw [Finset.sum_range_add]
  have hleft :
      (∑ firstIndex ∈ Finset.range firstOffset,
        ∑ secondIndex ∈ Finset.range (secondOffset + secondCount),
          ∑ thirdIndex ∈ Finset.range (thirdOffset + thirdCount),
            global firstIndex secondIndex thirdIndex) = 0 := by
    apply Finset.sum_eq_zero
    intro firstIndex hfirstIndex
    apply Finset.sum_eq_zero
    intro secondIndex hsecondIndex
    apply Finset.sum_eq_zero
    intro thirdIndex hthirdIndex
    exact hfirst firstIndex (Finset.mem_range.mp hfirstIndex)
      secondIndex (Finset.mem_range.mp hsecondIndex)
      thirdIndex (Finset.mem_range.mp hthirdIndex)
  rw [hleft, zero_add]
  apply Finset.sum_congr rfl
  intro firstIndex hfirstIndex
  rw [Finset.sum_range_add]
  have hbottom :
      (∑ secondIndex ∈ Finset.range secondOffset,
        ∑ thirdIndex ∈ Finset.range (thirdOffset + thirdCount),
          global (firstOffset + firstIndex) secondIndex thirdIndex) = 0 := by
    apply Finset.sum_eq_zero
    intro secondIndex hsecondIndex
    apply Finset.sum_eq_zero
    intro thirdIndex hthirdIndex
    exact hsecond firstIndex (Finset.mem_range.mp hfirstIndex)
      secondIndex (Finset.mem_range.mp hsecondIndex)
      thirdIndex (Finset.mem_range.mp hthirdIndex)
  rw [hbottom, zero_add]
  apply Finset.sum_congr rfl
  intro secondIndex hsecondIndex
  rw [Finset.sum_range_add]
  have hback :
      (∑ thirdIndex ∈ Finset.range thirdOffset,
        global (firstOffset + firstIndex) (secondOffset + secondIndex) thirdIndex) = 0 := by
    apply Finset.sum_eq_zero
    intro thirdIndex hthirdIndex
    exact hthird firstIndex (Finset.mem_range.mp hfirstIndex)
      secondIndex (Finset.mem_range.mp hsecondIndex)
      thirdIndex (Finset.mem_range.mp hthirdIndex)
  rw [hback, zero_add]
  apply Finset.sum_congr rfl
  intro thirdIndex hthirdIndex
  exact hshift firstIndex (Finset.mem_range.mp hfirstIndex)
    secondIndex (Finset.mem_range.mp hsecondIndex)
    thirdIndex (Finset.mem_range.mp hthirdIndex)

/-- Natural mass of the zero-scalar / full-Hodge corner face. -/
def dyadicHodgeThreeAxisCornerSubsetMass
    (scale : ℕ) (component coordinate input : Fin 3) : ℝ :=
  ∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
    ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
      ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
        ‖dyadicHodgeThreeAxisSubsetProductFace scale 0 0 0
          component coordinate input firstIndex secondIndex thirdIndex‖

/-- Global mass of the same corner inside the actual doubly padded allocation chart. -/
def dyadicHodgeThreeAxisCornerGlobalMass
    (scale : ℕ) (component coordinate input : Fin 3) : ℝ :=
  ∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
    ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
      ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ‖dyadicHodgeThreeAxisGlobalProductFace scale 0 0 0
          component coordinate input firstIndex secondIndex thirdIndex‖

/-- The actual allocation owner's `(0,0,0)` face is exactly the unweighted global corner. -/
theorem directDyadicHodgeThreeAxisAllocationFace_zero_zero_zero_eq_global
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) :
    directDyadicHodgeThreeAxisAllocationFace scale component coordinate input
        (0 : Fin 3) (0 : Fin 3) (0 : Fin 3)
        (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
          firstIndex secondIndex thirdIndex) =
      dyadicHodgeThreeAxisGlobalProductFace scale 0 0 0
        component coordinate input firstIndex secondIndex thirdIndex := by
  simp [directDyadicHodgeThreeAxisAllocationFace,
    threeAxisHodgeAllocationFace, dyadicHodgeThreeAxisGlobalProductFace,
    secondOrderBinomialWeight]

/-- Norm population of the actual source allocation corner. -/
def directDyadicHodgeThreeAxisCornerAllocationMass
    (scale : ℕ) (component coordinate input : Fin 3) : ℝ :=
  ∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
    ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
      ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ‖directDyadicHodgeThreeAxisAllocationFace scale component coordinate input
          (0 : Fin 3) (0 : Fin 3) (0 : Fin 3)
          (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
            firstIndex secondIndex thirdIndex)‖

/-- The source allocation receiver and the global product-face chart have identical corner mass. -/
theorem directDyadicHodgeThreeAxisCornerAllocationMass_eq_global
    (scale : ℕ) (component coordinate input : Fin 3) :
    directDyadicHodgeThreeAxisCornerAllocationMass scale component coordinate input =
      dyadicHodgeThreeAxisCornerGlobalMass scale component coordinate input := by
  simp only [directDyadicHodgeThreeAxisCornerAllocationMass,
    dyadicHodgeThreeAxisCornerGlobalMass,
    directDyadicHodgeThreeAxisAllocationFace_zero_zero_zero_eq_global]

/-- All three left residue populations vanish, so global and natural corner mass agree exactly. -/
theorem dyadicHodgeThreeAxisCornerGlobalMass_eq_subset
    (scale : ℕ) (component coordinate input : Fin 3) :
    dyadicHodgeThreeAxisCornerGlobalMass scale component coordinate input =
      dyadicHodgeThreeAxisCornerSubsetMass scale component coordinate input := by
  unfold dyadicHodgeThreeAxisCornerGlobalMass dyadicHodgeThreeAxisCornerSubsetMass
  nth_rewrite 1 [show dyadicHodgeApertureCount scale + 2 =
    2 + dyadicHodgeApertureCount scale by omega]
  nth_rewrite 1 [show dyadicHodgeApertureCount scale + 2 =
    2 + dyadicHodgeApertureCount scale by omega]
  nth_rewrite 1 [show dyadicHodgeApertureCount scale + 2 =
    2 + dyadicHodgeApertureCount scale by omega]
  apply sum_range_threeAxis_shift_of_prefix_zero
  · intro firstIndex hfirstIndex secondIndex _ thirdIndex _
    rw [show dyadicHodgeThreeAxisGlobalProductFace scale 0 0 0
      component coordinate input firstIndex secondIndex thirdIndex = 0 by
      simp only [dyadicHodgeThreeAxisGlobalProductFace,
        threeAxisMixedForwardDifference, Function.iterate_zero_apply]
      rw [directDyadicScalarCoefficient_threeAxisBackwardPadded_eq_zero_of_first_lt_two
        scale firstIndex secondIndex thirdIndex hfirstIndex]
      simp]
    simp
  · intro firstIndex _ secondIndex hsecondIndex thirdIndex _
    rw [show dyadicHodgeThreeAxisGlobalProductFace scale 0 0 0
      component coordinate input (2 + firstIndex) secondIndex thirdIndex = 0 by
      simp only [dyadicHodgeThreeAxisGlobalProductFace,
        threeAxisMixedForwardDifference, Function.iterate_zero_apply]
      rw [directDyadicScalarCoefficient_threeAxisBackwardPadded_eq_zero_of_second_lt_two
        scale (2 + firstIndex) secondIndex thirdIndex hsecondIndex]
      simp]
    simp
  · intro firstIndex _ secondIndex _ thirdIndex hthirdIndex
    rw [show dyadicHodgeThreeAxisGlobalProductFace scale 0 0 0
      component coordinate input (2 + firstIndex) (2 + secondIndex) thirdIndex = 0 by
      simp only [dyadicHodgeThreeAxisGlobalProductFace,
        threeAxisMixedForwardDifference, Function.iterate_zero_apply]
      rw [directDyadicScalarCoefficient_threeAxisBackwardPadded_eq_zero_of_third_lt_two
        scale (2 + firstIndex) (2 + secondIndex) thirdIndex hthirdIndex]
      simp]
    simp
  · intro firstIndex _ secondIndex _ thirdIndex _
    simpa [Nat.add_comm] using congrArg norm
      (dyadicHodgeThreeAxisGlobalProductFace_add_offsets_eq_subset
        scale 0 0 0 component coordinate input firstIndex secondIndex thirdIndex)

/-- The exact Hodge scale carried by the scalar-zero corner. -/
def dyadicHodgeThreeAxisCornerComplementBound (scale : ℕ) : ℝ :=
  4000000000000000 / (dyadicRadius scale : ℝ) ^ 6

/-- Every natural corner value is its scalar coefficient norm times the derived full-Hodge
envelope.  A zero scalar face is discharged before requesting a support stencil. -/
theorem norm_dyadicHodgeThreeAxisSubsetProductFace_zero_zero_zero_le
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) (hscale : 3 ≤ scale) :
    ‖dyadicHodgeThreeAxisSubsetProductFace scale 0 0 0
        component coordinate input firstIndex secondIndex thirdIndex‖ ≤
      ‖dyadicTensorBandThreeAxisVariation scale 0 0 0
        firstIndex secondIndex thirdIndex‖ *
        dyadicHodgeThreeAxisCornerComplementBound scale := by
  let frequency := dyadicHodgeThreeAxisSubsetPaddedFrequency scale 0 0 0
    firstIndex secondIndex thirdIndex
  have hscalar :=
    directDyadicScalarCoefficient_threeAxisSubsetPadded_zero_zero_zero_eq
      scale firstIndex secondIndex thirdIndex
  change ‖directDyadicScalarCoefficient scale frequency *
    threeAxisMixedForwardDifference 0 1 2 2 2 2
      (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
      (threeAxisStencilPoint 0 1 2 frequency 0 0 0)‖ ≤ _
  change directDyadicScalarCoefficient scale frequency = _ at hscalar
  rw [hscalar, norm_mul]
  by_cases hzero : dyadicTensorBandThreeAxisVariation scale 0 0 0
      firstIndex secondIndex thirdIndex = 0
  · simp [hzero]
  · have hglobal : threeAxisMixedForwardDifference 0 1 2 0 0 0
        (directDyadicScalarCoefficient scale) frequency ≠ 0 := by
      simp only [threeAxisMixedForwardDifference, Function.iterate_zero_apply]
      rw [hscalar]
      exact hzero
    have hstencil : ThreeAxisStencilControlled
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale)
        0 1 2 (threeAxisStencilPoint 0 1 2 frequency 0 0 0) 2 2 2 := by
      simpa [dyadicHodgeControlledLower, dyadicHodgeControlledBound] using
        (directDyadicScalar_threeAxis_support_controls_complementaryHodgeStencil
          scale 0 0 0
          (dyadicHodgeInnerCutoff_ge_three_of_scale_ge_three scale hscale)
          (by omega) (by omega) (by omega) frequency hglobal)
    have hhodge :=
      norm_hodgeJacobianMultiplierEntry_threeAxisMixedForwardDifference_two_two_two_le
        (lower := dyadicHodgeControlledLower scale)
        (bound := dyadicHodgeControlledBound scale)
        (dyadicHodgeControlledLower_pos scale hscale)
        (by unfold dyadicHodgeControlledBound; positivity)
        (threeAxisStencilPoint 0 1 2 frequency 0 0 0)
        component coordinate input hstencil
    have hhodgeScaled := hhodge.trans
      (hodgeJacobianEntryThreeAxisFullMixedEnvelope_dyadic_inverseCube_le scale hscale)
    gcongr
    simpa [dyadicHodgeThreeAxisCornerComplementBound] using hhodgeScaled

/-- The scalar corner population has exact cubic radial growth. -/
theorem sum_norm_dyadicTensorBandThreeAxisVariation_zero_zero_zero_le
    (scale : ℕ) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicTensorBandThreeAxisVariation scale 0 0 0
            firstIndex secondIndex thirdIndex‖) ≤
      1024 * (dyadicRadius scale : ℝ) ^ 3 := by
  refine (sum_norm_dyadicTensorBandThreeAxisVariation_le_envelopes scale 0 0 0).trans ?_
  simp only [nextProfileVariationEnvelope, baseProfileVariationEnvelope]
  ring_nf
  exact le_rfl

/-- The natural corner mass has the required inverse-cubic radial scale. -/
theorem dyadicHodgeThreeAxisCornerSubsetMass_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    dyadicHodgeThreeAxisCornerSubsetMass scale component coordinate input ≤
      4096000000000000000 / (dyadicRadius scale : ℝ) ^ 3 := by
  let bound := dyadicHodgeThreeAxisCornerComplementBound scale
  have hscalar := sum_norm_dyadicTensorBandThreeAxisVariation_zero_zero_zero_le scale
  have hradius : 0 < (dyadicRadius scale : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  unfold dyadicHodgeThreeAxisCornerSubsetMass
  calc
    _ ≤ ∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
        ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
            ‖dyadicTensorBandThreeAxisVariation scale 0 0 0
              firstIndex secondIndex thirdIndex‖ * bound := by
      gcongr with firstIndex hfirst secondIndex hsecond thirdIndex hthird
      exact norm_dyadicHodgeThreeAxisSubsetProductFace_zero_zero_zero_le
        scale component coordinate input firstIndex secondIndex thirdIndex hscale
    _ = (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
        ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
            ‖dyadicTensorBandThreeAxisVariation scale 0 0 0
              firstIndex secondIndex thirdIndex‖) * bound := by
      simp only [Finset.sum_mul]
    _ ≤ (1024 * (dyadicRadius scale : ℝ) ^ 3) * bound := by
      exact mul_le_mul_of_nonneg_right hscalar (by
        dsimp [bound, dyadicHodgeThreeAxisCornerComplementBound]
        positivity)
    _ = 4096000000000000000 / (dyadicRadius scale : ℝ) ^ 3 := by
      dsimp [bound, dyadicHodgeThreeAxisCornerComplementBound]
      field_simp [hradius.ne']
      ring

/-- The actual global allocation corner, with all six aperture flanks retained, has the same
uniform inverse-cubic bound. -/
theorem dyadicHodgeThreeAxisCornerGlobalMass_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    dyadicHodgeThreeAxisCornerGlobalMass scale component coordinate input ≤
      4096000000000000000 / (dyadicRadius scale : ℝ) ^ 3 := by
  rw [dyadicHodgeThreeAxisCornerGlobalMass_eq_subset]
  exact dyadicHodgeThreeAxisCornerSubsetMass_le
    scale component coordinate input hscale

/-- The actual source allocation corner has the uniform inverse-cubic radial bound. -/
theorem directDyadicHodgeThreeAxisCornerAllocationMass_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    directDyadicHodgeThreeAxisCornerAllocationMass scale component coordinate input ≤
      4096000000000000000 / (dyadicRadius scale : ℝ) ^ 3 := by
  rw [directDyadicHodgeThreeAxisCornerAllocationMass_eq_global]
  exact dyadicHodgeThreeAxisCornerGlobalMass_le
    scale component coordinate input hscale

section Audit

#print axioms dyadicHodgeThreeAxisCornerGlobalMass_eq_subset
#print axioms directDyadicHodgeThreeAxisCornerAllocationMass_eq_global
#print axioms norm_dyadicHodgeThreeAxisSubsetProductFace_zero_zero_zero_le
#print axioms sum_norm_dyadicTensorBandThreeAxisVariation_zero_zero_zero_le
#print axioms dyadicHodgeThreeAxisCornerSubsetMass_le
#print axioms dyadicHodgeThreeAxisCornerGlobalMass_le
#print axioms directDyadicHodgeThreeAxisCornerAllocationMass_le

end Audit

end Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisCornerMass
