import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeSubsetReceivers
import ElementaryHolonics.Millennium.NavierStokesDyadicTensorBandSubsetVariation

/-!
# Three-axis scalar subset variation of the direct dyadic band

**[proved-derived]** The scalar de la Vallée--Poussin band is a difference of two separated
three-coordinate profiles.  This owner differentiates all three profile axes independently and
retains the subtraction inside the direct band.  It returns one Fubini product bound for every
allocation `(a,b,c)`, including the top `(2,2,2)` mass `72 / R^3`.

This is the scalar half of the twenty-seven-face direct Hodge Leibniz return.  It does not identify
the scalar mass with the Hodge multiplier mass.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesThreeAxisScalarSubsetVariation

open Soma.Holonics.Millennium.NavierStokesAnnularHodgeMixedFubini
open Soma.Holonics.Millennium.NavierStokesAnnularTensorCoefficientVariation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeKernelVariation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicTensorBandVariation
open Soma.Holonics.Millennium.NavierStokesDyadicTensorBandSubsetVariation
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors

/-- One separated three-axis profile after independently selecting orders `0`, `1`, or `2`. -/
def separatedDyadicProfileThreeAxisVariation
    (scale firstOrder secondOrder thirdOrder : ℕ) (slice : ℕ → ℂ)
    (firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  separatedTensorCoefficient
    (zeroPaddedVariation firstOrder slice (dyadicHodgeApertureCount scale))
    (zeroPaddedVariation secondOrder slice (dyadicHodgeApertureCount scale))
    (zeroPaddedVariation thirdOrder slice (dyadicHodgeApertureCount scale))
    firstIndex secondIndex thirdIndex

/-- The genuine direct band, with all three selected differences taken before any norm. -/
def dyadicTensorBandThreeAxisVariation
    (scale firstOrder secondOrder thirdOrder : ℕ)
    (firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  separatedDyadicProfileThreeAxisVariation scale firstOrder secondOrder thirdOrder
      (dyadicNextCoordinateSlice scale) firstIndex secondIndex thirdIndex -
    separatedDyadicProfileThreeAxisVariation scale firstOrder secondOrder thirdOrder
      (dyadicBaseCoordinateSlice scale) firstIndex secondIndex thirdIndex

/-- The one-dimensional profile mass used by tensor Fubini. -/
def dyadicProfileVariationMass
    (scale order : ℕ) (slice : ℕ → ℂ) : ℝ :=
  ∑ index ∈ Finset.range (dyadicHodgeApertureCount scale + order),
    ‖zeroPaddedVariation order slice (dyadicHodgeApertureCount scale) index‖

/-- Exact tensor-Fubini control for every three-axis order allocation. -/
theorem sum_norm_dyadicTensorBandThreeAxisVariation_le_profile_masses
    (scale firstOrder secondOrder thirdOrder : ℕ) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + firstOrder),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + secondOrder),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale + thirdOrder),
          ‖dyadicTensorBandThreeAxisVariation scale firstOrder secondOrder thirdOrder
            firstIndex secondIndex thirdIndex‖) ≤
      dyadicProfileVariationMass scale firstOrder (dyadicNextCoordinateSlice scale) *
          dyadicProfileVariationMass scale secondOrder (dyadicNextCoordinateSlice scale) *
          dyadicProfileVariationMass scale thirdOrder (dyadicNextCoordinateSlice scale) +
        dyadicProfileVariationMass scale firstOrder (dyadicBaseCoordinateSlice scale) *
          dyadicProfileVariationMass scale secondOrder (dyadicBaseCoordinateSlice scale) *
          dyadicProfileVariationMass scale thirdOrder (dyadicBaseCoordinateSlice scale) := by
  let next := separatedDyadicProfileThreeAxisVariation
    scale firstOrder secondOrder thirdOrder (dyadicNextCoordinateSlice scale)
  let base := separatedDyadicProfileThreeAxisVariation
    scale firstOrder secondOrder thirdOrder (dyadicBaseCoordinateSlice scale)
  change (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + firstOrder),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + secondOrder),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale + thirdOrder),
          ‖next firstIndex secondIndex thirdIndex -
            base firstIndex secondIndex thirdIndex‖) ≤ _
  refine (sum_sum_sum_norm_sub_le next base
    (dyadicHodgeApertureCount scale + firstOrder)
    (dyadicHodgeApertureCount scale + secondOrder)
    (dyadicHodgeApertureCount scale + thirdOrder)).trans ?_
  dsimp [next, base, separatedDyadicProfileThreeAxisVariation,
    dyadicProfileVariationMass]
  rw [sum_norm_separatedTensorCoefficient,
    sum_norm_separatedTensorCoefficient]

/-! ## One-dimensional radial envelopes -/

/-- Next-profile variation constants: population, first variation, second variation. -/
def nextProfileVariationEnvelope (scale order : ℕ) : ℝ :=
  match order with
  | 0 => 8 * (dyadicRadius scale : ℝ)
  | 1 => 4
  | 2 => 2 / (dyadicRadius scale : ℝ)
  | _ => 0

/-- Base-profile variation constants on the same larger aperture. -/
def baseProfileVariationEnvelope (scale order : ℕ) : ℝ :=
  match order with
  | 0 => 8 * (dyadicRadius scale : ℝ)
  | 1 => 4
  | 2 => 4 / (dyadicRadius scale : ℝ)
  | _ => 0

theorem dyadicProfileVariationMass_next_le
    (scale order : ℕ) :
    dyadicProfileVariationMass scale order (dyadicNextCoordinateSlice scale) ≤
      nextProfileVariationEnvelope scale order := by
  rcases order with (_ | _ | _ | order)
  · simpa [dyadicProfileVariationMass, nextProfileVariationEnvelope,
      zeroPaddedVariation] using
        (sum_norm_dyadicNextCoordinateSlice_le_count scale).trans
          (dyadicHodgeApertureCount_real_le_eight_mul_radius scale)
  · simpa [dyadicProfileVariationMass, nextProfileVariationEnvelope,
      zeroPaddedVariation] using
        sum_norm_zeroPaddedBackwardDifference_dyadicNextCoordinateSlice_le_four scale
  · rw [dyadicProfileVariationMass, nextProfileVariationEnvelope]
    simp only [zeroPaddedVariation]
    rw [sum_norm_zeroPaddedSecondDifference_dyadicNextCoordinateSlice,
      dyadicHodgeParameter_next_real_eq_two_mul_radius]
    ring_nf
    rfl
  · simp [dyadicProfileVariationMass, nextProfileVariationEnvelope,
      zeroPaddedVariation]

theorem dyadicProfileVariationMass_base_le
    (scale order : ℕ) :
    dyadicProfileVariationMass scale order (dyadicBaseCoordinateSlice scale) ≤
      baseProfileVariationEnvelope scale order := by
  rcases order with (_ | _ | _ | order)
  · simpa [dyadicProfileVariationMass, baseProfileVariationEnvelope,
      zeroPaddedVariation] using
        (sum_norm_dyadicBaseCoordinateSlice_le_count scale).trans
          (dyadicHodgeApertureCount_real_le_eight_mul_radius scale)
  · simpa [dyadicProfileVariationMass, baseProfileVariationEnvelope,
      zeroPaddedVariation] using
        sum_norm_zeroPaddedBackwardDifference_dyadicBaseCoordinateSlice_le_four scale
  · rw [dyadicProfileVariationMass, baseProfileVariationEnvelope]
    simp only [zeroPaddedVariation]
    rw [sum_norm_zeroPaddedSecondDifference_dyadicBaseCoordinateSlice,
      dyadicHodgeParameter_base_real_eq_radius]
  · simp [dyadicProfileVariationMass, baseProfileVariationEnvelope,
      zeroPaddedVariation]

theorem nextProfileVariationEnvelope_nonneg (scale order : ℕ) :
    0 ≤ nextProfileVariationEnvelope scale order := by
  rcases order with (_ | _ | _ | order) <;>
    (simp [nextProfileVariationEnvelope] <;> positivity)

theorem baseProfileVariationEnvelope_nonneg (scale order : ℕ) :
    0 ≤ baseProfileVariationEnvelope scale order := by
  rcases order with (_ | _ | _ | order) <;>
    (simp [baseProfileVariationEnvelope] <;> positivity)

/-- One formula controls all twenty-seven scalar allocation faces. -/
theorem sum_norm_dyadicTensorBandThreeAxisVariation_le_envelopes
    (scale firstOrder secondOrder thirdOrder : ℕ) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + firstOrder),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + secondOrder),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale + thirdOrder),
          ‖dyadicTensorBandThreeAxisVariation scale firstOrder secondOrder thirdOrder
            firstIndex secondIndex thirdIndex‖) ≤
      nextProfileVariationEnvelope scale firstOrder *
          nextProfileVariationEnvelope scale secondOrder *
          nextProfileVariationEnvelope scale thirdOrder +
        baseProfileVariationEnvelope scale firstOrder *
          baseProfileVariationEnvelope scale secondOrder *
          baseProfileVariationEnvelope scale thirdOrder := by
  refine (sum_norm_dyadicTensorBandThreeAxisVariation_le_profile_masses
    scale firstOrder secondOrder thirdOrder).trans ?_
  have hn0 := dyadicProfileVariationMass_next_le scale firstOrder
  have hn1 := dyadicProfileVariationMass_next_le scale secondOrder
  have hn2 := dyadicProfileVariationMass_next_le scale thirdOrder
  have hb0 := dyadicProfileVariationMass_base_le scale firstOrder
  have hb1 := dyadicProfileVariationMass_base_le scale secondOrder
  have hb2 := dyadicProfileVariationMass_base_le scale thirdOrder
  have hn0' := nextProfileVariationEnvelope_nonneg scale firstOrder
  have hn1' := nextProfileVariationEnvelope_nonneg scale secondOrder
  have hb0' := baseProfileVariationEnvelope_nonneg scale firstOrder
  have hb1' := baseProfileVariationEnvelope_nonneg scale secondOrder
  have hnextMass0 : 0 ≤
      dyadicProfileVariationMass scale firstOrder (dyadicNextCoordinateSlice scale) := by
    unfold dyadicProfileVariationMass
    positivity
  have hnextMass1 : 0 ≤
      dyadicProfileVariationMass scale secondOrder (dyadicNextCoordinateSlice scale) := by
    unfold dyadicProfileVariationMass
    positivity
  have hnextMass2 : 0 ≤
      dyadicProfileVariationMass scale thirdOrder (dyadicNextCoordinateSlice scale) := by
    unfold dyadicProfileVariationMass
    positivity
  have hbaseMass0 : 0 ≤
      dyadicProfileVariationMass scale firstOrder (dyadicBaseCoordinateSlice scale) := by
    unfold dyadicProfileVariationMass
    positivity
  have hbaseMass1 : 0 ≤
      dyadicProfileVariationMass scale secondOrder (dyadicBaseCoordinateSlice scale) := by
    unfold dyadicProfileVariationMass
    positivity
  have hbaseMass2 : 0 ≤
      dyadicProfileVariationMass scale thirdOrder (dyadicBaseCoordinateSlice scale) := by
    unfold dyadicProfileVariationMass
    positivity
  apply add_le_add
  · exact mul_le_mul (mul_le_mul hn0 hn1 hnextMass1 hn0') hn2
      hnextMass2 (mul_nonneg hn0' hn1')
  · exact mul_le_mul (mul_le_mul hb0 hb1 hbaseMass1 hb0') hb2
      hbaseMass2 (mul_nonneg hb0' hb1')

/-- The top scalar face has the exact inverse-cube radial mass required by the direct-band
Leibniz allocation. -/
theorem sum_norm_dyadicTensorBandThreeAxisVariation_two_two_two_le
    (scale : ℕ) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
          ‖dyadicTensorBandThreeAxisVariation scale 2 2 2
            firstIndex secondIndex thirdIndex‖) ≤
      72 / (dyadicRadius scale : ℝ) ^ 3 := by
  refine (sum_norm_dyadicTensorBandThreeAxisVariation_le_envelopes
    scale 2 2 2).trans ?_
  have hradius : 0 < (dyadicRadius scale : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  simp only [nextProfileVariationEnvelope, baseProfileVariationEnvelope]
  field_simp [hradius.ne']
  norm_num

section Audit

#print axioms sum_norm_dyadicTensorBandThreeAxisVariation_le_envelopes
#print axioms sum_norm_dyadicTensorBandThreeAxisVariation_two_two_two_le

end Audit

end Soma.Holonics.Millennium.NavierStokesThreeAxisScalarSubsetVariation
