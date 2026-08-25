import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeThreeAxisResidualFaces

/-!
# The complete twenty-seven-face dyadic Hodge mass

**[proved-derived]** This owner retains the complete allocation address while it reconstructs the
staged `3 × 9` Leibniz return as a `Fin 3 × Fin 3 × Fin 3` sum.  Only after that exact history
comparison does it take the norm receiver, transport every face to the common global chart, and
sum the exact source-specific inverse-cubic numerators.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisFullMass

open Soma.Holonics.CoordinateSubsetReceiver
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesSmoothHodgeJacobianBand
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeHigherMixedVariation
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeKernelVariation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeSupportStencil
open Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeProductMass
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeSubsetReceivers
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisAllocation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisCornerMass
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisThirdTwoSlice
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisOtherTwoSlices
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisOneFace
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisResidualFaces

set_option maxHeartbeats 1000000

/-- One staged nine-face return is exactly the sum of its nine simultaneous allocation faces. -/
theorem stagedThreeAxisHodgeNineFaceReturn_eq_sum_faces
    (thirdAllocation : Fin 3) (left right : SpatialFrequency → ℂ)
    (frequency : SpatialFrequency) :
    stagedThreeAxisHodgeNineFaceReturn thirdAllocation left right frequency =
      ∑ firstAllocation : Fin 3, ∑ secondAllocation : Fin 3,
        threeAxisHodgeAllocationFace firstAllocation secondAllocation thirdAllocation
          left right frequency := by
  simp_rw [← stagedThreeAxisHodgeAllocationFace_eq]
  fin_cases thirdAllocation <;>
    simp [Fin.sum_univ_succ, stagedThreeAxisHodgeNineFaceReturn,
      stagedThreeAxisHodgeAllocationFace, twoAxisNineFaceReturn,
      secondOrderBinomialWeight, mixedForwardDifference,
      Function.iterate_zero_apply] <;> ring

/-- The staged `3 × 9` receiver retains exactly all twenty-seven allocation addresses. -/
theorem threeAxisHodgeAllocationReturn_eq_sum_faces
    (left right : SpatialFrequency → ℂ) (frequency : SpatialFrequency) :
    threeAxisHodgeAllocationReturn left right frequency =
      ∑ firstAllocation : Fin 3, ∑ secondAllocation : Fin 3,
        ∑ thirdAllocation : Fin 3,
          threeAxisHodgeAllocationFace firstAllocation secondAllocation thirdAllocation
            left right frequency := by
  rw [show threeAxisHodgeAllocationReturn left right frequency =
      stagedThreeAxisHodgeNineFaceReturn 2 left right frequency +
        stagedThreeAxisHodgeNineFaceReturn 1 left right frequency +
          stagedThreeAxisHodgeNineFaceReturn 0 left right frequency by rfl]
  rw [stagedThreeAxisHodgeNineFaceReturn_eq_sum_faces,
    stagedThreeAxisHodgeNineFaceReturn_eq_sum_faces,
    stagedThreeAxisHodgeNineFaceReturn_eq_sum_faces]
  simp [Fin.sum_univ_succ]
  ring

/-- The source-specific return is the exact sum of its twenty-seven addressed faces. -/
theorem directDyadicHodgeThreeAxisAllocationReturn_eq_sum_faces
    (scale : ℕ) (component coordinate input : Fin 3) (frequency : SpatialFrequency) :
    directDyadicHodgeThreeAxisAllocationReturn scale component coordinate input frequency =
      ∑ firstAllocation : Fin 3, ∑ secondAllocation : Fin 3,
        ∑ thirdAllocation : Fin 3,
          directDyadicHodgeThreeAxisAllocationFace scale component coordinate input
            firstAllocation secondAllocation thirdAllocation frequency := by
  exact threeAxisHodgeAllocationReturn_eq_sum_faces
    (directDyadicScalarCoefficient scale)
    (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
    frequency

/-- The norm receiver may forget interference only after the complete address sum is present. -/
theorem norm_directDyadicHodgeThreeAxisAllocationReturn_le_sum_face_norms
    (scale : ℕ) (component coordinate input : Fin 3) (frequency : SpatialFrequency) :
    ‖directDyadicHodgeThreeAxisAllocationReturn scale component coordinate input frequency‖ ≤
      ∑ firstAllocation : Fin 3, ∑ secondAllocation : Fin 3,
        ∑ thirdAllocation : Fin 3,
          ‖directDyadicHodgeThreeAxisAllocationFace scale component coordinate input
            firstAllocation secondAllocation thirdAllocation frequency‖ := by
  rw [directDyadicHodgeThreeAxisAllocationReturn_eq_sum_faces]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro firstAllocation _
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro secondAllocation _
  exact norm_sum_le _ _

/-- Complete common-chart mass of all twenty-seven actual allocation faces. -/
def directDyadicHodgeThreeAxisGlobalAllocationMass
    (scale : ℕ) (component coordinate input : Fin 3) : ℝ :=
  ∑ firstAllocation : Fin 3, ∑ secondAllocation : Fin 3,
    ∑ thirdAllocation : Fin 3,
      directDyadicHodgeThreeAxisGlobalAllocationFaceMass scale component coordinate input
        firstAllocation secondAllocation thirdAllocation

/-- Exact Fubini interchange for the six finite axes used by the allocation population. -/
theorem sixfold_sum_rotate
    {α β γ δ ε ζ M : Type*} [AddCommMonoid M]
    (sα : Finset α) (sβ : Finset β) (sγ : Finset γ)
    (sδ : Finset δ) (sε : Finset ε) (sζ : Finset ζ)
    (f : α → β → γ → δ → ε → ζ → M) :
    (∑ a ∈ sα, ∑ b ∈ sβ, ∑ c ∈ sγ, ∑ d ∈ sδ, ∑ e ∈ sε, ∑ z ∈ sζ,
      f a b c d e z) =
    ∑ d ∈ sδ, ∑ e ∈ sε, ∑ z ∈ sζ, ∑ a ∈ sα, ∑ b ∈ sβ, ∑ c ∈ sγ,
      f a b c d e z := by
  calc
    _ = ∑ a ∈ sα, ∑ b ∈ sβ, ∑ d ∈ sδ, ∑ c ∈ sγ, ∑ e ∈ sε, ∑ z ∈ sζ,
        f a b c d e z := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm
    _ = ∑ a ∈ sα, ∑ d ∈ sδ, ∑ b ∈ sβ, ∑ c ∈ sγ, ∑ e ∈ sε, ∑ z ∈ sζ,
        f a b c d e z := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ d ∈ sδ, ∑ a ∈ sα, ∑ b ∈ sβ, ∑ c ∈ sγ, ∑ e ∈ sε, ∑ z ∈ sζ,
        f a b c d e z := Finset.sum_comm
    _ = ∑ d ∈ sδ, ∑ a ∈ sα, ∑ b ∈ sβ, ∑ e ∈ sε, ∑ c ∈ sγ, ∑ z ∈ sζ,
        f a b c d e z := by
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm
    _ = ∑ d ∈ sδ, ∑ a ∈ sα, ∑ e ∈ sε, ∑ b ∈ sβ, ∑ c ∈ sγ, ∑ z ∈ sζ,
        f a b c d e z := by
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ d ∈ sδ, ∑ e ∈ sε, ∑ a ∈ sα, ∑ b ∈ sβ, ∑ c ∈ sγ, ∑ z ∈ sζ,
        f a b c d e z := by
      apply Finset.sum_congr rfl
      intro d _
      exact Finset.sum_comm
    _ = ∑ d ∈ sδ, ∑ e ∈ sε, ∑ a ∈ sα, ∑ b ∈ sβ, ∑ z ∈ sζ, ∑ c ∈ sγ,
        f a b c d e z := by
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm
    _ = ∑ d ∈ sδ, ∑ e ∈ sε, ∑ a ∈ sα, ∑ z ∈ sζ, ∑ b ∈ sβ, ∑ c ∈ sγ,
        f a b c d e z := by
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ d ∈ sδ, ∑ e ∈ sε, ∑ z ∈ sζ, ∑ a ∈ sα, ∑ b ∈ sβ, ∑ c ∈ sγ,
        f a b c d e z := by
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro e _
      exact Finset.sum_comm

/-- The finite norm population of the reconstructed return is bounded by the complete common-chart
face population.  No face is removed and no aperture is enlarged. -/
theorem directDyadicHodgeThreeAxisAllocationReturnMass_le_globalAllocationMass
    (scale : ℕ) (component coordinate input : Fin 3) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
          ‖directDyadicHodgeThreeAxisAllocationReturn scale component coordinate input
            (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
              firstIndex secondIndex thirdIndex)‖) ≤
      directDyadicHodgeThreeAxisGlobalAllocationMass scale component coordinate input := by
  calc
    _ ≤ ∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
          ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
            ∑ firstAllocation : Fin 3, ∑ secondAllocation : Fin 3,
              ∑ thirdAllocation : Fin 3,
                ‖directDyadicHodgeThreeAxisAllocationFace scale component coordinate input
                  firstAllocation secondAllocation thirdAllocation
                  (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
                    firstIndex secondIndex thirdIndex)‖ := by
      apply Finset.sum_le_sum
      intro firstIndex _
      apply Finset.sum_le_sum
      intro secondIndex _
      apply Finset.sum_le_sum
      intro thirdIndex _
      exact norm_directDyadicHodgeThreeAxisAllocationReturn_le_sum_face_norms
        scale component coordinate input _
    _ = directDyadicHodgeThreeAxisGlobalAllocationMass scale component coordinate input := by
      unfold directDyadicHodgeThreeAxisGlobalAllocationMass
      simp only [directDyadicHodgeThreeAxisGlobalAllocationFaceMass]
      exact sixfold_sum_rotate
        (Finset.range (dyadicHodgeApertureCount scale + 2))
        (Finset.range (dyadicHodgeApertureCount scale + 2))
        (Finset.range (dyadicHodgeApertureCount scale + 2))
        (Finset.univ : Finset (Fin 3)) (Finset.univ : Finset (Fin 3))
        (Finset.univ : Finset (Fin 3)) _

/-- Exact inverse-cubic numerator attached to each of the twenty-seven source allocation
addresses.  The integer is a receiver ledger, not a floating-point approximation. -/
def dyadicHodgeThreeAxisFullFaceRadialNumerator
    (firstAllocation secondAllocation thirdAllocation : Fin 3) : ℕ :=
  match firstAllocation.val, secondAllocation.val, thirdAllocation.val with
  | 0, 0, 0 => 4096000000000000000
  | 0, 0, 1 => 7663248998400000
  | 0, 0, 2 => 12288000000000
  | 0, 1, 0 => 7663248998400000
  | 0, 1, 1 => 35333734400000
  | 0, 1, 2 => 63744000000
  | 0, 2, 0 => 12288000000000
  | 0, 2, 1 => 63744000000
  | 0, 2, 2 => 208000000
  | 1, 0, 0 => 7663248998400000
  | 1, 0, 1 => 35333734400000
  | 1, 0, 2 => 63744000000
  | 1, 1, 0 => 35333734400000
  | 1, 1, 1 => 231424000000
  | 1, 1, 2 => 460800000
  | 1, 2, 0 => 63744000000
  | 1, 2, 1 => 460800000
  | 1, 2, 2 => 2240000
  | 2, 0, 0 => 12288000000000
  | 2, 0, 1 => 63744000000
  | 2, 0, 2 => 208000000
  | 2, 1, 0 => 63744000000
  | 2, 1, 1 => 460800000
  | 2, 1, 2 => 2240000
  | 2, 2, 0 => 208000000
  | 2, 2, 1 => 2240000
  | 2, 2, 2 => 72
  | _, _, _ => 0

/-- The natural `(0,0,0)` chart is the already controlled source corner after exact global
reindexing. -/
theorem directDyadicHodgeThreeAxisNaturalAllocationFaceMass_zero_zero_zero_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    directDyadicHodgeThreeAxisNaturalAllocationFaceMass scale component coordinate input
        (0 : Fin 3) (0 : Fin 3) (0 : Fin 3) ≤
      4096000000000000000 / (dyadicRadius scale : ℝ) ^ 3 := by
  rw [← directDyadicHodgeThreeAxisGlobalAllocationFaceMass_eq_natural]
  simpa [directDyadicHodgeThreeAxisGlobalAllocationFaceMass,
    directDyadicHodgeThreeAxisCornerAllocationMass] using
      directDyadicHodgeThreeAxisCornerAllocationMass_le
        scale component coordinate input hscale

/-- The generic natural mass specializes definitionally to the established third-order-two
owner. -/
theorem directDyadicHodgeThreeAxisNaturalAllocationFaceMass_third_two_eq
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstAllocation secondAllocation : Fin 3) :
    directDyadicHodgeThreeAxisNaturalAllocationFaceMass scale component coordinate input
        firstAllocation secondAllocation (2 : Fin 3) =
      directDyadicHodgeThreeAxisThirdTwoAllocationFaceMass scale component coordinate input
        firstAllocation secondAllocation := by
  rfl

/-- Exact ledger bound for the complete first-order-two slab. -/
theorem directDyadicHodgeThreeAxisNaturalAllocationFaceMass_first_two_le_numerator
    (scale : ℕ) (component coordinate input : Fin 3)
    (secondAllocation thirdAllocation : Fin 3) (hscale : 3 ≤ scale) :
    directDyadicHodgeThreeAxisNaturalAllocationFaceMass scale component coordinate input
        (2 : Fin 3) secondAllocation thirdAllocation ≤
      (dyadicHodgeThreeAxisFullFaceRadialNumerator
          (2 : Fin 3) secondAllocation thirdAllocation : ℝ) /
        (dyadicRadius scale : ℝ) ^ 3 := by
  calc
    _ ≤ (secondOrderBinomialWeight secondAllocation *
          secondOrderBinomialWeight thirdAllocation : ℕ) *
        (dyadicHodgeThirdTwoFaceRadialConstant
            secondAllocation.val thirdAllocation.val /
          (dyadicRadius scale : ℝ) ^ 3) :=
      directDyadicHodgeThreeAxisNaturalAllocationFaceMass_first_two_le_radial
        scale component coordinate input secondAllocation thirdAllocation hscale
    _ = _ := by
      fin_cases secondAllocation <;> fin_cases thirdAllocation <;>
        norm_num [dyadicHodgeThreeAxisFullFaceRadialNumerator,
          secondOrderBinomialWeight, dyadicHodgeThirdTwoFaceRadialConstant] <;> ring

/-- Exact ledger bound for the complete second-order-two slab. -/
theorem directDyadicHodgeThreeAxisNaturalAllocationFaceMass_second_two_le_numerator
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstAllocation thirdAllocation : Fin 3) (hscale : 3 ≤ scale) :
    directDyadicHodgeThreeAxisNaturalAllocationFaceMass scale component coordinate input
        firstAllocation (2 : Fin 3) thirdAllocation ≤
      (dyadicHodgeThreeAxisFullFaceRadialNumerator
          firstAllocation (2 : Fin 3) thirdAllocation : ℝ) /
        (dyadicRadius scale : ℝ) ^ 3 := by
  calc
    _ ≤ (secondOrderBinomialWeight firstAllocation *
          secondOrderBinomialWeight thirdAllocation : ℕ) *
        (dyadicHodgeThirdTwoFaceRadialConstant
            firstAllocation.val thirdAllocation.val /
          (dyadicRadius scale : ℝ) ^ 3) :=
      directDyadicHodgeThreeAxisNaturalAllocationFaceMass_second_two_le_radial
        scale component coordinate input firstAllocation thirdAllocation hscale
    _ = _ := by
      fin_cases firstAllocation <;> fin_cases thirdAllocation <;>
        norm_num [dyadicHodgeThreeAxisFullFaceRadialNumerator,
          secondOrderBinomialWeight, dyadicHodgeThirdTwoFaceRadialConstant] <;> ring

/-- Exact ledger bound for the complete third-order-two slab. -/
theorem directDyadicHodgeThreeAxisNaturalAllocationFaceMass_third_two_le_numerator
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstAllocation secondAllocation : Fin 3) (hscale : 3 ≤ scale) :
    directDyadicHodgeThreeAxisNaturalAllocationFaceMass scale component coordinate input
        firstAllocation secondAllocation (2 : Fin 3) ≤
      (dyadicHodgeThreeAxisFullFaceRadialNumerator
          firstAllocation secondAllocation (2 : Fin 3) : ℝ) /
        (dyadicRadius scale : ℝ) ^ 3 := by
  rw [directDyadicHodgeThreeAxisNaturalAllocationFaceMass_third_two_eq]
  calc
    _ ≤ (secondOrderBinomialWeight firstAllocation *
          secondOrderBinomialWeight secondAllocation : ℕ) *
        (dyadicHodgeThirdTwoFaceRadialConstant
            firstAllocation.val secondAllocation.val /
          (dyadicRadius scale : ℝ) ^ 3) :=
      directDyadicHodgeThreeAxisThirdTwoAllocationFaceMass_le_radial
        scale component coordinate input firstAllocation secondAllocation hscale
    _ = _ := by
      fin_cases firstAllocation <;> fin_cases secondAllocation <;>
        norm_num [dyadicHodgeThreeAxisFullFaceRadialNumerator,
          secondOrderBinomialWeight, dyadicHodgeThirdTwoFaceRadialConstant] <;> ring

/-- The eight addresses without an order-two coordinate are exactly the corner, the three `100`
faces, the three `110` faces, and the central `111` face. -/
theorem directDyadicHodgeThreeAxisNaturalAllocationFaceMass_no_two_le_numerator
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstAllocation secondAllocation thirdAllocation : Fin 3)
    (hfirst : firstAllocation ≠ (2 : Fin 3))
    (hsecond : secondAllocation ≠ (2 : Fin 3))
    (hthird : thirdAllocation ≠ (2 : Fin 3)) (hscale : 3 ≤ scale) :
    directDyadicHodgeThreeAxisNaturalAllocationFaceMass scale component coordinate input
        firstAllocation secondAllocation thirdAllocation ≤
      (dyadicHodgeThreeAxisFullFaceRadialNumerator
          firstAllocation secondAllocation thirdAllocation : ℝ) /
        (dyadicRadius scale : ℝ) ^ 3 := by
  fin_cases firstAllocation <;> fin_cases secondAllocation <;> fin_cases thirdAllocation
  all_goals first
    | exact (hfirst rfl).elim
    | exact (hsecond rfl).elim
    | exact (hthird rfl).elim
    | skip
  case «0».«0».«0» =>
    simpa [dyadicHodgeThreeAxisFullFaceRadialNumerator] using
      directDyadicHodgeThreeAxisNaturalAllocationFaceMass_zero_zero_zero_le
        scale component coordinate input hscale
  case «0».«0».«1» =>
    simpa [dyadicHodgeThreeAxisFullFaceRadialNumerator, oneTwoTwoScalarAllocation] using
      directDyadicHodgeThreeAxisNaturalAllocationFaceMass_residual122_le
        scale (2 : Fin 3) component coordinate input hscale
  case «0».«1».«0» =>
    simpa [dyadicHodgeThreeAxisFullFaceRadialNumerator, oneTwoTwoScalarAllocation] using
      directDyadicHodgeThreeAxisNaturalAllocationFaceMass_residual122_le
        scale (1 : Fin 3) component coordinate input hscale
  case «0».«1».«1» =>
    simpa [dyadicHodgeThreeAxisFullFaceRadialNumerator, oneOneTwoScalarAllocation] using
      directDyadicHodgeThreeAxisNaturalAllocationFaceMass_residual112_le
        scale (0 : Fin 3) component coordinate input hscale
  case «1».«0».«0» =>
    simpa [dyadicHodgeThreeAxisFullFaceRadialNumerator, oneTwoTwoScalarAllocation] using
      directDyadicHodgeThreeAxisNaturalAllocationFaceMass_residual122_le
        scale (0 : Fin 3) component coordinate input hscale
  case «1».«0».«1» =>
    simpa [dyadicHodgeThreeAxisFullFaceRadialNumerator, oneOneTwoScalarAllocation] using
      directDyadicHodgeThreeAxisNaturalAllocationFaceMass_residual112_le
        scale (1 : Fin 3) component coordinate input hscale
  case «1».«1».«0» =>
    simpa [dyadicHodgeThreeAxisFullFaceRadialNumerator, oneOneTwoScalarAllocation] using
      directDyadicHodgeThreeAxisNaturalAllocationFaceMass_residual112_le
        scale (2 : Fin 3) component coordinate input hscale
  case «1».«1».«1» =>
    simpa [dyadicHodgeThreeAxisFullFaceRadialNumerator] using
      directDyadicHodgeThreeAxisNaturalAllocationFaceMass_one_one_one_le
        scale component coordinate input hscale

/-- Every common-chart face is controlled by its exact integer numerator. -/
theorem directDyadicHodgeThreeAxisGlobalAllocationFaceMass_le_radialNumerator
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstAllocation secondAllocation thirdAllocation : Fin 3) (hscale : 3 ≤ scale) :
    directDyadicHodgeThreeAxisGlobalAllocationFaceMass scale component coordinate input
        firstAllocation secondAllocation thirdAllocation ≤
      (dyadicHodgeThreeAxisFullFaceRadialNumerator
          firstAllocation secondAllocation thirdAllocation : ℝ) /
        (dyadicRadius scale : ℝ) ^ 3 := by
  rw [directDyadicHodgeThreeAxisGlobalAllocationFaceMass_eq_natural]
  by_cases hfirst : firstAllocation = (2 : Fin 3)
  · subst firstAllocation
    exact directDyadicHodgeThreeAxisNaturalAllocationFaceMass_first_two_le_numerator
      scale component coordinate input secondAllocation thirdAllocation hscale
  by_cases hsecond : secondAllocation = (2 : Fin 3)
  · subst secondAllocation
    exact directDyadicHodgeThreeAxisNaturalAllocationFaceMass_second_two_le_numerator
      scale component coordinate input firstAllocation thirdAllocation hscale
  by_cases hthird : thirdAllocation = (2 : Fin 3)
  · subst thirdAllocation
    exact directDyadicHodgeThreeAxisNaturalAllocationFaceMass_third_two_le_numerator
      scale component coordinate input firstAllocation secondAllocation hscale
  exact directDyadicHodgeThreeAxisNaturalAllocationFaceMass_no_two_le_numerator
    scale component coordinate input firstAllocation secondAllocation thirdAllocation
      hfirst hsecond hthird hscale

/-- The exact sum of all twenty-seven integer face numerators. -/
theorem dyadicHodgeThreeAxisFullFaceRadialNumerator_sum :
    (∑ firstAllocation : Fin 3, ∑ secondAllocation : Fin 3,
      ∑ thirdAllocation : Fin 3,
        dyadicHodgeThreeAxisFullFaceRadialNumerator
          firstAllocation secondAllocation thirdAllocation) =
      4119133228099520072 := by
  norm_num [Fin.sum_univ_succ, dyadicHodgeThreeAxisFullFaceRadialNumerator]

/-- The complete common-chart allocation population has the exact summed inverse-cubic
numerator. -/
theorem directDyadicHodgeThreeAxisGlobalAllocationMass_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    directDyadicHodgeThreeAxisGlobalAllocationMass scale component coordinate input ≤
      4119133228099520072 / (dyadicRadius scale : ℝ) ^ 3 := by
  unfold directDyadicHodgeThreeAxisGlobalAllocationMass
  calc
    _ ≤ ∑ firstAllocation : Fin 3, ∑ secondAllocation : Fin 3,
        ∑ thirdAllocation : Fin 3,
          (dyadicHodgeThreeAxisFullFaceRadialNumerator
              firstAllocation secondAllocation thirdAllocation : ℝ) /
            (dyadicRadius scale : ℝ) ^ 3 := by
      apply Finset.sum_le_sum
      intro firstAllocation _
      apply Finset.sum_le_sum
      intro secondAllocation _
      apply Finset.sum_le_sum
      intro thirdAllocation _
      exact directDyadicHodgeThreeAxisGlobalAllocationFaceMass_le_radialNumerator
        scale component coordinate input firstAllocation secondAllocation thirdAllocation hscale
    _ = 4119133228099520072 / (dyadicRadius scale : ℝ) ^ 3 := by
      simp only [← Finset.sum_div]
      rw [show (∑ firstAllocation : Fin 3, ∑ secondAllocation : Fin 3,
          ∑ thirdAllocation : Fin 3,
            (dyadicHodgeThreeAxisFullFaceRadialNumerator
              firstAllocation secondAllocation thirdAllocation : ℝ)) =
          (4119133228099520072 : ℝ) by
        exact_mod_cast dyadicHodgeThreeAxisFullFaceRadialNumerator_sum]

/-- **[proved-derived]** The official full-coordinate Boolean receiver is inhabited by the exact
source-specific `64 → 27` reconstruction and has a uniform inverse-cubic mass bound. -/
theorem dyadicHodgeSubsetMass_univ_le_fullFaceRadial
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    dyadicHodgeSubsetMass (Finset.univ : CoordinateFace 3)
        scale component coordinate input ≤
      4119133228099520072 / (dyadicRadius scale : ℝ) ^ 3 := by
  calc
    _ = ∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
          ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
            ‖directDyadicHodgeThreeAxisAllocationReturn scale component coordinate input
              (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
                firstIndex secondIndex thirdIndex)‖ :=
      dyadicHodgeSubsetMass_univ_eq_allocationReturnMass
        scale component coordinate input
    _ ≤ directDyadicHodgeThreeAxisGlobalAllocationMass
        scale component coordinate input :=
      directDyadicHodgeThreeAxisAllocationReturnMass_le_globalAllocationMass
        scale component coordinate input
    _ ≤ 4119133228099520072 / (dyadicRadius scale : ℝ) ^ 3 :=
      directDyadicHodgeThreeAxisGlobalAllocationMass_le
        scale component coordinate input hscale

section Audit

#print axioms stagedThreeAxisHodgeNineFaceReturn_eq_sum_faces
#print axioms threeAxisHodgeAllocationReturn_eq_sum_faces
#print axioms directDyadicHodgeThreeAxisAllocationReturn_eq_sum_faces
#print axioms norm_directDyadicHodgeThreeAxisAllocationReturn_le_sum_face_norms
#print axioms directDyadicHodgeThreeAxisAllocationReturnMass_le_globalAllocationMass
#print axioms dyadicHodgeThreeAxisFullFaceRadialNumerator_sum
#print axioms directDyadicHodgeThreeAxisGlobalAllocationFaceMass_le_radialNumerator
#print axioms directDyadicHodgeThreeAxisGlobalAllocationMass_le
#print axioms dyadicHodgeSubsetMass_univ_le_fullFaceRadial

end Audit

end Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisFullMass
