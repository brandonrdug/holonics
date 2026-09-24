import ElementaryHolonics.Foundation.CoordinateSubsetReceiver
import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeTwoAxisMass

/-!
# The eight direct dyadic Hodge subset receivers

**[proved-derived]** A three-coordinate near/far decomposition has eight faces.  This owner
constructs the exact zero-padded coefficient receiver and Abel return for every face.  The empty
face is the centered direct synthesis itself; a nonempty face applies a second difference in each
of its addressed coordinates.  All aperture residues remain in the resulting finite coefficient
population.

No division by a character gap occurs here.  Thus the identities remain valid on the singular
coordinate subtori where one or more characters equal one.  The later near/far receiver may select
the lawful identity pointwise without pretending that the full mixed identity is globally
divisible.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesDyadicHodgeSubsetReceivers

open Soma.Holonics.CoordinateSubsetReceiver
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeMixedFubini
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeMixedVariation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeKernelVariation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeTwoAxisMass

/-! ## The seven nonempty coefficient faces -/

/-- Second difference in the second displayed coordinate. -/
def dyadicHodgeCubeSecondDifferenceSecond
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  zeroPaddedSecondDifferenceSecond
    (dyadicHodgeCubeCoefficient scale component coordinate input)
    (dyadicHodgeApertureCount scale) firstIndex secondIndex thirdIndex

/-- Second difference in the third displayed coordinate. -/
def dyadicHodgeCubeSecondDifferenceThird
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  zeroPaddedSecondDifferenceThird
    (dyadicHodgeCubeCoefficient scale component coordinate input)
    (dyadicHodgeApertureCount scale) firstIndex secondIndex thirdIndex

/-- Ordered second differences in the first and third displayed coordinates. -/
def dyadicHodgeCubeSecondDifferenceFirstThird
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  zeroPaddedSecondDifferenceFirst
    (zeroPaddedSecondDifferenceThird
      (dyadicHodgeCubeCoefficient scale component coordinate input)
      (dyadicHodgeApertureCount scale))
    (dyadicHodgeApertureCount scale) firstIndex secondIndex thirdIndex

/-- Ordered second differences in the second and third displayed coordinates. -/
def dyadicHodgeCubeSecondDifferenceSecondThird
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  zeroPaddedSecondDifferenceSecond
    (zeroPaddedSecondDifferenceThird
      (dyadicHodgeCubeCoefficient scale component coordinate input)
      (dyadicHodgeApertureCount scale))
    (dyadicHodgeApertureCount scale) firstIndex secondIndex thirdIndex

/-- The coefficient receiver addressed by an arbitrary Boolean face.  Differences are applied in
the fixed chart order `third -> second -> first`; this is the same ordered owner used by the full
mixed receiver. -/
def dyadicHodgeCubeSubsetDifference
    (face : CoordinateFace 3) (scale : ℕ) (component coordinate input : Fin 3) :
    ℕ → ℕ → ℕ → ℂ :=
  let coefficient := dyadicHodgeCubeCoefficient scale component coordinate input
  let afterThird :=
    if (2 : Fin 3) ∈ face then
      zeroPaddedSecondDifferenceThird coefficient (dyadicHodgeApertureCount scale)
    else coefficient
  let afterSecond :=
    if (1 : Fin 3) ∈ face then
      zeroPaddedSecondDifferenceSecond afterThird (dyadicHodgeApertureCount scale)
    else afterThird
  if (0 : Fin 3) ∈ face then
    zeroPaddedSecondDifferenceFirst afterSecond (dyadicHodgeApertureCount scale)
  else afterSecond

/-- Each active coordinate widens its finite zero-padded aperture by two addresses. -/
def dyadicHodgeSubsetCount (face : CoordinateFace 3) (scale : ℕ) (axis : Fin 3) : ℕ :=
  dyadicHodgeApertureCount scale + if axis ∈ face then 2 else 0

/-- The exact Abel factor carried by one Boolean coordinate face. -/
def dyadicHodgeSubsetGap (face : CoordinateFace 3) (q : UnitAddTorus (Fin 3)) : ℂ :=
  ∏ axis ∈ face, (1 - fourier 1 (q axis)) ^ 2

/-! ## Exact Abel returns on all eight faces -/

/-- Empty face: the direct kernel is already the centered finite synthesis. -/
theorem dyadicHodgeJacobianKernelEntry_emptyAbel
    (scale : ℕ) (component coordinate input : Fin 3)
    (q : UnitAddTorus (Fin 3)) :
    dyadicHodgeJacobianKernelEntry scale component coordinate input q =
      UnitAddTorus.mFourier (dyadicHodgeApertureBaseFrequency scale) q *
        finiteCharacterSynthesisThree
          (dyadicHodgeCubeCoefficient scale component coordinate input)
          (fourier 1 (q 0)) (fourier 1 (q 1)) (fourier 1 (q 2))
          (dyadicHodgeApertureCount scale) (dyadicHodgeApertureCount scale)
          (dyadicHodgeApertureCount scale) :=
  dyadicHodgeJacobianKernelEntry_eq_centeredSynthesis
    scale component coordinate input q

/-- Singleton face `{1}`. -/
theorem dyadicHodgeJacobianKernelEntry_secondAbel
    (scale : ℕ) (component coordinate input : Fin 3)
    (q : UnitAddTorus (Fin 3)) :
    (1 - fourier 1 (q 1)) ^ 2 *
        dyadicHodgeJacobianKernelEntry scale component coordinate input q =
      UnitAddTorus.mFourier (dyadicHodgeApertureBaseFrequency scale) q *
        finiteCharacterSynthesisThree
          (dyadicHodgeCubeSecondDifferenceSecond scale component coordinate input)
          (fourier 1 (q 0)) (fourier 1 (q 1)) (fourier 1 (q 2))
          (dyadicHodgeApertureCount scale) (dyadicHodgeApertureCount scale + 2)
          (dyadicHodgeApertureCount scale) := by
  rw [dyadicHodgeJacobianKernelEntry_eq_centeredSynthesis]
  unfold dyadicHodgeCubeSecondDifferenceSecond
  rw [finiteCharacterSynthesisThree_secondDifferenceSecond]
  ring

/-- Singleton face `{2}`. -/
theorem dyadicHodgeJacobianKernelEntry_thirdAbel
    (scale : ℕ) (component coordinate input : Fin 3)
    (q : UnitAddTorus (Fin 3)) :
    (1 - fourier 1 (q 2)) ^ 2 *
        dyadicHodgeJacobianKernelEntry scale component coordinate input q =
      UnitAddTorus.mFourier (dyadicHodgeApertureBaseFrequency scale) q *
        finiteCharacterSynthesisThree
          (dyadicHodgeCubeSecondDifferenceThird scale component coordinate input)
          (fourier 1 (q 0)) (fourier 1 (q 1)) (fourier 1 (q 2))
          (dyadicHodgeApertureCount scale) (dyadicHodgeApertureCount scale)
          (dyadicHodgeApertureCount scale + 2) := by
  rw [dyadicHodgeJacobianKernelEntry_eq_centeredSynthesis]
  unfold dyadicHodgeCubeSecondDifferenceThird
  rw [finiteCharacterSynthesisThree_secondDifferenceThird]
  ring

/-- Pair face `{0,1}`. -/
theorem dyadicHodgeJacobianKernelEntry_firstSecondAbel
    (scale : ℕ) (component coordinate input : Fin 3)
    (q : UnitAddTorus (Fin 3)) :
    (1 - fourier 1 (q 0)) ^ 2 * (1 - fourier 1 (q 1)) ^ 2 *
        dyadicHodgeJacobianKernelEntry scale component coordinate input q =
      UnitAddTorus.mFourier (dyadicHodgeApertureBaseFrequency scale) q *
        finiteCharacterSynthesisThree
          (dyadicHodgeCubeSecondDifferenceFirstSecond scale component coordinate input)
          (fourier 1 (q 0)) (fourier 1 (q 1)) (fourier 1 (q 2))
          (dyadicHodgeApertureCount scale + 2) (dyadicHodgeApertureCount scale + 2)
          (dyadicHodgeApertureCount scale) := by
  rw [dyadicHodgeJacobianKernelEntry_eq_centeredSynthesis]
  unfold dyadicHodgeCubeSecondDifferenceFirstSecond
  rw [finiteCharacterSynthesisThree_secondDifferenceFirst,
    finiteCharacterSynthesisThree_secondDifferenceSecond]
  ring

/-- Pair face `{0,2}`. -/
theorem dyadicHodgeJacobianKernelEntry_firstThirdAbel
    (scale : ℕ) (component coordinate input : Fin 3)
    (q : UnitAddTorus (Fin 3)) :
    (1 - fourier 1 (q 0)) ^ 2 * (1 - fourier 1 (q 2)) ^ 2 *
        dyadicHodgeJacobianKernelEntry scale component coordinate input q =
      UnitAddTorus.mFourier (dyadicHodgeApertureBaseFrequency scale) q *
        finiteCharacterSynthesisThree
          (dyadicHodgeCubeSecondDifferenceFirstThird scale component coordinate input)
          (fourier 1 (q 0)) (fourier 1 (q 1)) (fourier 1 (q 2))
          (dyadicHodgeApertureCount scale + 2) (dyadicHodgeApertureCount scale)
          (dyadicHodgeApertureCount scale + 2) := by
  rw [dyadicHodgeJacobianKernelEntry_eq_centeredSynthesis]
  unfold dyadicHodgeCubeSecondDifferenceFirstThird
  rw [finiteCharacterSynthesisThree_secondDifferenceFirst,
    finiteCharacterSynthesisThree_secondDifferenceThird]
  ring

/-- Pair face `{1,2}`. -/
theorem dyadicHodgeJacobianKernelEntry_secondThirdAbel
    (scale : ℕ) (component coordinate input : Fin 3)
    (q : UnitAddTorus (Fin 3)) :
    (1 - fourier 1 (q 1)) ^ 2 * (1 - fourier 1 (q 2)) ^ 2 *
        dyadicHodgeJacobianKernelEntry scale component coordinate input q =
      UnitAddTorus.mFourier (dyadicHodgeApertureBaseFrequency scale) q *
        finiteCharacterSynthesisThree
          (dyadicHodgeCubeSecondDifferenceSecondThird scale component coordinate input)
          (fourier 1 (q 0)) (fourier 1 (q 1)) (fourier 1 (q 2))
          (dyadicHodgeApertureCount scale) (dyadicHodgeApertureCount scale + 2)
          (dyadicHodgeApertureCount scale + 2) := by
  rw [dyadicHodgeJacobianKernelEntry_eq_centeredSynthesis]
  unfold dyadicHodgeCubeSecondDifferenceSecondThird
  rw [finiteCharacterSynthesisThree_secondDifferenceSecond,
    finiteCharacterSynthesisThree_secondDifferenceThird]
  ring

/-- **All eight faces in one theorem.**  The Abel gap, coefficient population, and three aperture
counts are selected by the same coordinate subset. -/
theorem dyadicHodgeJacobianKernelEntry_subsetAbel
    (face : CoordinateFace 3) (scale : ℕ) (component coordinate input : Fin 3)
    (q : UnitAddTorus (Fin 3)) :
    dyadicHodgeSubsetGap face q *
        dyadicHodgeJacobianKernelEntry scale component coordinate input q =
      UnitAddTorus.mFourier (dyadicHodgeApertureBaseFrequency scale) q *
        finiteCharacterSynthesisThree
          (dyadicHodgeCubeSubsetDifference face scale component coordinate input)
          (fourier 1 (q 0)) (fourier 1 (q 1)) (fourier 1 (q 2))
          (dyadicHodgeSubsetCount face scale 0)
          (dyadicHodgeSubsetCount face scale 1)
          (dyadicHodgeSubsetCount face scale 2) := by
  classical
  by_cases hzero : (0 : Fin 3) ∈ face <;>
    by_cases hone : (1 : Fin 3) ∈ face <;>
      by_cases htwo : (2 : Fin 3) ∈ face
  · have hface : face = ({0, 1, 2} : Finset (Fin 3)) := by
      ext axis
      fin_cases axis <;> simp [hzero, hone, htwo]
    subst face
    have hgap : dyadicHodgeSubsetGap ({0, 1, 2} : Finset (Fin 3)) q =
        (1 - fourier 1 (q 0)) ^ 2 * (1 - fourier 1 (q 1)) ^ 2 *
          (1 - fourier 1 (q 2)) ^ 2 := by
      simp [dyadicHodgeSubsetGap, Finset.prod_insert]
      ring
    have hpopulation :
        dyadicHodgeCubeSubsetDifference ({0, 1, 2} : Finset (Fin 3))
            scale component coordinate input =
          dyadicHodgeCubeSecondDifferenceAll scale component coordinate input := by
      funext firstIndex secondIndex thirdIndex
      rfl
    rw [hgap, hpopulation]
    simpa [dyadicHodgeSubsetCount] using
      dyadicHodgeJacobianKernelEntry_tripleAbel
        scale component coordinate input q
  · have hface : face = ({0, 1} : Finset (Fin 3)) := by
      ext axis
      fin_cases axis <;> simp [hzero, hone, htwo]
    subst face
    have hpopulation :
        dyadicHodgeCubeSubsetDifference ({0, 1} : Finset (Fin 3))
            scale component coordinate input =
          dyadicHodgeCubeSecondDifferenceFirstSecond
            scale component coordinate input := by
      funext firstIndex secondIndex thirdIndex
      rfl
    rw [hpopulation]
    simpa [dyadicHodgeSubsetGap, dyadicHodgeSubsetCount,
      Finset.prod_insert] using
        dyadicHodgeJacobianKernelEntry_firstSecondAbel
          scale component coordinate input q
  · have hface : face = ({0, 2} : Finset (Fin 3)) := by
      ext axis
      fin_cases axis <;> simp [hzero, hone, htwo]
    subst face
    have hpopulation :
        dyadicHodgeCubeSubsetDifference ({0, 2} : Finset (Fin 3))
            scale component coordinate input =
          dyadicHodgeCubeSecondDifferenceFirstThird
            scale component coordinate input := by
      funext firstIndex secondIndex thirdIndex
      rfl
    rw [hpopulation]
    simpa [dyadicHodgeSubsetGap, dyadicHodgeSubsetCount,
      Finset.prod_insert] using
        dyadicHodgeJacobianKernelEntry_firstThirdAbel
          scale component coordinate input q
  · have hface : face = ({0} : Finset (Fin 3)) := by
      ext axis
      fin_cases axis <;> simp [hzero, hone, htwo]
    subst face
    have hpopulation :
        dyadicHodgeCubeSubsetDifference ({0} : Finset (Fin 3))
            scale component coordinate input =
          dyadicHodgeCubeSecondDifferenceFirst scale component coordinate input := by
      funext firstIndex secondIndex thirdIndex
      rfl
    rw [hpopulation]
    simpa [dyadicHodgeSubsetGap, dyadicHodgeSubsetCount,
      Finset.prod_insert] using
        dyadicHodgeJacobianKernelEntry_firstAbel
          scale component coordinate input q
  · have hface : face = ({1, 2} : Finset (Fin 3)) := by
      ext axis
      fin_cases axis <;> simp [hzero, hone, htwo]
    subst face
    have hpopulation :
        dyadicHodgeCubeSubsetDifference ({1, 2} : Finset (Fin 3))
            scale component coordinate input =
          dyadicHodgeCubeSecondDifferenceSecondThird
            scale component coordinate input := by
      funext firstIndex secondIndex thirdIndex
      rfl
    rw [hpopulation]
    simpa [dyadicHodgeSubsetGap, dyadicHodgeSubsetCount,
      Finset.prod_insert] using
        dyadicHodgeJacobianKernelEntry_secondThirdAbel
          scale component coordinate input q
  · have hface : face = ({1} : Finset (Fin 3)) := by
      ext axis
      fin_cases axis <;> simp [hzero, hone, htwo]
    subst face
    have hpopulation :
        dyadicHodgeCubeSubsetDifference ({1} : Finset (Fin 3))
            scale component coordinate input =
          dyadicHodgeCubeSecondDifferenceSecond scale component coordinate input := by
      funext firstIndex secondIndex thirdIndex
      rfl
    rw [hpopulation]
    simpa [dyadicHodgeSubsetGap, dyadicHodgeSubsetCount,
      Finset.prod_insert] using
        dyadicHodgeJacobianKernelEntry_secondAbel
          scale component coordinate input q
  · have hface : face = ({2} : Finset (Fin 3)) := by
      ext axis
      fin_cases axis <;> simp [hzero, hone, htwo]
    subst face
    have hpopulation :
        dyadicHodgeCubeSubsetDifference ({2} : Finset (Fin 3))
            scale component coordinate input =
          dyadicHodgeCubeSecondDifferenceThird scale component coordinate input := by
      funext firstIndex secondIndex thirdIndex
      rfl
    rw [hpopulation]
    simpa [dyadicHodgeSubsetGap, dyadicHodgeSubsetCount,
      Finset.prod_insert] using
        dyadicHodgeJacobianKernelEntry_thirdAbel
          scale component coordinate input q
  · have hface : face = (∅ : Finset (Fin 3)) := by
      ext axis
      fin_cases axis <;> simp [hzero, hone, htwo]
    subst face
    simpa [dyadicHodgeSubsetGap, dyadicHodgeCubeSubsetDifference,
      dyadicHodgeSubsetCount] using
        dyadicHodgeJacobianKernelEntry_emptyAbel
          scale component coordinate input q

/-- The seven identities above together with the already proved first-coordinate and full mixed
identities inhabit every member of the three-coordinate Boolean receiver cube. -/
theorem eight_subset_abel_receivers_complete :
    (coordinateFaces 3).card = 8 ∧
      ∀ face ∈ coordinateFaces 3, ∀ scale component coordinate input q,
        dyadicHodgeSubsetGap face q *
            dyadicHodgeJacobianKernelEntry scale component coordinate input q =
          UnitAddTorus.mFourier (dyadicHodgeApertureBaseFrequency scale) q *
            finiteCharacterSynthesisThree
              (dyadicHodgeCubeSubsetDifference face scale component coordinate input)
              (fourier 1 (q 0)) (fourier 1 (q 1)) (fourier 1 (q 2))
              (dyadicHodgeSubsetCount face scale 0)
              (dyadicHodgeSubsetCount face scale 1)
              (dyadicHodgeSubsetCount face scale 2) := by
  refine ⟨card_coordinateFaces_three, ?_⟩
  intro face _hface
  exact dyadicHodgeJacobianKernelEntry_subsetAbel face

/-! ## The receiver-visible coefficient mass -/

/-- The complete absolute coefficient population behind one Boolean face. -/
def dyadicHodgeSubsetMass
    (face : CoordinateFace 3) (scale : ℕ) (component coordinate input : Fin 3) : ℝ :=
  ∑ firstIndex ∈ Finset.range (dyadicHodgeSubsetCount face scale 0),
    ∑ secondIndex ∈ Finset.range (dyadicHodgeSubsetCount face scale 1),
      ∑ thirdIndex ∈ Finset.range (dyadicHodgeSubsetCount face scale 2),
        ‖dyadicHodgeCubeSubsetDifference face scale component coordinate input
          firstIndex secondIndex thirdIndex‖

/-- Every subset Abel return is controlled with constant one by its complete coefficient mass.
No character factor is divided, so this statement remains valid on every singular coordinate
subtorus. -/
theorem norm_dyadicHodgeSubsetGap_mul_kernelEntry_le_mass
    (face : CoordinateFace 3) (scale : ℕ) (component coordinate input : Fin 3)
    (q : UnitAddTorus (Fin 3)) :
    ‖dyadicHodgeSubsetGap face q *
        dyadicHodgeJacobianKernelEntry scale component coordinate input q‖ ≤
      dyadicHodgeSubsetMass face scale component coordinate input := by
  rw [dyadicHodgeJacobianKernelEntry_subsetAbel, norm_mul]
  have hbase :
      ‖UnitAddTorus.mFourier (dyadicHodgeApertureBaseFrequency scale) q‖ = 1 := by
    simp [UnitAddTorus.mFourier, norm_prod, Circle.norm_coe]
  rw [hbase, one_mul]
  unfold dyadicHodgeSubsetMass
  apply norm_finiteCharacterSynthesisThree_le_mass
  all_goals rw [fourier_apply]
  all_goals exact Circle.norm_coe _

section Audit

#print axioms dyadicHodgeJacobianKernelEntry_secondAbel
#print axioms dyadicHodgeJacobianKernelEntry_thirdAbel
#print axioms dyadicHodgeJacobianKernelEntry_firstSecondAbel
#print axioms dyadicHodgeJacobianKernelEntry_firstThirdAbel
#print axioms dyadicHodgeJacobianKernelEntry_secondThirdAbel
#print axioms dyadicHodgeJacobianKernelEntry_subsetAbel
#print axioms eight_subset_abel_receivers_complete
#print axioms norm_dyadicHodgeSubsetGap_mul_kernelEntry_le_mass

end Audit

end Soma.Holonics.Millennium.NavierStokesDyadicHodgeSubsetReceivers
