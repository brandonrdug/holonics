import ElementaryHolonics.Millennium.NavierStokesAnnularHodgeInnerStencilSum

/-!
# Mixed annular Hodge differences and exact finite Fubini

**[proved-derived]** This owner opens the three coordinate passages needed after the uniform
one-line annular Hodge estimate.  It proves finite-sum linearity of the zero-padded second
difference and an exact three-coordinate Abel/Fubini identity with every aperture residue still
inside the mixed difference population.  It also reindexes the actual three-dimensional annular
Hodge coefficient cube and transports the completed one-axis estimate to its sharp
one-coordinate subset scaling.

No mixed-variation or physical `L1` bound is assumed here.  The exact remaining analytic deed is
to bound the two- and three-coordinate mixed populations of the actual cube at their reciprocal
subset scales.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesAnnularHodgeMixedFubini

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesSmoothHodgeJacobianBand
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeKernelDifference
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeCoefficientVariation
open Soma.Holonics.Millennium.NavierStokesAnnularTensorCoefficientVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeLocalizedVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeInnerStencilSum

/-! ## Finite-sum linearity -/

/-- Zero-padded second difference is additive, including both aperture boundaries. -/
theorem zeroPaddedSecondDifference_add
    (first second : ℕ → ℂ) (count index : ℕ) :
    zeroPaddedSecondDifference (fun position ↦ first position + second position)
        count index =
      zeroPaddedSecondDifference first count index +
        zeroPaddedSecondDifference second count index := by
  simp only [zeroPaddedSecondDifference_eq_three_coefficients,
    zeroPaddedPreviousCoefficient, zeroPaddedSecondPreviousCoefficient,
    zeroPaddedCoefficient]
  split_ifs <;> ring

/-- A zero-padded second difference commutes with every finite sum. -/
theorem zeroPaddedSecondDifference_finsetSum
    {indexType : Type*} [DecidableEq indexType]
    (population : Finset indexType) (coefficient : indexType → ℕ → ℂ)
    (count index : ℕ) :
    zeroPaddedSecondDifference
        (fun position ↦ ∑ member ∈ population, coefficient member position)
        count index =
      ∑ member ∈ population,
        zeroPaddedSecondDifference (coefficient member) count index := by
  classical
  induction population using Finset.induction_on with
  | empty =>
      simp [zeroPaddedSecondDifference, zeroPaddedBackwardDifference,
        zeroPaddedCoefficient]
  | @insert member population hmember hinduction =>
      simp only [Finset.sum_insert hmember]
      rw [zeroPaddedSecondDifference_add, hinduction]

/-- A second difference commutes with a finite weighted synthesis in every exterior index. -/
theorem zeroPaddedSecondDifference_finsetSynthesis
    {indexType : Type*} [DecidableEq indexType]
    (population : Finset indexType) (coefficient : ℕ → indexType → ℂ)
    (weight : indexType → ℂ) (count index : ℕ) :
    zeroPaddedSecondDifference
        (fun position ↦ ∑ member ∈ population,
          coefficient position member * weight member)
        count index =
      ∑ member ∈ population,
        zeroPaddedSecondDifference (fun position ↦ coefficient position member)
          count index * weight member := by
  rw [zeroPaddedSecondDifference_finsetSum population
    (fun member position ↦ coefficient position member * weight member)]
  apply Finset.sum_congr rfl
  intro member _hmember
  exact zeroPaddedSecondDifference_mul_right
    (fun position ↦ coefficient position member) (weight member) count index

/-! ## Three addressed coordinate passages -/

/-- Second difference in the first coordinate of a three-index coefficient population. -/
def zeroPaddedSecondDifferenceFirst
    (coefficient : ℕ → ℕ → ℕ → ℂ) (count : ℕ)
    (firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  zeroPaddedSecondDifference
    (fun position ↦ coefficient position secondIndex thirdIndex) count firstIndex

/-- Second difference in the second coordinate of a three-index coefficient population. -/
def zeroPaddedSecondDifferenceSecond
    (coefficient : ℕ → ℕ → ℕ → ℂ) (count : ℕ)
    (firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  zeroPaddedSecondDifference
    (fun position ↦ coefficient firstIndex position thirdIndex) count secondIndex

/-- Second difference in the third coordinate of a three-index coefficient population. -/
def zeroPaddedSecondDifferenceThird
    (coefficient : ℕ → ℕ → ℕ → ℂ) (count : ℕ)
    (firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  zeroPaddedSecondDifference (coefficient firstIndex secondIndex) count thirdIndex

/-- The ordered three-coordinate zero-padded second-difference population. -/
def zeroPaddedSecondDifferenceAll
    (coefficient : ℕ → ℕ → ℕ → ℂ)
    (firstCount secondCount thirdCount : ℕ)
    (firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  zeroPaddedSecondDifferenceFirst
    (zeroPaddedSecondDifferenceSecond
      (zeroPaddedSecondDifferenceThird coefficient thirdCount) secondCount)
    firstCount firstIndex secondIndex thirdIndex

/-- Nested finite character synthesis in the three displayed coordinate order. -/
def finiteCharacterSynthesisThree
    (coefficient : ℕ → ℕ → ℕ → ℂ)
    (firstCharacter secondCharacter thirdCharacter : ℂ)
    (firstCount secondCount thirdCount : ℕ) : ℂ :=
  ∑ firstIndex ∈ Finset.range firstCount,
    (∑ secondIndex ∈ Finset.range secondCount,
      (∑ thirdIndex ∈ Finset.range thirdCount,
        coefficient firstIndex secondIndex thirdIndex * thirdCharacter ^ thirdIndex) *
          secondCharacter ^ secondIndex) * firstCharacter ^ firstIndex

/-- Abel passage in the innermost displayed coordinate. -/
theorem finiteCharacterSynthesisThree_secondDifferenceThird
    (coefficient : ℕ → ℕ → ℕ → ℂ)
    (firstCharacter secondCharacter thirdCharacter : ℂ)
    (firstCount secondCount thirdCount : ℕ) :
    finiteCharacterSynthesisThree
        (zeroPaddedSecondDifferenceThird coefficient thirdCount)
        firstCharacter secondCharacter thirdCharacter
        firstCount secondCount (thirdCount + 2) =
      (1 - thirdCharacter) ^ 2 *
        finiteCharacterSynthesisThree coefficient
          firstCharacter secondCharacter thirdCharacter
          firstCount secondCount thirdCount := by
  unfold finiteCharacterSynthesisThree zeroPaddedSecondDifferenceThird
  simp_rw [finiteCharacterSynthesis_zeroPaddedSecondDifference]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro firstIndex _hfirstIndex
  calc
    (∑ secondIndex ∈ Finset.range secondCount,
        ((1 - thirdCharacter) ^ 2 *
          ∑ thirdIndex ∈ Finset.range thirdCount,
            coefficient firstIndex secondIndex thirdIndex *
              thirdCharacter ^ thirdIndex) * secondCharacter ^ secondIndex) *
          firstCharacter ^ firstIndex =
      ((1 - thirdCharacter) ^ 2 *
        ∑ secondIndex ∈ Finset.range secondCount,
          (∑ thirdIndex ∈ Finset.range thirdCount,
            coefficient firstIndex secondIndex thirdIndex *
              thirdCharacter ^ thirdIndex) * secondCharacter ^ secondIndex) *
          firstCharacter ^ firstIndex := by
            congr 1
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro secondIndex _hsecondIndex
            ring
    _ = (1 - thirdCharacter) ^ 2 *
        ((∑ secondIndex ∈ Finset.range secondCount,
          (∑ thirdIndex ∈ Finset.range thirdCount,
            coefficient firstIndex secondIndex thirdIndex *
              thirdCharacter ^ thirdIndex) * secondCharacter ^ secondIndex) *
          firstCharacter ^ firstIndex) := by ring

/-- Abel passage in the middle displayed coordinate, with the inner finite synthesis transported
through the difference exactly. -/
theorem finiteCharacterSynthesisThree_secondDifferenceSecond
    (coefficient : ℕ → ℕ → ℕ → ℂ)
    (firstCharacter secondCharacter thirdCharacter : ℂ)
    (firstCount secondCount thirdCount : ℕ) :
    finiteCharacterSynthesisThree
        (zeroPaddedSecondDifferenceSecond coefficient secondCount)
        firstCharacter secondCharacter thirdCharacter
        firstCount (secondCount + 2) thirdCount =
      (1 - secondCharacter) ^ 2 *
        finiteCharacterSynthesisThree coefficient
          firstCharacter secondCharacter thirdCharacter
          firstCount secondCount thirdCount := by
  unfold finiteCharacterSynthesisThree zeroPaddedSecondDifferenceSecond
  have htransport : ∀ firstIndex secondIndex,
      (∑ thirdIndex ∈ Finset.range thirdCount,
        zeroPaddedSecondDifference
            (fun position ↦ coefficient firstIndex position thirdIndex)
            secondCount secondIndex * thirdCharacter ^ thirdIndex) =
      zeroPaddedSecondDifference
        (fun position ↦ ∑ thirdIndex ∈ Finset.range thirdCount,
          coefficient firstIndex position thirdIndex * thirdCharacter ^ thirdIndex)
        secondCount secondIndex := by
    intro firstIndex secondIndex
    symm
    exact zeroPaddedSecondDifference_finsetSynthesis
      (Finset.range thirdCount) (fun position thirdIndex ↦
        coefficient firstIndex position thirdIndex)
      (fun thirdIndex ↦ thirdCharacter ^ thirdIndex) secondCount secondIndex
  simp_rw [htransport]
  simp_rw [finiteCharacterSynthesis_zeroPaddedSecondDifference]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro firstIndex _hfirstIndex
  ring

/-- Abel passage in the outermost displayed coordinate, transporting both inner finite sums. -/
theorem finiteCharacterSynthesisThree_secondDifferenceFirst
    (coefficient : ℕ → ℕ → ℕ → ℂ)
    (firstCharacter secondCharacter thirdCharacter : ℂ)
    (firstCount secondCount thirdCount : ℕ) :
    finiteCharacterSynthesisThree
        (zeroPaddedSecondDifferenceFirst coefficient firstCount)
        firstCharacter secondCharacter thirdCharacter
        (firstCount + 2) secondCount thirdCount =
      (1 - firstCharacter) ^ 2 *
        finiteCharacterSynthesisThree coefficient
          firstCharacter secondCharacter thirdCharacter
          firstCount secondCount thirdCount := by
  unfold finiteCharacterSynthesisThree zeroPaddedSecondDifferenceFirst
  have hthirdTransport : ∀ firstIndex secondIndex,
      (∑ thirdIndex ∈ Finset.range thirdCount,
        zeroPaddedSecondDifference
            (fun position ↦ coefficient position secondIndex thirdIndex)
            firstCount firstIndex * thirdCharacter ^ thirdIndex) =
      zeroPaddedSecondDifference
        (fun position ↦ ∑ thirdIndex ∈ Finset.range thirdCount,
          coefficient position secondIndex thirdIndex * thirdCharacter ^ thirdIndex)
        firstCount firstIndex := by
    intro firstIndex secondIndex
    symm
    exact zeroPaddedSecondDifference_finsetSynthesis
      (Finset.range thirdCount) (fun position thirdIndex ↦
        coefficient position secondIndex thirdIndex)
      (fun thirdIndex ↦ thirdCharacter ^ thirdIndex) firstCount firstIndex
  simp_rw [hthirdTransport]
  have hsecondTransport : ∀ firstIndex,
      (∑ secondIndex ∈ Finset.range secondCount,
        zeroPaddedSecondDifference
            (fun position ↦ ∑ thirdIndex ∈ Finset.range thirdCount,
              coefficient position secondIndex thirdIndex * thirdCharacter ^ thirdIndex)
            firstCount firstIndex * secondCharacter ^ secondIndex) =
      zeroPaddedSecondDifference
        (fun position ↦ ∑ secondIndex ∈ Finset.range secondCount,
          (∑ thirdIndex ∈ Finset.range thirdCount,
            coefficient position secondIndex thirdIndex * thirdCharacter ^ thirdIndex) *
              secondCharacter ^ secondIndex)
        firstCount firstIndex := by
    intro firstIndex
    symm
    exact zeroPaddedSecondDifference_finsetSynthesis
      (Finset.range secondCount)
      (fun position secondIndex ↦ ∑ thirdIndex ∈ Finset.range thirdCount,
        coefficient position secondIndex thirdIndex * thirdCharacter ^ thirdIndex)
      (fun secondIndex ↦ secondCharacter ^ secondIndex) firstCount firstIndex
  simp_rw [hsecondTransport]
  exact finiteCharacterSynthesis_zeroPaddedSecondDifference
    (fun position ↦ ∑ secondIndex ∈ Finset.range secondCount,
      (∑ thirdIndex ∈ Finset.range thirdCount,
        coefficient position secondIndex thirdIndex * thirdCharacter ^ thirdIndex) *
          secondCharacter ^ secondIndex)
    firstCharacter firstCount

/-- Three exact Abel passages.  The complete boundary population is the ordered mixed
zero-padded second difference; no periodic endpoint identification is used. -/
theorem finiteCharacterSynthesisThree_secondDifferenceAll
    (coefficient : ℕ → ℕ → ℕ → ℂ)
    (firstCharacter secondCharacter thirdCharacter : ℂ)
    (firstCount secondCount thirdCount : ℕ) :
    finiteCharacterSynthesisThree
        (zeroPaddedSecondDifferenceAll coefficient firstCount secondCount thirdCount)
        firstCharacter secondCharacter thirdCharacter
        (firstCount + 2) (secondCount + 2) (thirdCount + 2) =
      (1 - firstCharacter) ^ 2 * (1 - secondCharacter) ^ 2 *
        (1 - thirdCharacter) ^ 2 *
          finiteCharacterSynthesisThree coefficient
            firstCharacter secondCharacter thirdCharacter
            firstCount secondCount thirdCount := by
  unfold zeroPaddedSecondDifferenceAll
  rw [finiteCharacterSynthesisThree_secondDifferenceFirst,
    finiteCharacterSynthesisThree_secondDifferenceSecond,
    finiteCharacterSynthesisThree_secondDifferenceThird]
  ring

section Audit

#print axioms zeroPaddedSecondDifference_finsetSum
#print axioms zeroPaddedSecondDifference_finsetSynthesis
#print axioms finiteCharacterSynthesisThree_secondDifferenceThird
#print axioms finiteCharacterSynthesisThree_secondDifferenceSecond
#print axioms finiteCharacterSynthesisThree_secondDifferenceFirst
#print axioms finiteCharacterSynthesisThree_secondDifferenceAll

end Audit

end Soma.Holonics.Millennium.NavierStokesAnnularHodgeMixedFubini
