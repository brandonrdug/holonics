import HolonicsResearch.Foundation.ProductDegreeTwoNormalization

/-!
# Product degree-two realization

The actual product simplex chart transports the retained low-degree contractions and degree-two normalization through all faces. This remains the importing consumer and retains every original full-owner axiom selector.

[agent-inferred] Declarations moved once from ProductDegreeTwo along their
existing mathematical dependency. Their bodies, names and hypotheses are
unchanged; checked predecessor objects are reusable by the next consumer.
-/

noncomputable section

namespace Holonics.DiagonalChainTransport

open CategoryTheory
open Simplicial

/-! ## A genuine product simplicial set as the diagonal pair chart

The algebra above was intentionally independent of any chosen product presentation.  The next
object is the exact adapter it requires: every genuine product simplex is identified with its two
coordinate simplices, and the identification commutes with every face.  This is sufficient to
transport all low-degree contraction data; no point count or homology quotient enters. -/

/-- [definition] A source simplicial set whose complete simplices are the diagonal pairs of two
factor simplicial sets, with face transport retained as part of the datum. -/
structure ProductSimplexRealization (Product X Y : SSet) where
  simplexEquiv : ∀ degree : ℕ,
    FactorSimplex Product degree ≃ DiagonalOccurrence X Y degree
  face_naturality : ∀ {degree : ℕ} (omitted : Fin (degree + 2))
      (simplex : FactorSimplex Product (degree + 1)),
    simplexEquiv degree (face omitted simplex) =
      diagonalFace omitted (simplexEquiv (degree + 1) simplex)

/-- The complete finite current transported through a product-simplex realization. -/
def realizedProductCurrentEquiv {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y) (degree : ℕ) :
    FactorCurrent Product degree ≃ₗ[ℚ]
      Current (DiagonalOccurrence X Y degree) :=
  Finsupp.domLCongr (realization.simplexEquiv degree)

@[simp]
theorem realizedProductCurrentEquiv_generator {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y) {degree : ℕ}
    (simplex : FactorSimplex Product degree) :
    realizedProductCurrentEquiv realization degree (generator simplex) =
      generator (realization.simplexEquiv degree simplex) := by
  simp [realizedProductCurrentEquiv, Finsupp.domLCongr_apply,
    Finsupp.domCongr_apply, generator]

/-- [proved-derived; formal-checked] The genuine degree-one boundary is the diagonal pair
boundary under every product realization. -/
theorem realizedProductCurrentEquiv_boundary_one {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (current : FactorCurrent Product 1) :
    realizedProductCurrentEquiv realization 0
        (factorBoundary Product 0 current) =
      diagonalBoundaryOne X Y
        (realizedProductCurrentEquiv realization 1 current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [hleft, hright]
  | single simplex coefficient =>
      rw [show Finsupp.single simplex coefficient =
          coefficient • generator simplex by simp [generator]]
      simp only [map_smul, factorBoundary_generator,
        factorBoundaryAtom, map_sum, realizedProductCurrentEquiv_generator,
        diagonalBoundaryOne, extend_generator, diagonalBoundaryOneAtom]
      simp_rw [realization.face_naturality]
      rw [Fin.sum_univ_two]
      norm_num
      module

/-- [proved-derived; formal-checked] The genuine degree-two boundary is the complete diagonal
pair boundary, including all three faces. -/
theorem realizedProductCurrentEquiv_boundary_two {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (current : FactorCurrent Product 2) :
    realizedProductCurrentEquiv realization 1
        (factorBoundary Product 1 current) =
      diagonalBoundaryTwo X Y
        (realizedProductCurrentEquiv realization 2 current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [hleft, hright]
  | single simplex coefficient =>
      rw [show Finsupp.single simplex coefficient =
          coefficient • generator simplex by simp [generator]]
      simp only [map_smul, factorBoundary_generator,
        factorBoundaryAtom, map_sum, realizedProductCurrentEquiv_generator,
        diagonalBoundaryTwo, extend_generator, diagonalBoundaryTwoAtom]
      simp_rw [realization.face_naturality]
      rw [Fin.sum_univ_three]
      norm_num
      module

/-- [proved-derived; formal-checked] The genuine degree-three boundary is the complete four-face
diagonal pair boundary. -/
theorem realizedProductCurrentEquiv_boundary_three {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (current : FactorCurrent Product 3) :
    realizedProductCurrentEquiv realization 2
        (factorBoundary Product 2 current) =
      diagonalBoundaryThree X Y
        (realizedProductCurrentEquiv realization 3 current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [hleft, hright]
  | single simplex coefficient =>
      rw [show Finsupp.single simplex coefficient =
          coefficient • generator simplex by simp [generator]]
      simp only [map_smul, factorBoundary_generator,
        factorBoundaryAtom, map_sum, realizedProductCurrentEquiv_generator,
        diagonalBoundaryThree, extend_generator, diagonalBoundaryThreeAtom]
      simp_rw [realization.face_naturality]
      rw [Fin.sum_univ_four]
      norm_num
      module

/-- The first factor current extracted from one genuine product degree-two current. -/
def realizedProductFirstFactorDegreeTwoCurrent {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : FactorCurrent Product 2) : FactorCurrent X 2 :=
  productFirstFactorDegreeTwoCurrent datumX datumY
    (separateTwo X Y (realizedProductCurrentEquiv realization 2 current))

/-- The second factor current extracted from the same complete occurrence population. -/
def realizedProductSecondFactorDegreeTwoCurrent {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : FactorCurrent Product 2) : FactorCurrent Y 2 :=
  productSecondFactorDegreeTwoCurrent datumX datumY
    (separateTwo X Y (realizedProductCurrentEquiv realization 2 current))

theorem realizedProductSeparatedDegreeTwo_closed {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (current : FactorCurrent Product 2)
    (closed : factorBoundary Product 1 current = 0) :
    totalBoundaryTwo X Y
        (separateTwo X Y (realizedProductCurrentEquiv realization 2 current)) = 0 := by
  have diagonalClosed :
      diagonalBoundaryTwo X Y
          (realizedProductCurrentEquiv realization 2 current) = 0 := by
    rw [← realizedProductCurrentEquiv_boundary_two, closed, map_zero]
  have law := LinearMap.congr_fun (boundary_separateTwo X Y)
    (realizedProductCurrentEquiv realization 2 current)
  simpa only [LinearMap.comp_apply, diagonalClosed, map_zero] using law

theorem realizedProductFirstFactorDegreeTwoCurrent_closed {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : FactorCurrent Product 2)
    (closed : factorBoundary Product 1 current = 0) :
    factorBoundary X 1
        (realizedProductFirstFactorDegreeTwoCurrent
          realization datumX datumY current) = 0 := by
  exact productFirstFactorDegreeTwoCurrent_closed datumX datumY _
    (realizedProductSeparatedDegreeTwo_closed realization current closed)

theorem realizedProductSecondFactorDegreeTwoCurrent_closed {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : FactorCurrent Product 2)
    (closed : factorBoundary Product 1 current = 0) :
    factorBoundary Y 1
        (realizedProductSecondFactorDegreeTwoCurrent
          realization datumX datumY current) = 0 := by
  exact productSecondFactorDegreeTwoCurrent_closed datumX datumY _
    (realizedProductSeparatedDegreeTwo_closed realization current closed)

/-- The complete degree-three reconstruction witness returned in the genuine source chart. -/
def realizedProductDegreeTwoNormalizationFiller {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : FactorCurrent Product 2) : FactorCurrent Product 3 :=
  (realizedProductCurrentEquiv realization 3).symm
    (rejoinThree X Y
        (productDegreeTwoNormalizationFiller datumX datumY
          (separateTwo X Y
            (realizedProductCurrentEquiv realization 2 current))) -
      diagonalReconstructionFillerTwo X Y
        (realizedProductCurrentEquiv realization 2 current))

/-- [proved-derived; formal-checked] The complete product decomposition in the genuine simplex
chart.  The returned factor cycles are closed, and the displayed degree-three current witnesses
the difference between the source cycle and their two basepoint inclusions. -/
theorem realizedProductDegreeTwoNormalizationFiller_boundary {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : FactorCurrent Product 2)
    (closed : factorBoundary Product 1 current = 0) :
    factorBoundary Product 2
        (realizedProductDegreeTwoNormalizationFiller
          realization datumX datumY current) =
      current -
        (realizedProductCurrentEquiv realization 2).symm
          (rejoinTwo X Y
            (leftAxis
                (pairFirstBase datumX
                  (realizedProductSecondFactorDegreeTwoCurrent
                    realization datumX datumY current)) +
              rightAxis
                (pairSecondBase datumY
                  (realizedProductFirstFactorDegreeTwoCurrent
                    realization datumX datumY current)))) := by
  let diagonal := realizedProductCurrentEquiv realization 2 current
  let separated := separateTwo X Y diagonal
  have diagonalClosed : diagonalBoundaryTwo X Y diagonal = 0 := by
    dsimp [diagonal]
    rw [← realizedProductCurrentEquiv_boundary_two, closed, map_zero]
  have separatedClosed : totalBoundaryTwo X Y separated = 0 := by
    have law := LinearMap.congr_fun (boundary_separateTwo X Y) diagonal
    simpa only [LinearMap.comp_apply, diagonalClosed, map_zero] using law
  apply (realizedProductCurrentEquiv realization 2).injective
  rw [realizedProductCurrentEquiv_boundary_three]
  simp only [realizedProductDegreeTwoNormalizationFiller,
    LinearEquiv.apply_symm_apply, map_sub]
  change diagonalBoundaryThree X Y
        (rejoinThree X Y
          (productDegreeTwoNormalizationFiller datumX datumY separated)) -
      diagonalBoundaryThree X Y
        (diagonalReconstructionFillerTwo X Y diagonal) = _
  have rejoinBoundary := LinearMap.congr_fun (boundary_rejoinThree X Y)
    (productDegreeTwoNormalizationFiller datumX datumY separated)
  change diagonalBoundaryThree X Y
      (rejoinThree X Y
        (productDegreeTwoNormalizationFiller datumX datumY separated)) =
    rejoinTwo X Y
      (totalBoundaryThree X Y
        (productDegreeTwoNormalizationFiller datumX datumY separated)) at rejoinBoundary
  rw [rejoinBoundary,
    productDegreeTwoNormalizationFiller_boundary datumX datumY separated separatedClosed]
  have defectBoundary :=
    diagonalRoundTripDefectTwo_eq_boundary_of_cycle diagonal diagonalClosed
  change rejoinTwo X Y (separateTwo X Y diagonal) - diagonal =
    diagonalBoundaryThree X Y
      (diagonalReconstructionFillerTwo X Y diagonal) at defectBoundary
  rw [← defectBoundary]
  simp only [map_sub, map_add,
    realizedProductFirstFactorDegreeTwoCurrent,
    realizedProductSecondFactorDegreeTwoCurrent, diagonal, separated,
    LinearEquiv.apply_symm_apply]
  module

/-- [proved-derived; formal-checked] The product augmentation kills every diagonal one-boundary.
This is the exact statement that an oriented edge does not create or destroy its total degree-zero
population. -/
theorem productAugmentation_diagonalBoundaryOne {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : Current (DiagonalOccurrence X Y 1)) :
    productAugmentation datumX datumY
        (diagonalBoundaryOne X Y current) = 0 := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [hleft, hright]
  | single pair coefficient =>
      rcases pair with ⟨left, right⟩
      have leftEquality :
          datumX.augmentation (generator (face 0 left)) =
            datumX.augmentation (generator (face 1 left)) := by
        apply sub_eq_zero.mp
        simpa [factorBoundary, factorBoundaryAtom, Fin.sum_univ_two,
          sub_eq_add_neg] using
          datumX.augmentation_boundary_zero (generator left)
      have rightEquality :
          datumY.augmentation (generator (face 0 right)) =
            datumY.augmentation (generator (face 1 right)) := by
        apply sub_eq_zero.mp
        simpa [factorBoundary, factorBoundaryAtom, Fin.sum_univ_two,
          sub_eq_add_neg] using
          datumY.augmentation_boundary_zero (generator right)
      rw [show Finsupp.single (left, right) coefficient =
          coefficient • generator (left, right) by simp [generator]]
      simp only [map_smul, diagonalBoundaryOne, extend_generator,
        diagonalBoundaryOneAtom, map_sub, smul_sub]
      simp only [diagonalFace]
      rw [productAugmentation_generator, productAugmentation_generator]
      rw [leftEquality, rightEquality]
      module

/-- The retained basepoint in a genuine product chart. -/
def realizedProductBasepoint {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y) :
    FactorSimplex Product 0 :=
  (realization.simplexEquiv 0).symm (datumX.basepoint, datumY.basepoint)

@[simp]
theorem realizedProductCurrentEquiv_basepoint {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y) :
    realizedProductCurrentEquiv realization 0
        (generator (realizedProductBasepoint realization datumX datumY)) =
      generator (datumX.basepoint, datumY.basepoint) := by
  rw [realizedProductCurrentEquiv_generator]
  simp [realizedProductBasepoint]

/-- Product augmentation transported to the genuine source simplicial set. -/
def realizedProductAugmentation {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y) :
    FactorCurrent Product 0 →ₗ[ℚ] ℚ :=
  (productAugmentation datumX datumY).comp
    (realizedProductCurrentEquiv realization 0).toLinearMap

/-- Product degree-zero contraction transported back to the genuine source chart. -/
def realizedProductH0 {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y) :
    FactorCurrent Product 0 →ₗ[ℚ] FactorCurrent Product 1 :=
  (realizedProductCurrentEquiv realization 1).symm.toLinearMap.comp
    ((productH0Diagonal datumX datumY).comp
      (realizedProductCurrentEquiv realization 0).toLinearMap)

/-- Product degree-one contraction transported back to the genuine source chart. -/
def realizedProductH1 {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y) :
    FactorCurrent Product 1 →ₗ[ℚ] FactorCurrent Product 2 :=
  (realizedProductCurrentEquiv realization 2).symm.toLinearMap.comp
    ((productH1Diagonal datumX datumY).comp
      (realizedProductCurrentEquiv realization 1).toLinearMap)

/-- [proved-derived; formal-checked] Low-degree contraction data composes across a genuine
product realization.  The construction retains the coordinate-simplex equivalence, the complete
mixed-axis current, and both inverse current charts. -/
def realizedProductLowDegreeCurrentDatum {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y) :
    LowDegreeCurrentDatum Product where
  basepoint := realizedProductBasepoint realization datumX datumY
  augmentation := realizedProductAugmentation realization datumX datumY
  augmentation_basepoint := by
    change productAugmentation datumX datumY
        (realizedProductCurrentEquiv realization 0
          (generator (realizedProductBasepoint realization datumX datumY))) = 1
    rw [realizedProductCurrentEquiv_basepoint,
      productAugmentation_generator, datumX.augmentation_basepoint,
      datumY.augmentation_basepoint, one_mul]
  augmentation_boundary_zero := by
    intro current
    change productAugmentation datumX datumY
        (realizedProductCurrentEquiv realization 0
          (factorBoundary Product 0 current)) = 0
    rw [realizedProductCurrentEquiv_boundary_one,
      productAugmentation_diagonalBoundaryOne]
  boundary_boundary_zero := by
    intro current
    apply (realizedProductCurrentEquiv realization 0).injective
    rw [map_zero, realizedProductCurrentEquiv_boundary_one,
      realizedProductCurrentEquiv_boundary_two,
      diagonalBoundaryOne_diagonalBoundaryTwo datumX datumY]
  h0 := realizedProductH0 realization datumX datumY
  h0_boundary := by
    intro current
    apply (realizedProductCurrentEquiv realization 0).injective
    calc
      realizedProductCurrentEquiv realization 0
          (factorBoundary Product 0
            (realizedProductH0 realization datumX datumY current)) =
        diagonalBoundaryOne X Y
          (realizedProductCurrentEquiv realization 1
            (realizedProductH0 realization datumX datumY current)) :=
        realizedProductCurrentEquiv_boundary_one realization _
      _ = diagonalBoundaryOne X Y
          (productH0Diagonal datumX datumY
            (realizedProductCurrentEquiv realization 0 current)) := by
        apply congrArg (diagonalBoundaryOne X Y)
        simp only [realizedProductH0, LinearMap.comp_apply]
        exact (realizedProductCurrentEquiv realization 1).apply_symm_apply _
      _ = realizedProductCurrentEquiv realization 0 current -
          productAugmentation datumX datumY
              (realizedProductCurrentEquiv realization 0 current) •
            generator (datumX.basepoint, datumY.basepoint) :=
        diagonalBoundaryOne_productH0Diagonal datumX datumY _
      _ = realizedProductCurrentEquiv realization 0
          (current -
            realizedProductAugmentation realization datumX datumY current •
              generator
                (realizedProductBasepoint realization datumX datumY)) := by
        rw [map_sub, map_smul, realizedProductCurrentEquiv_basepoint]
        rfl
  h1 := realizedProductH1 realization datumX datumY
  h1_boundary_of_closed := by
    intro current closed
    apply (realizedProductCurrentEquiv realization 1).injective
    calc
      realizedProductCurrentEquiv realization 1
          (factorBoundary Product 1
            (realizedProductH1 realization datumX datumY current)) =
        diagonalBoundaryTwo X Y
          (realizedProductCurrentEquiv realization 2
            (realizedProductH1 realization datumX datumY current)) :=
        realizedProductCurrentEquiv_boundary_two realization _
      _ = diagonalBoundaryTwo X Y
          (productH1Diagonal datumX datumY
            (realizedProductCurrentEquiv realization 1 current)) := by
        apply congrArg (diagonalBoundaryTwo X Y)
        simp only [realizedProductH1, LinearMap.comp_apply]
        exact (realizedProductCurrentEquiv realization 2).apply_symm_apply _
      _ = realizedProductCurrentEquiv realization 1 current := by
        apply diagonalBoundaryTwo_productH1Diagonal_of_closed
        rw [← realizedProductCurrentEquiv_boundary_one, closed, map_zero]

section Audit

#print axioms diagonalBoundaryOne_productH0Diagonal
#print axioms totalBoundaryTwo_productTotalOneFilling
#print axioms diagonalBoundaryTwo_productH1Diagonal_of_closed
#print axioms productFirstFactorDegreeTwoCurrent_closed
#print axioms productSecondFactorDegreeTwoCurrent_closed
#print axioms leftOuterNormalizationCorrection_boundary
#print axioms rightOuterNormalizationCorrection_boundary
#print axioms productDegreeTwoNormalizationFiller_boundary
#print axioms coupledMiddleCorrection_reduces_to_outer
#print axioms totalBoundaryOne_totalBoundaryTwo
#print axioms diagonalBoundaryOne_diagonalBoundaryTwo
#print axioms realizedProductCurrentEquiv_boundary_one
#print axioms realizedProductCurrentEquiv_boundary_two
#print axioms realizedProductCurrentEquiv_boundary_three
#print axioms realizedProductFirstFactorDegreeTwoCurrent_closed
#print axioms realizedProductSecondFactorDegreeTwoCurrent_closed
#print axioms realizedProductDegreeTwoNormalizationFiller_boundary
#print axioms productAugmentation_diagonalBoundaryOne
#print axioms realizedProductLowDegreeCurrentDatum

end Audit

end Holonics.DiagonalChainTransport
