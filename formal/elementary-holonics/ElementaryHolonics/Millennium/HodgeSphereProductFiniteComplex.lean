import ElementaryHolonics.Millennium.HodgeProjectiveLineSingularReduction
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.Homotopy

/-!
# The finite degree-two complex behind the sphere-product Hodge passage

The preceding construction reduces the actual projective-line product to `S² × S²` in genuine
rational singular homology.  This file now replaces the informal phrase "the cellular model is
`ℚ²`" by an object in the same category as the singular chain complex:

* the degree-two cellular carrier is a rational module with the two ruling cells as coordinates;
* the full even cellular complex retains the degree-zero cell, both degree-two cells, and the
  degree-four cell;
* its categorical homology in degree two is computed exactly;
* a chain-homotopy equivalence from the genuine singular complex to this finite complex is shown
  to construct the required cellular-to-singular comparison, and therefore the comparison for the
  actual projective surface.

The unresolved object after this file is consequently chain-level and explicit: construct the
two fundamental singular cycles and the contraction/reduction homotopies.  No homology-level
isomorphism or Hodge conclusion is stored as a field here.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeSphereProductFiniteComplex

open CategoryTheory
open Soma.Holonics.Millennium.HodgeProjectiveLineProduct
open Soma.Holonics.Millennium.HodgeProjectiveLineCellularCohomology
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction

/-- [definition] The two addressed real-dimension-two cells as a rational module. -/
def degreeTwoCellModule : ModuleCat ℚ := ModuleCat.of ℚ Bidegree

/-- [definition] The cellular module in every degree.  The `0`, `2`, and `4` occurrences are kept
as different addressed degrees even though the outer two have the same scalar coordinate type. -/
def surfaceCellModule : ℕ → ModuleCat ℚ
  | 0 => ModuleCat.of ℚ ℚ
  | 2 => degreeTwoCellModule
  | 4 => ModuleCat.of ℚ ℚ
  | _ => ModuleCat.of ℚ (Fin 0 → ℚ)

/-- [definition] The complete even cellular chain complex of the product cell filtration.

Every differential is zero because there are no odd-dimensional cells.  Retaining degrees zero
and four is essential: deleting them would make a chain-homotopy equivalence with the genuine
surface singular complex impossible. -/
def surfaceCellComplex : ChainComplex (ModuleCat ℚ) ℕ :=
  ChainComplex.of surfaceCellModule (fun _ => 0) (fun _ => by simp)

theorem surfaceCellComplex_d (degree : ℕ) :
    surfaceCellComplex.d (degree + 1) degree = 0 := by
  exact ChainComplex.of_d surfaceCellModule (fun _ => 0) degree

/-- [proved-derived; formal-checked] The categorical degree-two homology of the complete even
cellular complex is exactly the two-cell module. -/
def surfaceCellHomologyIsoBidegree :
    surfaceCellComplex.homology 2 ≅ degreeTwoCellModule :=
  (surfaceCellComplex.isoHomologyπ 3 2 (by simp)
      (surfaceCellComplex_d 2)).symm ≪≫
    surfaceCellComplex.iCyclesIso 2 1 (by simp)
      (surfaceCellComplex_d 1)

/-- [proved-derived; formal-checked] The preceding categorical isomorphism as a rational linear
equivalence. -/
def surfaceCellHomologyEquivBidegree :
    surfaceCellComplex.homology 2 ≃ₗ[ℚ] Bidegree :=
  surfaceCellHomologyIsoBidegree.toLinearEquiv

/-! ## One graded computation, not one proof per degree -/

/-- [proved-derived; formal-checked] Because every differential in the cellular carrier is zero,
its homology is its chain module in **every** degree.  This is the single graded theorem behind the
separate degree-zero, degree-two, degree-four, and vanishing faces; those faces are projections of
this equivalence rather than independent calculations. -/
def surfaceCellHomologyIsoModule :
    ∀ degree : ℕ, surfaceCellComplex.homology degree ≅ surfaceCellModule degree
  | 0 =>
      (surfaceCellComplex.isoHomologyπ 1 0 (by simp)
        (surfaceCellComplex_d 0)).symm ≪≫
        surfaceCellComplex.cycles₀Iso
  | degree + 1 =>
      (surfaceCellComplex.isoHomologyπ (degree + 2) (degree + 1) (by simp)
        (surfaceCellComplex_d (degree + 1))).symm ≪≫
        surfaceCellComplex.iCyclesIso (degree + 1) degree (by simp)
          (surfaceCellComplex_d degree)

/-- [proved-derived; formal-checked] The preceding simultaneous categorical computation as a
rational linear equivalence at an arbitrary receiver degree. -/
def surfaceCellHomologyEquivModule (degree : ℕ) :
    surfaceCellComplex.homology degree ≃ₗ[ℚ] surfaceCellModule degree :=
  (surfaceCellHomologyIsoModule degree).toLinearEquiv

/-- [definition] The genuine rational singular chain complex of `S² × S²`. -/
abbrev SphereProductSingularChainComplex : ChainComplex (ModuleCat ℚ) ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
    rationalCoefficient).obj sphereProductTopCat

/-- [definition] The exact chain-level residual.  Its fields are chain maps and chain homotopies,
not a predeclared homology comparison. -/
abbrev SphereProductCellularReduction :=
  HomotopyEquiv SphereProductSingularChainComplex surfaceCellComplex

/-- [proved-derived; formal-checked] One chain-homotopy coarse graining computes the complete
graded rational singular homology family at once.  No degree is privileged in the construction;
specialized `H_i` statements are receiver projections of this family. -/
def singularHomologyEquivCellModule (reduction : SphereProductCellularReduction)
    (degree : ℕ) :
    RationalSingularHomology degree sphereProductTopCat ≃ₗ[ℚ]
      surfaceCellModule degree :=
  (reduction.toHomologyIso degree).toLinearEquiv.trans
    (surfaceCellHomologyEquivModule degree)

/-- [proved-derived; formal-checked] A chain-level reduction computes the genuine singular
degree-two homology as the two-cell bidegree carrier. -/
def singularHomologyEquivBidegree (reduction : SphereProductCellularReduction) :
    RationalSingularHomology 2 sphereProductTopCat ≃ₗ[ℚ] Bidegree :=
  (reduction.toHomologyIso 2).toLinearEquiv.trans surfaceCellHomologyEquivBidegree

/-- [proved-derived; formal-checked] A chain-level reduction constructs the exact comparison
needed by the geometric Hodge passage; no homology equivalence is separately assumed. -/
def sphereProductComparisonOfReduction (reduction : SphereProductCellularReduction) :
    SphereProductDegreeTwoComparison :=
  cellularH2BidegreeEquiv.trans (singularHomologyEquivBidegree reduction).symm

/-- [proved-derived; formal-checked] The same chain-level witness returns the comparison on the
actual projective-line product through the already constructed homeomorphism. -/
def surfaceComparisonOfReduction (reduction : SphereProductCellularReduction) :
    SurfaceDegreeTwoComparison :=
  surfaceComparisonOfSphereProduct (sphereProductComparisonOfReduction reduction)

/-- [proved-derived; formal-checked] Constructing the chain reduction is strictly sufficient for
inhabiting both complete comparison populations. -/
theorem comparisonPopulations_nonempty (reduction : SphereProductCellularReduction) :
    Nonempty SphereProductDegreeTwoComparison ∧ Nonempty SurfaceDegreeTwoComparison :=
  ⟨⟨sphereProductComparisonOfReduction reduction⟩,
    ⟨surfaceComparisonOfReduction reduction⟩⟩

section Audit

#print axioms surfaceCellComplex_d
#print axioms surfaceCellHomologyIsoBidegree
#print axioms surfaceCellHomologyEquivBidegree
#print axioms surfaceCellHomologyIsoModule
#print axioms surfaceCellHomologyEquivModule
#print axioms singularHomologyEquivCellModule
#print axioms singularHomologyEquivBidegree
#print axioms sphereProductComparisonOfReduction
#print axioms surfaceComparisonOfReduction
#print axioms comparisonPopulations_nonempty

end Audit

end Soma.Holonics.Millennium.HodgeSphereProductFiniteComplex
