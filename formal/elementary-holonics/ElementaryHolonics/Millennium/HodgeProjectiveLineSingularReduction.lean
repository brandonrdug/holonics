import ElementaryHolonics.Millennium.HodgeProjectiveLineSegre
import Mathlib.Algebra.Category.ModuleCat.Topology.Homology
import Mathlib.AlgebraicTopology.SingularHomology.Basic

/-!
# Singular-homology reduction for the projective-line product

The actual carrier is already homeomorphic to `S² × S²`.  This file sends that homeomorphism
through Mathlib's rational singular-homology functor.  Consequently, in every degree, the genuine
singular homology of the projective surface is isomorphic to that of the sphere product.

For degree two we retain the exact missing comparison as a type of linear equivalences from the
constructed cellular `H²` carrier.  Composition with the functorial homeomorphism gives an
equivalence between:

* comparisons with singular degree two of the actual projective surface; and
* comparisons with singular degree two of `S² × S²`.

Thus topology/projectivization no longer belongs to the residual.  What remains is the explicit
sphere-product singular calculation (and then the cohomology/Hodge typing), not a missing library
name or an unspecified external comparison.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction

open CategoryTheory
open Soma.Holonics.Millennium.HodgeProjectiveLineProduct
open Soma.Holonics.Millennium.HodgeProjectiveLineCellularCohomology
open Soma.Holonics.Millennium.HodgeProjectiveLineTopology

/-- [definition] Rational coefficients as an object of the rational module category. -/
abbrev rationalCoefficient : ModuleCat ℚ := ModuleCat.of ℚ ℚ

/-- [definition] Genuine singular homology with rational coefficients. -/
abbrev RationalSingularHomology (degree : ℕ) (space : TopCat) : ModuleCat ℚ :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) degree).obj
    rationalCoefficient).obj space

/-- [definition] The actual topological projective-line product. -/
def surfaceTopCat : TopCat := TopCat.of Surface

/-- [definition] The receiving sphere product. -/
abbrev TwoSphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

def sphereProductTopCat : TopCat := TopCat.of (TwoSphere × TwoSphere)

/-- [proved-derived; formal-checked] The actual homeomorphism is an isomorphism in `TopCat`. -/
def surfaceSphereTopIso : surfaceTopCat ≅ sphereProductTopCat :=
  TopCat.isoOfHomeo surfaceHomeomorphSphereProduct

/-- [proved-derived; formal-checked] Rational singular homology is invariant under the constructed
homeomorphism in every degree. -/
def surfaceSingularHomologyIsoSphereProduct (degree : ℕ) :
    RationalSingularHomology degree surfaceTopCat ≅
      RationalSingularHomology degree sphereProductTopCat :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) degree).obj
    rationalCoefficient).mapIso surfaceSphereTopIso)

/-- [proved-derived; formal-checked] The same return as an exact rational linear equivalence. -/
def surfaceSingularHomologyEquivSphereProduct (degree : ℕ) :
    RationalSingularHomology degree surfaceTopCat ≃ₗ[ℚ]
      RationalSingularHomology degree sphereProductTopCat :=
  (surfaceSingularHomologyIsoSphereProduct degree).toLinearEquiv

/-- [definition] A complete comparison from the constructed degree-two cellular carrier to the
actual surface's genuine rational singular degree-two homology. -/
abbrev SurfaceDegreeTwoComparison :=
  CellularH2 ≃ₗ[ℚ] RationalSingularHomology 2 surfaceTopCat

/-- [definition] The same comparison after transporting the target to `S² × S²`. -/
abbrev SphereProductDegreeTwoComparison :=
  CellularH2 ≃ₗ[ℚ] RationalSingularHomology 2 sphereProductTopCat

/-- [proved-derived; formal-checked] A sphere-product comparison reconstructs the actual-surface
comparison exactly. -/
def surfaceComparisonOfSphereProduct
    (comparison : SphereProductDegreeTwoComparison) : SurfaceDegreeTwoComparison :=
  comparison.trans (surfaceSingularHomologyEquivSphereProduct 2).symm

/-- [proved-derived; formal-checked] An actual-surface comparison transports to the sphere product. -/
def sphereProductComparisonOfSurface
    (comparison : SurfaceDegreeTwoComparison) : SphereProductDegreeTwoComparison :=
  comparison.trans (surfaceSingularHomologyEquivSphereProduct 2)

theorem sphereProductComparisonOfSurface_roundtrip
    (comparison : SphereProductDegreeTwoComparison) :
    sphereProductComparisonOfSurface (surfaceComparisonOfSphereProduct comparison) = comparison := by
  ext cellularClass
  simp [sphereProductComparisonOfSurface, surfaceComparisonOfSphereProduct]

theorem surfaceComparisonOfSphereProduct_roundtrip
    (comparison : SurfaceDegreeTwoComparison) :
    surfaceComparisonOfSphereProduct (sphereProductComparisonOfSurface comparison) = comparison := by
  ext cellularClass
  simp [sphereProductComparisonOfSurface, surfaceComparisonOfSphereProduct]

/-- [proved-derived; formal-checked] The complete populations of surface and sphere-product
comparisons are equivalent.  This retains every possible comparison rather than choosing one. -/
def degreeTwoComparisonEquiv :
    SurfaceDegreeTwoComparison ≃ SphereProductDegreeTwoComparison where
  toFun := sphereProductComparisonOfSurface
  invFun := surfaceComparisonOfSphereProduct
  left_inv := surfaceComparisonOfSphereProduct_roundtrip
  right_inv := sphereProductComparisonOfSurface_roundtrip

theorem surfaceComparison_nonempty_iff_sphereProductComparison_nonempty :
    Nonempty SurfaceDegreeTwoComparison ↔ Nonempty SphereProductDegreeTwoComparison :=
  degreeTwoComparisonEquiv.nonempty_congr

section Audit

#print axioms surfaceSphereTopIso
#print axioms surfaceSingularHomologyIsoSphereProduct
#print axioms surfaceSingularHomologyEquivSphereProduct
#print axioms surfaceComparisonOfSphereProduct
#print axioms sphereProductComparisonOfSurface
#print axioms degreeTwoComparisonEquiv
#print axioms surfaceComparison_nonempty_iff_sphereProductComparison_nonempty

end Audit

end Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
