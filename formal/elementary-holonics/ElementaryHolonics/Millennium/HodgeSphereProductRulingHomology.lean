import ElementaryHolonics.Millennium.HodgeSphereProductRulingCycles

/-!
# The two geometric ruling cycles as genuine rational singular-homology classes

The four triangular charts constructed on `S²` have an exact alternating boundary cancellation.
Their two addressed inclusions into `S² × S²` therefore define cycles in the genuine rational
singular chain complex.  This file performs the categorical passage from those chain elements to
the kernel object and then to homology, rather than postulating their homology classes.

It returns a concrete linear comparison candidate from the two cellular bidegree coordinates to
genuine singular homology.  Proving that map is an equivalence is the next theorem obligation; the
map itself and its values on both geometric generators are constructed here.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeSphereProductRulingHomology

open CategoryTheory
open Soma.Holonics.Millennium.HodgeProjectiveLineProduct
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeSphereProductFiniteComplex
open Soma.Holonics.Millennium.HodgeSphereProductRulingCycles

abbrev ProductChains := SphereProductSingularChainComplex

abbrev ScalarModule := ModuleCat.of ℚ ℚ

def chainElementMorphism (chain : ProductChains.X 2) :
    ScalarModule ⟶ ProductChains.X 2 :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ chain)

@[simp]
theorem chainElementMorphism_apply (chain : ProductChains.X 2) (q : ℚ) :
    chainElementMorphism chain q = q • chain := rfl

theorem chainElementMorphism_comp_boundary_eq_zero
    (chain : ProductChains.X 2)
    (hchain : ProductChains.d 2 1 chain = 0) :
    chainElementMorphism chain ≫ ProductChains.d 2 1 = 0 := by
  ext
  change ProductChains.d 2 1 ((1 : ℚ) • chain) = 0
  simpa using hchain

def cycleLift (chain : ProductChains.X 2)
    (hchain : ProductChains.d 2 1 chain = 0) :
    ScalarModule ⟶ ProductChains.cycles 2 :=
  ProductChains.liftCycles (chainElementMorphism chain) 1 (by simp)
    (chainElementMorphism_comp_boundary_eq_zero chain hchain)

theorem cycleLift_i (chain : ProductChains.X 2)
    (hchain : ProductChains.d 2 1 chain = 0) :
    cycleLift chain hchain ≫ ProductChains.iCycles 2 =
      chainElementMorphism chain := by
  apply HomologicalComplex.liftCycles_i

def homologyClassMorphism (chain : ProductChains.X 2)
    (hchain : ProductChains.d 2 1 chain = 0) :
    ScalarModule ⟶ RationalSingularHomology 2 sphereProductTopCat :=
  cycleLift chain hchain ≫ ProductChains.homologyπ 2

def homologyClass (chain : ProductChains.X 2)
    (hchain : ProductChains.d 2 1 chain = 0) :
    RationalSingularHomology 2 sphereProductTopCat :=
  homologyClassMorphism chain hchain 1

def firstRulingHomologyClass : RationalSingularHomology 2 sphereProductTopCat :=
  homologyClass firstRulingCycle firstRulingCycle_boundary_zero

def secondRulingHomologyClass : RationalSingularHomology 2 sphereProductTopCat :=
  homologyClass secondRulingCycle secondRulingCycle_boundary_zero

def rulingHomologyMap : Bidegree →ₗ[ℚ]
    RationalSingularHomology 2 sphereProductTopCat where
  toFun x := x 0 • firstRulingHomologyClass + x 1 • secondRulingHomologyClass
  map_add' x y := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' q x := by
    simp only [Pi.smul_apply, smul_add, smul_smul, RingHom.id_apply, smul_eq_mul]

theorem rulingHomologyMap_firstFibre :
    rulingHomologyMap firstFibre = firstRulingHomologyClass := by
  simp [rulingHomologyMap, firstFibre]

theorem rulingHomologyMap_secondFibre :
    rulingHomologyMap secondFibre = secondRulingHomologyClass := by
  simp [rulingHomologyMap, secondFibre]

section Audit

#print axioms chainElementMorphism_comp_boundary_eq_zero
#print axioms rulingHomologyMap_firstFibre
#print axioms rulingHomologyMap_secondFibre

end Audit

end Soma.Holonics.Millennium.HodgeSphereProductRulingHomology
