import ElementaryHolonics.Millennium.HodgeTwoSphereFundamentalCycle
import ElementaryHolonics.Millennium.HodgeSphereProductFiniteComplex

noncomputable section

namespace Soma.Holonics.Millennium.HodgeSphereProductRulingCycles

open CategoryTheory
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeSphereProductFiniteComplex
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle

abbrev Sphere :=
  Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle.TwoSphere

def sphereBasepoint : Sphere :=
  radialFace 0 (stdSimplex.vertex (S := ℝ) (0 : Fin 3))

def firstRulingContinuousMap : C(Sphere, Sphere × Sphere) where
  toFun point := (point, sphereBasepoint)
  continuous_toFun := continuous_id.prodMk continuous_const

def secondRulingContinuousMap : C(Sphere, Sphere × Sphere) where
  toFun point := (sphereBasepoint, point)
  continuous_toFun := continuous_const.prodMk continuous_id

def firstRulingTopMap : sphereTopCat ⟶ sphereProductTopCat :=
  TopCat.ofHom firstRulingContinuousMap

def secondRulingTopMap : sphereTopCat ⟶ sphereProductTopCat :=
  TopCat.ofHom secondRulingContinuousMap

def firstRulingChainMap :
    SphereSingularChainComplex ⟶ SphereProductSingularChainComplex :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
    rationalCoefficient).map firstRulingTopMap

def secondRulingChainMap :
    SphereSingularChainComplex ⟶ SphereProductSingularChainComplex :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
    rationalCoefficient).map secondRulingTopMap

def firstRulingCycle : SphereProductSingularChainComplex.X 2 :=
  firstRulingChainMap.f 2 sphereFundamentalCandidate

def secondRulingCycle : SphereProductSingularChainComplex.X 2 :=
  secondRulingChainMap.f 2 sphereFundamentalCandidate

theorem firstRulingCycle_boundary_zero :
    (SphereProductSingularChainComplex.d 2 1) firstRulingCycle = 0 := by
  change (firstRulingChainMap.f 2 ≫ SphereProductSingularChainComplex.d 2 1)
    sphereFundamentalCandidate = 0
  rw [firstRulingChainMap.comm 2 1]
  change firstRulingChainMap.f 1
    ((SphereSingularChainComplex.d 2 1) sphereFundamentalCandidate) = 0
  rw [sphereFundamentalCandidate_boundary_zero, map_zero]

theorem secondRulingCycle_boundary_zero :
    (SphereProductSingularChainComplex.d 2 1) secondRulingCycle = 0 := by
  change (secondRulingChainMap.f 2 ≫ SphereProductSingularChainComplex.d 2 1)
    sphereFundamentalCandidate = 0
  rw [secondRulingChainMap.comm 2 1]
  change secondRulingChainMap.f 1
    ((SphereSingularChainComplex.d 2 1) sphereFundamentalCandidate) = 0
  rw [sphereFundamentalCandidate_boundary_zero, map_zero]

section Audit

#print axioms firstRulingCycle_boundary_zero
#print axioms secondRulingCycle_boundary_zero

end Audit

end Soma.Holonics.Millennium.HodgeSphereProductRulingCycles
