import CMComplexBase

/-! A degree-zero factor in the actual Proj chart inclusion square. -/
noncomputable section
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

def unitDegreeZeroChartMap (f x c : HomogeneousRing) (hc : c ∈ CMGrading 0)
    (hx : x = f * c) : Away CMGrading f →+* Away CMGrading x :=
  awayMap CMGrading hc hx

theorem unitDegreeZeroChartMap_square (f x c : HomogeneousRing)
    {d : ℕ} (hf : f ∈ CMGrading d) (hd : 0 < d)
    (hc : c ∈ CMGrading 0) (hx : x = f * c) :
    Spec.map (CommRingCat.ofHom (unitDegreeZeroChartMap f x c hc hx)) ≫
      Proj.awayι CMGrading f hf hd =
    Proj.awayι CMGrading x (by simpa only [Nat.add_zero] using
      (hx ▸ (SetLike.mul_mem_graded hf hc))) hd := by
  exact Proj.SpecMap_awayMap_awayι CMGrading hf hd hc hx

#print axioms unitDegreeZeroChartMap_square
theorem unitDegreeZeroChartMap_mk (f x c : HomogeneousRing) {d : ℕ}
    (hf : f ∈ CMGrading d) (hxDegree : x ∈ CMGrading d)
    (hc : c ∈ CMGrading 0) (hx : x = f * c) (n : ℕ)
    (p : HomogeneousRing) (hp : p ∈ CMGrading (n • d)) :
    unitDegreeZeroChartMap f x c hc hx (Away.mk CMGrading hf n p hp) =
      Away.mk CMGrading hxDegree n (p * c ^ n)
        (by simpa only [smul_zero, add_zero] using
          SetLike.mul_mem_graded hp (SetLike.pow_mem_graded n hc)) := by
  exact awayMap_mk CMGrading hc hx n hf p hp
#print axioms unitDegreeZeroChartMap_mk
end Holonics.Hodge.CMGraphSource
