import CMComplexBase

/-! Equality transport for actual graded localization charts. -/
noncomputable section
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

def awayCoordinateTransport {f g : HomogeneousRing} (h : f = g) :
    Away CMGrading f ≃+* Away CMGrading g := by
  subst g
  exact RingEquiv.refl _

theorem awayCoordinateTransport_mk {f g : HomogeneousRing} (h : f = g)
    {d : ℕ} (hf : f ∈ CMGrading d) (hg : g ∈ CMGrading d)
    (n : ℕ) (p : HomogeneousRing) (hp : p ∈ CMGrading (n • d)) :
    awayCoordinateTransport h (Away.mk CMGrading hf n p hp) =
      Away.mk CMGrading hg n p hp := by
  subst g
  rfl

theorem awayCoordinateTransport_scheme {f g : HomogeneousRing} (h : f = g)
    {d : ℕ} (hf : f ∈ CMGrading d) (hg : g ∈ CMGrading d) (hd : 0 < d) :
    Spec.map (CommRingCat.ofHom (awayCoordinateTransport h).toRingHom) ≫
      Proj.awayι CMGrading f hf hd = Proj.awayι CMGrading g hg hd := by
  subst g
  simp [awayCoordinateTransport]


#print axioms awayCoordinateTransport_mk
#print axioms awayCoordinateTransport_scheme
end Holonics.Hodge.CMGraphSource
