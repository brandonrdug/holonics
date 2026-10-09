import CMGradedDescent

/-!
# The projective CM map fixes the coefficient base

The degree-zero identification is the coordinateCount=3 specialization of
HodgeProjectiveSpaceAmbient.degreeZeroEquiv. It is stated locally to avoid
loading that owner's larger receiver closure in the bounded isolated check.
The Proj comparison uses the actual graded-localization chart maps.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

namespace Holonics.Hodge.CMGraphSource

attribute [local instance] MvPolynomial.gradedAlgebra

theorem degreeZero_eq_constant (p : CMGrading 0) :
    (p : HomogeneousRing) = MvPolynomial.C ((p : HomogeneousRing).coeff 0) := by
  have hp : (p : HomogeneousRing).IsHomogeneous 0 :=
    (MvPolynomial.mem_homogeneousSubmodule _ _).mp p.property
  calc
    (p : HomogeneousRing) = MvPolynomial.homogeneousComponent 0 (p : HomogeneousRing) :=
      (MvPolynomial.homogeneousComponent_eq_self hp).symm
    _ = _ := MvPolynomial.homogeneousComponent_zero _

def cmDegreeZeroEquiv : CMGrading 0 ≃+* ℂ where
  toFun p := (p : HomogeneousRing).coeff 0
  invFun c := ⟨MvPolynomial.C c,
    (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_C _ c)⟩
  left_inv p := by apply Subtype.ext; exact (degreeZero_eq_constant p).symm
  right_inv c := by simp
  map_add' p q := by simp
  map_mul' p q := by
    change ((p : HomogeneousRing) * (q : HomogeneousRing)).coeff 0 = _
    rw [degreeZero_eq_constant p, degreeZero_eq_constant q]
    simp

theorem gradedIota_fixes_degreeZero (p : CMGrading 0) : gradedIota p = (p : HomogeneousRing) := by
  rw [degreeZero_eq_constant p]
  simp [gradedIota, homogeneousIota, homogeneousPullback]

theorem awayMap_fromZero (s : HomogeneousRing) (p : CMGrading 0) :
    Away.map gradedIota s (fromZeroRingHom CMGrading (.powers s) p) =
      fromZeroRingHom CMGrading (.powers (gradedIota s)) p := by
  change HomogeneousLocalization.map gradedIota _
    (HomogeneousLocalization.mk ⟨0, p, 1, by simp⟩) =
      HomogeneousLocalization.mk ⟨0, p, 1, by simp⟩
  rw [HomogeneousLocalization.map_mk]
  apply (HomogeneousLocalization.ext_iff_val _ _).mpr
  simp [HomogeneousLocalization.val_mk, gradedIota_fixes_degreeZero p]

theorem ambientIota_toSpecZero :
    projectiveAmbientIota.hom ≫ Proj.toSpecZero CMGrading = Proj.toSpecZero CMGrading := by
  apply (Proj.mapAffineOpenCover gradedIota irrelevant_le_map_iota).openCover.hom_ext
  intro s
  change Proj.awayι CMGrading (gradedIota s.2)
      (gradedIota.map_mem s.2.2) s.1.2 ≫
      (Proj.map gradedIota irrelevant_le_map_iota ≫ Proj.toSpecZero CMGrading) =
    Proj.awayι CMGrading (gradedIota s.2) (gradedIota.map_mem s.2.2) s.1.2 ≫
      Proj.toSpecZero CMGrading
  rw [← Category.assoc, Proj.awayι_comp_map gradedIota irrelevant_le_map_iota
      s.1.2 s.2.1 s.2.2, Category.assoc,
    Proj.awayι_toSpecZero, Proj.awayι_toSpecZero, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  exact awayMap_fromZero s.2 p

def cmComplexPoint : Scheme := Spec (.of ℂ)

def cmBaseIso : Spec (.of (CMGrading 0)) ≅ cmComplexPoint :=
  Scheme.Spec.mapIso (cmDegreeZeroEquiv.symm.toCommRingCatIso.op)

def cmAmbientBase : CMProjectiveAmbient ⟶ cmComplexPoint :=
  Proj.toSpecZero CMGrading ≫ cmBaseIso.hom

theorem ambientIota_over_complex : projectiveAmbientIota.hom ≫ cmAmbientBase = cmAmbientBase := by
  rw [cmAmbientBase, ← Category.assoc, ambientIota_toSpecZero]

#print axioms cmDegreeZeroEquiv
#print axioms awayMap_fromZero
#print axioms ambientIota_toSpecZero
#print axioms ambientIota_over_complex

end Holonics.Hodge.CMGraphSource
