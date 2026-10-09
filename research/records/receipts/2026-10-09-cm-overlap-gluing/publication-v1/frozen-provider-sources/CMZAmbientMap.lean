import CMZCoordinateMap
import CMCoordinateTransport

/-! The actual projective ambient CM chart square. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

theorem zAwayIota_transport :
    zAwayIota = (awayCoordinateTransport zCoordinate_iota_fixed).toRingHom.comp
      (Away.map gradedIota zCoordinate) := by
  apply RingHom.ext
  intro a
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective CMGrading (coordinate_degree_one 2) a
  rw [RingHom.comp_apply, Away.map_mk]
  change zAwayIota (Away.mk CMGrading _ n p hp) =
    awayCoordinateTransport zCoordinate_iota_fixed (Away.mk CMGrading _ n (gradedIota p) _)
  rw [awayCoordinateTransport_mk]
  exact zAwayIota_mk n p (by simpa using hp)

theorem zAwayIota_ambient_square :
    Proj.awayι CMGrading zCoordinate (coordinate_degree_one 2) (by norm_num) ≫
      projectiveAmbientIota.hom =
    Spec.map (CommRingCat.ofHom zAwayIota) ≫
      Proj.awayι CMGrading zCoordinate (coordinate_degree_one 2) (by norm_num) := by
  have h := Proj.awayι_comp_map gradedIota irrelevant_le_map_iota
    (by norm_num : 0 < (1 : ℕ)) zCoordinate (coordinate_degree_one 2)
  calc
    _ = Spec.map (CommRingCat.ofHom (awayCoordinateTransport zCoordinate_iota_fixed).toRingHom) ≫
        Proj.awayι CMGrading (gradedIota zCoordinate)
          (gradedIota.map_mem (coordinate_degree_one 2)) (by norm_num) ≫
        projectiveAmbientIota.hom := by
      rw [← Category.assoc, awayCoordinateTransport_scheme]
    _ = Spec.map (CommRingCat.ofHom (awayCoordinateTransport zCoordinate_iota_fixed).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Away.map gradedIota zCoordinate)) ≫
        Proj.awayι CMGrading zCoordinate (coordinate_degree_one 2) (by norm_num) := by erw [h]
    _ = _ := by
      rw [← Spec.map_comp_assoc, zAwayIota_transport]
      rfl

#print axioms zAwayIota_ambient_square
end Holonics.Hodge.CMGraphSource
