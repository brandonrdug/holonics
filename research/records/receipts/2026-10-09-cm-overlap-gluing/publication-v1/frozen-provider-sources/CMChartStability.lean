import CMChartCover
import CMYChartReduced

/-! The constructed projective CM morphism restricts to both actual cubic charts. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

@[simp] theorem gradedIota_zCoordinate : gradedIota zCoordinate = zCoordinate := by
  simp [gradedIota, homogeneousIota, homogeneousPullback, zCoordinate]
@[simp] theorem gradedIota_yCoordinate :
    gradedIota yCoordinate = MvPolynomial.C Complex.I * yCoordinate := by
  simp [gradedIota, homogeneousIota, homogeneousPullback, yCoordinate]

theorem ambientIota_zChart_preimage :
    projectiveAmbientIota.hom ⁻¹ᵁ zAmbientAffineOpen.1 = zAmbientAffineOpen.1 := by
  change Proj.map gradedIota irrelevant_le_map_iota ⁻¹ᵁ Proj.basicOpen CMGrading zCoordinate = _
  rw [Proj.map_preimage_basicOpen, gradedIota_zCoordinate]
  rfl
theorem ambientIota_yChart_preimage :
    projectiveAmbientIota.hom ⁻¹ᵁ yAmbientAffineOpen.1 = yAmbientAffineOpen.1 := by
  change Proj.map gradedIota irrelevant_le_map_iota ⁻¹ᵁ Proj.basicOpen CMGrading yCoordinate = _
  rw [Proj.map_preimage_basicOpen, gradedIota_yCoordinate]
  ext p
  change MvPolynomial.C Complex.I * yCoordinate ∉ p.asHomogeneousIdeal ↔
    yCoordinate ∉ p.asHomogeneousIdeal
  have hi : IsUnit (MvPolynomial.C Complex.I : HomogeneousRing) :=
    (isUnit_iff_ne_zero.mpr Complex.I_ne_zero).map MvPolynomial.C
  exact not_congr (Ideal.unit_mul_mem_iff_mem p.asHomogeneousIdeal.toIdeal hi)

theorem cubicIota_zChart_preimage : cubicIotaHom ⁻¹ᵁ zCubicOpen = zCubicOpen := by
  ext p
  change cubicEmbedding (cubicIotaHom p) ∈ zAmbientAffineOpen.1 ↔
    cubicEmbedding p ∈ zAmbientAffineOpen.1
  have he := congrArg (fun f : CMProjectiveCubic ⟶ CMProjectiveAmbient => f p)
    cubicIotaHom_embedding
  change cubicEmbedding (cubicIotaHom p) = projectiveAmbientIota.hom (cubicEmbedding p) at he
  rw [he]
  change cubicEmbedding p ∈ projectiveAmbientIota.hom ⁻¹ᵁ zAmbientAffineOpen.1 ↔ _
  rw [ambientIota_zChart_preimage]
theorem cubicIota_yChart_preimage : cubicIotaHom ⁻¹ᵁ yCubicOpen = yCubicOpen := by
  ext p
  change cubicEmbedding (cubicIotaHom p) ∈ yAmbientAffineOpen.1 ↔
    cubicEmbedding p ∈ yAmbientAffineOpen.1
  have he := congrArg (fun f : CMProjectiveCubic ⟶ CMProjectiveAmbient => f p)
    cubicIotaHom_embedding
  change cubicEmbedding (cubicIotaHom p) = projectiveAmbientIota.hom (cubicEmbedding p) at he
  rw [he]
  change cubicEmbedding p ∈ projectiveAmbientIota.hom ⁻¹ᵁ yAmbientAffineOpen.1 ↔ _
  rw [ambientIota_yChart_preimage]

def cubicIotaZRestriction : zCubicOpen.toScheme ⟶ zCubicOpen.toScheme :=
  cubicIotaHom.resLE zCubicOpen zCubicOpen (by rw [cubicIota_zChart_preimage])
def cubicIotaYRestriction : yCubicOpen.toScheme ⟶ yCubicOpen.toScheme :=
  cubicIotaHom.resLE yCubicOpen yCubicOpen (by rw [cubicIota_yChart_preimage])

theorem cubicIotaZRestriction_ι : cubicIotaZRestriction ≫ zCubicOpen.ι =
    zCubicOpen.ι ≫ cubicIotaHom := by simp [cubicIotaZRestriction]
theorem cubicIotaYRestriction_ι : cubicIotaYRestriction ≫ yCubicOpen.ι =
    yCubicOpen.ι ≫ cubicIotaHom := by simp [cubicIotaYRestriction]

#print axioms cubicIota_zChart_preimage
#print axioms cubicIota_yChart_preimage
#print axioms cubicIotaZRestriction_ι
#print axioms cubicIotaYRestriction_ι
end Holonics.Hodge.CMGraphSource
