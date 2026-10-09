import CMGradedDescent
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# The CM map on an actual closed projective cubic subscheme

The cubic is the reduced induced closed subscheme of the actual Proj
ambient on the proved homogeneous cubic zero locus. Its ideal sheaf and
the restricted automorphism are constructed, using invariance proved from
the homogeneous substitution. No projective cycle realization is assumed.

The comparison of this reduced induced structure with the cubic quotient
and the previously constructed Weierstrass affine charts is still owed.
The graph is a closed subscheme; its Cartier-divisor and cycle-class
comparisons are further obligations.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Holonics.Hodge.CMGraphSource

attribute [local instance] MvPolynomial.gradedAlgebra

def cubicClosed : Closeds CMProjectiveAmbient :=
  ⟨cubicProjectiveLocus, ProjectiveSpectrum.isClosed_zeroLocus CMGrading {projectiveCubic}⟩

def cubicIdealSheaf : CMProjectiveAmbient.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal cubicClosed

theorem ambient_hom_inv_returns (p : CMProjectiveAmbient) :
    projectiveAmbientIota.hom (projectiveAmbientIota.inv p) = p := by
  change (projectiveAmbientIota.inv ≫ projectiveAmbientIota.hom) p = p
  rw [Iso.inv_hom_id]
  rfl

theorem ambient_inv_hom_returns (p : CMProjectiveAmbient) :
    projectiveAmbientIota.inv (projectiveAmbientIota.hom p) = p := by
  change (projectiveAmbientIota.hom ≫ projectiveAmbientIota.inv) p = p
  rw [Iso.hom_inv_id]
  rfl

theorem ambient_inverse_preserves_cubic (p : CMProjectiveAmbient) :
    projectiveAmbientIota.inv p ∈ cubicProjectiveLocus ↔ p ∈ cubicProjectiveLocus := by
  have h := projectiveAmbientIota_preserves_cubic (projectiveAmbientIota.inv p)
  rw [ambient_hom_inv_returns] at h
  exact h.symm

theorem ambient_hom_image_cubic :
    projectiveAmbientIota.hom '' (cubicClosed : Set CMProjectiveAmbient) = cubicClosed := by
  apply Set.Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact (projectiveAmbientIota_preserves_cubic p).mpr hp
  · intro p hp
    exact ⟨projectiveAmbientIota.inv p, (ambient_inverse_preserves_cubic p).mpr hp,
      ambient_hom_inv_returns p⟩

theorem ambient_inv_image_cubic :
    projectiveAmbientIota.inv '' (cubicClosed : Set CMProjectiveAmbient) = cubicClosed := by
  apply Set.Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact (ambient_inverse_preserves_cubic p).mpr hp
  · intro p hp
    exact ⟨projectiveAmbientIota.hom p, (projectiveAmbientIota_preserves_cubic p).mpr hp,
      ambient_inv_hom_returns p⟩

theorem cubicIdealSheaf_map_hom : cubicIdealSheaf.map projectiveAmbientIota.hom =
    cubicIdealSheaf := by
  unfold cubicIdealSheaf
  rw [Scheme.IdealSheafData.map_vanishingIdeal]
  have he : Closeds.closure (projectiveAmbientIota.hom ''
      (cubicClosed : Set CMProjectiveAmbient)) = cubicClosed := by
    apply SetLike.coe_injective
    rw [Closeds.coe_closure, ambient_hom_image_cubic, cubicClosed.isClosed.closure_eq]
  rw [he]

theorem cubicIdealSheaf_map_inv : cubicIdealSheaf.map projectiveAmbientIota.inv =
    cubicIdealSheaf := by
  unfold cubicIdealSheaf
  rw [Scheme.IdealSheafData.map_vanishingIdeal]
  have he : Closeds.closure (projectiveAmbientIota.inv ''
      (cubicClosed : Set CMProjectiveAmbient)) = cubicClosed := by
    apply SetLike.coe_injective
    rw [Closeds.coe_closure, ambient_inv_image_cubic, cubicClosed.isClosed.closure_eq]
  rw [he]

abbrev CMProjectiveCubic : Scheme := cubicIdealSheaf.subscheme
abbrev cubicEmbedding : CMProjectiveCubic ⟶ CMProjectiveAmbient :=
  cubicIdealSheaf.subschemeι

def cubicIotaHom : CMProjectiveCubic ⟶ CMProjectiveCubic :=
  IsClosedImmersion.lift cubicEmbedding (cubicEmbedding ≫ projectiveAmbientIota.hom) (by
    have hk : cubicEmbedding.ker = cubicIdealSheaf := cubicIdealSheaf.ker_subschemeι
    rw [Scheme.Hom.ker_comp, hk, cubicIdealSheaf_map_hom])

def cubicIotaInv : CMProjectiveCubic ⟶ CMProjectiveCubic :=
  IsClosedImmersion.lift cubicEmbedding (cubicEmbedding ≫ projectiveAmbientIota.inv) (by
    have hk : cubicEmbedding.ker = cubicIdealSheaf := cubicIdealSheaf.ker_subschemeι
    rw [Scheme.Hom.ker_comp, hk, cubicIdealSheaf_map_inv])

@[simp, reassoc (attr := simp)] theorem cubicIotaHom_embedding : cubicIotaHom ≫ cubicEmbedding =
    cubicEmbedding ≫ projectiveAmbientIota.hom := IsClosedImmersion.lift_fac _ _ _

@[simp, reassoc (attr := simp)] theorem cubicIotaInv_embedding : cubicIotaInv ≫ cubicEmbedding =
    cubicEmbedding ≫ projectiveAmbientIota.inv := IsClosedImmersion.lift_fac _ _ _

def cubicIota : CMProjectiveCubic ≅ CMProjectiveCubic where
  hom := cubicIotaHom
  inv := cubicIotaInv
  hom_inv_id := by
    apply (cancel_mono cubicEmbedding).mp
    simp [Category.assoc]
  inv_hom_id := by
    apply (cancel_mono cubicEmbedding).mp
    simp [Category.assoc]

#print axioms cubicIdealSheaf_map_hom
#print axioms cubicIdealSheaf_map_inv
#print axioms cubicIota

end Holonics.Hodge.CMGraphSource
