import CMProjectiveGraph
import CMComplexBase

/-!
# The constructed CM graph in the product over the complex point

This consumes the proved Proj coefficient-base square and the constructed
closed cubic automorphism. The result is an actual closed scheme graph in
C x_C C for the reduced induced cubic C. Its chart identification, smooth
surface/Cartier-divisor comparison, intersection multiplicities and rational
cycle class remain subsequent geometric proof obligations.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Holonics.Hodge.CMGraphSource

def cmCubicBase : CMProjectiveCubic ⟶ cmComplexPoint := cubicEmbedding ≫ cmAmbientBase

theorem cubicIota_over_complex : cubicIota.hom ≫ cmCubicBase = cmCubicBase := by
  change cubicIotaHom ≫ (cubicEmbedding ≫ cmAmbientBase) = cubicEmbedding ≫ cmAmbientBase
  rw [← Category.assoc, cubicIotaHom_embedding, Category.assoc, ambientIota_over_complex]

def cmComplexGraph : CMProjectiveCubic ⟶ pullback cmCubicBase cmCubicBase :=
  pullback.lift (𝟙 _) cubicIota.hom (Category.id_comp _) ≫
    (pullback.congrHom cubicIota_over_complex rfl).hom

theorem cmComplexGraph_closedImmersion : IsClosedImmersion cmComplexGraph := by
  have : IsClosedImmersion (pullback.lift (𝟙 CMProjectiveCubic) cubicIota.hom
      (Category.id_comp (cubicIota.hom ≫ cmCubicBase))) := inferInstance
  unfold cmComplexGraph
  infer_instance

theorem cmComplexGraph_first_projection : cmComplexGraph ≫
    pullback.fst cmCubicBase cmCubicBase = 𝟙 CMProjectiveCubic := by
  unfold cmComplexGraph
  simp only [Category.assoc, pullback.congrHom_hom, Category.comp_id, pullback.lift_fst]

theorem cmComplexGraph_second_projection : cmComplexGraph ≫
    pullback.snd cmCubicBase cmCubicBase = cubicIota.hom := by
  unfold cmComplexGraph
  simp only [Category.assoc, pullback.congrHom_hom, Category.comp_id, pullback.lift_snd]

#print axioms cubicIota_over_complex
#print axioms cmComplexGraph_closedImmersion
#print axioms cmComplexGraph_first_projection
#print axioms cmComplexGraph_second_projection

end Holonics.Hodge.CMGraphSource
