import CMProjectiveCubic
import CMComplexBase

/-!
# The constructed CM graph in the product over the complex point

This consumes the proved Proj coefficient-base square and the constructed
closed cubic automorphism. The result is an actual closed scheme graph in
C x_C C for the reduced induced cubic C. This narrow constructor omits separatedness imports. Its equality with the earlier graph and closed-immersion property are checked separately. The chart identification, smooth
surface/Cartier-divisor comparison, intersection multiplicities and rational
cycle class remain subsequent geometric proof obligations.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Holonics.Hodge.CMGraphSource

def cmConcreteCubicBase : CMProjectiveCubic ⟶ cmComplexPoint := cubicEmbedding ≫ cmAmbientBase

theorem cubicIota_concrete_base : cubicIota.hom ≫ cmConcreteCubicBase = cmConcreteCubicBase := by
  change cubicIotaHom ≫ (cubicEmbedding ≫ cmAmbientBase) = cubicEmbedding ≫ cmAmbientBase
  rw [← Category.assoc, cubicIotaHom_embedding, Category.assoc, ambientIota_over_complex]

def cmConcreteComplexGraph : CMProjectiveCubic ⟶ pullback cmConcreteCubicBase cmConcreteCubicBase :=
  pullback.lift (𝟙 _) cubicIota.hom (Category.id_comp _) ≫
    (pullback.congrHom cubicIota_concrete_base rfl).hom

theorem cmConcreteComplexGraph_first_projection : cmConcreteComplexGraph ≫
    pullback.fst cmConcreteCubicBase cmConcreteCubicBase = 𝟙 CMProjectiveCubic := by
  unfold cmConcreteComplexGraph
  simp only [Category.assoc, pullback.congrHom_hom, Category.comp_id, pullback.lift_fst]

theorem cmConcreteComplexGraph_second_projection : cmConcreteComplexGraph ≫
    pullback.snd cmConcreteCubicBase cmConcreteCubicBase = cubicIota.hom := by
  unfold cmConcreteComplexGraph
  simp only [Category.assoc, pullback.congrHom_hom, Category.comp_id, pullback.lift_snd]

#print axioms cubicIota_concrete_base
#print axioms cmConcreteComplexGraph_first_projection
#print axioms cmConcreteComplexGraph_second_projection

end Holonics.Hodge.CMGraphSource
