import CMProjectiveCubic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
The constructed cubic automorphism has a closed graph over the terminal
base. This is an actual scheme graph; its identification over Spec C,
Cartier-divisor structure, and cycle-class map remain separate obligations.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Holonics.Hodge.CMGraphSource

attribute [local instance] MvPolynomial.gradedAlgebra

instance : CMProjectiveCubic.IsSeparated := by
  constructor
  have : IsSeparated (cubicEmbedding ≫ terminal.from CMProjectiveAmbient) := inferInstance
  simpa using this

def projectiveCubicGraph : CMProjectiveCubic ⟶
    pullback (cubicIota.hom ≫ terminal.from CMProjectiveCubic)
      (terminal.from CMProjectiveCubic) :=
  pullback.lift (𝟙 _) cubicIota.hom (Category.id_comp _)

theorem projectiveCubicGraph_closedImmersion : IsClosedImmersion projectiveCubicGraph := by
  unfold projectiveCubicGraph
  infer_instance

theorem projectiveCubicGraph_first_projection : projectiveCubicGraph ≫
    pullback.fst (cubicIota.hom ≫ terminal.from CMProjectiveCubic)
      (terminal.from CMProjectiveCubic) = 𝟙 _ := by
  unfold projectiveCubicGraph
  exact pullback.lift_fst _ _ _

theorem projectiveCubicGraph_second_projection : projectiveCubicGraph ≫
    pullback.snd (cubicIota.hom ≫ terminal.from CMProjectiveCubic)
      (terminal.from CMProjectiveCubic) = cubicIota.hom := by
  unfold projectiveCubicGraph
  exact pullback.lift_snd _ _ _

#print axioms projectiveCubicGraph_closedImmersion
#print axioms projectiveCubicGraph_first_projection
#print axioms projectiveCubicGraph_second_projection

end Holonics.Hodge.CMGraphSource
