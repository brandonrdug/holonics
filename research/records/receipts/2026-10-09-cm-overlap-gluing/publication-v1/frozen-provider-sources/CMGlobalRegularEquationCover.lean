import CMGlobalAmbientFaceCover

/-! The ambient open covers include the complement of each actual support.
On this complement the actual ideal sheaf is the unit ideal. Together with
all four regular principal equations this is the concrete local Cartier
condition, without introducing a separate Cartier library. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource
universe u

def idealComplementOpen {X : Scheme.{u}} (I : X.IdealSheafData) : X.Opens :=
  ⟨(I.support : Set X)ᶜ, I.support.isClosed.isOpen_compl⟩

theorem idealComplementOpen_unit {X : Scheme.{u}} (I : X.IdealSheafData) :
    I.comap (idealComplementOpen I).ι = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff (I.comap (idealComplementOpen I).ι)).mp
  rw [Scheme.IdealSheafData.support_comap]
  apply TopologicalSpace.Closeds.ext
  ext x
  change ((idealComplementOpen I).ι x ∈ (I.support : Set X)) ↔ False
  exact iff_false_intro x.2

theorem actual_graph_global_regular_open_cover (p : CMActualAmbientProduct) :
    p ∈ yGraphPAmbientOpen.opensRange ∨ p ∈ yGraphQAmbientOpen.opensRange ∨
    p ∈ zGraphFactorAmbientOpen.opensRange ∨ p ∈ zGraphVSumAmbientOpen.opensRange ∨
    p ∈ idealComplementOpen cmConcreteComplexGraph.ker := by
  by_cases hp : p ∈ cmConcreteComplexGraph.ker.support
  · rcases actual_graph_support_face_cover p hp with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hp)))

theorem actual_diagonal_global_regular_open_cover (p : CMActualAmbientProduct) :
    p ∈ yDiagonalPAmbientOpen.opensRange ∨ p ∈ yDiagonalQAmbientOpen.opensRange ∨
    p ∈ zDiagonalFactorAmbientOpen.opensRange ∨ p ∈ zDiagonalVSumAmbientOpen.opensRange ∨
    p ∈ idealComplementOpen cmComplexDiagonal.ker := by
  by_cases hp : p ∈ cmComplexDiagonal.ker.support
  · rcases actual_diagonal_support_face_cover p hp with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hp)))

#print axioms idealComplementOpen_unit
#print axioms actual_graph_global_regular_open_cover
#print axioms actual_diagonal_global_regular_open_cover
#print axioms yGraphPActual_regular_equation
#print axioms yGraphQActual_regular_equation
#print axioms yDiagonalPActual_regular_equation
#print axioms yDiagonalQActual_regular_equation
#print axioms zGraphFactorActual_regular_equation
#print axioms zGraphVSumActual_regular_equation
#print axioms zDiagonalFactorActual_regular_equation
#print axioms zDiagonalVSumActual_regular_equation
end Holonics.Hodge.CMGraphSource
