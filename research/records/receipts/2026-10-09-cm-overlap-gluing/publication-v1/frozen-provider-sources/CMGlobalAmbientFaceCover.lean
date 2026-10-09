import CMActualAmbientRegularFaces
import CMAmbientPairCover
import CMYAmbientFaceCoverage
import CMChartCover

/-! The regular principal affine opens cover the entire actual graph and
actual diagonal support. The product chart cover is required only along
these embeddings, and is not claimed to cover every point of E x_C E. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource

theorem actual_curve_chart_range_cover (q : CMProjectiveCubic) :
    (∃ x : Spec (.of YChartCubicRing), yCurveChartInclusion x = q) ∨
      (∃ x : Spec (.of CurveRing), zCurveChartInclusion x = q) := by
  rcases cubic_chart_opens_cover q with hy | hz
  · left
    change q ∈ Set.range yCurveChartInclusion
    change q ∈ yCurveChartInclusion.opensRange
    dsimp only [yCurveChartInclusion]
    rw [Scheme.Hom.opensRange_comp_of_isIso, yReducedCubicOpen.opensRange_ι]
    exact hy
  · right
    change q ∈ Set.range zCurveChartInclusion
    change q ∈ zCurveChartInclusion.opensRange
    dsimp only [zCurveChartInclusion]
    rw [Scheme.Hom.opensRange_comp_of_isIso, zCubicOpen.opensRange_ι]
    exact hz

theorem actual_graph_image_face_cover (q : CMProjectiveCubic) :
    cmConcreteComplexGraph q ∈ yGraphPAmbientOpen.opensRange ∨
    cmConcreteComplexGraph q ∈ yGraphQAmbientOpen.opensRange ∨
    cmConcreteComplexGraph q ∈ zGraphFactorAmbientOpen.opensRange ∨
    cmConcreteComplexGraph q ∈ zGraphVSumAmbientOpen.opensRange := by
  rcases actual_curve_chart_range_cover q with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · have h := ambient_pair_cover (CommRingCat.ofHom yGraphReceiver.toRingHom)
      yProductChartInclusion yCurveChartInclusion cmConcreteComplexGraph
      yTensorGraph_actual_square yGraphP yGraphQ yGraph_faces_cover x
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have h := ambient_pair_cover (CommRingCat.ofHom graphReceiver.toRingHom)
      zProductChartInclusion zCurveChartInclusion cmConcreteComplexGraph
      zTensorGraph_actual_square graphCubicFactor graphVSum graph_principal_faces_cover x
    exact Or.inr (Or.inr h)

theorem actual_diagonal_image_face_cover (q : CMProjectiveCubic) :
    cmComplexDiagonal q ∈ yDiagonalPAmbientOpen.opensRange ∨
    cmComplexDiagonal q ∈ yDiagonalQAmbientOpen.opensRange ∨
    cmComplexDiagonal q ∈ zDiagonalFactorAmbientOpen.opensRange ∨
    cmComplexDiagonal q ∈ zDiagonalVSumAmbientOpen.opensRange := by
  rcases actual_curve_chart_range_cover q with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · have h := ambient_pair_cover (CommRingCat.ofHom yDiagonalReceiver.toRingHom)
      yProductChartInclusion yCurveChartInclusion cmComplexDiagonal
      yTensorDiagonal_actual_square yDiagonalP yDiagonalQ yDiagonal_faces_cover x
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have h := ambient_pair_cover (CommRingCat.ofHom diagonalReceiver.toRingHom)
      zProductChartInclusion zCurveChartInclusion cmComplexDiagonal
      zTensorDiagonal_actual_square diagonalCubicFactor diagonalVSum diagonal_principal_faces_cover x
    exact Or.inr (Or.inr h)

theorem actual_graph_support_face_cover (p : CMActualAmbientProduct)
    (hp : p ∈ cmConcreteComplexGraph.ker.support) :
    p ∈ yGraphPAmbientOpen.opensRange ∨ p ∈ yGraphQAmbientOpen.opensRange ∨
    p ∈ zGraphFactorAmbientOpen.opensRange ∨ p ∈ zGraphVSumAmbientOpen.opensRange := by
  letI : IsClosedImmersion cmConcreteComplexGraph := cmConcreteGraph_closedImmersion
  change p ∈ (cmConcreteComplexGraph.ker.support : Set CMActualAmbientProduct) at hp
  rw [Scheme.Hom.support_ker, cmConcreteComplexGraph.isClosedEmbedding.isClosed_range.closure_eq] at hp
  obtain ⟨q, rfl⟩ := hp
  exact actual_graph_image_face_cover q

theorem actual_diagonal_support_face_cover (p : CMActualAmbientProduct)
    (hp : p ∈ cmComplexDiagonal.ker.support) :
    p ∈ yDiagonalPAmbientOpen.opensRange ∨ p ∈ yDiagonalQAmbientOpen.opensRange ∨
    p ∈ zDiagonalFactorAmbientOpen.opensRange ∨ p ∈ zDiagonalVSumAmbientOpen.opensRange := by
  letI : IsClosedImmersion cmComplexDiagonal := by
    dsimp only [cmComplexDiagonal]
    infer_instance
  change p ∈ (cmComplexDiagonal.ker.support : Set CMActualAmbientProduct) at hp
  rw [Scheme.Hom.support_ker, cmComplexDiagonal.isClosedEmbedding.isClosed_range.closure_eq] at hp
  obtain ⟨q, rfl⟩ := hp
  exact actual_diagonal_image_face_cover q

#print axioms actual_curve_chart_range_cover
#print axioms actual_graph_image_face_cover
#print axioms actual_diagonal_image_face_cover
#print axioms actual_graph_support_face_cover
#print axioms actual_diagonal_support_face_cover
end Holonics.Hodge.CMGraphSource
