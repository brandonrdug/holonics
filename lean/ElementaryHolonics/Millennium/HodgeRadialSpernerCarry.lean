import ElementaryHolonics.Millennium.HodgeFiniteClosedStarLabeling

/-!
# Relative radial constraints for the tetrahedral Sperner carry

The radial realization of the face opposite vertex `f` never enters the open star of `f`.  This
is not a drawing convention: after centering and radial normalization, the omitted barycentric
coordinate is the minimum of the four exact tetrahedral coordinates.  Therefore every star label
carrying a point of that radial face differs from the omitted vertex.

This is the boundary condition for the relative Sperner passage.  Subsequent edge and face current
theorems will combine it with the global closed-star labels to derive the radial return rather than
store that return as a field.

Truth status: every theorem is `[proved-derived; formal-checked]` from the explicit radial map and
the exact tetrahedral star coordinates.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeRadialSpernerCarry

open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeTetrahedralSphereComplex
open Soma.Holonics.Millennium.HodgeTetrahedralChainComplex
open Soma.Holonics.Millennium.HodgeTetrahedralLabelCarry
open Soma.Holonics.Millennium.HodgeTetrahedralStarCover
open Soma.Holonics.Millennium.HodgeTetrahedralCarrierAssembly

set_option maxHeartbeats 2000000

/-- [proved-derived; formal-checked] The four star coordinates of a radial face are exactly the
normalized centered barycentric coordinates. -/
theorem sphereTetraCoordinate_radialFace (face vertex : Fin 4) (point : Triangle) :
    sphereTetraCoordinate vertex (radialFace face point) =
      ‖centeredFaceVector face point‖⁻¹ *
        (tetraFace face point vertex - (1 / 4 : ℝ)) := by
  have coordinateSum := stdSimplex.sum_eq_one (tetraFace face point)
  rw [Fin.sum_univ_four] at coordinateSum
  fin_cases vertex
  · rfl
  · rfl
  · rfl
  · simp only [sphereTetraCoordinate, Fin.isValue, OfNat.ofNat, radialFace]
    change -(‖centeredFaceVector face point‖⁻¹ *
          (tetraFace face point 0 - (1 / 4 : ℝ)) +
        ‖centeredFaceVector face point‖⁻¹ *
          (tetraFace face point 1 - (1 / 4 : ℝ)) +
        ‖centeredFaceVector face point‖⁻¹ *
          (tetraFace face point 2 - (1 / 4 : ℝ))) =
      ‖centeredFaceVector face point‖⁻¹ *
        (tetraFace face point 3 - (1 / 4 : ℝ))
    have coordinateThree : tetraFace face point 3 =
        1 - tetraFace face point 0 - tetraFace face point 1 -
          tetraFace face point 2 := by
      linarith
    rw [coordinateThree]
    ring

/-- [proved-derived; formal-checked] A radial point on the face opposite `face` cannot lie in the
open star of that omitted vertex. -/
theorem radialFace_not_mem_opposite_vertexStar (face : Fin 4) (point : Triangle) :
    radialFace face point ∉ vertexStar face := by
  rintro ⟨lower, lowerLaw⟩
  rw [sphereTetraCoordinate_radialFace face lower point,
    sphereTetraCoordinate_radialFace face face point] at lowerLaw
  have normPositive : 0 < ‖centeredFaceVector face point‖ :=
    norm_pos_iff.mpr (centeredFaceVector_ne_zero face point)
  have lowerNonnegative := stdSimplex.zero_le (tetraFace face point) lower
  have faceZero := tetraFace_missing_coordinate face point
  rw [faceZero] at lowerLaw
  have inversePositive : 0 < ‖centeredFaceVector face point‖⁻¹ :=
    inv_pos.mpr normPositive
  nlinarith

/-- [proved-derived; formal-checked] Every star which carries a radial point has a label distinct
from the omitted face vertex. -/
theorem radial_carried_label_ne_opposite (face label : Fin 4) (point : Triangle)
    (carried : radialFace face point ∈ vertexStar label) :
    label ≠ face := by
  intro equal
  subst label
  exact radialFace_not_mem_opposite_vertexStar face point carried

/-- [proved-derived; formal-checked] At an actual radial tetrahedron vertex, open-star carrying
forces the unique corresponding tetrahedral label.  This is the zero-dimensional endpoint law
used after every refined radial edge telescopes. -/
theorem radialVertex_carried_label_eq (face : Fin 4) (vertex : Fin 3)
    (label : Fin 4)
    (carried : radialFace face (stdSimplex.vertex vertex) ∈ vertexStar label) :
    label = face.succAbove vertex := by
  rcases carried with ⟨lower, lowerLaw⟩
  rw [sphereTetraCoordinate_radialFace face lower,
    sphereTetraCoordinate_radialFace face label] at lowerLaw
  have normPositive : 0 < ‖centeredFaceVector face (stdSimplex.vertex vertex)‖ :=
    norm_pos_iff.mpr (centeredFaceVector_ne_zero face (stdSimplex.vertex vertex))
  have inversePositive :
      0 < ‖centeredFaceVector face (stdSimplex.vertex vertex)‖⁻¹ :=
    inv_pos.mpr normPositive
  generalize hscale :
    ‖centeredFaceVector face (stdSimplex.vertex vertex)‖⁻¹ = scale at lowerLaw
  have scalePositive : 0 < scale := by
    rw [← hscale]
    exact inversePositive
  fin_cases face <;> fin_cases vertex <;> fin_cases label <;> fin_cases lower <;>
    simp [tetraFace, Fin.succAbove] at lowerLaw ⊢ <;> nlinarith

/-- [proved-derived; formal-checked] Labels constrained to the two endpoints of one tetrahedral
edge can carry current only on that edge. -/
theorem orientedEdgeCarry_supported_on_edge (edge : TetraEdge) (initial terminal : TetraVertex)
    (initialAllowed : initial = edgeInitial edge ∨ initial = edgeTerminal edge)
    (terminalAllowed : terminal = edgeInitial edge ∨ terminal = edgeTerminal edge)
    (observed : TetraEdge) (different : observed ≠ edge) :
    orientedEdgeCarry initial terminal observed = 0 := by
  cases edge <;>
    rcases initialAllowed with initialAllowed | initialAllowed <;>
    rcases terminalAllowed with terminalAllowed | terminalAllowed <;>
    subst initial <;> subst terminal <;> cases observed <;>
    simp_all [orientedEdgeCarry, edgeInitial, edgeTerminal, Fin.ext_iff]

/-- [proved-derived; formal-checked] A current supported on one tetrahedral edge and returning its
canonical terminal-minus-initial boundary is exactly the addressed edge atom.  This is the finite
receiver used after a refined binary edge path telescopes. -/
theorem edgeChain_eq_edgeUnit_of_supported_boundary (edge : TetraEdge) (chain : EdgeChain)
    (supported : ∀ observed, observed ≠ edge → chain observed = 0)
    (returnsBoundary : vertexBoundary chain =
      vertexUnit (edgeTerminal edge) - vertexUnit (edgeInitial edge)) :
    chain = edgeUnit edge := by
  have self : chain edge = 1 := by
    cases edge with
    | e01 =>
        have coordinateReturn := congrFun returnsBoundary (1 : TetraVertex)
        simp [vertexBoundary, vertexUnit, edgeInitial, edgeTerminal,
          supported .e12 (by decide), supported .e13 (by decide)] at coordinateReturn
        exact coordinateReturn
    | e02 =>
        have coordinateReturn := congrFun returnsBoundary (2 : TetraVertex)
        simp [vertexBoundary, vertexUnit, edgeInitial, edgeTerminal,
          supported .e12 (by decide), supported .e23 (by decide)] at coordinateReturn
        exact coordinateReturn
    | e03 =>
        have coordinateReturn := congrFun returnsBoundary (3 : TetraVertex)
        simp [vertexBoundary, vertexUnit, edgeInitial, edgeTerminal,
          supported .e13 (by decide), supported .e23 (by decide)] at coordinateReturn
        exact coordinateReturn
    | e12 =>
        have coordinateReturn := congrFun returnsBoundary (2 : TetraVertex)
        simp [vertexBoundary, vertexUnit, edgeInitial, edgeTerminal,
          supported .e02 (by decide), supported .e23 (by decide)] at coordinateReturn
        exact coordinateReturn
    | e13 =>
        have coordinateReturn := congrFun returnsBoundary (3 : TetraVertex)
        simp [vertexBoundary, vertexUnit, edgeInitial, edgeTerminal,
          supported .e03 (by decide), supported .e23 (by decide)] at coordinateReturn
        exact coordinateReturn
    | e23 =>
        have coordinateReturn := congrFun returnsBoundary (3 : TetraVertex)
        simp [vertexBoundary, vertexUnit, edgeInitial, edgeTerminal,
          supported .e03 (by decide), supported .e13 (by decide)] at coordinateReturn
        exact coordinateReturn
  funext observed
  by_cases same : observed = edge
  · subst observed
    simp [edgeUnit, self]
  · simp [edgeUnit, same, supported observed same]

/-- [proved-derived; formal-checked] If all three labels avoid the omitted vertex `face`, their
oriented triangle current is supported only on that addressed face. -/
theorem orientedFaceCarry_supported_on_face (face a b c : TetraVertex)
    (aAllowed : a ≠ face) (bAllowed : b ≠ face) (cAllowed : c ≠ face)
    (observed : TetraVertex) (different : observed ≠ face) :
    orientedFaceCarry a b c observed = 0 := by
  fin_cases face <;> fin_cases a <;> fin_cases b <;> fin_cases c <;>
    fin_cases observed <;>
    simp_all [orientedFaceCarry, triangleOrientation, Fin.ext_iff]

/-- [proved-derived; formal-checked] A two-current supported on one tetrahedral face and returning
the canonical three-edge boundary is exactly that face atom.  Thus the relative face coefficient
is forced; it is not an orientation estimate. -/
theorem faceChain_eq_faceUnit_of_supported_boundary (face : TetraVertex) (chain : FaceChain)
    (supported : ∀ observed, observed ≠ face → chain observed = 0)
    (returnsBoundary : faceBoundary chain = faceBoundary (faceUnit face)) :
    chain = faceUnit face := by
  have self : chain face = 1 := by
    fin_cases face
    · have coordinateReturn := congrFun returnsBoundary TetraEdge.e12
      simp [faceBoundary, boundaryColumn, faceUnit, Fin.sum_univ_four,
        supported 1 (by decide), supported 2 (by decide),
        supported 3 (by decide)] at coordinateReturn
      exact coordinateReturn
    · have coordinateReturn := congrFun returnsBoundary TetraEdge.e02
      simp [faceBoundary, boundaryColumn, faceUnit, Fin.sum_univ_four,
        supported 0 (by decide), supported 2 (by decide),
        supported 3 (by decide)] at coordinateReturn
      exact coordinateReturn
    · have coordinateReturn := congrFun returnsBoundary TetraEdge.e01
      simp [faceBoundary, boundaryColumn, faceUnit, Fin.sum_univ_four,
        supported 0 (by decide), supported 1 (by decide),
        supported 3 (by decide)] at coordinateReturn
      exact coordinateReturn
    · have coordinateReturn := congrFun returnsBoundary TetraEdge.e12
      simp [faceBoundary, boundaryColumn, faceUnit, Fin.sum_univ_four,
        supported 0 (by decide), supported 1 (by decide),
        supported 2 (by decide)] at coordinateReturn
      exact coordinateReturn
  funext observed
  by_cases same : observed = face
  · subst observed
    simp [faceUnit, self]
  · simp [faceUnit, same, supported observed same]

section Audit

#print axioms sphereTetraCoordinate_radialFace
#print axioms radialFace_not_mem_opposite_vertexStar
#print axioms radial_carried_label_ne_opposite
#print axioms radialVertex_carried_label_eq
#print axioms orientedEdgeCarry_supported_on_edge
#print axioms edgeChain_eq_edgeUnit_of_supported_boundary
#print axioms orientedFaceCarry_supported_on_face
#print axioms faceChain_eq_faceUnit_of_supported_boundary

end Audit

end Soma.Holonics.Millennium.HodgeRadialSpernerCarry
