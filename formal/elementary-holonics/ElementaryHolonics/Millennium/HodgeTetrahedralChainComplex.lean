import ElementaryHolonics.Millennium.HodgeTetrahedralSphereComplex

/-!
# The complete finite tetrahedral chain complex

The earlier tetrahedral owner constructs the face-to-edge boundary and its exact singular
realization.  This file supplies the missing lower incidence: the six oriented edges run from the
smaller to the larger vertex, and their vertex boundary is terminal minus initial.  The resulting
degree `2 -> 1 -> 0` passage satisfies `∂₁∂₂ = 0` and is packaged as a genuine rational chain
complex, with zero carrier in every degree above two.

This is the finite target for the remaining source-specific construction.  It does not define a
map from arbitrary singular simplices by choosing a chart.  Such a map must be a genuine chain map
and must return the complete seam/subdivision testimony needed to prove its left-inverse law on the
four radial face simplices.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeTetrahedralChainComplex

open CategoryTheory
open Soma.Holonics.Millennium.HodgeTetrahedralSphereComplex

abbrev TetraVertex := Fin 4
abbrev VertexChain := TetraVertex → ℚ

/-- The initial vertex of an edge in the globally increasing orientation. -/
def edgeInitial : TetraEdge → TetraVertex
  | .e01 => 0
  | .e02 => 0
  | .e03 => 0
  | .e12 => 1
  | .e13 => 1
  | .e23 => 2

/-- The terminal vertex of an edge in the globally increasing orientation. -/
def edgeTerminal : TetraEdge → TetraVertex
  | .e01 => 1
  | .e02 => 2
  | .e03 => 3
  | .e12 => 2
  | .e13 => 3
  | .e23 => 3

theorem edgeInitial_lt_edgeTerminal (edge : TetraEdge) :
    edgeInitial edge < edgeTerminal edge := by
  cases edge <;> decide

/-- One addressed edge occurrence in the finite edge carrier. -/
def edgeUnit (edge : TetraEdge) : EdgeChain :=
  fun observed => if observed = edge then 1 else 0

/-- One addressed vertex occurrence. -/
def vertexUnit (vertex : TetraVertex) : VertexChain :=
  fun observed => if observed = vertex then 1 else 0

/-- The terminal-minus-initial incidence of every finite one-chain. -/
def vertexBoundary : EdgeChain →ₗ[ℚ] VertexChain where
  toFun chain := ![
    -chain .e01 - chain .e02 - chain .e03,
    chain .e01 - chain .e12 - chain .e13,
    chain .e02 + chain .e12 - chain .e23,
    chain .e03 + chain .e13 + chain .e23]
  map_add' left right := by
    funext vertex
    fin_cases vertex <;> simp <;> ring
  map_smul' scalar chain := by
    funext vertex
    fin_cases vertex <;> simp <;> ring

/-- The coordinate formula really is terminal minus initial on each addressed edge. -/
theorem vertexBoundary_edgeUnit (edge : TetraEdge) :
    vertexBoundary (edgeUnit edge) =
      vertexUnit (edgeTerminal edge) - vertexUnit (edgeInitial edge) := by
  cases edge <;>
    funext vertex <;>
    fin_cases vertex <;>
    simp [vertexBoundary, edgeUnit, vertexUnit, edgeInitial, edgeTerminal]

/-- The existing face incidence and the new vertex incidence compose to zero exactly. -/
theorem vertexBoundary_faceBoundary (chain : FaceChain) :
    vertexBoundary (faceBoundary chain) = 0 := by
  funext vertex
  fin_cases vertex <;>
    simp [vertexBoundary, faceBoundary, boundaryColumn, Fin.sum_univ_four] <;>
    ring

/-- One exact face current filling a finite tetrahedral edge cycle.  The zeroth face coefficient is
the gauge choice; the remaining three coefficients are read from the opposite edges. -/
def edgeCycleFiller (chain : EdgeChain) : FaceChain :=
  ![0, chain .e23, chain .e13, chain .e12]

/-- [proved-derived; formal-checked] Every closed finite tetrahedral one-current is the boundary of
the explicit face current above.  Thus the finite target has `H₁ = 0` without a dimension count or
an admitted rank computation. -/
theorem faceBoundary_edgeCycleFiller (chain : EdgeChain)
    (closed : vertexBoundary chain = 0) :
    faceBoundary (edgeCycleFiller chain) = chain := by
  have h0 := congrFun closed (0 : Fin 4)
  have h1 := congrFun closed (1 : Fin 4)
  have h2 := congrFun closed (2 : Fin 4)
  have h3 := congrFun closed (3 : Fin 4)
  simp [vertexBoundary] at h0 h1 h2 h3
  funext edge
  cases edge <;>
    simp [faceBoundary, edgeCycleFiller, boundaryColumn, Fin.sum_univ_four] <;>
    linarith

/-- The addressed rational carrier in each homological degree. -/
abbrev tetrahedralChainModule : ℕ → ModuleCat ℚ
  | 0 => ModuleCat.of ℚ VertexChain
  | 1 => ModuleCat.of ℚ EdgeChain
  | 2 => ModuleCat.of ℚ FaceChain
  | _ => ModuleCat.of ℚ (Fin 0 → ℚ)

/-- The only nonzero differentials are edge-to-vertex and face-to-edge incidence. -/
def tetrahedralDifferential : (degree : ℕ) →
    tetrahedralChainModule (degree + 1) ⟶ tetrahedralChainModule degree
  | 0 => ModuleCat.ofHom vertexBoundary
  | 1 => ModuleCat.ofHom faceBoundary
  | _ + 2 => 0

theorem tetrahedralDifferential_comp (degree : ℕ) :
    tetrahedralDifferential (degree + 1) ≫ tetrahedralDifferential degree = 0 := by
  cases degree with
  | zero =>
      ext chain
      exact vertexBoundary_faceBoundary chain
  | succ degree =>
      cases degree with
      | zero => rw [show tetrahedralDifferential 2 = 0 by rfl, Limits.zero_comp]
      | succ degree => simp [tetrahedralDifferential]

/-- The complete finite tetrahedral `2 -> 1 -> 0` chain complex. -/
abbrev tetrahedralChainComplex : ChainComplex (ModuleCat ℚ) ℕ :=
  ChainComplex.of tetrahedralChainModule tetrahedralDifferential
    tetrahedralDifferential_comp

theorem tetrahedralChainComplex_d_zero :
    tetrahedralChainComplex.d 1 0 = ModuleCat.ofHom vertexBoundary := by
  exact ChainComplex.of_d tetrahedralChainModule tetrahedralDifferential 0

theorem tetrahedralChainComplex_d_one :
    tetrahedralChainComplex.d 2 1 = ModuleCat.ofHom faceBoundary := by
  exact ChainComplex.of_d tetrahedralChainModule tetrahedralDifferential 1

theorem tetrahedralChainComplex_d_three_two :
    tetrahedralChainComplex.d 3 2 = 0 := by
  exact ChainComplex.of_d tetrahedralChainModule tetrahedralDifferential 2

section Audit

#print axioms edgeInitial_lt_edgeTerminal
#print axioms vertexBoundary_edgeUnit
#print axioms vertexBoundary_faceBoundary
#print axioms faceBoundary_edgeCycleFiller
#print axioms tetrahedralDifferential_comp
#print axioms tetrahedralChainComplex_d_zero
#print axioms tetrahedralChainComplex_d_one
#print axioms tetrahedralChainComplex_d_three_two

end Audit

end Soma.Holonics.Millennium.HodgeTetrahedralChainComplex
