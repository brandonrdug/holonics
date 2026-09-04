import ElementaryHolonics.Foundation.Holon
import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
# Exact diagonal-to-product chain transport in degrees zero through three

A product simplex arrives diagonally: both factors are sampled over the same ordered source
simplex.  The receiving product complex instead separates it into the three degree-two incidence
populations `0×2`, `1×1`, and `2×0`.  This file constructs that separation on free rational
currents while retaining every ordered pair occurrence.

The main theorem is the low-degree local-to-global law: diagonal boundary followed by separation
is exactly separated boundary.  It is the degree-two Alexander--Whitney law, presented here as an
elementary holonic transport rather than as an endpoint-only tensor identity.  In particular the
middle `1×1` population is the off-axis interaction current; it is neither silently discarded nor
identified with either ruling.
-/

noncomputable section

namespace Soma.Holonics.DiagonalChainTransport

open CategoryTheory
open Simplicial

/-- An addressed simplex occurrence in a simplicial set. -/
abbrev Simplex (X : SSet) (degree : ℕ) :=
  X.obj (Opposite.op (SimplexCategory.mk degree))

/-- One oriented codimension-one face. -/
def face {X : SSet} {degree : ℕ} (omitted : Fin (degree + 2))
    (simplex : Simplex X (degree + 1)) : Simplex X degree :=
  X.δ omitted simplex

/-- A free rational current retains the complete finite occurrence population. -/
abbrev Current (Occurrence : Type*) := Occurrence →₀ ℚ

/-- One occurrence with unit coefficient. -/
def generator {Occurrence : Type*} (occurrence : Occurrence) : Current Occurrence :=
  Finsupp.single occurrence 1

/-- Coproduct-linear extension of an occurrence receiver. -/
def extend {Source Target : Type*} (receiver : Source → Current Target) :
    Current Source →ₗ[ℚ] Current Target :=
  Finsupp.linearCombination ℚ receiver

@[simp]
theorem extend_generator {Source Target : Type*} (receiver : Source → Current Target)
    (source : Source) :
    extend receiver (generator source) = receiver source := by
  simp [extend, generator]

/-- One simplex in each factor, still sharing a single source degree. -/
abbrev DiagonalOccurrence (X Y : SSet) (degree : ℕ) :=
  Simplex X degree × Simplex Y degree

/-- Componentwise face transport retains the diagonal source lineage. -/
def diagonalFace {X Y : SSet} {degree : ℕ} (omitted : Fin (degree + 2))
    (occurrence : DiagonalOccurrence X Y (degree + 1)) :
    DiagonalOccurrence X Y degree :=
  (face omitted occurrence.1, face omitted occurrence.2)

def diagonalBoundaryOneAtom {X Y : SSet}
    (occurrence : DiagonalOccurrence X Y 1) :
    Current (DiagonalOccurrence X Y 0) :=
  generator (diagonalFace 0 occurrence) - generator (diagonalFace 1 occurrence)

def diagonalBoundaryTwoAtom {X Y : SSet}
    (occurrence : DiagonalOccurrence X Y 2) :
    Current (DiagonalOccurrence X Y 1) :=
  generator (diagonalFace 0 occurrence) - generator (diagonalFace 1 occurrence) +
    generator (diagonalFace 2 occurrence)

def diagonalBoundaryOne (X Y : SSet) :
    Current (DiagonalOccurrence X Y 1) →ₗ[ℚ]
      Current (DiagonalOccurrence X Y 0) :=
  extend diagonalBoundaryOneAtom

def diagonalBoundaryTwo (X Y : SSet) :
    Current (DiagonalOccurrence X Y 2) →ₗ[ℚ]
      Current (DiagonalOccurrence X Y 1) :=
  extend diagonalBoundaryTwoAtom

def diagonalBoundaryThreeAtom {X Y : SSet}
    (occurrence : DiagonalOccurrence X Y 3) :
    Current (DiagonalOccurrence X Y 2) :=
  generator (diagonalFace 0 occurrence) - generator (diagonalFace 1 occurrence) +
    generator (diagonalFace 2 occurrence) - generator (diagonalFace 3 occurrence)

def diagonalBoundaryThree (X Y : SSet) :
    Current (DiagonalOccurrence X Y 3) →ₗ[ℚ]
      Current (DiagonalOccurrence X Y 2) :=
  extend diagonalBoundaryThreeAtom

/-- The two total-degree-one axes. -/
inductive TotalOneOccurrence (X Y : SSet)
  | left : Simplex X 0 → Simplex Y 1 → TotalOneOccurrence X Y
  | right : Simplex X 1 → Simplex Y 0 → TotalOneOccurrence X Y

/-- The three total-degree-two axes, including the genuine off-axis `1×1` interaction. -/
inductive TotalTwoOccurrence (X Y : SSet)
  | left : Simplex X 0 → Simplex Y 2 → TotalTwoOccurrence X Y
  | middle : Simplex X 1 → Simplex Y 1 → TotalTwoOccurrence X Y
  | right : Simplex X 2 → Simplex Y 0 → TotalTwoOccurrence X Y

/-- The four total-degree-three axes.  The two interior populations retain the distinct
`1×2` and `2×1` incidence orientations rather than merging them into one mixed count. -/
inductive TotalThreeOccurrence (X Y : SSet)
  | left : Simplex X 0 → Simplex Y 3 → TotalThreeOccurrence X Y
  | leftMiddle : Simplex X 1 → Simplex Y 2 → TotalThreeOccurrence X Y
  | rightMiddle : Simplex X 2 → Simplex Y 1 → TotalThreeOccurrence X Y
  | right : Simplex X 3 → Simplex Y 0 → TotalThreeOccurrence X Y

/-- The common total-degree-zero receiver. -/
abbrev TotalZeroOccurrence (X Y : SSet) := Simplex X 0 × Simplex Y 0

def totalBoundaryOneAtom {X Y : SSet} : TotalOneOccurrence X Y →
    Current (TotalZeroOccurrence X Y)
  | .left x y =>
      generator (x, face 0 y) - generator (x, face 1 y)
  | .right x y =>
      generator (face 0 x, y) - generator (face 1 x, y)

def totalBoundaryTwoAtom {X Y : SSet} : TotalTwoOccurrence X Y →
    Current (TotalOneOccurrence X Y)
  | .left x y =>
      generator (.left x (face 0 y)) - generator (.left x (face 1 y)) +
        generator (.left x (face 2 y))
  | .middle x y =>
      generator (.left (face 0 x) y) - generator (.left (face 1 x) y) -
        generator (.right x (face 0 y)) + generator (.right x (face 1 y))
  | .right x y =>
      generator (.right (face 0 x) y) - generator (.right (face 1 x) y) +
        generator (.right (face 2 x) y)

def totalBoundaryOne (X Y : SSet) : Current (TotalOneOccurrence X Y) →ₗ[ℚ]
    Current (TotalZeroOccurrence X Y) :=
  extend totalBoundaryOneAtom

def totalBoundaryTwo (X Y : SSet) : Current (TotalTwoOccurrence X Y) →ₗ[ℚ]
    Current (TotalOneOccurrence X Y) :=
  extend totalBoundaryTwoAtom

/-- Tensor-product boundary on each retained total-degree-three axis.  The sign of the second
factor is the parity of the first factor's degree. -/
def totalBoundaryThreeAtom {X Y : SSet} : TotalThreeOccurrence X Y →
    Current (TotalTwoOccurrence X Y)
  | .left x y =>
      generator (.left x (face 0 y)) - generator (.left x (face 1 y)) +
        generator (.left x (face 2 y)) - generator (.left x (face 3 y))
  | .leftMiddle x y =>
      generator (.left (face 0 x) y) - generator (.left (face 1 x) y) -
        generator (.middle x (face 0 y)) + generator (.middle x (face 1 y)) -
          generator (.middle x (face 2 y))
  | .rightMiddle x y =>
      generator (.middle (face 0 x) y) - generator (.middle (face 1 x) y) +
        generator (.middle (face 2 x) y) + generator (.right x (face 0 y)) -
          generator (.right x (face 1 y))
  | .right x y =>
      generator (.right (face 0 x) y) - generator (.right (face 1 x) y) +
        generator (.right (face 2 x) y) - generator (.right (face 3 x) y)

def totalBoundaryThree (X Y : SSet) : Current (TotalThreeOccurrence X Y) →ₗ[ℚ]
    Current (TotalTwoOccurrence X Y) :=
  extend totalBoundaryThreeAtom

/-- Initial vertex of an addressed edge. -/
def initialVertex {X : SSet} (edge : Simplex X 1) : Simplex X 0 :=
  face 1 edge

/-- Terminal vertex of an addressed edge. -/
def terminalVertex {X : SSet} (edge : Simplex X 1) : Simplex X 0 :=
  face 0 edge

/-- Initial vertex of an addressed triangle. -/
def triangleInitialVertex {X : SSet} (triangle : Simplex X 2) : Simplex X 0 :=
  initialVertex (face 2 triangle)

/-- Terminal vertex of an addressed triangle. -/
def triangleTerminalVertex {X : SSet} (triangle : Simplex X 2) : Simplex X 0 :=
  terminalVertex (face 0 triangle)

/-- Degree-one diagonal separation into the `0×1` and `1×0` axes. -/
def separateOneAtom {X Y : SSet} (occurrence : DiagonalOccurrence X Y 1) :
    Current (TotalOneOccurrence X Y) :=
  generator (.left (initialVertex occurrence.1) occurrence.2) +
    generator (.right occurrence.1 (terminalVertex occurrence.2))

/-- Degree-two diagonal separation into `0×2`, `1×1`, and `2×0`. -/
def separateTwoAtom {X Y : SSet} (occurrence : DiagonalOccurrence X Y 2) :
    Current (TotalTwoOccurrence X Y) :=
  generator (.left (triangleInitialVertex occurrence.1) occurrence.2) +
    generator (.middle (face 2 occurrence.1) (face 0 occurrence.2)) +
    generator (.right occurrence.1 (triangleTerminalVertex occurrence.2))

/-- Initial vertex of an addressed tetrahedron. -/
def tetrahedronInitialVertex {X : SSet} (tetrahedron : Simplex X 3) : Simplex X 0 :=
  triangleInitialVertex (face 3 tetrahedron)

/-- Terminal vertex of an addressed tetrahedron. -/
def tetrahedronTerminalVertex {X : SSet} (tetrahedron : Simplex X 3) : Simplex X 0 :=
  triangleTerminalVertex (face 0 tetrahedron)

/-- Front edge with ordered vertices `0,1`. -/
def tetrahedronFrontEdge {X : SSet} (tetrahedron : Simplex X 3) : Simplex X 1 :=
  face 2 (face 3 tetrahedron)

/-- Back edge with ordered vertices `2,3`. -/
def tetrahedronBackEdge {X : SSet} (tetrahedron : Simplex X 3) : Simplex X 1 :=
  face 0 (face 0 tetrahedron)

/-- Degree-three diagonal separation into all four ordered total-degree axes. -/
def separateThreeAtom {X Y : SSet} (occurrence : DiagonalOccurrence X Y 3) :
    Current (TotalThreeOccurrence X Y) :=
  generator (.left (tetrahedronInitialVertex occurrence.1) occurrence.2) +
    generator (.leftMiddle (tetrahedronFrontEdge occurrence.1) (face 0 occurrence.2)) +
    generator (.rightMiddle (face 3 occurrence.1) (tetrahedronBackEdge occurrence.2)) +
    generator (.right occurrence.1 (tetrahedronTerminalVertex occurrence.2))

def separateOne (X Y : SSet) : Current (DiagonalOccurrence X Y 1) →ₗ[ℚ]
    Current (TotalOneOccurrence X Y) :=
  extend separateOneAtom

def separateTwo (X Y : SSet) : Current (DiagonalOccurrence X Y 2) →ₗ[ℚ]
    Current (TotalTwoOccurrence X Y) :=
  extend separateTwoAtom

def separateThree (X Y : SSet) : Current (DiagonalOccurrence X Y 3) →ₗ[ℚ]
    Current (TotalThreeOccurrence X Y) :=
  extend separateThreeAtom

/-- One vertex occurrence repeated into an edge. -/
def repeatVertexEdge {X : SSet} (vertex : Simplex X 0) : Simplex X 1 :=
  X.σ 0 vertex

/-- One vertex occurrence repeated into a triangle. -/
def repeatVertexTriangle {X : SSet} (vertex : Simplex X 0) : Simplex X 2 :=
  X.σ 0 (X.σ 0 vertex)

/-- One vertex occurrence repeated into a tetrahedron. -/
def repeatVertexTetrahedron {X : SSet} (vertex : Simplex X 0) : Simplex X 3 :=
  X.σ 0 (X.σ 0 (X.σ 0 vertex))

/-- Rejoin one separated degree-one axis into a diagonal occurrence. -/
def rejoinOneAtom {X Y : SSet} : TotalOneOccurrence X Y →
    Current (DiagonalOccurrence X Y 1)
  | .left x y => generator (repeatVertexEdge x, y)
  | .right x y => generator (x, repeatVertexEdge y)

/-- Rejoin the three total-degree-two axes.  The middle square is its two ordered triangular
shuffles with opposite signs; neither diagonal is treated as an unordered tensor shadow. -/
def rejoinTwoAtom {X Y : SSet} : TotalTwoOccurrence X Y →
    Current (DiagonalOccurrence X Y 2)
  | .left x y => generator (repeatVertexTriangle x, y)
  | .middle x y =>
      generator (X.σ 1 x, Y.σ 0 y) - generator (X.σ 0 x, Y.σ 1 y)
  | .right x y => generator (x, repeatVertexTriangle y)

def rejoinOne (X Y : SSet) : Current (TotalOneOccurrence X Y) →ₗ[ℚ]
    Current (DiagonalOccurrence X Y 1) :=
  extend rejoinOneAtom

def rejoinTwo (X Y : SSet) : Current (TotalTwoOccurrence X Y) →ₗ[ℚ]
    Current (DiagonalOccurrence X Y 2) :=
  extend rejoinTwoAtom

/-- Rejoin the four total-degree-three axes.  Each interior axis is the complete signed
shuffle population: three occurrences for `1×2` and three for `2×1`.  Thus the return retains
which of the three ordered source steps belonged to which factor rather than keeping only the
diagonal endpoint pair. -/
def rejoinThreeAtom {X Y : SSet} : TotalThreeOccurrence X Y →
    Current (DiagonalOccurrence X Y 3)
  | .left x y => generator (repeatVertexTetrahedron x, y)
  | .leftMiddle x y =>
      generator (X.σ 2 (X.σ 1 x), Y.σ 0 y) -
        generator (X.σ 2 (X.σ 0 x), Y.σ 1 y) +
          generator (X.σ 1 (X.σ 0 x), Y.σ 2 y)
  | .rightMiddle x y =>
      generator (X.σ 2 x, Y.σ 1 (Y.σ 0 y)) -
        generator (X.σ 1 x, Y.σ 2 (Y.σ 0 y)) +
          generator (X.σ 0 x, Y.σ 2 (Y.σ 1 y))
  | .right x y => generator (x, repeatVertexTetrahedron y)

def rejoinThree (X Y : SSet) : Current (TotalThreeOccurrence X Y) →ₗ[ℚ]
    Current (DiagonalOccurrence X Y 3) :=
  extend rejoinThreeAtom

/-- The degree-one part of the retained diagonal reconstruction homotopy. -/
def diagonalReconstructionFillerOneAtom {X Y : SSet}
    (occurrence : DiagonalOccurrence X Y 1) :
    Current (DiagonalOccurrence X Y 2) :=
  generator (X.σ 0 occurrence.1, Y.σ 1 occurrence.2)

def diagonalReconstructionFillerOne (X Y : SSet) :
    Current (DiagonalOccurrence X Y 1) →ₗ[ℚ]
      Current (DiagonalOccurrence X Y 2) :=
  extend diagonalReconstructionFillerOneAtom

/-- The degree-two filler keeps four independently addressed tetrahedral occurrences.  The terms
are the exact low-degree prism populations forced by the separate--shuffle return. -/
def diagonalReconstructionFillerTwoAtom {X Y : SSet}
    (occurrence : DiagonalOccurrence X Y 2) :
    Current (DiagonalOccurrence X Y 3) :=
  -generator
      (X.σ 0 (X.σ 0 (face 2 occurrence.1)), Y.σ 2 occurrence.2) +
    generator
      (X.σ 2 (X.σ 0 (face 2 occurrence.1)), Y.σ 1 occurrence.2) +
    generator
      (X.σ 0 occurrence.1, Y.σ 1 (Y.σ 1 (face 1 occurrence.2))) -
    generator (X.σ 1 occurrence.1, Y.σ 2 occurrence.2)

def diagonalReconstructionFillerTwo (X Y : SSet) :
    Current (DiagonalOccurrence X Y 2) →ₗ[ℚ]
      Current (DiagonalOccurrence X Y 3) :=
  extend diagonalReconstructionFillerTwoAtom

/-- The degree-one residue retained after separating and then rejoining the two product axes. -/
def diagonalRoundTripDefectOne (X Y : SSet) :
    Current (DiagonalOccurrence X Y 1) →ₗ[ℚ]
      Current (DiagonalOccurrence X Y 1) :=
  (rejoinOne X Y).comp (separateOne X Y) - LinearMap.id

/-- The degree-two reconstruction residue retained after separating the three product axes and
rejoining their ordered shuffles.  It is deliberately not quotiented by degeneracies. -/
def diagonalRoundTripDefectTwo (X Y : SSet) :
    Current (DiagonalOccurrence X Y 2) →ₗ[ℚ]
      Current (DiagonalOccurrence X Y 2) :=
  (rejoinTwo X Y).comp (separateTwo X Y) - LinearMap.id

@[simp] private theorem face_zero_repeatTriangle {X : SSet} (vertex : Simplex X 0) :
    face 0 (repeatVertexTriangle vertex) = repeatVertexEdge vertex := by
  exact X.δ_comp_σ_self_apply 0 (X.σ 0 vertex)

@[simp] private theorem face_one_repeatTriangle {X : SSet} (vertex : Simplex X 0) :
    face 1 (repeatVertexTriangle vertex) = repeatVertexEdge vertex := by
  exact X.δ_comp_σ_succ_apply 0 (X.σ 0 vertex)

@[simp] private theorem face_two_repeatTriangle {X : SSet} (vertex : Simplex X 0) :
    face 2 (repeatVertexTriangle vertex) = repeatVertexEdge vertex := by
  have law := X.δ_comp_σ_of_gt_apply
    (i := (1 : Fin 2)) (j := (0 : Fin 1)) (by decide) (X.σ 0 vertex)
  change X.δ 2 (X.σ 0 (X.σ 0 vertex)) = X.σ 0 vertex
  have inner : X.δ (1 : Fin 2) (X.σ (0 : Fin 1) vertex) = vertex := by
    simpa using X.δ_comp_σ_succ_apply (0 : Fin 1) vertex
  calc
    _ = X.σ 0 (X.δ 1 (X.σ 0 vertex)) := by simpa using law
    _ = X.σ 0 vertex := congrArg (X.σ (0 : Fin 1)) inner

@[simp] private theorem face_zero_repeatLast {X : SSet} (edge : Simplex X 1) :
    face 0 (X.σ 1 edge) = repeatVertexEdge (face 0 edge) := by
  simpa [face, repeatVertexEdge] using
    (X.δ_comp_σ_of_le_apply (i := (0 : Fin 2)) (j := 0)
      (by decide) edge)

@[simp] private theorem face_one_repeatLast {X : SSet} (edge : Simplex X 1) :
    face 1 (X.σ 1 edge) = edge := by
  exact X.δ_comp_σ_self_apply 1 edge

@[simp] private theorem face_two_repeatLast {X : SSet} (edge : Simplex X 1) :
    face 2 (X.σ 1 edge) = edge := by
  exact X.δ_comp_σ_succ_apply 1 edge

@[simp] private theorem face_zero_repeatFirst {X : SSet} (edge : Simplex X 1) :
    face 0 (X.σ 0 edge) = edge := by
  exact X.δ_comp_σ_self_apply 0 edge

@[simp] private theorem face_one_repeatFirst {X : SSet} (edge : Simplex X 1) :
    face 1 (X.σ 0 edge) = edge := by
  exact X.δ_comp_σ_succ_apply 0 edge

@[simp] private theorem face_two_repeatFirst {X : SSet} (edge : Simplex X 1) :
    face 2 (X.σ 0 edge) = repeatVertexEdge (face 1 edge) := by
  have law := X.δ_comp_σ_of_gt_apply
    (i := (1 : Fin 2)) (j := (0 : Fin 1)) (by decide) edge
  simpa [face, repeatVertexEdge] using law

@[simp] private theorem face_zero_degenerateZeroTriangle {X : SSet}
    (triangle : Simplex X 2) : face 0 (X.σ 0 triangle) = triangle := by
  exact X.δ_comp_σ_self_apply 0 triangle

@[simp] private theorem face_one_degenerateZeroTriangle {X : SSet}
    (triangle : Simplex X 2) : face 1 (X.σ 0 triangle) = triangle := by
  exact X.δ_comp_σ_succ_apply 0 triangle

@[simp] private theorem face_two_degenerateZeroTriangle {X : SSet}
    (triangle : Simplex X 2) :
    face 2 (X.σ 0 triangle) = X.σ 0 (face 1 triangle) := by
  have law := X.δ_comp_σ_of_gt_apply
    (i := (1 : Fin 3)) (j := (0 : Fin 2)) (by decide) triangle
  simpa [face] using law

@[simp] private theorem face_three_degenerateZeroTriangle {X : SSet}
    (triangle : Simplex X 2) :
    face 3 (X.σ 0 triangle) = X.σ 0 (face 2 triangle) := by
  have law := X.δ_comp_σ_of_gt_apply
    (i := (2 : Fin 3)) (j := (0 : Fin 2)) (by decide) triangle
  simpa [face] using law

@[simp] private theorem face_zero_degenerateOneTriangle {X : SSet}
    (triangle : Simplex X 2) :
    face 0 (X.σ 1 triangle) = X.σ 0 (face 0 triangle) := by
  have law := X.δ_comp_σ_of_le_apply
    (i := (0 : Fin 3)) (j := (0 : Fin 2)) (by decide) triangle
  simpa [face] using law

@[simp] private theorem face_one_degenerateOneTriangle {X : SSet}
    (triangle : Simplex X 2) : face 1 (X.σ 1 triangle) = triangle := by
  exact X.δ_comp_σ_self_apply 1 triangle

@[simp] private theorem face_two_degenerateOneTriangle {X : SSet}
    (triangle : Simplex X 2) : face 2 (X.σ 1 triangle) = triangle := by
  exact X.δ_comp_σ_succ_apply 1 triangle

@[simp] private theorem face_three_degenerateOneTriangle {X : SSet}
    (triangle : Simplex X 2) :
    face 3 (X.σ 1 triangle) = X.σ 1 (face 2 triangle) := by
  have law := X.δ_comp_σ_of_gt_apply
    (i := (2 : Fin 3)) (j := (1 : Fin 2)) (by decide) triangle
  simpa [face] using law

@[simp] private theorem face_zero_degenerateTwoTriangle {X : SSet}
    (triangle : Simplex X 2) :
    face 0 (X.σ 2 triangle) = X.σ 1 (face 0 triangle) := by
  have law := X.δ_comp_σ_of_le_apply
    (i := (0 : Fin 3)) (j := (1 : Fin 2)) (by decide) triangle
  simpa [face] using law

@[simp] private theorem face_one_degenerateTwoTriangle {X : SSet}
    (triangle : Simplex X 2) :
    face 1 (X.σ 2 triangle) = X.σ 1 (face 1 triangle) := by
  have law := X.δ_comp_σ_of_le_apply
    (i := (1 : Fin 3)) (j := (1 : Fin 2)) (by decide) triangle
  simpa [face] using law

@[simp] private theorem face_two_degenerateTwoTriangle {X : SSet}
    (triangle : Simplex X 2) : face 2 (X.σ 2 triangle) = triangle := by
  exact X.δ_comp_σ_self_apply 2 triangle

@[simp] private theorem face_three_degenerateTwoTriangle {X : SSet}
    (triangle : Simplex X 2) : face 3 (X.σ 2 triangle) = triangle := by
  exact X.δ_comp_σ_succ_apply 2 triangle

@[simp] private theorem face_zero_repeatTetrahedron {X : SSet}
    (vertex : Simplex X 0) :
    face 0 (repeatVertexTetrahedron vertex) = repeatVertexTriangle vertex := by
  exact X.δ_comp_σ_self_apply 0 (repeatVertexTriangle vertex)

@[simp] private theorem face_one_repeatTetrahedron {X : SSet}
    (vertex : Simplex X 0) :
    face 1 (repeatVertexTetrahedron vertex) = repeatVertexTriangle vertex := by
  exact X.δ_comp_σ_succ_apply 0 (repeatVertexTriangle vertex)

@[simp] private theorem face_two_repeatTetrahedron {X : SSet}
    (vertex : Simplex X 0) :
    face 2 (repeatVertexTetrahedron vertex) = repeatVertexTriangle vertex := by
  change face 2 (X.σ 0 (repeatVertexTriangle vertex)) = repeatVertexTriangle vertex
  rw [face_two_degenerateZeroTriangle, face_one_repeatTriangle]
  rfl

@[simp] private theorem face_three_repeatTetrahedron {X : SSet}
    (vertex : Simplex X 0) :
    face 3 (repeatVertexTetrahedron vertex) = repeatVertexTriangle vertex := by
  change face 3 (X.σ 0 (repeatVertexTriangle vertex)) = repeatVertexTriangle vertex
  rw [face_three_degenerateZeroTriangle, face_two_repeatTriangle]
  rfl

@[simp] private theorem repeatLast_repeatVertexEdge {X : SSet}
    (vertex : Simplex X 0) :
    X.σ 1 (repeatVertexEdge vertex) = repeatVertexTriangle vertex := by
  symm
  simpa [repeatVertexEdge, repeatVertexTriangle] using
    (X.σ_comp_σ_apply (i := (0 : Fin 1)) (j := (0 : Fin 1)) (by decide) vertex)

/-- [proved-derived; formal-checked] Rejoining one separated degree-three occurrence commutes
with its complete tensor-product boundary.  The six interior shuffle occurrences cancel in the
three shared square faces and leave precisely the four retained degree-two axes. -/
theorem boundary_rejoinThreeAtom {X Y : SSet} (occurrence : TotalThreeOccurrence X Y) :
    diagonalBoundaryThree X Y (rejoinThreeAtom occurrence) =
      rejoinTwo X Y (totalBoundaryThreeAtom occurrence) := by
  cases occurrence with
  | left x y =>
      simp [diagonalBoundaryThree, diagonalBoundaryThreeAtom, rejoinThreeAtom,
        rejoinTwo, rejoinTwoAtom, totalBoundaryThreeAtom, diagonalFace,
        extend_generator]
  | leftMiddle x y =>
      simp [diagonalBoundaryThree, diagonalBoundaryThreeAtom, rejoinThreeAtom,
        rejoinTwo, rejoinTwoAtom, totalBoundaryThreeAtom, diagonalFace,
        extend_generator]
      module
  | rightMiddle x y =>
      simp [diagonalBoundaryThree, diagonalBoundaryThreeAtom, rejoinThreeAtom,
        rejoinTwo, rejoinTwoAtom, totalBoundaryThreeAtom, diagonalFace,
        extend_generator]
      module
  | right x y =>
      simp [diagonalBoundaryThree, diagonalBoundaryThreeAtom, rejoinThreeAtom,
        rejoinTwo, rejoinTwoAtom, totalBoundaryThreeAtom, diagonalFace,
        extend_generator]

/-- [proved-derived; formal-checked] The degree-three shuffle return commutes with boundary on
every finite rational separated current. -/
theorem boundary_rejoinThree (X Y : SSet) :
    (diagonalBoundaryThree X Y).comp (rejoinThree X Y) =
      (rejoinTwo X Y).comp (totalBoundaryThree X Y) := by
  apply Finsupp.lhom_ext
  intro occurrence coefficient
  rw [show Finsupp.single occurrence coefficient =
      coefficient • generator occurrence by simp [generator]]
  simp only [LinearMap.comp_apply, map_smul, rejoinThree,
    totalBoundaryThree, extend_generator]
  exact congrArg (coefficient • ·) (boundary_rejoinThreeAtom occurrence)

/-- [proved-derived; formal-checked] Rejoining either polarized degree-one axis preserves its
complete endpoint difference. -/
theorem boundary_rejoinOneAtom {X Y : SSet} (occurrence : TotalOneOccurrence X Y) :
    diagonalBoundaryOne X Y (rejoinOneAtom occurrence) =
      totalBoundaryOneAtom occurrence := by
  cases occurrence with
  | left x y =>
      have faceZero : face 0 (repeatVertexEdge x) = x := by
        exact X.δ_comp_σ_self_apply 0 x
      have faceOne : face 1 (repeatVertexEdge x) = x := by
        exact X.δ_comp_σ_succ_apply 0 x
      simp only [diagonalBoundaryOne, rejoinOneAtom, extend_generator,
        diagonalBoundaryOneAtom, diagonalFace, totalBoundaryOneAtom]
      rw [faceZero, faceOne]
  | right x y =>
      have faceZero : face 0 (repeatVertexEdge y) = y := by
        exact Y.δ_comp_σ_self_apply 0 y
      have faceOne : face 1 (repeatVertexEdge y) = y := by
        exact Y.δ_comp_σ_succ_apply 0 y
      simp only [diagonalBoundaryOne, rejoinOneAtom, extend_generator,
        diagonalBoundaryOneAtom, diagonalFace, totalBoundaryOneAtom]
      rw [faceZero, faceOne]

/-- [proved-derived; formal-checked] The degree-one shuffle return is a chain map on every
finite addressed current. -/
theorem boundary_rejoinOne (X Y : SSet) :
    (diagonalBoundaryOne X Y).comp (rejoinOne X Y) = totalBoundaryOne X Y := by
  apply Finsupp.lhom_ext
  intro occurrence coefficient
  rw [show Finsupp.single occurrence coefficient =
      coefficient • generator occurrence by simp [generator]]
  simp only [LinearMap.comp_apply, map_smul, rejoinOne,
    totalBoundaryOne, extend_generator]
  exact congrArg (coefficient • ·) (boundary_rejoinOneAtom occurrence)

/-- [proved-derived; formal-checked] Rejoining one separated degree-two occurrence commutes with
its complete boundary. -/
theorem boundary_rejoinTwoAtom {X Y : SSet} (occurrence : TotalTwoOccurrence X Y) :
    diagonalBoundaryTwo X Y (rejoinTwoAtom occurrence) =
      rejoinOne X Y (totalBoundaryTwoAtom occurrence) := by
  cases occurrence with
  | left x y =>
      simp [diagonalBoundaryTwo, diagonalBoundaryTwoAtom, rejoinTwoAtom,
        rejoinOne, rejoinOneAtom, totalBoundaryTwoAtom, diagonalFace,
        extend_generator]
  | middle x y =>
      simp [diagonalBoundaryTwo, diagonalBoundaryTwoAtom, rejoinTwoAtom,
        rejoinOne, rejoinOneAtom, totalBoundaryTwoAtom, diagonalFace,
        extend_generator]
      module
  | right x y =>
      simp [diagonalBoundaryTwo, diagonalBoundaryTwoAtom, rejoinTwoAtom,
        rejoinOne, rejoinOneAtom, totalBoundaryTwoAtom, diagonalFace,
        extend_generator]

/-- [proved-derived; formal-checked] The rejoining boundary square commutes on every finite
rational separated current. -/
theorem boundary_rejoinTwo (X Y : SSet) :
    (diagonalBoundaryTwo X Y).comp (rejoinTwo X Y) =
      (rejoinOne X Y).comp (totalBoundaryTwo X Y) := by
  apply Finsupp.lhom_ext
  intro occurrence coefficient
  rw [show Finsupp.single occurrence coefficient =
      coefficient • generator occurrence by simp [generator]]
  simp only [LinearMap.comp_apply, map_smul, rejoinTwo, totalBoundaryTwo,
    extend_generator]
  exact congrArg (coefficient • ·) (boundary_rejoinTwoAtom occurrence)

private theorem vertex_one_zero {X : SSet} (triangle : Simplex X 2) :
    initialVertex (face 0 triangle) = terminalVertex (face 2 triangle) := by
  simpa [initialVertex, terminalVertex, face] using
    (X.δ_comp_δ_apply (i := (0 : Fin 2)) (j := (1 : Fin 2))
      (by decide) triangle).symm

private theorem vertex_zero_left {X : SSet} (triangle : Simplex X 2) :
    initialVertex (face 1 triangle) = triangleInitialVertex triangle := by
  simpa [initialVertex, triangleInitialVertex, face] using
    (X.δ_comp_δ_self_apply (i := (1 : Fin 2)) triangle)

private theorem vertex_two_right {X : SSet} (triangle : Simplex X 2) :
    terminalVertex (face 1 triangle) = triangleTerminalVertex triangle := by
  simpa [terminalVertex, triangleTerminalVertex, face] using
    (X.δ_comp_δ_self_apply (i := (0 : Fin 2)) triangle).symm

private theorem face_one_zero {X : SSet} (triangle : Simplex X 2) :
    face 1 (face 0 triangle) = face 0 (face 2 triangle) := by
  simpa [initialVertex, terminalVertex] using vertex_one_zero triangle

private theorem face_one_one {X : SSet} (triangle : Simplex X 2) :
    face 1 (face 1 triangle) = face 1 (face 2 triangle) := by
  simpa [initialVertex, triangleInitialVertex] using vertex_zero_left triangle

private theorem face_zero_one {X : SSet} (triangle : Simplex X 2) :
    face 0 (face 1 triangle) = face 0 (face 0 triangle) := by
  simpa [terminalVertex, triangleTerminalVertex] using vertex_two_right triangle

/-- [proved-derived; formal-checked] The degree-one reconstruction residue is the exact boundary
of one addressed diagonal triangle. -/
theorem boundary_diagonalReconstructionFillerOneAtom {X Y : SSet}
    (occurrence : DiagonalOccurrence X Y 1) :
    diagonalBoundaryTwo X Y (diagonalReconstructionFillerOneAtom occurrence) =
      diagonalRoundTripDefectOne X Y (generator occurrence) := by
  rcases occurrence with ⟨x, y⟩
  simp [diagonalReconstructionFillerOneAtom, diagonalBoundaryTwo,
    diagonalBoundaryTwoAtom, diagonalRoundTripDefectOne, rejoinOne, separateOne,
    rejoinOneAtom, separateOneAtom, diagonalFace, initialVertex, terminalVertex,
    extend_generator]
  module

/-- [proved-derived; formal-checked] The degree-one diagonal reconstruction residue is filled
uniformly on every finite current. -/
theorem boundary_diagonalReconstructionFillerOne (X Y : SSet) :
    (diagonalBoundaryTwo X Y).comp (diagonalReconstructionFillerOne X Y) =
      diagonalRoundTripDefectOne X Y := by
  apply Finsupp.lhom_ext
  intro occurrence coefficient
  rw [show Finsupp.single occurrence coefficient =
      coefficient • generator occurrence by simp [generator]]
  simp only [LinearMap.comp_apply, map_smul,
    diagonalReconstructionFillerOne, extend_generator]
  exact congrArg (coefficient • ·)
    (boundary_diagonalReconstructionFillerOneAtom occurrence)

/-- [proved-derived; formal-checked] Degree-one Alexander--Whitney separation preserves the
complete endpoint difference of one diagonal edge. -/
theorem boundary_separateOneAtom {X Y : SSet}
    (occurrence : DiagonalOccurrence X Y 1) :
    totalBoundaryOne X Y (separateOneAtom occurrence) =
      diagonalBoundaryOneAtom occurrence := by
  rcases occurrence with ⟨left, right⟩
  simp [separateOneAtom, totalBoundaryOne, totalBoundaryOneAtom,
    diagonalBoundaryOneAtom, diagonalFace, initialVertex, terminalVertex,
    extend_generator]

/-- [proved-derived; formal-checked] Degree-one diagonal separation is a chain map on every
finite addressed current. -/
theorem boundary_separateOne (X Y : SSet) :
    (totalBoundaryOne X Y).comp (separateOne X Y) = diagonalBoundaryOne X Y := by
  apply Finsupp.lhom_ext
  intro occurrence coefficient
  rw [show Finsupp.single occurrence coefficient =
      coefficient • generator occurrence by simp [generator]]
  simp only [LinearMap.comp_apply, map_smul, separateOne,
    diagonalBoundaryOne, extend_generator]
  exact congrArg (coefficient • ·) (boundary_separateOneAtom occurrence)

/-- [proved-derived; formal-checked] On one addressed diagonal triangle, separating axes commutes
exactly with the complete alternating boundary.  The middle interaction contributes both axis
currents with opposite Koszul orientation, and all internal occurrences cancel. -/
theorem boundary_separateTwoAtom {X Y : SSet}
    (occurrence : DiagonalOccurrence X Y 2) :
    totalBoundaryTwo X Y (separateTwoAtom occurrence) =
      separateOne X Y (diagonalBoundaryTwoAtom occurrence) := by
  rcases occurrence with ⟨x, y⟩
  simp only [separateTwoAtom, diagonalBoundaryTwoAtom, map_add, map_sub,
    extend_generator, totalBoundaryTwo, totalBoundaryTwoAtom, separateOne,
    separateOneAtom, diagonalFace, initialVertex, terminalVertex,
    triangleInitialVertex, triangleTerminalVertex]
  rw [face_one_zero x, face_one_one x,
    face_one_zero y, face_zero_one y]
  module

/-- [proved-derived; formal-checked] The degree-three Alexander--Whitney occurrence carries the
complete four-face diagonal boundary into the four total axes.  In particular, genuine product
three-boundaries become genuine boundaries in the separated receiver rather than merely closed
degree-two currents. -/
theorem boundary_separateThreeAtom {X Y : SSet}
    (occurrence : DiagonalOccurrence X Y 3) :
    totalBoundaryThree X Y (separateThreeAtom occurrence) =
      separateTwo X Y (diagonalBoundaryThreeAtom occurrence) := by
  rcases occurrence with ⟨x, y⟩
  have x03 : face 0 (face 3 x) = face 2 (face 0 x) := by
    simpa [face] using
      (X.δ_comp_δ'_apply (i := (0 : Fin 3)) (j := (3 : Fin 4)) (by decide) x)
  have x13 : face 1 (face 3 x) = face 2 (face 1 x) := by
    simpa [face] using
      (X.δ_comp_δ'_apply (i := (1 : Fin 3)) (j := (3 : Fin 4)) (by decide) x)
  have x23 : face 2 (face 3 x) = face 2 (face 2 x) := by
    simpa [face] using
      (X.δ_comp_δ'_apply (i := (2 : Fin 3)) (j := (3 : Fin 4)) (by decide) x)
  have y01 : face 0 (face 1 y) = face 0 (face 0 y) := by
    simpa [face] using
      (Y.δ_comp_δ'_apply (i := (0 : Fin 3)) (j := (1 : Fin 4)) (by decide) y)
  have y02 : face 0 (face 2 y) = face 1 (face 0 y) := by
    simpa [face] using
      (Y.δ_comp_δ'_apply (i := (0 : Fin 3)) (j := (2 : Fin 4)) (by decide) y)
  have y03 : face 0 (face 3 y) = face 2 (face 0 y) := by
    simpa [face] using
      (Y.δ_comp_δ'_apply (i := (0 : Fin 3)) (j := (3 : Fin 4)) (by decide) y)
  have xLeftZero :
      face 0 (face 2 (face 3 x)) = face 1 (face 2 (face 0 x)) := by
    calc
      face 0 (face 2 (face 3 x)) = face 1 (face 0 (face 3 x)) := by
        simpa [face] using
          (X.δ_comp_δ'_apply (i := (0 : Fin 2)) (j := (2 : Fin 3))
            (by decide) (face 3 x))
      _ = face 1 (face 2 (face 0 x)) := congrArg (face (X := X) 1) x03
  have xLeftOne :
      face 1 (face 2 (face 3 x)) = face 1 (face 2 (face 1 x)) := by
    calc
      face 1 (face 2 (face 3 x)) = face 1 (face 1 (face 3 x)) := by
        simpa [face] using
          (X.δ_comp_δ'_apply (i := (1 : Fin 2)) (j := (2 : Fin 3))
            (by decide) (face 3 x))
      _ = face 1 (face 2 (face 1 x)) := congrArg (face (X := X) 1) x13
  have xLeftTwo :
      face 1 (face 2 (face 3 x)) = face 1 (face 2 (face 2 x)) :=
    congrArg (face (X := X) 1) x23
  have yRightOne :
      face 0 (face 0 (face 0 y)) = face 0 (face 0 (face 1 y)) := by
    exact (congrArg (face (X := Y) 0) y01).symm
  have yRightTwo :
      face 0 (face 0 (face 0 y)) = face 0 (face 0 (face 2 y)) := by
    calc
      face 0 (face 0 (face 0 y)) = face 0 (face 1 (face 0 y)) := by
        simpa [face] using
          (Y.δ_comp_δ'_apply (i := (0 : Fin 2)) (j := (1 : Fin 3))
            (by decide) (face 0 y)).symm
      _ = face 0 (face 0 (face 2 y)) := congrArg (face (X := Y) 0) y02.symm
  have yRightThree :
      face 1 (face 0 (face 0 y)) = face 0 (face 0 (face 3 y)) := by
    calc
      face 1 (face 0 (face 0 y)) = face 0 (face 2 (face 0 y)) := by
        simpa [face] using
          (Y.δ_comp_δ'_apply (i := (0 : Fin 2)) (j := (2 : Fin 3))
            (by decide) (face 0 y)).symm
      _ = face 0 (face 0 (face 3 y)) := congrArg (face (X := Y) 0) y03.symm
  simp only [separateThreeAtom, diagonalBoundaryThreeAtom, map_add, map_sub,
    extend_generator, totalBoundaryThree, totalBoundaryThreeAtom, separateTwo,
    separateTwoAtom, diagonalFace, tetrahedronInitialVertex,
    tetrahedronTerminalVertex, tetrahedronFrontEdge, tetrahedronBackEdge,
    triangleInitialVertex, triangleTerminalVertex, initialVertex, terminalVertex]
  rw [xLeftZero, xLeftTwo.symm, xLeftOne,
    yRightOne.symm, yRightTwo.symm, yRightThree.symm,
    x03, x13, x23, y01, y02, y03]
  module

/-- [proved-derived; formal-checked] Degree-three diagonal separation commutes with boundary on
every finite rational current.  This is the precise law needed for a degree-two homology receiver:
source boundaries remain boundaries after axis separation. -/
theorem boundary_separateThree (X Y : SSet) :
    (totalBoundaryThree X Y).comp (separateThree X Y) =
      (separateTwo X Y).comp (diagonalBoundaryThree X Y) := by
  apply Finsupp.lhom_ext
  intro occurrence coefficient
  rw [show Finsupp.single occurrence coefficient =
      coefficient • generator occurrence by simp [generator]]
  simp only [LinearMap.comp_apply, map_smul, separateThree,
    diagonalBoundaryThree, extend_generator]
  exact congrArg (coefficient • ·) (boundary_separateThreeAtom occurrence)

/-- [proved-derived; formal-checked] The four addressed degree-three occurrences form the exact
low-degree reconstruction homotopy.  Their boundary plus the degree-one filler of the source
boundary is precisely the complete separate--rejoin defect of one diagonal triangle. -/
theorem boundary_diagonalReconstructionFillerTwoAtom {X Y : SSet}
    (occurrence : DiagonalOccurrence X Y 2) :
    diagonalBoundaryThree X Y (diagonalReconstructionFillerTwoAtom occurrence) +
        diagonalReconstructionFillerOne X Y (diagonalBoundaryTwoAtom occurrence) =
      diagonalRoundTripDefectTwo X Y (generator occurrence) := by
  rcases occurrence with ⟨x, y⟩
  simp [diagonalReconstructionFillerTwoAtom, diagonalReconstructionFillerOne,
    diagonalReconstructionFillerOneAtom, diagonalBoundaryThree,
    diagonalBoundaryThreeAtom, diagonalBoundaryTwoAtom,
    diagonalRoundTripDefectTwo, rejoinTwo, separateTwo, rejoinTwoAtom,
    separateTwoAtom, diagonalFace, triangleInitialVertex, triangleTerminalVertex,
    initialVertex, terminalVertex, repeatVertexTriangle, repeatVertexEdge,
    extend_generator]
  rw [face_zero_one y]
  module

/-- [proved-derived; formal-checked] The reconstruction homotopy holds for every finite rational
diagonal two-current, not only for one generator occurrence. -/
theorem diagonalReconstructionHomotopyTwo (X Y : SSet) :
    (diagonalBoundaryThree X Y).comp (diagonalReconstructionFillerTwo X Y) +
        (diagonalReconstructionFillerOne X Y).comp (diagonalBoundaryTwo X Y) =
      diagonalRoundTripDefectTwo X Y := by
  apply Finsupp.lhom_ext
  intro occurrence coefficient
  rw [show Finsupp.single occurrence coefficient =
      coefficient • generator occurrence by simp [generator]]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, map_smul,
    diagonalReconstructionFillerTwo, diagonalBoundaryTwo, extend_generator]
  simpa [smul_add] using congrArg (coefficient • ·)
    (boundary_diagonalReconstructionFillerTwoAtom occurrence)

/-- [proved-derived; formal-checked] Every closed diagonal two-current has an explicit uniform
degree-three filler for its complete separate--rejoin reconstruction defect. -/
theorem diagonalRoundTripDefectTwo_eq_boundary_of_cycle {X Y : SSet}
    (current : Current (DiagonalOccurrence X Y 2))
    (closed : diagonalBoundaryTwo X Y current = 0) :
    diagonalRoundTripDefectTwo X Y current =
      diagonalBoundaryThree X Y (diagonalReconstructionFillerTwo X Y current) := by
  have law := LinearMap.congr_fun (diagonalReconstructionHomotopyTwo X Y) current
  change diagonalBoundaryThree X Y (diagonalReconstructionFillerTwo X Y current) +
      diagonalReconstructionFillerOne X Y (diagonalBoundaryTwo X Y current) =
    diagonalRoundTripDefectTwo X Y current at law
  rw [closed, map_zero, add_zero] at law
  exact law.symm

/-- [proved-derived; formal-checked] The exact diagonal-to-product transport law on every finite
rational degree-two current. -/
theorem boundary_separateTwo (X Y : SSet) :
    (totalBoundaryTwo X Y).comp (separateTwo X Y) =
      (separateOne X Y).comp (diagonalBoundaryTwo X Y) := by
  apply Finsupp.lhom_ext
  intro occurrence coefficient
  simp only [LinearMap.comp_apply]
  rw [show Finsupp.single occurrence coefficient =
      coefficient • generator occurrence by simp [generator]]
  simp only [map_smul, separateTwo, diagonalBoundaryTwo, separateOne,
    extend_generator]
  exact congrArg (coefficient • ·) (boundary_separateTwoAtom occurrence)

/-- [proved-derived; formal-checked] The complete reconstruction residue is itself transported by
the diagonal boundary.  Hence the missing Eilenberg--Zilber datum is now isolated exactly: a
degree-three filler of this retained closed defect, rather than an unspecified product comparison. -/
theorem boundary_diagonalRoundTripDefectTwo (X Y : SSet) :
    (diagonalBoundaryTwo X Y).comp (diagonalRoundTripDefectTwo X Y) =
      (diagonalRoundTripDefectOne X Y).comp (diagonalBoundaryTwo X Y) := by
  apply LinearMap.ext
  intro current
  simp only [diagonalRoundTripDefectTwo, diagonalRoundTripDefectOne,
    LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
  rw [map_sub]
  have rejoinLaw := LinearMap.congr_fun
    (boundary_rejoinTwo X Y) (separateTwo X Y current)
  change diagonalBoundaryTwo X Y
      (rejoinTwo X Y (separateTwo X Y current)) =
    rejoinOne X Y (totalBoundaryTwo X Y (separateTwo X Y current)) at rejoinLaw
  rw [rejoinLaw]
  have separateLaw := LinearMap.congr_fun (boundary_separateTwo X Y) current
  change totalBoundaryTwo X Y (separateTwo X Y current) =
    separateOne X Y (diagonalBoundaryTwo X Y current) at separateLaw
  rw [separateLaw]

/-- [proved-derived; formal-checked] On a closed diagonal two-current, the exact round-trip
reconstruction residue is closed.  The occurrence retained by this boundary holon is the original
cycle, so a later filler cannot silently forget the source reconstruction fibre. -/
def diagonalRoundTripDefectBoundaryHolon (X Y : SSet) :
    BoundaryHolon (Current (DiagonalOccurrence X Y 1))
      (Current (DiagonalOccurrence X Y 2)) where
  Occurrence := LinearMap.ker (diagonalBoundaryTwo X Y)
  source _ := 0
  target _ := 0
  receive occurrence := diagonalRoundTripDefectTwo X Y occurrence.1
  boundary := (diagonalBoundaryTwo X Y).toAddMonoidHom
  returnsBoundary := by
    intro occurrence
    change diagonalBoundaryTwo X Y
        (diagonalRoundTripDefectTwo X Y occurrence.1) = 0 - 0
    have law := LinearMap.congr_fun
      (boundary_diagonalRoundTripDefectTwo X Y) occurrence.1
    simp only [LinearMap.comp_apply,
      diagonalRoundTripDefectOne, LinearMap.sub_apply, LinearMap.id_apply] at law
    simpa using law

/-- [proved-derived; formal-checked] The separated degree-two transport is an elementary boundary
holon: its source is the separated boundary current, its target is null, and its received current
retains all three product axes. -/
def separationBoundaryHolon (X Y : SSet) :
    BoundaryHolon (Current (TotalOneOccurrence X Y))
      (Current (TotalTwoOccurrence X Y)) where
  Occurrence := LinearMap.ker (diagonalBoundaryTwo X Y)
  source _ := 0
  target _ := 0
  receive occurrence := separateTwo X Y occurrence.1
  boundary := (totalBoundaryTwo X Y).toAddMonoidHom
  returnsBoundary := by
    intro occurrence
    change totalBoundaryTwo X Y (separateTwo X Y occurrence.1) = 0 - 0
    have law := LinearMap.congr_fun (boundary_separateTwo X Y) occurrence.1
    simp only [LinearMap.comp_apply] at law
    simpa using law

section Audit

#print axioms boundary_rejoinOne
#print axioms boundary_separateOne
#print axioms boundary_diagonalReconstructionFillerOne
#print axioms boundary_separateTwoAtom
#print axioms boundary_separateTwo
#print axioms boundary_separateThreeAtom
#print axioms boundary_separateThree
#print axioms separationBoundaryHolon
#print axioms boundary_diagonalRoundTripDefectTwo
#print axioms diagonalRoundTripDefectBoundaryHolon
#print axioms boundary_diagonalReconstructionFillerOneAtom
#print axioms boundary_diagonalReconstructionFillerTwoAtom
#print axioms diagonalReconstructionHomotopyTwo
#print axioms diagonalRoundTripDefectTwo_eq_boundary_of_cycle

end Audit

end Soma.Holonics.DiagonalChainTransport
