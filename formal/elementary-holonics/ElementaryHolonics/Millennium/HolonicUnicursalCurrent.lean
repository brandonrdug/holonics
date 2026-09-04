import ElementaryHolonics.Millennium.HolonicDifferenceCalculus
import Mathlib.Tactic

/-!
# A unicursal stroke is an addressed current, and its star fan is an exact gluing

The drawing is not represented by one scalar or by its final picture.  A stroke retains the
ordered edge occurrences, their joining vertices, its exterior boundary, and the receiver which
reads transported action along it.  The fundamental theorem is finite telescoping:

```text
sum (potential(target) - potential(source)) = potential(finish) - potential(start).
```

Calling the same passage a loss reverses the receiver orientation and therefore returns
`potential(start) - potential(finish)`, the negative of the transported action.  There is no
conflict of boundary conventions.

A center fan attaches one oriented triangle to every consecutive edge of the stroke.  All internal
spokes occur twice with opposite orientations, leaving precisely the stroke plus its closing edge.
For a closed stroke the fan boundary is the stroke.  This is the exact local-to-global gluing law
suggested by a star drawing, and also its necessary Hodge guard: a filled planar star is a
two-boundary, so unicursality alone cannot certify a nonzero homology class.  A nonvanishing theorem
still needs a receiver which annihilates higher boundaries and detects the realized class.

Affine intersection and knot data require an additional geometric realization of the edge word.
They are not inferred from the abstract word or its zero exterior boundary.
-/

namespace Soma.Holonics.Millennium.HolonicUnicursalCurrent

open scoped BigOperators

universe u

variable {Vertex : Type u}

/-- A signed population of vertices. -/
abbrev VertexChain (Vertex : Type u) := Vertex → ℤ

/-- A signed population of directed vertex pairs. -/
abbrev EdgeChain (Vertex : Type u) := Vertex → Vertex → ℤ

/-- One addressed occurrence at a vertex. -/
def vertexAtom [DecidableEq Vertex] (vertex : Vertex) : VertexChain Vertex :=
  fun receiver => if receiver = vertex then 1 else 0

/-- One addressed directed-edge occurrence. -/
def directedEdgeAtom [DecidableEq Vertex] (source target : Vertex) : EdgeChain Vertex :=
  fun readSource readTarget =>
    if readSource = source ∧ readTarget = target then 1 else 0

/-- The oriented current retains both hands of an edge.  A degenerate edge is therefore zero. -/
def orientedEdgeCurrent [DecidableEq Vertex] (source target : Vertex) : EdgeChain Vertex :=
  directedEdgeAtom source target - directedEdgeAtom target source

theorem orientedEdgeCurrent_reverse [DecidableEq Vertex] (source target : Vertex) :
    orientedEdgeCurrent target source = -orientedEdgeCurrent source target := by
  unfold orientedEdgeCurrent
  abel

theorem orientedEdgeCurrent_self [DecidableEq Vertex] (vertex : Vertex) :
    orientedEdgeCurrent vertex vertex = 0 := by
  unfold orientedEdgeCurrent
  abel

/-- The vertex boundary of one oriented edge is terminal minus initial. -/
def orientedEdgeBoundary [DecidableEq Vertex] (source target : Vertex) :
    VertexChain Vertex :=
  vertexAtom target - vertexAtom source

/-- One edge occurrence in an ordered stroke. -/
structure StrokeEdge (Vertex : Type u) where
  source : Vertex
  target : Vertex

namespace StrokeEdge

/-- The signed edge-current face of one retained occurrence. -/
def current [DecidableEq Vertex] (edge : StrokeEdge Vertex) : EdgeChain Vertex :=
  orientedEdgeCurrent edge.source edge.target

/-- The exterior vertex-boundary face of one retained occurrence. -/
def boundary [DecidableEq Vertex] (edge : StrokeEdge Vertex) : VertexChain Vertex :=
  orientedEdgeBoundary edge.source edge.target

/-- A potential receiver reads the transported action along the oriented edge. -/
def action {G : Type*} [AddCommGroup G] (potential : Vertex → G)
    (edge : StrokeEdge Vertex) : G :=
  potential edge.target - potential edge.source

/-- Reversal retains the same two endpoints and exchanges their orientation. -/
def reverse (edge : StrokeEdge Vertex) : StrokeEdge Vertex :=
  ⟨edge.target, edge.source⟩

theorem action_reverse {G : Type*} [AddCommGroup G] (potential : Vertex → G)
    (edge : StrokeEdge Vertex) :
    edge.reverse.action potential = -edge.action potential := by
  simp [action, reverse]

end StrokeEdge

/-- The final vertex after traversing an ordered tail from `start`. -/
def endpoint (start : Vertex) : List Vertex → Vertex
  | [] => start
  | next :: tail => endpoint next tail

/-- The complete ordered edge population of a stroke. -/
def edgeWord (start : Vertex) : List Vertex → List (StrokeEdge Vertex)
  | [] => []
  | next :: tail => ⟨start, next⟩ :: edgeWord next tail

@[simp]
theorem edgeWord_length (start : Vertex) (tail : List Vertex) :
    (edgeWord start tail).length = tail.length := by
  induction tail generalizing start with
  | nil => rfl
  | cons next tail ih => simp [edgeWord, ih]

/-- Edge words compose at the actual terminal vertex of the first word. -/
theorem edgeWord_append (start : Vertex) (left right : List Vertex) :
    edgeWord start (left ++ right) =
      edgeWord start left ++ edgeWord (endpoint start left) right := by
  induction left generalizing start with
  | nil => rfl
  | cons next left ih =>
      simp only [List.cons_append, edgeWord, endpoint, List.cons.injEq, true_and]
      exact ih next

/-- The retained signed edge population, before any boundary or potential receiver. -/
def strokeCurrent [DecidableEq Vertex] (start : Vertex) : List Vertex → EdgeChain Vertex
  | [] => 0
  | next :: tail =>
      orientedEdgeCurrent start next + strokeCurrent next tail

/-- The current is exactly the sum of the retained edge occurrences. -/
theorem strokeCurrent_eq_edgeWord_sum [DecidableEq Vertex]
    (start : Vertex) (tail : List Vertex) :
    strokeCurrent start tail = ((edgeWord start tail).map StrokeEdge.current).sum := by
  induction tail generalizing start with
  | nil => rfl
  | cons next tail ih =>
      simp only [strokeCurrent, edgeWord, List.map_cons, List.sum_cons]
      rw [ih next]
      rfl

/-- A potential receiver integrates the local oriented differences along the stroke. -/
def strokeAction {G : Type*} [AddCommGroup G]
    (potential : Vertex → G) (start : Vertex) : List Vertex → G
  | [] => 0
  | next :: tail =>
      (potential next - potential start) + strokeAction potential next tail

/-- **Finite fundamental theorem.** Every internal potential face cancels exactly. -/
theorem strokeAction_eq_endpoint_sub_source {G : Type*} [AddCommGroup G]
    (potential : Vertex → G) (start : Vertex) (tail : List Vertex) :
    strokeAction potential start tail =
      potential (endpoint start tail) - potential start := by
  induction tail generalizing start with
  | nil => simp [strokeAction, endpoint]
  | cons next tail ih =>
      simp only [strokeAction, endpoint]
      rw [ih next]
      abel

/-- The exported-loss chart reads the same passage with the opposite boundary orientation. -/
def outwardLoss {G : Type*} [AddCommGroup G]
    (potential : Vertex → G) (start : Vertex) (tail : List Vertex) : G :=
  potential start - potential (endpoint start tail)

theorem outwardLoss_eq_neg_strokeAction {G : Type*} [AddCommGroup G]
    (potential : Vertex → G) (start : Vertex) (tail : List Vertex) :
    outwardLoss potential start tail = -strokeAction potential start tail := by
  rw [strokeAction_eq_endpoint_sub_source]
  unfold outwardLoss
  abel

/-- A stroke closes when its final addressed vertex is its initial addressed vertex. -/
def IsClosed (start : Vertex) (tail : List Vertex) : Prop :=
  endpoint start tail = start

theorem closed_strokeAction_zero {G : Type*} [AddCommGroup G]
    (potential : Vertex → G) (start : Vertex) (tail : List Vertex)
    (closed : IsClosed start tail) :
    strokeAction potential start tail = 0 := by
  rw [strokeAction_eq_endpoint_sub_source, closed]
  simp

/-! ## The star/fan gluing -/

/-- One oriented triangular face, written as `(center, first, second)`. -/
structure OrientedTriangle (Vertex : Type u) where
  center : Vertex
  first : Vertex
  second : Vertex

namespace OrientedTriangle

/-- Its edge boundary is `first -> second -> center -> first`. -/
def boundary [DecidableEq Vertex] (triangle : OrientedTriangle Vertex) : EdgeChain Vertex :=
  orientedEdgeCurrent triangle.first triangle.second +
    orientedEdgeCurrent triangle.second triangle.center +
      orientedEdgeCurrent triangle.center triangle.first

/-- The boundary of one triangle's boundary is exactly zero. -/
theorem vertexBoundary_zero [DecidableEq Vertex] (triangle : OrientedTriangle Vertex) :
    orientedEdgeBoundary triangle.first triangle.second +
        orientedEdgeBoundary triangle.second triangle.center +
          orientedEdgeBoundary triangle.center triangle.first = 0 := by
  unfold orientedEdgeBoundary
  abel

end OrientedTriangle

/-- The complete addressed triangle population of a center fan. -/
def fanTriangles (center start : Vertex) : List Vertex → List (OrientedTriangle Vertex)
  | [] => []
  | next :: tail => ⟨center, start, next⟩ :: fanTriangles center next tail

/-- Sum the oriented boundaries of every triangle in the fan. -/
def fanBoundaryCurrent [DecidableEq Vertex]
    (center start : Vertex) : List Vertex → EdgeChain Vertex
  | [] => 0
  | next :: tail =>
      (OrientedTriangle.boundary ⟨center, start, next⟩) +
        fanBoundaryCurrent center next tail

/-- The fan current is exactly the sum of the retained triangle occurrences. -/
theorem fanBoundaryCurrent_eq_triangle_sum [DecidableEq Vertex]
    (center start : Vertex) (tail : List Vertex) :
    fanBoundaryCurrent center start tail =
      ((fanTriangles center start tail).map OrientedTriangle.boundary).sum := by
  induction tail generalizing start with
  | nil => rfl
  | cons next tail ih =>
      simp only [fanBoundaryCurrent, fanTriangles, List.map_cons, List.sum_cons]
      rw [ih next]

/-- **Star-fan gluing.** Every internal spoke cancels, leaving the stroke and closing edges. -/
theorem fanBoundaryCurrent_eq_stroke_add_closure [DecidableEq Vertex]
    (center start : Vertex) (tail : List Vertex) :
    fanBoundaryCurrent center start tail =
      strokeCurrent start tail +
        orientedEdgeCurrent (endpoint start tail) center +
          orientedEdgeCurrent center start := by
  induction tail generalizing start with
  | nil =>
      simp only [fanBoundaryCurrent, strokeCurrent, endpoint, zero_add]
      rw [orientedEdgeCurrent_reverse center start]
      abel
  | cons next tail ih =>
      simp only [fanBoundaryCurrent, strokeCurrent, endpoint,
        OrientedTriangle.boundary]
      rw [ih next]
      rw [orientedEdgeCurrent_reverse center next]
      abel

/-- A closed unicursal stroke is exactly the boundary of its center fan. -/
theorem closed_fanBoundaryCurrent_eq_stroke [DecidableEq Vertex]
    (center start : Vertex) (tail : List Vertex) (closed : IsClosed start tail) :
    fanBoundaryCurrent center start tail = strokeCurrent start tail := by
  rw [fanBoundaryCurrent_eq_stroke_add_closure, closed]
  rw [orientedEdgeCurrent_reverse center start]
  abel

/-! ## The five-point star as one exact word -/

/-- The outer vertices encountered before returning to the start. -/
def pentagramUniqueVertices : List (Fin 5) := [0, 2, 4, 1, 3]

/-- The tail of the conventional five-point unicursal stroke, including its return to zero. -/
def pentagramTail : List (Fin 5) := [2, 4, 1, 3, 0]

theorem pentagram_visits_every_outer_vertex_once :
    pentagramUniqueVertices.Nodup ∧
      ∀ vertex : Fin 5, vertex ∈ pentagramUniqueVertices := by
  decide

theorem pentagram_has_five_edge_occurrences :
    (edgeWord (0 : Fin 5) pentagramTail).length = 5 := by
  decide

theorem pentagram_isClosed : IsClosed (0 : Fin 5) pentagramTail := by
  rfl

/-- Every additive potential has zero complete return around the closed pentagram word. -/
theorem pentagram_action_zero {G : Type*} [AddCommGroup G]
    (potential : Fin 5 → G) :
    strokeAction potential 0 pentagramTail = 0 :=
  closed_strokeAction_zero potential 0 pentagramTail pentagram_isClosed

/-- The abstract pentagram current is a fan boundary for every declared center in its carrier. -/
theorem pentagram_is_fanBoundary (center : Fin 5) :
    fanBoundaryCurrent center 0 pentagramTail = strokeCurrent 0 pentagramTail :=
  closed_fanBoundaryCurrent_eq_stroke center 0 pentagramTail pentagram_isClosed

section Audit

#print axioms edgeWord_append
#print axioms strokeCurrent_eq_edgeWord_sum
#print axioms strokeAction_eq_endpoint_sub_source
#print axioms outwardLoss_eq_neg_strokeAction
#print axioms OrientedTriangle.vertexBoundary_zero
#print axioms fanBoundaryCurrent_eq_stroke_add_closure
#print axioms closed_fanBoundaryCurrent_eq_stroke
#print axioms pentagram_visits_every_outer_vertex_once
#print axioms pentagram_is_fanBoundary

end Audit

end Soma.Holonics.Millennium.HolonicUnicursalCurrent
