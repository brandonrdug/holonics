import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Basic
import ElementaryHolonics.Geometry.CrossRatio
import ElementaryHolonics.Millennium.NavierStokes
import ElementaryHolonics.Millennium.Swing

/-!
# Material polygons: exact finite receivers carried by a Navier--Stokes velocity field

This module adds the finite geometric carrier needed to ask polygonal questions of the actual
three-dimensional Navier--Stokes object.  A material polygon has at least three addressed vertices;
each vertex follows the velocity field on the oriented time half-line.  Its cyclic edge population
is retained before any receiver takes a sum.

The exact results are deliberately local and finite:

* the oriented boundary-edge population sums to zero at every time;
* every scalar potential, hence pressure at a fixed time, has zero total cyclic increment;
* the polygonal circulation receiver is defined, and a spatially constant current has zero such
  circulation;
* a turn ledger derives the `(n - 2) * pi` interior-angle budget from local supplementary angles
  and a winding-one exterior return;
* angle defect is additive under gluing and invariant when actual and reference angles undergo the
  same chart rebase;
* a returned quadrilateral retains the failure of a transported path to close.  Its flat fourth
  vertex is exactly a Swing followed by edge transport, while its four-point projective face is the
  existing undivided cross-ratio presentation;
* the repository's refine-and-fork coupling `2^forks C / (2^scale r)` is invariant when refinement
  and binary branching advance together.

These are not a Kelvin theorem, a Gauss--Bonnet theorem, a gyrogroup construction, or an Einstein
field equation.  In particular, the returned quadrilateral is a typed precursor carrying a
holonomy defect; calling it a gyroparallelogram would additionally require an owned gyrogroup law.
The coupling uses the typed arc `C` and differential scale `r`; it does not silently identify the
result with a curvature tensor.
-/

noncomputable section

open scoped BigOperators
open Set

namespace Soma.Holonics.Millennium.NavierStokesMaterialPolygon

open Soma.Holonics
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.NavierStokes

/-! ## 1. The material polygon and its cyclic boundary -/

/-- A polygon with `extra + 3` vertices.  The parameterization makes nondegeneracy of the index
population structural: every admitted polygon has at least three addressed vertices. -/
abbrev PolygonIndex (extra : ℕ) := Fin (extra + 3)

/-- The next addressed vertex, including the final-to-initial closing edge. -/
def cyclicSuccessor (extra : ℕ) : Equiv.Perm (PolygonIndex extra) :=
  Equiv.addRight 1

/-- One oriented edge in a cyclic vertex population. -/
def edge {G : Type*} [AddCommGroup G] {extra : ℕ}
    (vertex : PolygonIndex extra → G) (i : PolygonIndex extra) : G :=
  vertex (cyclicSuccessor extra i) - vertex i

/-- **Conservation of the polygonal boundary.**  The complete oriented edge population of every
closed finite polygon sums to zero.  This is incidence conservation, before any metric or angle
receiver is selected. -/
theorem sum_edges_eq_zero {G : Type*} [AddCommGroup G] {extra : ℕ}
    (vertex : PolygonIndex extra → G) :
    ∑ i, edge vertex i = 0 := by
  rw [show (∑ i, edge vertex i) =
      (∑ i, vertex (cyclicSuccessor extra i)) - ∑ i, vertex i by
        simp [edge, Finset.sum_sub_distrib]]
  rw [Equiv.sum_comp (cyclicSuccessor extra) vertex, sub_self]

/-- The cyclic increment population of a scalar potential on the vertices. -/
def cyclicIncrement {K : Type*} [AddCommGroup K] {extra : ℕ}
    (potential : PolygonIndex extra → K) (i : PolygonIndex extra) : K :=
  potential (cyclicSuccessor extra i) - potential i

/-- Every scalar potential has zero total increment around a closed polygon. -/
theorem sum_cyclicIncrement_eq_zero {K : Type*} [AddCommGroup K] {extra : ℕ}
    (potential : PolygonIndex extra → K) :
    ∑ i, cyclicIncrement potential i = 0 :=
  sum_edges_eq_zero potential

/-- A finite Lagrangian polygon carried by the actual Navier--Stokes velocity field.  `carried`
orients time through `Ici 0` and says that every addressed vertex is a tracer trajectory. -/
structure MaterialPolygon (extra : ℕ) (velocity : VelocityField) where
  vertex : ℝ → PolygonIndex extra → Space
  carried : ∀ i t, 0 ≤ t →
    derivWithin (fun τ ↦ vertex τ i) (Ici 0) t = velocity (vertex t i) t

/-- The complete vertex population at one receiver time. -/
def MaterialPolygon.snapshot {extra : ℕ} {velocity : VelocityField}
    (polygon : MaterialPolygon extra velocity) (t : ℝ) : PolygonIndex extra → Space :=
  polygon.vertex t

/-- The oriented edge at a receiver time. -/
def MaterialPolygon.edgeAt {extra : ℕ} {velocity : VelocityField}
    (polygon : MaterialPolygon extra velocity) (t : ℝ) (i : PolygonIndex extra) : Space :=
  edge (polygon.snapshot t) i

/-- Every material snapshot remains a closed boundary, independently of how the velocity field
deforms it. -/
theorem MaterialPolygon.sum_edgesAt_eq_zero {extra : ℕ} {velocity : VelocityField}
    (polygon : MaterialPolygon extra velocity) (t : ℝ) :
    ∑ i, polygon.edgeAt t i = 0 :=
  sum_edges_eq_zero (polygon.snapshot t)

/-- The carrying law exposed at one nonnegative receiver time. -/
theorem MaterialPolygon.deriv_vertex_eq_velocity {extra : ℕ} {velocity : VelocityField}
    (polygon : MaterialPolygon extra velocity) (i : PolygonIndex extra) {t : ℝ} (ht : 0 ≤ t) :
    derivWithin (fun τ ↦ polygon.vertex τ i) (Ici 0) t = velocity (polygon.vertex t i) t :=
  polygon.carried i t ht

/-! ## 2. Pressure increments and the circulation receiver -/

/-- Pressure differences on all cyclic edges at one receiver time. -/
def MaterialPolygon.pressureIncrementAt {extra : ℕ} {velocity : VelocityField}
    (polygon : MaterialPolygon extra velocity) (pressure : PressureField)
    (t : ℝ) (i : PolygonIndex extra) : ℝ :=
  pressure (polygon.vertex t (cyclicSuccessor extra i)) t - pressure (polygon.vertex t i) t

/-- **Pressure has no cyclic residue.**  At every time, all pressure differences around the closed
material polygon telescope exactly.  This is the finite polygonal sibling of the local fact that
curl annihilates a sufficiently regular pressure gradient; it does not require that analytic fact. -/
theorem MaterialPolygon.sum_pressureIncrementAt_eq_zero
    {extra : ℕ} {velocity : VelocityField}
    (polygon : MaterialPolygon extra velocity) (pressure : PressureField) (t : ℝ) :
    ∑ i, polygon.pressureIncrementAt pressure t i = 0 := by
  exact sum_cyclicIncrement_eq_zero (fun i ↦ pressure (polygon.vertex t i) t)

/-- A finite polygonal circulation face.  This is a left-endpoint edge pairing, not a line integral
and not yet a Kelvin invariant. -/
def polygonalCirculation {extra : ℕ}
    (current vertex : PolygonIndex extra → Space) : ℝ :=
  ∑ i, inner ℝ (current i) (edge vertex i)

/-- A spatially constant current has zero polygonal circulation because the retained boundary
population closes. -/
theorem polygonalCirculation_constant_eq_zero {extra : ℕ}
    (u : Space) (vertex : PolygonIndex extra → Space) :
    polygonalCirculation (fun _ ↦ u) vertex = 0 := by
  rw [polygonalCirculation, ← inner_sum, sum_edges_eq_zero]
  simp

/-- The velocity circulation face of a material snapshot. -/
def MaterialPolygon.velocityCirculation {extra : ℕ} {velocity : VelocityField}
    (polygon : MaterialPolygon extra velocity) (t : ℝ) : ℝ :=
  polygonalCirculation (fun i ↦ velocity (polygon.vertex t i) t) (polygon.snapshot t)

/-! ## 3. Angle conservation and receiver-visible defect -/

/-- A retained turn presentation.  `actual` is what a receiver reads; `reference` is the flat or
transported comparison supplied by that receiver's chart. -/
structure TurnPresentation where
  actual : ℝ
  reference : ℝ

/-- The angle/turn defect retained before it is interpreted as curvature. -/
def TurnPresentation.defect (turn : TurnPresentation) : ℝ :=
  turn.actual - turn.reference

/-- A common chart rebase changes both readings but not their returned difference. -/
theorem TurnPresentation.defect_commonRebase (turn : TurnPresentation) (shift : ℝ) :
    ({ actual := turn.actual + shift
       reference := turn.reference + shift } : TurnPresentation).defect = turn.defect := by
  simp [TurnPresentation.defect]

/-- Defect is additive when two presented faces are glued. -/
theorem TurnPresentation.defect_glue (left right : TurnPresentation) :
    ({ actual := left.actual + right.actual
       reference := left.reference + right.reference } : TurnPresentation).defect =
      left.defect + right.defect := by
  simp [TurnPresentation.defect]
  ring

/-- The turn ledger for an `extra + 3`-gon.  The geometric obligations are explicit hypotheses:
each interior/exterior pair is supplementary, and the exterior turns make one full return. -/
structure PolygonTurnLedger (extra : ℕ) where
  interior : PolygonIndex extra → ℝ
  exterior : PolygonIndex extra → ℝ
  halfTurn : ℝ
  supplementary : ∀ i, interior i + exterior i = halfTurn
  windingOne : ∑ i, exterior i = 2 * halfTurn

/-- **The interior-angle budget follows from local incidence and one returned winding.** -/
theorem PolygonTurnLedger.sum_interior (ledger : PolygonTurnLedger extra) :
    ∑ i, ledger.interior i = (extra + 1 : ℕ) * ledger.halfTurn := by
  have hsupp : ∑ i, (ledger.interior i + ledger.exterior i) =
      ∑ _i : PolygonIndex extra, ledger.halfTurn := by
    apply Finset.sum_congr rfl
    intro i _
    exact ledger.supplementary i
  have hcard : ∑ _i : PolygonIndex extra, ledger.halfTurn =
      (extra + 3 : ℕ) * ledger.halfTurn := by
    simp
  rw [Finset.sum_add_distrib] at hsupp
  rw [hcard] at hsupp
  rw [ledger.windingOne] at hsupp
  norm_num at hsupp ⊢
  linarith

/-- The familiar `(n - 2) * pi` face for an `n = extra + 3` polygon.  Simplicity,
nondegeneracy, principal-angle choice, and winding one are represented by the ledger hypotheses;
they are not inferred from an arbitrary vertex list. -/
theorem PolygonTurnLedger.sum_interior_pi (ledger : PolygonTurnLedger extra)
    (hpi : ledger.halfTurn = Real.pi) :
    ∑ i, ledger.interior i = (extra + 1 : ℕ) * Real.pi := by
  rw [ledger.sum_interior, hpi]

/-! ## 4. Swing, projective ratio, and a returned quadrilateral -/

/-- Four addressed occurrences: one source, two transported arms, and the point actually returned.
The return is retained even when it does not close the flat parallelogram. -/
structure ReturnedQuadrilateral (G : Type*) where
  source : G
  left : G
  right : G
  returned : G

variable {G : Type*} [AddCommGroup G]

/-- The fourth point predicted by flat additive transport. -/
def ReturnedQuadrilateral.flatFourth (q : ReturnedQuadrilateral G) : G :=
  q.left + q.right - q.source

/-- Construct the same flat fourth point by swinging the source through the left anchor and then
transporting the right arm. -/
def ReturnedQuadrilateral.swingThenTransport (q : ReturnedQuadrilateral G) : G :=
  Swing.swing q.left q.source + (q.right - q.left)

/-- The flat parallelogram completion is exactly a Swing followed by edge transport. -/
theorem ReturnedQuadrilateral.swingThenTransport_eq_flatFourth
    (q : ReturnedQuadrilateral G) :
    q.swingThenTransport = q.flatFourth := by
  simp [ReturnedQuadrilateral.swingThenTransport, ReturnedQuadrilateral.flatFourth, Swing.swing]
  abel

/-- The returned holonomy defect: what remains after the flat completion is removed. -/
def ReturnedQuadrilateral.returnDefect (q : ReturnedQuadrilateral G) : G :=
  q.returned - q.flatFourth

/-- Vanishing defect is exactly closure of the flat parallelogram. -/
theorem ReturnedQuadrilateral.returnDefect_eq_zero_iff (q : ReturnedQuadrilateral G) :
    q.returnDefect = 0 ↔ q.returned = q.flatFourth := by
  change q.returned - q.flatFourth = 0 ↔ q.returned = q.flatFourth
  exact sub_eq_zero

/-- Common translation of all four occurrences preserves the return defect. -/
theorem ReturnedQuadrilateral.returnDefect_translate (q : ReturnedQuadrilateral G) (z : G) :
    ({ source := q.source + z
       left := q.left + z
       right := q.right + z
       returned := q.returned + z } : ReturnedQuadrilateral G).returnDefect = q.returnDefect := by
  simp [ReturnedQuadrilateral.returnDefect, ReturnedQuadrilateral.flatFourth]
  abel

section ProjectiveFace

variable {K : Type*} [Field K]

/-- The exact undivided four-point receiver of a returned scalar quadrilateral. -/
def ReturnedQuadrilateral.projectiveFace (q : ReturnedQuadrilateral K) : RatioPresentation K :=
  swingPair q.source q.left q.right q.returned

/-- Affine chart transport scales both coordinates of the exact projective face together. -/
theorem ReturnedQuadrilateral.projectiveFace_affine
    (q : ReturnedQuadrilateral K) (u v : K) :
    ({ source := u * q.source + v
       left := u * q.left + v
       right := u * q.right + v
       returned := u * q.returned + v } : ReturnedQuadrilateral K).projectiveFace =
      q.projectiveFace.scale (u * u) := by
  exact swingPair_affine_coordinates q.source q.left q.right q.returned u v

/-- Consequently the translated/scaled quadrilateral has the same projective ratio class. -/
theorem ReturnedQuadrilateral.projectiveFace_affine_projectively
    (q : ReturnedQuadrilateral K) (u v : K) :
    RatioPresentation.ProjectivelyEq
      ({ source := u * q.source + v
         left := u * q.left + v
         right := u * q.right + v
         returned := u * q.returned + v } : ReturnedQuadrilateral K).projectiveFace
      q.projectiveFace := by
  exact swingPair_affine_projectively q.source q.left q.right q.returned u v

end ProjectiveFace

/-! ## 5. The exact refine-and-fork scale law -/

/-- The boundary coupling at binary fork depth `forks` and dyadic scale depth `scale`.
`arc` is the retained integral/arc quantity `C`; `differential` is the local scale `r`. -/
def refineForkCoupling (forks scale : ℕ) (arc differential : ℝ) : ℝ :=
  (2 : ℝ) ^ forks * arc / ((2 : ℝ) ^ scale * differential)

/-- Refining the scale by one octave while adding one binary fork leaves the coupling fixed. -/
theorem refineForkCoupling_succ_succ (forks scale : ℕ) (arc differential : ℝ)
    (hdifferential : differential ≠ 0) :
    refineForkCoupling (forks + 1) (scale + 1) arc differential =
      refineForkCoupling forks scale arc differential := by
  simp only [refineForkCoupling, pow_succ]
  field_simp

/-- At fork depth two and the settled scale, the coupling is `2^2 (C / r) = 4 C / r`.
This is the exact formula available here; any identification with a gravity tensor is additional
physics, not part of this theorem. -/
theorem refineForkCoupling_two_zero (arc differential : ℝ) :
    refineForkCoupling 2 0 arc differential = 4 * (arc / differential) := by
  norm_num [refineForkCoupling, div_eq_mul_inv]
  ring

section Audit

#print axioms sum_edges_eq_zero
#print axioms MaterialPolygon.sum_pressureIncrementAt_eq_zero
#print axioms polygonalCirculation_constant_eq_zero
#print axioms PolygonTurnLedger.sum_interior_pi
#print axioms ReturnedQuadrilateral.swingThenTransport_eq_flatFourth
#print axioms ReturnedQuadrilateral.projectiveFace_affine_projectively
#print axioms refineForkCoupling_succ_succ

end Audit

end Soma.Holonics.Millennium.NavierStokesMaterialPolygon
