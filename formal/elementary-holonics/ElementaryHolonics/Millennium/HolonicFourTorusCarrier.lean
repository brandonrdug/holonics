import ElementaryHolonics.Millennium.HolonicRankFourWindingRealization
import ElementaryHolonics.Foundation.BoundaryReceiver

/-!
# A finite four-torus carrier with four surviving cycle directions

The doubled solid-torus realization distinguishes four branch-chain coefficients but kills two of
them after quotienting by two-boundaries.  The correct finite carrier for the real body of a
complex two-torus is instead a product of four cyclic axes.  This file constructs its vertices,
oriented edges, square faces, cellular boundaries, four axis windings, and four dual cuts.

Every axis winding closes, every dual cut vanishes on every two-boundary, and the four cut readings
reconstruct the complete rank-four lattice coefficient vector.  Hence all four directions survive
the cellular homology receiver; no smooth or complex-geometric realization is asserted here.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicFourTorusCarrier

open scoped BigOperators
open Soma.Holonics.Foundation
open Soma.Holonics
open Soma.Holonics.Geometry.SixSphereMonodromy

/-- The four oriented axes of the finite carrier. -/
abbrev Direction := Fin 4

/-- Every cyclic axis is nonempty and has `grain + 1` addressed vertices. -/
abbrev AxisIndex (grain : ℕ) := Fin (grain + 1)

/-- A vertex is one addressed coordinate on each of the four cyclic axes. -/
abbrev Vertex (grain : ℕ) := Direction → AxisIndex grain

/-- The cyclic successor on each axis. -/
def axisNext {grain : ℕ} : AxisIndex grain ≃ AxisIndex grain :=
  Equiv.addRight 1

/-- One elementary swing advances exactly one axis coordinate. -/
def stepVertex (direction : Direction) (vertex : Vertex grain) : Vertex grain :=
  Function.update vertex direction (axisNext (vertex direction))

@[simp]
theorem stepVertex_same (direction : Direction) (vertex : Vertex grain) :
    stepVertex direction vertex direction = axisNext (vertex direction) := by
  simp [stepVertex]

@[simp]
theorem stepVertex_ne (direction other : Direction) (vertex : Vertex grain)
    (hne : other ≠ direction) :
    stepVertex direction vertex other = vertex other := by
  simp [stepVertex, hne]

/-- Swings in distinct cyclic directions commute at the vertex receiver. -/
theorem stepVertex_commute (first second : Direction) (vertex : Vertex grain)
    (hne : first ≠ second) :
    stepVertex first (stepVertex second vertex) =
      stepVertex second (stepVertex first vertex) := by
  ext direction
  by_cases hfirst : direction = first
  · subst direction
    simp [stepVertex, hne, Ne.symm hne]
  · by_cases hsecond : direction = second
    · subst direction
      simp [stepVertex, hfirst, hne]
    · simp [stepVertex, hfirst, hsecond]

/-- An oriented edge records its swung axis and its initial vertex. -/
structure Edge (grain : ℕ) where
  direction : Direction
  base : Vertex grain
  deriving DecidableEq, Fintype

/-- A square face records two distinct swing directions and its initial vertex. -/
structure Face (grain : ℕ) where
  first : Direction
  second : Direction
  first_ne_second : first ≠ second
  base : Vertex grain
  deriving DecidableEq, Fintype

/-- Integer cellular chains retain every addressed cell coefficient. -/
abbrev Chain (α : Type*) := α →₀ ℤ

/-- Terminal minus initial incidence of one oriented axis edge. -/
def edgeBoundary (edge : Edge grain) : Chain (Vertex grain) :=
  Finsupp.single (stepVertex edge.direction edge.base) 1 -
    Finsupp.single edge.base 1

/-- Linear extension of the edge boundary. -/
def boundaryOne : Chain (Edge grain) →ₗ[ℤ] Chain (Vertex grain) :=
  Finsupp.linearCombination ℤ edgeBoundary

@[simp]
theorem boundaryOne_single (edge : Edge grain) (coefficient : ℤ) :
    boundaryOne (Finsupp.single edge coefficient) = coefficient • edgeBoundary edge := by
  simp [boundaryOne]

/-- The oriented commutator square of two distinct elementary swings. -/
def faceBoundary (face : Face grain) : Chain (Edge grain) :=
  Finsupp.single ⟨face.first, face.base⟩ 1 +
    Finsupp.single ⟨face.second, stepVertex face.first face.base⟩ 1 -
    Finsupp.single ⟨face.first, stepVertex face.second face.base⟩ 1 -
    Finsupp.single ⟨face.second, face.base⟩ 1

/-- Every elementary swing square closes: `∂₁∂₂ = 0`. -/
theorem boundaryOne_faceBoundary_eq_zero (face : Face grain) :
    boundaryOne (faceBoundary face) = 0 := by
  rcases face with ⟨first, second, hne, base⟩
  simp only [faceBoundary, map_add, map_sub, boundaryOne_single, one_smul, edgeBoundary]
  rw [stepVertex_commute first second base hne]
  abel

/-- Linear extension of the square-face boundary. -/
def boundaryTwo : Chain (Face grain) →ₗ[ℤ] Chain (Edge grain) :=
  Finsupp.linearCombination ℤ faceBoundary

@[simp]
theorem boundaryTwo_single (face : Face grain) (coefficient : ℤ) :
    boundaryTwo (Finsupp.single face coefficient) = coefficient • faceBoundary face := by
  simp [boundaryTwo]

/-- The addressed vertex on one axis with every transverse coordinate fixed at zero. -/
def axisVertex (direction : Direction) (coordinate : AxisIndex grain) : Vertex grain :=
  Function.update 0 direction coordinate

theorem stepVertex_axisVertex (direction : Direction) (coordinate : AxisIndex grain) :
    stepVertex direction (axisVertex direction coordinate) =
      axisVertex direction (axisNext coordinate) := by
  ext other
  by_cases h : other = direction
  · subst other
    simp [stepVertex, axisVertex]
  · simp [stepVertex, axisVertex, h]

/-- One closed winding around the declared cyclic axis. -/
def axisWindingChain (direction : Direction) : Chain (Edge grain) :=
  ∑ coordinate : AxisIndex grain,
    Finsupp.single ⟨direction, axisVertex direction coordinate⟩ 1

/-- Every axis winding has zero vertex boundary. -/
theorem boundaryOne_axisWindingChain_eq_zero (direction : Direction) :
    boundaryOne (axisWindingChain (grain := grain) direction) = 0 := by
  rw [axisWindingChain, map_sum]
  simp only [boundaryOne_single, one_smul, edgeBoundary, stepVertex_axisVertex]
  rw [Finset.sum_sub_distrib]
  have hshift := Equiv.sum_comp (axisNext (grain := grain))
    (fun coordinate : AxisIndex grain ↦
      Finsupp.single (axisVertex direction coordinate) (1 : ℤ))
  rw [hshift]
  exact sub_self _

/-- Exact evaluation of an integer edge cochain. -/
def evaluateCochain (cochain : Edge grain → ℤ) : Chain (Edge grain) →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ cochain

/-- A dual cut reads edges in one direction exactly where they cross one declared coordinate. -/
def dualAxisCut (direction : Direction) (cut : AxisIndex grain) : Edge grain → ℤ :=
  fun edge ↦ if edge.direction = direction ∧ edge.base direction = cut then 1 else 0

/-- A dual cut meets its corresponding unit winding exactly once. -/
theorem dualAxisCut_pairs_same_winding (direction : Direction) (cut : AxisIndex grain) :
    evaluateCochain (dualAxisCut direction cut)
      (axisWindingChain direction) = 1 := by
  rw [axisWindingChain, map_sum]
  simp [evaluateCochain, dualAxisCut, axisVertex]

/-- A dual cut is blind to every transverse winding direction. -/
theorem dualAxisCut_pairs_other_winding (direction other : Direction)
    (cut : AxisIndex grain) (hne : other ≠ direction) :
    evaluateCochain (dualAxisCut direction cut)
      (axisWindingChain other) = 0 := by
  rw [axisWindingChain, map_sum]
  simp [evaluateCochain, dualAxisCut, hne]

/-- Every dual axis cut vanishes on the boundary of every elementary square. -/
theorem dualAxisCut_pairs_faceBoundary_eq_zero
    (direction : Direction) (cut : AxisIndex grain) (face : Face grain) :
    evaluateCochain (dualAxisCut direction cut) (faceBoundary face) = 0 := by
  rcases face with ⟨first, second, hne, base⟩
  by_cases hfirst : direction = first
  · subst first
    have hsecond : second ≠ direction := Ne.symm hne
    simp [faceBoundary, evaluateCochain, dualAxisCut, stepVertex, hne, hsecond]
  · by_cases hsecond : direction = second
    · subst second
      simp [faceBoundary, evaluateCochain, dualAxisCut, stepVertex, hfirst, hne]
    · simp [faceBoundary, evaluateCochain, dualAxisCut, hfirst, hsecond]

/-- Consequently every dual axis cut vanishes on every cellular two-boundary. -/
theorem dualAxisCut_pairs_boundaryTwo_eq_zero
    (direction : Direction) (cut : AxisIndex grain) (faces : Chain (Face grain)) :
    evaluateCochain (dualAxisCut direction cut) (boundaryTwo faces) = 0 := by
  let composite : Chain (Face grain) →ₗ[ℤ] ℤ :=
    (evaluateCochain (dualAxisCut direction cut)).comp boundaryTwo
  have hzero : composite = 0 := by
    apply Finsupp.lhom_ext
    intro face coefficient
    simp [composite, dualAxisCut_pairs_faceBoundary_eq_zero]
  exact LinearMap.congr_fun hzero faces

/-- No unit axis winding is a cellular two-boundary. -/
theorem axisWindingChain_isNot_boundaryTwo
    (direction : Direction) (cut : AxisIndex grain) :
    ¬ ∃ faces : Chain (Face grain), boundaryTwo faces = axisWindingChain direction := by
  change axisWindingChain direction ∉ Set.range boundaryTwo.toAddMonoidHom
  exact not_mem_range_of_receiver_boundary_eq_zero
    boundaryTwo.toAddMonoidHom
    (evaluateCochain (dualAxisCut direction cut)).toAddMonoidHom
    (dualAxisCut_pairs_boundaryTwo_eq_zero direction cut)
    (by
      change evaluateCochain (dualAxisCut direction cut) (axisWindingChain direction) ≠ 0
      rw [dualAxisCut_pairs_same_winding]
      norm_num)

/-- A rank-four lattice vector realizes as the corresponding integer combination of the four
surviving axis windings. -/
def axisCycleRealization (cycle : Lattice) : Chain (Edge grain) :=
  ∑ direction : Direction, cycle direction • axisWindingChain direction

/-- The four dual cuts form the coefficient receiver of an arbitrary edge chain. -/
def axisCycleReceiver (chain : Chain (Edge grain)) : Lattice :=
  fun direction ↦ evaluateCochain (dualAxisCut direction (0 : AxisIndex grain)) chain

/-- The four-cut receiver is a left inverse of the four-axis realization. -/
theorem axisCycleReceiver_realization (cycle : Lattice) :
    axisCycleReceiver (axisCycleRealization (grain := grain) cycle) = cycle := by
  ext observed
  rw [axisCycleReceiver, axisCycleRealization, map_sum]
  rw [Finset.sum_eq_single observed]
  · simp [dualAxisCut_pairs_same_winding]
  · intro other hother hne
    simp [dualAxisCut_pairs_other_winding observed other _ hne]
  · simp

/-- The finite four-torus realization loses no rank-four lattice occurrence. -/
theorem axisCycleRealization_injective :
    Function.Injective (axisCycleRealization (grain := grain)) :=
  Function.LeftInverse.injective axisCycleReceiver_realization

/-- The faithful rank-four cycle realization as an addressed passage. -/
def axisCyclePassage : AddressedPassage Lattice (Chain (Edge grain)) :=
  AddressedPassage.graph axisCycleRealization

/-- Every realized lattice cycle remains in the complete addressed fibre. -/
theorem axisCyclePassage_retains_cycle (cycle : Lattice) :
    Nonempty ((axisCyclePassage (grain := grain)).Fibre cycle (axisCycleRealization cycle)) :=
  ⟨AddressedPassage.graphFibre _ cycle⟩

/-- A dual lattice probe consumes the four exact cut currents of a finite four-torus chain. -/
def axisCurrentPairing (probe : Lattice) (chain : Chain (Edge grain)) : ℝ :=
  ∑ direction : Direction,
    (probe direction : ℝ) * (axisCycleReceiver chain direction : ℝ)

/-- On every realized rank-four cycle, the finite cut-current pairing is exactly the cast of the
integral cycle/dual-cycle receiver. -/
theorem axisCurrentPairing_realization (probe cycle : Lattice) :
    axisCurrentPairing probe (axisCycleRealization (grain := grain) cycle) =
      ((Soma.Holonics.Millennium.HolonicTorusMonodromyReceiver.cyclePairing
        probe cycle : ℤ) : ℝ) := by
  rw [axisCurrentPairing, axisCycleReceiver_realization]
  simp [Soma.Holonics.Millennium.HolonicTorusMonodromyReceiver.cyclePairing, dotProduct]

/-- The faithful four-torus current receiver commutes with the order-three monodromy. -/
theorem axisCurrentPairing_T1_A1 (probe cycle : Lattice) :
    axisCurrentPairing (A1.mulVec probe)
        (axisCycleRealization (grain := grain) (T1.mulVec cycle)) =
      axisCurrentPairing probe (axisCycleRealization (grain := grain) cycle) := by
  rw [axisCurrentPairing_realization, axisCurrentPairing_realization,
    Soma.Holonics.Millennium.HolonicTorusMonodromyReceiver.cyclePairing_T1_A1]

/-- The faithful four-torus current receiver commutes with the order-four monodromy. -/
theorem axisCurrentPairing_T2_A2 (probe cycle : Lattice) :
    axisCurrentPairing (A2.mulVec probe)
        (axisCycleRealization (grain := grain) (T2.mulVec cycle)) =
      axisCurrentPairing probe (axisCycleRealization (grain := grain) cycle) := by
  rw [axisCurrentPairing_realization, axisCurrentPairing_realization,
    Soma.Holonics.Millennium.HolonicTorusMonodromyReceiver.cyclePairing_T2_A2]

/-- The faithful four-torus current receiver commutes with the unipotent cusp monodromy. -/
theorem axisCurrentPairing_T0_M0 (probe cycle : Lattice) :
    axisCurrentPairing (M0.mulVec probe)
        (axisCycleRealization (grain := grain) (T0.mulVec cycle)) =
      axisCurrentPairing probe (axisCycleRealization (grain := grain) cycle) := by
  rw [axisCurrentPairing_realization, axisCurrentPairing_realization,
    Soma.Holonics.Millennium.HolonicTorusMonodromyReceiver.cyclePairing_T0_M0]

end Soma.Holonics.Millennium.HolonicFourTorusCarrier

section Audit
open Soma.Holonics.Millennium.HolonicFourTorusCarrier
#print axioms stepVertex_commute
#print axioms boundaryOne_faceBoundary_eq_zero
#print axioms boundaryOne_axisWindingChain_eq_zero
#print axioms dualAxisCut_pairs_same_winding
#print axioms dualAxisCut_pairs_other_winding
#print axioms dualAxisCut_pairs_faceBoundary_eq_zero
#print axioms dualAxisCut_pairs_boundaryTwo_eq_zero
#print axioms axisWindingChain_isNot_boundaryTwo
#print axioms axisCycleReceiver_realization
#print axioms axisCycleRealization_injective
#print axioms axisCyclePassage_retains_cycle
#print axioms axisCurrentPairing_realization
#print axioms axisCurrentPairing_T1_A1
#print axioms axisCurrentPairing_T2_A2
#print axioms axisCurrentPairing_T0_M0
end Audit
