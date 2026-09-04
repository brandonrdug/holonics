import ElementaryHolonics.Millennium.HolonicFourTorusCarrier
import ElementaryHolonics.Millennium.HolonicComplexParametron

/-!
# The finite four-torus realizes a Complex Parametron incidence body

The faithful rank-four carrier now enters the existing Complex Parametron algebra: four-torus
vertices are nodes, oriented axis edges are branches, and cellular boundary is the signed incidence
matrix.  Integer edge currents embed exactly in real branch sections.  Discrete integration by
parts factors the Parametron drive action through the cellular boundary, while the four cut-current
receiver reconstructs every realized period-lattice coefficient and remains monodromy covariant.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicFourTorusParametronRealization

open scoped BigOperators
open Soma.Holonics
open Soma.Holonics.Geometry.SixSphereMonodromy
open Soma.Holonics.Millennium.HolonicComplexParametron
open Soma.Holonics.Millennium.HolonicFourTorusCarrier
open Soma.Holonics.Millennium.HolonicTorusMonodromyReceiver

/-- Four-torus vertices are the finite Parametron node population. -/
abbrev ParametronNode (grain : ℕ) := Vertex grain

/-- Oriented four-torus axis edges are the finite Parametron branch population. -/
abbrev ParametronBranch (grain : ℕ) := Edge grain

/-- Exact signed cellular incidence, embedded from integers into reals. -/
def cellularIncidence (edge : ParametronBranch grain) (node : ParametronNode grain) : ℝ :=
  (edgeBoundary edge node : ℤ)

private theorem sum_single_incidence_mul
    (node : ParametronNode grain) (state : ParametronNode grain → ℝ) :
    ∑ x, ((Finsupp.single node (1 : ℤ) x : ℤ) : ℝ) * state x = state node := by
  simp [Finsupp.single_apply]

/-- Every branch drop is terminal potential minus initial potential. -/
theorem branchDrop_cellularIncidence_eq_endpointDifference
    (state : ParametronNode grain → ℝ) (edge : ParametronBranch grain) :
    branchDrop cellularIncidence state edge =
      state (stepVertex edge.direction edge.base) - state edge.base := by
  simp only [branchDrop, cellularIncidence, edgeBoundary, Finsupp.sub_apply, Int.cast_sub,
    sub_mul]
  rw [Finset.sum_sub_distrib, sum_single_incidence_mul, sum_single_incidence_mul]

/-- Integer cellular current embeds exactly into the real branch-current section. -/
def chainDrive (chain : Chain (ParametronBranch grain)) : ParametronBranch grain → ℝ :=
  fun edge ↦ chain edge

/-- The integer-to-real current chart loses no addressed edge-chain occurrence. -/
theorem chainDrive_injective : Function.Injective (chainDrive (grain := grain)) := by
  intro left right heq
  ext edge
  have hreal : (left edge : ℝ) = (right edge : ℝ) := by
    simpa [chainDrive] using congrFun heq edge
  exact_mod_cast hreal

/-- The real incidence sum at a node is exactly the cast cellular boundary coefficient. -/
theorem cellularIncidence_sum_eq_boundaryOne
    (chain : Chain (ParametronBranch grain)) (node : ParametronNode grain) :
    ∑ edge, chainDrive chain edge * cellularIncidence edge node =
      ((boundaryOne chain node : ℤ) : ℝ) := by
  change (∑ edge, (chain edge : ℝ) * (edgeBoundary edge node : ℤ)) =
    ((boundaryOne chain node : ℤ) : ℝ)
  rw [boundaryOne, Finsupp.linearCombination_apply, Finsupp.sum_apply]
  rw [Finsupp.sum_fintype]
  · norm_cast
  · intro edge
    simp

/-- Discrete integration by parts on the four-torus Parametron body. -/
theorem driveAction_chainDrive_eq_boundaryPairing
    (chain : Chain (ParametronBranch grain)) (state : ParametronNode grain → ℝ) :
    driveAction (chainDrive chain) cellularIncidence state =
      ∑ node, ((boundaryOne chain node : ℤ) : ℝ) * state node := by
  unfold driveAction branchDrop
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro node hnode
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, cellularIncidence_sum_eq_boundaryOne]

/-- Every closed four-torus current has zero pairing with every exact nodal potential drop. -/
theorem driveAction_chainDrive_eq_zero_of_boundaryOne_eq_zero
    (chain : Chain (ParametronBranch grain)) (hclosed : boundaryOne chain = 0)
    (state : ParametronNode grain → ℝ) :
    driveAction (chainDrive chain) cellularIncidence state = 0 := by
  rw [driveAction_chainDrive_eq_boundaryPairing, hclosed]
  simp

/-- Real current through one declared axis cut. -/
def axisCrossSectionCurrent (direction : Direction) (cut : AxisIndex grain)
    (current : ParametronBranch grain → ℝ) : ℝ :=
  ∑ edge, current edge * (dualAxisCut direction cut edge : ℝ)

/-- On an integer current, the real cut receiver is exactly the cast integer cochain receiver. -/
theorem axisCrossSectionCurrent_chainDrive_eq_cast_evaluateCochain
    (direction : Direction) (cut : AxisIndex grain)
    (chain : Chain (ParametronBranch grain)) :
    axisCrossSectionCurrent direction cut (chainDrive chain) =
      (evaluateCochain (dualAxisCut direction cut) chain : ℝ) := by
  have hinteger :
      evaluateCochain (dualAxisCut direction cut) chain =
        ∑ edge, chain edge * dualAxisCut direction cut edge := by
    rw [evaluateCochain, Finsupp.linearCombination_apply]
    simpa using Finsupp.sum_fintype chain
      (fun edge coefficient ↦ coefficient • dualAxisCut direction cut edge)
      (by intro edge; simp)
  unfold axisCrossSectionCurrent chainDrive
  rw [hinteger]
  norm_cast

/-- The complete four-cut real current face. -/
def fourAxisCurrentReceiver (current : ParametronBranch grain → ℝ) : Direction → ℝ :=
  fun direction ↦ axisCrossSectionCurrent direction (0 : AxisIndex grain) current

/-- The real four-cut receiver is the coordinatewise cast of the integer four-cut receiver. -/
theorem fourAxisCurrentReceiver_chainDrive
    (chain : Chain (ParametronBranch grain)) :
    fourAxisCurrentReceiver (chainDrive chain) =
      fun direction ↦ (axisCycleReceiver chain direction : ℝ) := by
  funext direction
  exact axisCrossSectionCurrent_chainDrive_eq_cast_evaluateCochain direction 0 chain

/-- The four real cut currents reconstruct every realized period-lattice coefficient. -/
theorem fourAxisCurrentReceiver_realization (cycle : Lattice) :
    fourAxisCurrentReceiver
        (chainDrive (axisCycleRealization (grain := grain) cycle)) =
      fun direction ↦ (cycle direction : ℝ) := by
  rw [fourAxisCurrentReceiver_chainDrive, axisCycleReceiver_realization]

/-- A dual lattice probe pairs with the complete real four-cut current face. -/
def fourAxisCurrentPairing (probe : Lattice)
    (current : ParametronBranch grain → ℝ) : ℝ :=
  ∑ direction : Direction, (probe direction : ℝ) * fourAxisCurrentReceiver current direction

/-- The realized Complex Parametron current pairing is exactly the integral cycle pairing. -/
theorem fourAxisCurrentPairing_realization (probe cycle : Lattice) :
    fourAxisCurrentPairing probe
        (chainDrive (axisCycleRealization (grain := grain) cycle)) =
      ((cyclePairing probe cycle : ℤ) : ℝ) := by
  rw [fourAxisCurrentPairing, fourAxisCurrentReceiver_realization]
  simp [cyclePairing, dotProduct]

/-- The realized Complex Parametron current square commutes with order-three monodromy. -/
theorem fourAxisCurrentPairing_T1_A1 (probe cycle : Lattice) :
    fourAxisCurrentPairing (A1.mulVec probe)
        (chainDrive (axisCycleRealization (grain := grain) (T1.mulVec cycle))) =
      fourAxisCurrentPairing probe
        (chainDrive (axisCycleRealization (grain := grain) cycle)) := by
  rw [fourAxisCurrentPairing_realization, fourAxisCurrentPairing_realization,
    cyclePairing_T1_A1]

/-- The realized Complex Parametron current square commutes with order-four monodromy. -/
theorem fourAxisCurrentPairing_T2_A2 (probe cycle : Lattice) :
    fourAxisCurrentPairing (A2.mulVec probe)
        (chainDrive (axisCycleRealization (grain := grain) (T2.mulVec cycle))) =
      fourAxisCurrentPairing probe
        (chainDrive (axisCycleRealization (grain := grain) cycle)) := by
  rw [fourAxisCurrentPairing_realization, fourAxisCurrentPairing_realization,
    cyclePairing_T2_A2]

/-- The realized Complex Parametron current square commutes with unipotent cusp monodromy. -/
theorem fourAxisCurrentPairing_T0_M0 (probe cycle : Lattice) :
    fourAxisCurrentPairing (M0.mulVec probe)
        (chainDrive (axisCycleRealization (grain := grain) (T0.mulVec cycle))) =
      fourAxisCurrentPairing probe
        (chainDrive (axisCycleRealization (grain := grain) cycle)) := by
  rw [fourAxisCurrentPairing_realization, fourAxisCurrentPairing_realization,
    cyclePairing_T0_M0]

end Soma.Holonics.Millennium.HolonicFourTorusParametronRealization

section Audit
open Soma.Holonics.Millennium.HolonicFourTorusParametronRealization
#print axioms branchDrop_cellularIncidence_eq_endpointDifference
#print axioms chainDrive_injective
#print axioms cellularIncidence_sum_eq_boundaryOne
#print axioms driveAction_chainDrive_eq_boundaryPairing
#print axioms driveAction_chainDrive_eq_zero_of_boundaryOne_eq_zero
#print axioms axisCrossSectionCurrent_chainDrive_eq_cast_evaluateCochain
#print axioms fourAxisCurrentReceiver_chainDrive
#print axioms fourAxisCurrentReceiver_realization
#print axioms fourAxisCurrentPairing_realization
#print axioms fourAxisCurrentPairing_T1_A1
#print axioms fourAxisCurrentPairing_T2_A2
#print axioms fourAxisCurrentPairing_T0_M0
end Audit
