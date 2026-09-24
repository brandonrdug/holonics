import ElementaryHolonics.Millennium.HolonicFourTorusParametronRealization
import ElementaryHolonics.Foundation.BoundaryScalePassage
import Mathlib.Tactic

/-!
# Rational four-torus current chart

The finite four-torus carrier already supplies integer axis windings, dual cuts, square
boundaries, and vertex boundaries.  This owner extends that exact chart to rational branch
currents.  The four-cut receiver returns a rational axis face; the axis realization is its chosen
section, and the residual is retained as the complete receiver fibre invisible to those cuts.

The scale passage below is deliberately receiver-relative: it transports a fine current through
`J_target ∘ C_source` and carries the four-cut face by identity.  It makes no claim that the
finite geometric carriers at two grains are fully refined or equivalent.
-/

namespace Soma.Holonics.Physics.FourTorusCurrentChart

noncomputable section

open scoped BigOperators
open Soma.Holonics
open Soma.Holonics.Millennium.HolonicFourTorusCarrier
open Soma.Holonics.Millennium.HolonicFourTorusParametronRealization
open Soma.Holonics.Millennium.HolonicTorusMonodromyReceiver
open Soma.Holonics.Millennium.HolonicGranularBoundaryRadiation

abbrev RationalLattice := Direction → ℚ

/-- Rational branch-current sections on the addressed edge population. -/
abbrev RationalCurrent (grain : ℕ) := Edge grain → ℚ

/-- The rational current carried by one integer axis winding. -/
def rationalAxisWinding (grain : ℕ) (direction : Direction) : RationalCurrent grain :=
  fun edge ↦ (axisWindingChain (grain := grain) direction edge : ℚ)

/-- The rational four-axis realization `J`. -/
def axisRealization (grain : ℕ) : RationalLattice →ₗ[ℚ] RationalCurrent grain where
  toFun cycle edge := ∑ direction : Direction,
    cycle direction * rationalAxisWinding grain direction edge
  map_add' left right := by
    funext edge
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' scalar cycle := by
    funext edge
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro direction hdirection
    simp only [RingHom.id_apply]
    ring

/-- The rational four-cut receiver `C`. -/
def axisReceiver (grain : ℕ) : RationalCurrent grain →ₗ[ℚ] RationalLattice where
  toFun current direction := ∑ edge : Edge grain,
    current edge * (dualAxisCut direction (0 : AxisIndex grain) edge : ℚ)
  map_add' left right := by
    funext direction
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' scalar current := by
    funext direction
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro edge hedge
    simp only [RingHom.id_apply]
    ring

/-! The short chart names used by the current reduction. -/

abbrev J (grain : ℕ) := axisRealization grain
abbrev C (grain : ℕ) := axisReceiver grain

private theorem rationalCut_axisWinding
    (grain : ℕ) (observed direction : Direction) :
    (∑ edge : Edge grain,
      rationalAxisWinding grain direction edge *
        (dualAxisCut observed (0 : AxisIndex grain) edge : ℚ)) =
      if observed = direction then 1 else 0 := by
  by_cases same : observed = direction
  · subst observed
    have integer_identity := dualAxisCut_pairs_same_winding
      (grain := grain) direction (0 : AxisIndex grain)
    simp only [rationalAxisWinding]
    change (∑ edge : Edge grain,
      (axisWindingChain direction edge : ℚ) *
        (dualAxisCut direction (0 : AxisIndex grain) edge : ℚ)) = 1
    have cast_identity :
        ((evaluateCochain (dualAxisCut direction (0 : AxisIndex grain))
          (axisWindingChain direction) : ℤ) : ℚ) = 1 := by
      exact_mod_cast integer_identity
    simpa [evaluateCochain, Finsupp.linearCombination_apply,
      Finsupp.sum_apply, Finsupp.sum_fintype] using cast_identity
  · have integer_identity := dualAxisCut_pairs_other_winding
      (grain := grain) observed direction (0 : AxisIndex grain) (Ne.symm same)
    simp only [rationalAxisWinding, if_neg same]
    change (∑ edge : Edge grain,
      (axisWindingChain direction edge : ℚ) *
        (dualAxisCut observed (0 : AxisIndex grain) edge : ℚ)) = 0
    have cast_identity :
        ((evaluateCochain (dualAxisCut observed (0 : AxisIndex grain))
          (axisWindingChain direction) : ℤ) : ℚ) = 0 := by
      exact_mod_cast integer_identity
    simpa [evaluateCochain, Finsupp.linearCombination_apply,
      Finsupp.sum_apply, Finsupp.sum_fintype] using cast_identity

@[simp] theorem axisReceiver_axisRealization (grain : ℕ) (cycle : RationalLattice) :
    axisReceiver grain (axisRealization grain cycle) = cycle := by
  funext observed
  simp only [axisReceiver, axisRealization, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  fin_cases observed <;> simp [rationalCut_axisWinding]

theorem axisRealization_injective (grain : ℕ) :
    Function.Injective (axisRealization grain) :=
  Function.LeftInverse.injective (axisReceiver_axisRealization grain)

/-- The complete rational receiver fibre remainder after extracting the four cuts. -/
def residual (grain : ℕ) (current : RationalCurrent grain) : RationalCurrent grain :=
  current - axisRealization grain (axisReceiver grain current)

theorem current_decomposition (grain : ℕ) (current : RationalCurrent grain) :
    current = axisRealization grain (axisReceiver grain current) + residual grain current := by
  simp [residual, sub_eq_add_neg]

theorem axisReceiver_residual_eq_zero (grain : ℕ) (current : RationalCurrent grain) :
    axisReceiver grain (residual grain current) = 0 := by
  simp [residual, axisReceiver_axisRealization]

/-- Rational cellular vertex boundary of a branch current. -/
def vertexBoundary (grain : ℕ) : RationalCurrent grain →ₗ[ℚ] (Vertex grain → ℚ) where
  toFun current vertex := ∑ edge : Edge grain,
    current edge * (edgeBoundary edge vertex : ℚ)
  map_add' left right := by
    funext vertex
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' scalar current := by
    funext vertex
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro edge hedge
    simp only [RingHom.id_apply]
    ring

private theorem vertexBoundary_rationalAxisWinding_eq_zero
    (grain : ℕ) (direction : Direction) :
    vertexBoundary grain (rationalAxisWinding grain direction) = 0 := by
  funext vertex
  have integer_identity := boundaryOne_axisWindingChain_eq_zero
    (grain := grain) direction
  have cast_identity :
      ((boundaryOne (axisWindingChain direction) vertex : ℤ) : ℚ) = 0 := by
    exact_mod_cast congrArg (fun chain : Chain (Vertex grain) => chain vertex)
      integer_identity
  simpa [vertexBoundary, rationalAxisWinding, boundaryOne,
    Finsupp.linearCombination_apply, Finsupp.sum_apply, Finsupp.sum_fintype] using cast_identity

theorem vertexBoundary_axisRealization_eq_zero
    (grain : ℕ) (cycle : RationalLattice) :
    vertexBoundary grain (axisRealization grain cycle) = 0 := by
  funext vertex
  simp only [vertexBoundary, axisRealization, LinearMap.coe_mk, AddHom.coe_mk,
    rationalAxisWinding]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro direction hdirection
  have hzero := congrArg (fun function : Vertex grain → ℚ => function vertex)
    (vertexBoundary_rationalAxisWinding_eq_zero grain direction)
  change (∑ edge : Edge grain,
      (axisWindingChain direction edge : ℚ) * (edgeBoundary edge vertex : ℚ)) = 0 at hzero
  rw [hzero, mul_zero]

/-- The rational face-boundary current of one addressed square. -/
def faceBoundaryCurrent (face : Face grain) : RationalCurrent grain :=
  fun edge ↦ (faceBoundary face edge : ℚ)

/-- The rational all-face boundary map `D` into branch currents.  It sums every addressed square
boundary; `twoFace` in the companion reduction selects the two active faces `c0` and `c1`. -/
def D (grain : ℕ) : (Face grain → ℚ) →ₗ[ℚ] RationalCurrent grain where
  toFun faces edge := ∑ face : Face grain,
    faces face * (faceBoundary face edge : ℚ)
  map_add' left right := by
    funext edge
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' scalar faces := by
    funext edge
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro face hface
    simp only [RingHom.id_apply]
    ring

theorem axisReceiver_faceBoundaryCurrent_eq_zero
    (grain : ℕ) (face : Face grain) :
    axisReceiver grain (faceBoundaryCurrent face) = 0 := by
  funext direction
  have integer_identity := dualAxisCut_pairs_faceBoundary_eq_zero
    (grain := grain) direction (0 : AxisIndex grain) face
  have cast_identity :
      ((evaluateCochain (dualAxisCut direction (0 : AxisIndex grain))
        (faceBoundary face) : ℤ) : ℚ) = 0 := by
    exact_mod_cast integer_identity
  simpa [axisReceiver, faceBoundaryCurrent, evaluateCochain,
    Finsupp.linearCombination_apply, Finsupp.sum_apply, Finsupp.sum_fintype] using cast_identity

theorem C_D_eq_zero (grain : ℕ) (faces : Face grain → ℚ) :
    C grain (D grain faces) = 0 := by
  funext direction
  simp only [C, axisReceiver, D, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro face hface
  have hzero := congrArg (fun reading : RationalLattice => reading direction)
    (axisReceiver_faceBoundaryCurrent_eq_zero grain face)
  change (∑ edge : Edge grain,
      (faceBoundary face edge : ℚ) *
        (dualAxisCut direction (0 : AxisIndex grain) edge : ℚ)) = 0 at hzero
  rw [hzero, mul_zero]

theorem vertexBoundary_faceBoundaryCurrent_eq_zero
    (grain : ℕ) (face : Face grain) :
    vertexBoundary grain (faceBoundaryCurrent face) = 0 := by
  funext vertex
  have integer_identity := boundaryOne_faceBoundary_eq_zero
    (grain := grain) face
  have cast_identity :
      ((boundaryOne (faceBoundary face) vertex : ℤ) : ℚ) = 0 := by
    exact_mod_cast congrArg (fun chain : Chain (Vertex grain) => chain vertex)
      integer_identity
  simpa [vertexBoundary, faceBoundaryCurrent, boundaryOne,
    Finsupp.linearCombination_apply, Finsupp.sum_apply, Finsupp.sum_fintype] using cast_identity

theorem vertexBoundary_D_eq_zero (grain : ℕ) (faces : Face grain → ℚ) :
    vertexBoundary grain (D grain faces) = 0 := by
  funext vertex
  simp only [vertexBoundary, D, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro face hface
  have hzero := congrArg (fun reading : Vertex grain → ℚ => reading vertex)
    (vertexBoundary_faceBoundaryCurrent_eq_zero grain face)
  change (∑ edge : Edge grain,
      (faceBoundary face edge : ℚ) * (edgeBoundary edge vertex : ℚ)) = 0 at hzero
  rw [hzero, mul_zero]

def F01 (grain : ℕ) : Face grain :=
  ⟨0, 1, by decide, 0⟩

def F02 (grain : ℕ) : Face grain :=
  ⟨0, 2, by decide, 0⟩

def c0 (grain : ℕ) : RationalCurrent grain := faceBoundaryCurrent (F01 grain)

def c1 (grain : ℕ) : RationalCurrent grain := faceBoundaryCurrent (F02 grain)

theorem F01_axisReceiver_eq_zero (grain : ℕ) :
    axisReceiver grain (faceBoundaryCurrent (F01 grain)) = 0 :=
  axisReceiver_faceBoundaryCurrent_eq_zero grain (F01 grain)

theorem F02_axisReceiver_eq_zero (grain : ℕ) :
    axisReceiver grain (faceBoundaryCurrent (F02 grain)) = 0 :=
  axisReceiver_faceBoundaryCurrent_eq_zero grain (F02 grain)

theorem F01_vertexBoundary_eq_zero (grain : ℕ) :
    vertexBoundary grain (faceBoundaryCurrent (F01 grain)) = 0 :=
  vertexBoundary_faceBoundaryCurrent_eq_zero grain (F01 grain)

theorem F02_vertexBoundary_eq_zero (grain : ℕ) :
    vertexBoundary grain (faceBoundaryCurrent (F02 grain)) = 0 :=
  vertexBoundary_faceBoundaryCurrent_eq_zero grain (F02 grain)

theorem C_c0_eq_zero (grain : ℕ) : C grain (c0 grain) = 0 := by
  exact F01_axisReceiver_eq_zero grain

theorem C_c1_eq_zero (grain : ℕ) : C grain (c1 grain) = 0 := by
  exact F02_axisReceiver_eq_zero grain

theorem vertexBoundary_c0_eq_zero (grain : ℕ) :
    vertexBoundary grain (c0 grain) = 0 :=
  F01_vertexBoundary_eq_zero grain

theorem vertexBoundary_c1_eq_zero (grain : ℕ) :
    vertexBoundary grain (c1 grain) = 0 :=
  F02_vertexBoundary_eq_zero grain

/-! ## Receiver-relative scale passage -/

open Soma.Holonics.Millennium.HolonicGranularBoundaryRadiation

def fourCutScalePassage (fineGrain coarseGrain : ℕ) :
    BoundaryScalePassage ℚ (RationalCurrent fineGrain) RationalLattice
      (RationalCurrent coarseGrain) RationalLattice where
  fineBoundary := axisReceiver fineGrain
  coarseBoundary := axisReceiver coarseGrain
  interiorTransport := (axisRealization coarseGrain).comp (axisReceiver fineGrain)
  boundaryTransport := LinearMap.id
  boundary_natural := by
    ext current
    simp [LinearMap.comp_apply, axisReceiver_axisRealization]

theorem fourCutScalePassage_transport_boundary
    (fineGrain coarseGrain : ℕ) (current : RationalCurrent fineGrain) :
    (fourCutScalePassage fineGrain coarseGrain).coarseBoundary
        ((fourCutScalePassage fineGrain coarseGrain).interiorTransport current) =
      (fourCutScalePassage fineGrain coarseGrain).boundaryTransport
        ((fourCutScalePassage fineGrain coarseGrain).fineBoundary current) :=
  (fourCutScalePassage fineGrain coarseGrain).transport_boundary current

end

end Soma.Holonics.Physics.FourTorusCurrentChart

section Audit
open Soma.Holonics.Physics.FourTorusCurrentChart
#print axioms axisReceiver_axisRealization
#print axioms axisRealization_injective
#print axioms current_decomposition
#print axioms axisReceiver_residual_eq_zero
#print axioms C_D_eq_zero
#print axioms vertexBoundary_axisRealization_eq_zero
#print axioms vertexBoundary_D_eq_zero
#print axioms axisReceiver_faceBoundaryCurrent_eq_zero
#print axioms vertexBoundary_faceBoundaryCurrent_eq_zero
#print axioms fourCutScalePassage_transport_boundary
end Audit
