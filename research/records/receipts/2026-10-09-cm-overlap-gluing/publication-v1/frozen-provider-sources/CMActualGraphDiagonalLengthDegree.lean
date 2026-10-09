import CMActualGraphDiagonalMultiplicity
import CMActualFixedResidueDegree
import Mathlib.Data.Fintype.BigOperators

/-! The finite degree of the actual graph--diagonal scheme cut is the sum of
its intrinsic local lengths weighted by the actual structure morphism's
residue degrees. The actual point enumeration supplies the finite partition;
the scalar-preserving quotient comparison supplies its local multiplicities;
the actual base-map squares supply the residue weights. No coefficient is
assigned from point count alone.

agent-inferred: keep the scheme-cut length degree separate from a Chow or
Hodge intersection product until that receiver's comparison is constructed.
This external helical pair receiver touches faces and placement, cell
holonomy and tube; helix, pair and tower remain attached. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource

def cmActualFixedPointAt : Bool → CMProjectiveFixedScheme
  | false => cmActualYFixedPoint
  | true => cmActualZFixedPoint

theorem cmActualFixedPointAt_bijective : Function.Bijective cmActualFixedPointAt := by
  constructor
  · intro a b h
    cases a <;> cases b
    · rfl
    · exact False.elim (actualFixed_two_points_distinct h)
    · exact False.elim (actualFixed_two_points_distinct h.symm)
    · rfl
  · intro q
    rcases actualFixed_two_point_population q with h | h
    · exact ⟨false, h.symm⟩
    · exact ⟨true, h.symm⟩

def cmActualFixedPointEquiv : Bool ≃ CMProjectiveFixedScheme :=
  Equiv.ofBijective cmActualFixedPointAt cmActualFixedPointAt_bijective

-- The proved finite partition supplies this local instance at instance transparency.
@[instance_reducible]
def cmActualFixedFintype : Fintype CMProjectiveFixedScheme :=
  Fintype.ofEquiv Bool cmActualFixedPointEquiv

attribute [local instance] cmActualFixedFintype

/-- Finite scheme-cut degree, using intrinsic local multiplicities and the
residue degrees of the actual structure morphism. -/
def cmActualGraphDiagonalLengthDegree : ℕ∞ :=
  ∑ q : CMProjectiveFixedScheme,
    Module.length (CMProjectiveFixedScheme.presheaf.stalk q)
      (CMProjectiveFixedScheme.presheaf.stalk q) *
        (cmActualFixedBase.residueDegree q : ℕ∞)

theorem cmActualGraphDiagonalLengthDegree_eq_local :
    cmActualGraphDiagonalLengthDegree =
      cmActualYGraphDiagonalMultiplicity *
        (cmActualFixedBase.residueDegree cmActualYFixedPoint : ℕ∞) +
      cmActualZGraphDiagonalMultiplicity *
        (cmActualFixedBase.residueDegree cmActualZFixedPoint : ℕ∞) := by
  unfold cmActualGraphDiagonalLengthDegree
  rw [← cmActualFixedPointEquiv.sum_comp]
  change (∑ b : Bool,
    Module.length (CMProjectiveFixedScheme.presheaf.stalk (cmActualFixedPointAt b))
      (CMProjectiveFixedScheme.presheaf.stalk (cmActualFixedPointAt b)) *
        (cmActualFixedBase.residueDegree (cmActualFixedPointAt b) : ℕ∞)) = _
  rw [Fintype.sum_bool]
  simp only [cmActualFixedPointAt, ← cmActualYGraphDiagonalMultiplicity_eq_intrinsic,
    ← cmActualZGraphDiagonalMultiplicity_eq_intrinsic]
  exact add_comm _ _

theorem cmActualGraphDiagonalLengthDegree_two : cmActualGraphDiagonalLengthDegree = 2 := by
  rw [cmActualGraphDiagonalLengthDegree_eq_local,
    cmActualYGraphDiagonalMultiplicityOne, cmActualZGraphDiagonalMultiplicityOne,
    cmActualYFixedResidueDegreeOne, cmActualZFixedResidueDegreeOne]
  norm_num

#print axioms cmActualFixedPointAt_bijective
#print axioms cmActualGraphDiagonalLengthDegree_eq_local
#print axioms cmActualGraphDiagonalLengthDegree_two
end Holonics.Hodge.CMGraphSource
