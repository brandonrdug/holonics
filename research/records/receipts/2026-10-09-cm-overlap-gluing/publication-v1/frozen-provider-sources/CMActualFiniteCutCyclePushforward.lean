import CMActualGraphDiagonalLengthDegree
import CMActualGraphDiagonalTorComparison
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.Algebra.BigOperators.Finprod

/-! SOURCE-ONLY CANDIDATE, NOT CHECKED BY LEAN.

The receiver is the actual finite graph--diagonal cut F over Spec C.
Its coefficient at q is the intrinsic stalk length, and the two coefficients
are compared to the already checked actual local Serre Tor-length sums.
The native AlgebraicCycle.map consumes the actual structure morphism and its
actual residue degrees. The finite point partition proves quasi-compactness.

agent-inferred: use this one native, explicitly zero-weight pushforward as
the next consumer of the local result. Zero weights are declared operands
of Mathlib's ungraded map API. This source does not assert a codimension
typing on the ambient product, a Chow product, rational-equivalence descent,
or a Betti/cup-product pairing. Those are separate comparison obligations.

The external helical pair interaction touches faces and placement, cell
holonomy, tube and tower thread; helix and pair stay attached. The recorded
failures avoided are an unjoined comparison entering a consumer, an authored
answer in place of a derivation, and ideal-module rank substituted for the
rational Hodge carrier rank. Refs #62. No compiler or shared lease used.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory AlgebraicGeometry

namespace Holonics.Hodge.CMGraphSource

attribute [local instance] cmActualFixedFintype

private def cmActualCutComplexPointUnique : Unique cmComplexPoint := by
  change Unique (PrimeSpectrum ℂ)
  infer_instance

attribute [local instance] cmActualCutComplexPointUnique

theorem cmActualFixedBase_quasiCompact : QuasiCompact cmActualFixedBase := by
  constructor
  intro U _ _
  exact (Set.toFinite (cmActualFixedBase ⁻¹' U)).isCompact

attribute [local instance] cmActualFixedBase_quasiCompact

/-- Native algebraic-cycle coefficients are intrinsic local lengths.
The accepted local Tor comparisons certify the two resulting coefficients. -/
def cmActualFiniteCutCycle : AlgebraicCycle CMProjectiveFixedScheme ℤ where
  toFun q :=
    (Module.length (CMProjectiveFixedScheme.presheaf.stalk q)
      (CMProjectiveFixedScheme.presheaf.stalk q)).toNat
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' _ _ :=
    ⟨Set.univ, Filter.univ_mem, Set.toFinite _⟩

theorem cmActualFiniteCutCycle_coefficient (q : CMProjectiveFixedScheme) :
    cmActualFiniteCutCycle q = 1 := by
  change ((Module.length (CMProjectiveFixedScheme.presheaf.stalk q)
    (CMProjectiveFixedScheme.presheaf.stalk q)).toNat : ℤ) = 1
  rw [cmActualFixedIntrinsicLengthOne]
  norm_num

theorem cmActualFiniteCutCycle_Y_eq_Serre :
    cmActualFiniteCutCycle cmActualYFixedPoint =
      cmActualYGraphDiagonalSerreMultiplicity := by
  rw [cmActualFiniteCutCycle_coefficient,
    cmActualYGraphDiagonalSerreMultiplicity_eq_length,
    cmActualYCutQuotient_ambient_length_one]
  norm_num

theorem cmActualFiniteCutCycle_Z_eq_Serre :
    cmActualFiniteCutCycle cmActualZFixedPoint =
      cmActualZGraphDiagonalSerreMultiplicity := by
  rw [cmActualFiniteCutCycle_coefficient,
    cmActualZGraphDiagonalSerreMultiplicity_eq_length,
    cmActualZCutQuotient_ambient_length_one]
  norm_num

/-- The dimensions supplied to the native ungraded map are explicitly zero.
This does not supply an ambient codimension theorem. -/
def cmActualFiniteCutPushforward : AlgebraicCycle cmComplexPoint ℤ :=
  AlgebraicCycle.map cmActualFixedBase
    (fun _ => (0 : ℕ)) (fun _ => (0 : ℕ)) cmActualFiniteCutCycle

private theorem cmActualFiniteCut_card : Fintype.card CMProjectiveFixedScheme = 2 := by
  rw [← Fintype.card_congr cmActualFixedPointEquiv]
  decide

theorem cmActualFiniteCutPushforward_coefficient (b : cmComplexPoint) :
    cmActualFiniteCutPushforward b = 2 := by
  change (∑ᶠ q ∈ cmActualFixedBase ⁻¹' {b}, cmActualFiniteCutCycle q *
    (AlgebraicCycle.mapCoeff cmActualFixedBase
      (fun _ => (0 : ℕ)) (fun _ => (0 : ℕ)) q : ℤ)) = 2
  have hpreimage : cmActualFixedBase ⁻¹' {b} = Set.univ := by
    ext q
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  rw [hpreimage, finsum_mem_univ, finsum_eq_sum_of_fintype]
  simp [AlgebraicCycle.mapCoeff, cmActualFiniteCutCycle_coefficient,
    cmActualFixedResidueDegreeOne, cmActualFiniteCut_card]

theorem cmActualFiniteCutPushforward_eq_lengthDegree (b : cmComplexPoint) :
    cmActualFiniteCutPushforward b =
      (cmActualGraphDiagonalLengthDegree.toNat : ℤ) := by
  rw [cmActualFiniteCutPushforward_coefficient,
    cmActualGraphDiagonalLengthDegree_two]
  norm_num

theorem cmActualFiniteCutPushforward_eq_pointCycle :
    cmActualFiniteCutPushforward =
      Function.locallyFinsuppWithin.single (IsLocalRing.closedPoint ℂ) (2 : ℤ) := by
  ext b
  rw [cmActualFiniteCutPushforward_coefficient]
  simp [Function.locallyFinsuppWithin.single_apply,
    Subsingleton.elim b (IsLocalRing.closedPoint ℂ)]

-- These audits are planned validation requests; they have not been executed.
#print axioms cmActualFixedBase_quasiCompact
#print axioms cmActualFiniteCutCycle_Y_eq_Serre
#print axioms cmActualFiniteCutCycle_Z_eq_Serre
#print axioms cmActualFiniteCutPushforward_coefficient
#print axioms cmActualFiniteCutPushforward_eq_lengthDegree
#print axioms cmActualFiniteCutPushforward_eq_pointCycle

end Holonics.Hodge.CMGraphSource
