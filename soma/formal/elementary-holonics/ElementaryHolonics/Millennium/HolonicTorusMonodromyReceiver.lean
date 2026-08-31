import ElementaryHolonics.Geometry.SixSphereMonodromy
import ElementaryHolonics.Millennium.HolonicTorusParametronRealization
import ElementaryHolonics.Foundation.TransportLift

/-!
# Exact monodromy covariance of the torus cycle receiver

The complex two-torus family carries a rank-four integral lattice.  Its displayed monodromies act
on primal cycles by `T1`, `T2`, and `T0`, while the inverse-transpose matrices `A1`, `A2`, and `M0`
act on dual receiver probes.  This file proves that their integer pairing is unchanged and, more
strongly, that the complete reconstruction fibre of every fixed receiver value is transported by
an explicit equivalence.

This is the algebraic monodromy edge required by Gate L2.  It does not yet identify the rank-four
period lattice with four independent winding populations in the finite polygonal Parametron body;
that realization passage remains the next geometric edge.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicTorusMonodromyReceiver

open Soma.Holonics.Geometry.SixSphereMonodromy
open Soma.Holonics.Foundation.Lift

/-- The exact integer receiver pairing between one addressed dual probe and one primal cycle. -/
def cyclePairing (probe cycle : Lattice) : ℤ :=
  dotProduct probe cycle

/-- With its probe fixed, the cycle pairing is an additive receiver on the full lattice. -/
def cyclePairingAddHom (probe : Lattice) : Lattice →+ ℤ where
  toFun := cyclePairing probe
  map_zero' := by simp [cyclePairing]
  map_add' left right := by
    simp [cyclePairing, dotProduct, mul_add, Finset.sum_add_distrib]

/-- Every integer matrix supplies an additive transport of the primal lattice. -/
def latticeActionAddHom (matrix : LatticeEnd) : Lattice →+ Lattice where
  toFun := matrix.mulVec
  map_zero' := by simp
  map_add' left right := Matrix.mulVec_add matrix left right

/-- A matrix with an exhibited two-sided inverse acts by an additive lattice equivalence. -/
def latticeActionEquiv (matrix inverse : LatticeEnd)
    (matrix_inverse : matrix * inverse = 1)
    (inverse_matrix : inverse * matrix = 1) : Lattice ≃+ Lattice where
  toFun := matrix.mulVec
  invFun := inverse.mulVec
  left_inv cycle := by
    rw [Matrix.mulVec_mulVec, inverse_matrix, Matrix.one_mulVec]
  right_inv cycle := by
    rw [Matrix.mulVec_mulVec, matrix_inverse, Matrix.one_mulVec]
  map_add' left right := Matrix.mulVec_add matrix left right

private theorem transpose_product_eq_one
    (left right : LatticeEnd) (h : left * right = 1) :
    right.transpose * left.transpose = 1 := by
  simpa only [Matrix.transpose_mul, Matrix.transpose_one] using
    congrArg (fun matrix : LatticeEnd ↦ matrix.transpose) h

/-- Inverse-transpose transport of the probe exactly cancels primal basis transport. -/
theorem cyclePairing_covariant_of_inverseTranspose
    (matrix dual : LatticeEnd) (hdual : dual.transpose * matrix = 1)
    (probe cycle : Lattice) :
    cyclePairing (dual.mulVec probe) (matrix.mulVec cycle) = cyclePairing probe cycle := by
  unfold cyclePairing
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, hdual,
    Matrix.vecMul_one]

/-- The order-three primal and dual monodromies preserve the exact cycle receiver. -/
theorem cyclePairing_T1_A1 (probe cycle : Lattice) :
    cyclePairing (A1.mulVec probe) (T1.mulVec cycle) = cyclePairing probe cycle := by
  apply cyclePairing_covariant_of_inverseTranspose
  exact transpose_product_eq_one _ _ A1_isInverseTranspose.2

/-- The order-four primal and dual monodromies preserve the exact cycle receiver. -/
theorem cyclePairing_T2_A2 (probe cycle : Lattice) :
    cyclePairing (A2.mulVec probe) (T2.mulVec cycle) = cyclePairing probe cycle := by
  apply cyclePairing_covariant_of_inverseTranspose
  exact transpose_product_eq_one _ _ A2_isInverseTranspose.2

/-- The unipotent cusp and its dual preserve the exact cycle receiver. -/
theorem cyclePairing_T0_M0 (probe cycle : Lattice) :
    cyclePairing (M0.mulVec probe) (T0.mulVec cycle) = cyclePairing probe cycle := by
  apply cyclePairing_covariant_of_inverseTranspose
  exact transpose_product_eq_one _ _ M0_isInverseTranspose.2

/-- The order-three monodromy is an exact equivalence of the primal lattice. -/
def T1CycleEquiv : Lattice ≃+ Lattice :=
  latticeActionEquiv T1 A1.transpose
    (transpose_product_eq_one _ _ A1_isInverseTranspose.1)
    (transpose_product_eq_one _ _ A1_isInverseTranspose.2)

/-- The order-four monodromy is an exact equivalence of the primal lattice. -/
def T2CycleEquiv : Lattice ≃+ Lattice :=
  latticeActionEquiv T2 A2.transpose
    (transpose_product_eq_one _ _ A2_isInverseTranspose.1)
    (transpose_product_eq_one _ _ A2_isInverseTranspose.2)

/-- The unipotent cusp monodromy is an exact equivalence of the primal lattice. -/
def T0CycleEquiv : Lattice ≃+ Lattice :=
  latticeActionEquiv T0 M0.transpose
    (transpose_product_eq_one _ _ M0_isInverseTranspose.1)
    (transpose_product_eq_one _ _ M0_isInverseTranspose.2)

/-- A natural receiver square transports not merely its value but every source occurrence in the
complete reconstruction fibre. -/
def receiverFibreCovariance
    (sourceTarget : Lattice ≃+ Lattice) (sourceProbe targetProbe : Lattice)
    (natural : ∀ cycle,
      cyclePairing targetProbe (sourceTarget cycle) = cyclePairing sourceProbe cycle)
    (value : ℤ) :
    ReconstructionFibre (cyclePairingAddHom sourceProbe) value ≃
      ReconstructionFibre (cyclePairingAddHom targetProbe) value where
  toFun source := ⟨sourceTarget source.1, by
    change cyclePairing targetProbe (sourceTarget source.1) = value
    rw [natural]
    have sourceProperty := source.property
    change cyclePairing sourceProbe source.1 = value at sourceProperty
    exact sourceProperty⟩
  invFun target := ⟨sourceTarget.symm target.1, by
    change cyclePairing sourceProbe (sourceTarget.symm target.1) = value
    calc
      cyclePairing sourceProbe (sourceTarget.symm target.1) =
          cyclePairing targetProbe (sourceTarget (sourceTarget.symm target.1)) :=
        (natural (sourceTarget.symm target.1)).symm
      _ = cyclePairing targetProbe target.1 := by rw [sourceTarget.apply_symm_apply]
      _ = value := by
        have targetProperty := target.property
        change cyclePairing targetProbe target.1 = value at targetProperty
        exact targetProperty⟩
  left_inv source := by
    apply Subtype.ext
    exact sourceTarget.symm_apply_apply source.1
  right_inv target := by
    apply Subtype.ext
    exact sourceTarget.apply_symm_apply target.1

/-- Every order-three receiver fibre is carried exactly to the corresponding transported-probe
fibre. -/
def T1ReceiverFibreEquiv (probe : Lattice) (value : ℤ) :
    ReconstructionFibre (cyclePairingAddHom probe) value ≃
      ReconstructionFibre (cyclePairingAddHom (A1.mulVec probe)) value :=
  receiverFibreCovariance T1CycleEquiv probe (A1.mulVec probe)
    (cyclePairing_T1_A1 probe) value

/-- Every order-four receiver fibre is carried exactly to the corresponding transported-probe
fibre. -/
def T2ReceiverFibreEquiv (probe : Lattice) (value : ℤ) :
    ReconstructionFibre (cyclePairingAddHom probe) value ≃
      ReconstructionFibre (cyclePairingAddHom (A2.mulVec probe)) value :=
  receiverFibreCovariance T2CycleEquiv probe (A2.mulVec probe)
    (cyclePairing_T2_A2 probe) value

/-- Every unipotent-cusp receiver fibre is carried exactly to the corresponding transported-probe
fibre. -/
def T0ReceiverFibreEquiv (probe : Lattice) (value : ℤ) :
    ReconstructionFibre (cyclePairingAddHom probe) value ≃
      ReconstructionFibre (cyclePairingAddHom (M0.mulVec probe)) value :=
  receiverFibreCovariance T0CycleEquiv probe (M0.mulVec probe)
    (cyclePairing_T0_M0 probe) value

end Soma.Holonics.Millennium.HolonicTorusMonodromyReceiver

section Audit
open Soma.Holonics.Millennium.HolonicTorusMonodromyReceiver
#print axioms cyclePairing_covariant_of_inverseTranspose
#print axioms cyclePairing_T1_A1
#print axioms cyclePairing_T2_A2
#print axioms cyclePairing_T0_M0
#print axioms T1CycleEquiv
#print axioms T2CycleEquiv
#print axioms T0CycleEquiv
#print axioms receiverFibreCovariance
#print axioms T1ReceiverFibreEquiv
#print axioms T2ReceiverFibreEquiv
#print axioms T0ReceiverFibreEquiv
end Audit
