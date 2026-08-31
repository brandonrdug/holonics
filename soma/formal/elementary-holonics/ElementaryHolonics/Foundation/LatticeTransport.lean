import ElementaryHolonics.Foundation.TransportLift
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic

/-!
# Lattice transport returns kernel, image, cokernel, index, torsion, and saturation

There is no lattice or matrix "divisor" in this owner.  A declared integer-linear transport
returns its kernel, image, cokernel, and complete lift fibres.  Finite index is the exact cardinal
of the cokernel only when finiteness is carried as part of the receipt.

Saturation is also returned without selecting representatives: a target is saturated by the image
when a nonzero integer multiple enters the image.  Equivalently, its cokernel class has an exhibited
integer torsion witness.  This is the exact place where finite-index and torsion information lives.
-/

namespace Soma.Holonics.Foundation.LatticeTransport

open Soma.Holonics.Foundation.Lift

universe u v

variable (Source : Type u) (Target : Type v)
  [AddCommGroup Source] [AddCommGroup Target]

/-- [definition] A typed integer-lattice transport together with the proof that its cokernel is
finite. -/
structure LatticeIndexReceipt where
  transport : Source →ₗ[ℤ] Target
  finiteCokernel : Finite (Target ⧸ transport.range)

namespace LatticeIndexReceipt

variable {Source : Type u} {Target : Type v}
  [AddCommGroup Source] [AddCommGroup Target]

/-- The directions annihilated by the lattice transport. -/
def kernel (receipt : LatticeIndexReceipt Source Target) : Submodule ℤ Source :=
  receipt.transport.ker

/-- The target directions actually reached by the lattice transport. -/
def image (receipt : LatticeIndexReceipt Source Target) : Submodule ℤ Target :=
  receipt.transport.range

/-- The unresolved target directions modulo the reached image. -/
abbrev Cokernel (receipt : LatticeIndexReceipt Source Target) :=
  Target ⧸ receipt.image

/-- The complete predecessor population behind one target. -/
def reconstructionFibre (receipt : LatticeIndexReceipt Source Target) (target : Target) : Type u :=
  TransportLift receipt.transport target

/-- The unresolved cokernel class of one target. -/
def cokernelClass (receipt : LatticeIndexReceipt Source Target) (target : Target) :
    receipt.Cokernel :=
  Submodule.Quotient.mk target

/-- [definition] The exact lattice index is the finite cokernel cardinal supplied by the receipt. -/
noncomputable def index (receipt : LatticeIndexReceipt Source Target) : ℕ := by
  letI : Finite receipt.Cokernel := receipt.finiteCokernel
  exact Nat.card receipt.Cokernel

/-- [proved-derived; formal-checked] A target has a lift exactly when it lies in the image. -/
theorem nonempty_reconstructionFibre_iff_mem_image
    (receipt : LatticeIndexReceipt Source Target) (target : Target) :
    Nonempty (receipt.reconstructionFibre target) ↔ target ∈ receipt.image := by
  constructor
  · rintro ⟨lift⟩
    exact ⟨lift.1, lift.2⟩
  · rintro ⟨source, exact⟩
    exact ⟨⟨source, exact⟩⟩

/-- [proved-derived; formal-checked] The lifting obstruction is exactly the nonzero cokernel
class. -/
theorem nonempty_reconstructionFibre_iff_cokernelClass_eq_zero
    (receipt : LatticeIndexReceipt Source Target) (target : Target) :
    Nonempty (receipt.reconstructionFibre target) ↔ receipt.cokernelClass target = 0 := by
  rw [receipt.nonempty_reconstructionFibre_iff_mem_image]
  exact (Submodule.Quotient.mk_eq_zero receipt.image).symm

/-- [definition] The torsion population of the cokernel, retained as an actual submodule. -/
def cokernelTorsion (receipt : LatticeIndexReceipt Source Target) :
    Submodule ℤ receipt.Cokernel :=
  Submodule.torsion ℤ receipt.Cokernel

/-- [definition] A target is in the saturation of the image when some nonzero integer multiple
enters the image. -/
def SaturatedByImage (receipt : LatticeIndexReceipt Source Target) (target : Target) : Prop :=
  ∃ scale : ℤ, scale ≠ 0 ∧ scale • target ∈ receipt.image

/-- Every reached target lies in the saturation, witnessed at scale one. -/
theorem mem_image_implies_saturated (receipt : LatticeIndexReceipt Source Target)
    {target : Target} (h : target ∈ receipt.image) :
    receipt.SaturatedByImage target := by
  exact ⟨1, one_ne_zero, by simpa using h⟩

/-- [proved-derived; formal-checked] Saturation is exactly an exhibited torsion witness in the
cokernel class.  No Smith representative or pseudoinverse is selected. -/
theorem saturated_iff_cokernelClass_has_torsionWitness
    (receipt : LatticeIndexReceipt Source Target) (target : Target) :
    receipt.SaturatedByImage target ↔
      ∃ scale : ℤ, scale ≠ 0 ∧ scale • receipt.cokernelClass target = 0 := by
  constructor
  · rintro ⟨scale, hscale, hmem⟩
    refine ⟨scale, hscale, ?_⟩
    rw [cokernelClass, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hmem
  · rintro ⟨scale, hscale, hzero⟩
    refine ⟨scale, hscale, ?_⟩
    rw [cokernelClass, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero] at hzero
    exact hzero

/-- [proved-derived; formal-checked] The saturation predicate is exactly membership of the target's
cokernel class in the actual torsion submodule. -/
theorem cokernelClass_mem_torsion_iff_saturated
    (receipt : LatticeIndexReceipt Source Target) (target : Target) :
    receipt.cokernelClass target ∈ receipt.cokernelTorsion ↔
      receipt.SaturatedByImage target := by
  rw [cokernelTorsion, Submodule.mem_torsion_iff]
  constructor
  · rintro ⟨scale, hzero⟩
    apply (receipt.saturated_iff_cokernelClass_has_torsionWitness target).mpr
    exact ⟨scale.1, (mem_nonZeroDivisors_iff_ne_zero.mp scale.2), by
      change (scale.1 : ℤ) • receipt.cokernelClass target = 0
      exact hzero⟩
  · intro hsaturated
    obtain ⟨scale, hscale, hzero⟩ :=
      (receipt.saturated_iff_cokernelClass_has_torsionWitness target).mp hsaturated
    exact ⟨⟨scale, mem_nonZeroDivisors_of_ne_zero hscale⟩, by simpa using hzero⟩

/-- [definition] An image is saturated when every target whose nonzero multiple is reached was
already reached. -/
def ImageIsSaturated (receipt : LatticeIndexReceipt Source Target) : Prop :=
  ∀ target, receipt.SaturatedByImage target → target ∈ receipt.image

/-- [proved-derived; formal-checked] For a saturated image, every exhibited cokernel torsion class
coming from a target is already zero. -/
theorem cokernel_torsionWitness_vanishes_of_saturated
    (receipt : LatticeIndexReceipt Source Target) (hsaturated : receipt.ImageIsSaturated)
    (target : Target) (witness : ∃ scale : ℤ, scale ≠ 0 ∧
      scale • receipt.cokernelClass target = 0) :
    receipt.cokernelClass target = 0 := by
  have hs : receipt.SaturatedByImage target :=
    (receipt.saturated_iff_cokernelClass_has_torsionWitness target).mpr witness
  exact (Submodule.Quotient.mk_eq_zero receipt.image).mpr (hsaturated target hs)

section Audit

#print axioms nonempty_reconstructionFibre_iff_mem_image
#print axioms nonempty_reconstructionFibre_iff_cokernelClass_eq_zero
#print axioms saturated_iff_cokernelClass_has_torsionWitness
#print axioms cokernelClass_mem_torsion_iff_saturated
#print axioms cokernel_torsionWitness_vanishes_of_saturated

end Audit

end LatticeIndexReceipt

end Soma.Holonics.Foundation.LatticeTransport
