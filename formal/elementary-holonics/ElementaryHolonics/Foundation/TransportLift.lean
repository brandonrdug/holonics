import ElementaryHolonics.Foundation.Receiver
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Transport lifting replaces untyped division

[definition] A request to "divide" a general transported object is represented here as the exact
lifting problem `transport source = target`.  Its return is the complete source fibre.  The fibre
may be empty, a singleton, or plural; none of those cases is silently coerced into an inverse.

[proved-derived; formal-checked] For an additive transport, every inhabited lift fibre is exactly
a translate of the kernel.  This is the matrix/tensor-shaped replacement for scalar division:
the obstruction is failure to lie in the range, uniqueness is triviality of the relevant kernel
fibre, and every unresolved direction is returned rather than selected.
-/

namespace Soma.Holonics.Foundation.Lift

universe u v

/-- [definition] The complete source population lifting one target through a typed transport. -/
def TransportLift {Source : Type u} {Target : Type v}
    (transport : Source → Target) (target : Target) : Type u :=
  {source : Source // transport source = target}

/-- [definition] `TransportLift` is the preimage fibre of the transport receiver. -/
abbrev PreimageFibre {Source : Type u} {Target : Type v}
    (transport : Source → Target) (target : Target) :=
  TransportLift transport target

/-- Every exhibited source supplies an exact lift of its returned target. -/
def ofSource {Source : Type u} {Target : Type v} (transport : Source → Target)
    (source : Source) : TransportLift transport (transport source) :=
  ⟨source, rfl⟩

/-- [proved-derived; formal-checked] A lift exists exactly when the target is in the transport's
actual range. -/
theorem nonempty_iff_mem_range {Source : Type u} {Target : Type v}
    (transport : Source → Target) (target : Target) :
    Nonempty (TransportLift transport target) ↔ target ∈ Set.range transport := by
  constructor
  · rintro ⟨⟨source, exact⟩⟩
    exact ⟨source, exact⟩
  · rintro ⟨source, exact⟩
    exact ⟨⟨source, exact⟩⟩

/-- [definition] An exact obstruction is a proof that the requested target lies outside the
transport range. -/
structure LiftObstruction {Source : Type u} {Target : Type v}
    (transport : Source → Target) (target : Target) : Prop where
  outsideRange : target ∉ Set.range transport

/-- [proved-derived; formal-checked] An obstruction makes the lift fibre empty. -/
theorem LiftObstruction.noLift {Source : Type u} {Target : Type v}
    {transport : Source → Target} {target : Target}
    (obstruction : LiftObstruction transport target) :
    IsEmpty (TransportLift transport target) := by
  refine ⟨fun lift ↦ obstruction.outsideRange ?_⟩
  exact ⟨lift.1, lift.2⟩

/-- [proved-derived; formal-checked] A lift fibre is a singleton precisely when every two
sources returning the target are equal. -/
theorem subsingleton_iff_unique_source {Source : Type u} {Target : Type v}
    (transport : Source → Target) (target : Target) :
    Subsingleton (TransportLift transport target) ↔
      ∀ left right, transport left = target → transport right = target → left = right := by
  constructor
  · intro h left right hleft hright
    exact congrArg Subtype.val (h.elim ⟨left, hleft⟩ ⟨right, hright⟩)
  · intro h
    refine ⟨?_⟩
    intro left right
    exact Subtype.ext (h left.1 right.1 left.2 right.2)

/-! ## Additive transports: every inhabited fibre is a kernel translate -/

variable {Source : Type u} {Target : Type v} [AddCommGroup Source] [AddCommGroup Target]

/-- Two lifts of one target differ by a direction in the additive kernel. -/
theorem difference_mem_kernel (transport : Source →+ Target) {target : Target}
    (left right : TransportLift transport target) :
    left.1 - right.1 ∈ transport.ker := by
  rw [AddMonoidHom.mem_ker, map_sub, left.2, right.2, sub_self]

/-- Translating one lift by a kernel direction returns another lift of the same target. -/
def translateByKernel (transport : Source →+ Target) {target : Target}
    (base : TransportLift transport target) (direction : transport.ker) :
    TransportLift transport target :=
  ⟨base.1 + direction.1, by
    rw [map_add, base.2, direction.2, add_zero]⟩

/-- [proved-derived; formal-checked] Once one lift exists, the complete preimage fibre is
equivalent to the kernel—not merely counted by it. -/
def fibreEquivKernel (transport : Source →+ Target) {target : Target}
    (base : TransportLift transport target) :
    TransportLift transport target ≃ transport.ker where
  toFun other := ⟨other.1 - base.1, difference_mem_kernel transport other base⟩
  invFun direction := translateByKernel transport base direction
  left_inv other := by
    apply Subtype.ext
    simp [translateByKernel]
  right_inv direction := by
    apply Subtype.ext
    simp [translateByKernel]

/-- [proved-derived; formal-checked] A trivial additive kernel makes every inhabited lift fibre
unique. -/
theorem subsingleton_of_kernel_eq_bot (transport : Source →+ Target)
    (hkernel : transport.ker = ⊥) (target : Target) :
    Subsingleton (TransportLift transport target) := by
  rw [subsingleton_iff_unique_source]
  intro left right hleft hright
  have hdifference : left - right ∈ transport.ker := by
    rw [AddMonoidHom.mem_ker, map_sub, hleft, hright, sub_self]
  rw [hkernel, AddSubgroup.mem_bot, sub_eq_zero] at hdifference
  exact hdifference

section Audit

#print axioms nonempty_iff_mem_range
#print axioms LiftObstruction.noLift
#print axioms subsingleton_iff_unique_source
#print axioms difference_mem_kernel
#print axioms fibreEquivKernel
#print axioms subsingleton_of_kernel_eq_bot

end Audit

end Soma.Holonics.Foundation.Lift
