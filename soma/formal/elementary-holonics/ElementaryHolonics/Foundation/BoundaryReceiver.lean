import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# A visible cycle cannot be a boundary

This is the source-neutral receiver law shared by the singular-homology, cellular-winding, and
discrete-current constructions.  A receiver which annihilates every admitted boundary but returns
a nonzero difference on a cycle separates that cycle from the boundary image.

The theorem deliberately does not construct a receiver.  Each source still owes its own typed
receiver, boundary-compatibility proof, and nonzero reading.  The zero receiver is therefore an
immediate negative control: it satisfies boundary annihilation but cannot establish visibility.
-/

namespace Soma.Holonics.Foundation

/-- A boundary-annihilating receiver with a nonzero reading separates the observed cycle from the
boundary image. -/
theorem not_mem_range_of_receiver_ne_zero
    {X Y Z : Type*}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    (boundary : Y →+ X)
    (receiver : X →+ Z)
    (annihilates : receiver.comp boundary = 0)
    {cycle : X}
    (visible : receiver cycle ≠ 0) :
    cycle ∉ Set.range boundary := by
  rintro ⟨source, rfl⟩
  apply visible
  change (receiver.comp boundary) source = 0
  rw [annihilates]
  rfl

/-- The same separation law stated with a pointwise boundary-annihilation hypothesis. -/
theorem not_mem_range_of_receiver_boundary_eq_zero
    {X Y Z : Type*}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    (boundary : Y →+ X)
    (receiver : X →+ Z)
    (annihilates : ∀ source, receiver (boundary source) = 0)
    {cycle : X}
    (visible : receiver cycle ≠ 0) :
    cycle ∉ Set.range boundary := by
  rintro ⟨source, rfl⟩
  exact visible (annihilates source)

/-- A nonzero reading is impossible for the zero receiver; this is the minimal negative control. -/
theorem zero_receiver_not_visible
    {X Z : Type*}
    [AddCommGroup X] [AddCommGroup Z]
    (cycle : X) :
    ¬ ((0 : X →+ Z) cycle ≠ 0) := by
  simp

#print axioms not_mem_range_of_receiver_ne_zero
#print axioms not_mem_range_of_receiver_boundary_eq_zero
#print axioms zero_receiver_not_visible

end Soma.Holonics.Foundation
