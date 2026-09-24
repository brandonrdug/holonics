import Mathlib

/-!
# Section residuals

For a linear receiver and a (possibly nonlinear) right-inverse section, the
section coordinates and the receiver-blind remainder reconstruct the source
exactly.  Changing section changes only the kernel-valued residual; no history
or archive is introduced.
-/

namespace Holonics.Foundation.SectionResidual

variable {E Q : Type*} [AddCommGroup E] [AddCommGroup Q]
  [Module ℝ E] [Module ℝ Q]

structure Section (q : E →ₗ[ℝ] Q) where
  value : Q → E
  rightInverse : ∀ a, q (value a) = a

def remainder {q : E →ₗ[ℝ] Q} (s : Section q) (x : E) : E :=
  x - s.value (q x)

theorem receiver_remainder_zero {q : E →ₗ[ℝ] Q} (s : Section q) (x : E) :
    q (remainder s x) = 0 := by
  simp [remainder, map_sub, s.rightInverse]

theorem source_reconstructs {q : E →ₗ[ℝ] Q} (s : Section q) (x : E) :
    s.value (q x) + remainder s x = x := by
  simp [remainder]

theorem section_value_is_receiver {q : E →ₗ[ℝ] Q} (s : Section q) (a : Q) :
    q (s.value a) = a :=
  s.rightInverse a

def shift {q : E →ₗ[ℝ] Q} (s s' : Section q) (a : Q) : E :=
  s'.value a - s.value a

theorem shift_kernel {q : E →ₗ[ℝ] Q} (s s' : Section q) (a : Q) :
    q (shift s s' a) = 0 := by
  simp [shift, map_sub, s.rightInverse, s'.rightInverse]

theorem remainder_change {q : E →ₗ[ℝ] Q} (s s' : Section q) (x : E) :
    remainder s' x = remainder s x - shift s s' (q x) := by
  simp [remainder, shift]

theorem shift_cocycle {q : E →ₗ[ℝ] Q} (s₁ s₂ s₃ : Section q) (a : Q) :
    shift s₁ s₃ a = shift s₁ s₂ a + shift s₂ s₃ a := by
  simp [shift]

theorem residual_reconstructs_with_shift {q : E →ₗ[ℝ] Q}
    (s s' : Section q) (x : E) :
    s'.value (q x) + remainder s x - shift s s' (q x) = x := by
  have h := source_reconstructs s' x
  rw [remainder_change s s' x] at h
  calc
    s'.value (q x) + remainder s x - shift s s' (q x) =
        s'.value (q x) + (remainder s x - shift s s' (q x)) := by abel
    _ = x := h

end Holonics.Foundation.SectionResidual
