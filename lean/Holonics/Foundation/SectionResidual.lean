import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Tactic.Ring

/-!
# Section residuals

For a linear receiver and a (possibly nonlinear) right-inverse section, the
section coordinates and the receiver-blind remainder reconstruct the source
exactly.  Changing section changes only the kernel-valued residual; no history
or archive is introduced.
-/

/-! [agent-inferred] The section/remainder laws use real modules, linear maps
and additive cancellation. Import their owners explicitly rather than all
Mathlib; every existing statement and proof below is unchanged. -/

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

/-! [agent-inferred] A possibly nonlinear receiving face reads the exact source
return at its contemporary section. The lower return is composed through the
first section, so its mixed term is retained. These are the general laws from
the accepted private recursive section source, relocated into their existing
owner; the Hodge cut below is their concrete consumer. -/

section ReceivingFace
variable {P : Type*} [AddCommGroup P] [Module ℝ P]

def receiverDefect {q : E →ₗ[ℝ] Q} (R : E → ℂ) (s : Section q) (x : E) : ℂ :=
  R (s.value (q x)+remainder s x)-R (s.value (q x))

theorem exact_receiver_defect {q : E →ₗ[ℝ] Q} (R : E → ℂ) (s : Section q) (x : E) :
    R x = R (s.value (q x))+receiverDefect R s x := by
  unfold receiverDefect
  rw [source_reconstructs]
  ring

/-- No linearity of either section or the receiving face is assumed. The
second-level defect is read through the first section at its actual pivot. -/
theorem two_level_receiver_defects {q : E →ₗ[ℝ] Q} {p : Q →ₗ[ℝ] P}
    (R : E → ℂ) (s₁ : Section q) (s₂ : Section p) (x : E) :
    R x = R (s₁.value (s₂.value (p (q x))))+
      receiverDefect R s₁ x+receiverDefect (fun y => R (s₁.value y)) s₂ (q x) := by
  have h₂ := exact_receiver_defect (fun y => R (s₁.value y)) s₂ (q x)
  calc
    R x = R (s₁.value (q x))+receiverDefect R s₁ x := exact_receiver_defect R s₁ x
    _ = (R (s₁.value (s₂.value (p (q x))))+
        receiverDefect (fun y => R (s₁.value y)) s₂ (q x))+receiverDefect R s₁ x := by rw [h₂]
    _ = _ := by ring

/-- A linear receiving face reads its remainder additively at one level.
At a deeper level the composite face must still satisfy this hypothesis. -/
theorem linear_receiver_defect {q : E →ₗ[ℝ] Q}
    (R : E →ₗ[ℝ] ℂ) (s : Section q) (x : E) :
    receiverDefect R s x = R (remainder s x) := by
  unfold receiverDefect
  rw [map_add]
  ring

end ReceivingFace

end Holonics.Foundation.SectionResidual

#print axioms Holonics.Foundation.SectionResidual.receiverDefect
#print axioms Holonics.Foundation.SectionResidual.exact_receiver_defect
#print axioms Holonics.Foundation.SectionResidual.two_level_receiver_defects
#print axioms Holonics.Foundation.SectionResidual.linear_receiver_defect
