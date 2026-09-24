import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic

/-! # Gaussian shift amplitudes carry their changing base point

The coefficient and argument shift form one action. This is the elementary cocycle used by
the existing flowed Gamma source, not a rule for replaying an occurrence history.
-/

noncomputable section

namespace Holonics.Transport.GaussianRebase

def amplitude (t L z : ℂ) : ℂ := Complex.exp (-t * L ^ 2 - z * L)

def shift (t L z : ℂ) : ℂ := z + 2 * t * L

def act (t L : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  amplitude t L z * f (shift t L z)

theorem shift_comp (t L M z : ℂ) : shift t M (shift t L z) = shift t (L + M) z := by
  unfold shift
  ring

/-- The second coefficient is evaluated at the returned, not original, argument. -/
theorem amplitude_cocycle (t L M z : ℂ) :
    amplitude t L z * amplitude t M (shift t L z) = amplitude t (L + M) z := by
  unfold amplitude shift
  rw [← Complex.exp_add]
  congr 1
  ring

theorem act_comp (t L M : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    act t L (act t M f) z = act t (L + M) f z := by
  simp only [act, ← mul_assoc, amplitude_cocycle, shift_comp]

theorem act_zero (t : ℂ) (f : ℂ → ℂ) (z : ℂ) : act t 0 f z = f z := by
  simp [act, amplitude, shift]

theorem returned_inverse (t L : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    act t L (act t (-L) f) z = f z := by
  rw [act_comp]
  simpa using act_zero t f z

/-- Reversing only the coefficient label at the old base leaves a Gaussian residue. -/
theorem unrebased_return (t L z : ℂ) :
    amplitude t L z * amplitude t (-L) z = Complex.exp (-2 * t * L ^ 2) := by
  unfold amplitude
  rw [← Complex.exp_add]
  congr 1
  ring

theorem retimed_amplitude (t dt L z : ℂ) :
    amplitude (t + dt) L z = amplitude t L z * Complex.exp (-dt * L ^ 2) := by
  unfold amplitude
  rw [← Complex.exp_add]
  congr 1
  ring

theorem retimed_shift (t dt L z : ℂ) :
    shift (t + dt) L z = shift t L z + 2 * dt * L := by
  unfold shift
  ring

#print axioms amplitude_cocycle
#print axioms returned_inverse
#print axioms unrebased_return

end Holonics.Transport.GaussianRebase
