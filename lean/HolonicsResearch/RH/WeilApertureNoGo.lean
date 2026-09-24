import Mathlib

/-!
# The fixed Sonin aperture cannot carry a new prime overlap

A prime-power translation by at least the logarithmic aperture length
moves the open supported current entirely outside that aperture. Projecting
it immediately back therefore returns zero. This is the exact obstruction
to constructing the semilocal Weil remainder by conjugating the old base
operator while keeping its support fixed. It does not rule out a growing
aperture, a changed metric, or the required semilocal connection.
-/

noncomputable section

namespace Holonics.RH.WeilApertureNoGo

/-- The open logarithmic support aperture of length L. Its boundary is
excluded, matching an L² aperture up to null sets without using a.e.
quotients in this exact pointwise chart. -/
def aperture (L : ℝ) (a : ℝ → ℂ) (x : ℝ) : ℂ :=
  if -L / 2 < x ∧ x < L / 2 then a x else 0

/-- Translation in the logarithmic source coordinate. -/
def translate (t : ℝ) (a : ℝ → ℂ) (x : ℝ) : ℂ :=
  a (x + t)

theorem aperture_idempotent (L : ℝ) (a : ℝ → ℂ) :
    aperture L (aperture L a) = aperture L a := by
  funext x
  by_cases hx : -L / 2 < x ∧ x < L / 2
  · simp [aperture, hx]
  · simp [aperture, hx]

/-- At a shift at least the aperture length, no point belongs to both
the original open interval and the returned translated interval. -/
theorem aperture_translate_aperture_zero
    {L t : ℝ} (ht : L ≤ t) (a : ℝ → ℂ) :
    aperture L (translate t (aperture L a)) = 0 := by
  funext x
  by_cases hx : -L / 2 < x ∧ x < L / 2
  · have hshift : ¬ (-L / 2 < x + t ∧ x + t < L / 2) := by
      intro h
      linarith [hx.1, ht, h.2]
    simp [aperture, translate, hx, hshift]
  · simp [aperture, hx]

/-- Every prime-power logarithmic shift is at least log 2, so the
base aperture of length log 2 sees no returned overlap. -/
theorem prime_power_base_aperture_zero
    (p m : ℕ) (hp : 2 ≤ p) (hm : 1 ≤ m) (a : ℝ → ℂ) :
    aperture (Real.log 2)
      (translate ((m : ℝ) * Real.log p)
        (aperture (Real.log 2) a)) = 0 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogp : Real.log 2 ≤ Real.log p := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hp
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hshift : Real.log 2 ≤ (m : ℝ) * Real.log p := by
    nlinarith
  exact aperture_translate_aperture_zero hshift a

end Holonics.RH.WeilApertureNoGo

section Audit
open Holonics.RH.WeilApertureNoGo
#print axioms aperture_idempotent
#print axioms aperture_translate_aperture_zero
#print axioms prime_power_base_aperture_zero
end Audit

