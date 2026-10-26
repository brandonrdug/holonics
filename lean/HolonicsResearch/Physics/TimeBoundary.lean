import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# A time boundary keeps the colour and the action, and is the pumped mode

The record `research/records/2026-10-26_A_GALOIS_GAP_IS_A_MODES_MOMENTUM_AN_ORBITS_GAPS_MULTIPLY_TO_ITS_PRIME_AND_A_TIME_BOUNDARY_IS_THE_PUMPED_MODE.md`
(§8) reads a step of a line's impedance at one instant, `Z → Z′` with charge and flux continuous
(Morgenthaler), as the map `A ↦ α A + β·conj(A)` on a mode's complex amplitude, with
`α = (1 + r)/2`, `β = (1 − r)/2` and `r = Z/Z′`. The forward wave keeps `α A` and the backward
wave `β A`; the wavenumber, which is the colour, is kept. The same map is the tower's pumped mode.
This file proves #410's (l).

[proved-standard; formal-checked] What is proved.

1. **In the chart `(Re, Im)` the step is `diag(1, r)`** (`timeBoundary_re`, `timeBoundary_im`):
   the in-phase part is kept and the quadrature part is scaled by `r`.
2. **`α² − β² = r`** (`alpha_sq_sub_beta_sq`).
3. **The action is conserved** (`action_conserved`): `Z′(|αA|² − |βA|²) = Z|A|²`, the forward
   action less the backward action in the new medium equals the action in the old one. The energy
   changes, so the medium's change does work.
4. **The step is non-expansive for `0 ≤ r ≤ 1`** (`timeBoundary_nonexpansive`): `|A′| ≤ |A|`.
5. **Conjugation is time reversal** (`timeBoundary_conj`): the step commutes with `conj`.
6. **The time mirror is `r = 0`** (`timeBoundary_zero`): the step keeps only `Re A`, split equally
   forward and backward.

Consumers: the atlas row `wave.time-boundary`.
-/

namespace Holonics.Physics.TimeBoundary

open Complex ComplexConjugate

/-- [definition] The step of the impedance at one instant, `r = Z/Z′`: `A ↦ α A + β·conj(A)`. -/
noncomputable def timeBoundary (r : ℝ) (A : ℂ) : ℂ :=
  (((1 + r) / 2 : ℝ) : ℂ) * A + (((1 - r) / 2 : ℝ) : ℂ) * conj A

/-- [proved-standard; formal-checked] The in-phase part is kept. -/
theorem timeBoundary_re (r : ℝ) (A : ℂ) : (timeBoundary r A).re = A.re := by
  simp [timeBoundary]
  ring

/-- [proved-standard; formal-checked] The quadrature part is scaled by `r`. -/
theorem timeBoundary_im (r : ℝ) (A : ℂ) : (timeBoundary r A).im = r * A.im := by
  simp [timeBoundary]
  ring

/-- [proved-standard; formal-checked] `α² − β² = r`. -/
theorem alpha_sq_sub_beta_sq (r : ℝ) : ((1 + r) / 2) ^ 2 - ((1 - r) / 2) ^ 2 = r := by
  ring

/-- [proved-standard; formal-checked] **The action is conserved:** `Z′(|αA|² − |βA|²) = Z|A|²`. -/
theorem action_conserved {Z Z' : ℝ} (hZ' : Z' ≠ 0) (A : ℂ) :
    Z' * (normSq ((((1 + Z / Z') / 2 : ℝ) : ℂ) * A) - normSq ((((1 - Z / Z') / 2 : ℝ) : ℂ) * A)) =
      Z * normSq A := by
  simp only [normSq_mul, normSq_ofReal]
  field_simp
  ring

/-- [proved-standard; formal-checked] **Non-expansive for `0 ≤ r ≤ 1`.** -/
theorem timeBoundary_nonexpansive {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) (A : ℂ) :
    normSq (timeBoundary r A) ≤ normSq A := by
  rw [normSq_apply, normSq_apply, timeBoundary_re, timeBoundary_im]
  have hr : r * r ≤ 1 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hr) (mul_self_nonneg A.im)]

/-- [proved-standard; formal-checked] **Conjugation is time reversal:** the step commutes with it. -/
theorem timeBoundary_conj (r : ℝ) (A : ℂ) :
    timeBoundary r (conj A) = conj (timeBoundary r A) := by
  apply Complex.ext
  · simp only [timeBoundary_re, conj_re]
  · simp only [timeBoundary_im, conj_im]
    ring

/-- [proved-standard; formal-checked] **The time mirror is `r = 0`:** only `Re A` is kept. -/
theorem timeBoundary_zero (A : ℂ) : timeBoundary 0 A = (A.re : ℂ) := by
  apply Complex.ext
  · simp [timeBoundary_re]
  · simp [timeBoundary_im]

end Holonics.Physics.TimeBoundary
