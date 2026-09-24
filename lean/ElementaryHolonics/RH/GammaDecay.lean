import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-!
# The Gamma factor decays exponentially on a vertical line, with no Stirling estimate

`GammaBound` bounds `‖Γ(s)‖` by `Γ(Re s)` — the horizon law, magnitude blind to the imaginary
direction — and that bound is *flat* in `t`.  It cannot see the exponential decay that makes `Λ`
small on vertical lines, and the strip front stalled there on a stated absence: *"mathlib carries
no complex Stirling estimate."*

**That absence was never the obstruction.**  Euler's reflection formula gives the decay exactly,
in closed form, with no asymptotics at all.  On the critical line `s = 1/2 + it` the reflection
`1 − s` is the *conjugate* of `s`, so the reflection formula reads

```text
Γ(s) · conj(Γ(s)) = π / sin(π s) ,   i.e.   ‖Γ(1/2 + it)‖² = π / cosh(π t) .
```

An **equality**, not an estimate.  The same move on `s = it` gives `‖Γ(it)‖² = π/(t·sinh(π t))`.

This is the corpus's own reading of what a reflection is: the critical line is `Fix(J)` for the
anti-linear `J(z) = 1 − z̄`, and **a function's magnitude on the fixed locus of an anti-linear
involution is forced by the functional equation alone.**  Off the line the two involutions part
company and one needs a genuine transport — which is what Hadamard's three-lines supplies.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.RH.GammaDecay

open Complex Real

/-- On the critical line the reflection `s ↦ 1 − s` is complex conjugation. -/
theorem theReflectionIsConjugationOnTheCriticalLine (t : ℝ) :
    (starRingEnd ℂ) (1 / 2 + (t : ℂ) * Complex.I) = 1 - (1 / 2 + (t : ℂ) * Complex.I) := by
  simp [Complex.ext_iff]
  ring

/-- The sine at the reflected argument is a hyperbolic cosine — real, positive, and growing. -/
theorem theSineOnTheCriticalLineIsACosh (t : ℝ) :
    Complex.sin ((Real.pi : ℂ) * (1 / 2 + (t : ℂ) * Complex.I))
      = ((Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
  have hz : (Real.pi : ℂ) * (1 / 2 + (t : ℂ) * Complex.I)
      = (Real.pi : ℂ) / 2 + ((Real.pi * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hz, Complex.sin_add, Complex.sin_pi_div_two, Complex.cos_pi_div_two]
  rw [Complex.cos_mul_I]
  simp [Complex.ofReal_cosh]

/-- **THE MAGNITUDE OF `Γ` ON THE CRITICAL LINE, EXACTLY.**  `‖Γ(1/2 + it)‖² = π / cosh(π t)`.
Euler's reflection formula plus the fact that on this line reflection *is* conjugation.  No
Stirling estimate, no asymptotic expansion, no error term — an identity. -/
theorem theGammaMagnitudeOnTheCriticalLineIsExact (t : ℝ) :
    ‖Complex.Gamma (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * t) := by
  set z : ℂ := 1 / 2 + (t : ℂ) * Complex.I with hzdef
  have key := Complex.Gamma_mul_Gamma_one_sub z
  rw [← theReflectionIsConjugationOnTheCriticalLine t, ← hzdef, Complex.Gamma_conj,
    Complex.mul_conj] at key
  rw [hzdef] at key
  rw [theSineOnTheCriticalLineIsACosh t] at key
  have hcosh : (0:ℝ) < Real.cosh (Real.pi * t) := Real.cosh_pos _
  have : ((Complex.normSq (Complex.Gamma z) : ℝ) : ℂ)
      = ((Real.pi / Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
    rw [key]; push_cast; field_simp
  have hreal := Complex.ofReal_inj.mp this
  rw [Complex.normSq_eq_norm_sq] at hreal
  exact hreal

/-- **HENCE EXPONENTIAL DECAY, WITH AN EXPLICIT CONSTANT.**  `cosh x ≥ e^x/2`, so
`‖Γ(1/2+it)‖² ≤ 2π e^{−π|t|}` and the Gamma factor is exponentially small up the line. -/
theorem theGammaDecaysExponentiallyOnTheCriticalLine (t : ℝ) :
    ‖Complex.Gamma (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 2
      ≤ 2 * Real.pi * Real.exp (-(Real.pi * |t|)) := by
  rw [theGammaMagnitudeOnTheCriticalLineIsExact t]
  have hpos : (0:ℝ) < Real.exp (Real.pi * |t|) := Real.exp_pos _
  have hcosh : Real.exp (Real.pi * |t|) / 2 ≤ Real.cosh (Real.pi * t) := by
    rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
      rw [Real.cosh_eq]
      have : (0:ℝ) ≤ Real.exp (-(Real.pi * t)) := (Real.exp_pos _).le
      linarith
    · rw [h, Real.cosh_eq]
      have h1 : Real.pi * -t = -(Real.pi * t) := by ring
      rw [h1]
      have : (0:ℝ) ≤ Real.exp (Real.pi * t) := (Real.exp_pos _).le
      linarith
  have hcpos : (0:ℝ) < Real.cosh (Real.pi * t) := Real.cosh_pos _
  set E : ℝ := Real.exp (Real.pi * |t|) with hEdef
  have hEpos : (0:ℝ) < E := Real.exp_pos _
  have hinv : E⁻¹ * E = 1 := inv_mul_cancel₀ (ne_of_gt hEpos)
  have hneg : Real.exp (-(Real.pi * |t|)) = E⁻¹ := by rw [hEdef, ← Real.exp_neg]
  rw [hneg, div_le_iff₀ hcpos]
  have hstep : 2 * Real.pi * E⁻¹ * (E / 2) ≤ 2 * Real.pi * E⁻¹ * Real.cosh (Real.pi * t) :=
    mul_le_mul_of_nonneg_left hcosh (by positivity)
  have hcollapse : 2 * Real.pi * E⁻¹ * (E / 2) = Real.pi := by
    field_simp
  linarith [hstep, hcollapse.ge, hcollapse.le]

end Soma.Holonics.RH.GammaDecay
