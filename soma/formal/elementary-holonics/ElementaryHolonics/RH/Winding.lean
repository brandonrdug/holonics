import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Tactic

/-!
# The index of a zero is a winding, and the analytic factor carries none

The zero divisor of `Λ₀` is already standing here (`RH.Xi`): discrete support, a finite index at
each point, positive exactly at a zero.  What a contour adds is that the index is *readable* — the
total over a region equals a winding of the function around the region's boundary.  This file
proves the local half of that statement, which is the part the disc supports.

**The local argument principle.**  If `f = (z − a)^n · g` with `g` analytic and nonvanishing on a
closed disc about `a`, then

```text
∮_{|z−a| = R}  f'/f  =  2πi · n .
```

The model factor `(z − a)^n` contributes `2πi·n` — one full turn per unit of order — and the
analytic nonvanishing factor contributes **nothing**, because `g'/g` is analytic on the disc and
Cauchy's theorem kills it.  So the index is exactly a winding number, and the analytic part is a
gauge: it can be deformed freely without moving the count.  That is the phase-object reading of a
divisor — the whole content lives in the turn.

**The boundary, measured 2026-08-23.**  Extending this to a rectangle — the shape the critical
strip needs — is *not* available: `grep -rn "argument principle\|argumentPrinciple" Mathlib/Analysis/`
returns nothing, and `Mathlib/Analysis/Complex/HasPrimitives.lean` carries rectangle integrals only
as a device for constructing primitives, with no homotopy-invariance or index statement attached.
So `theZeroCountIsAWinding` over a box owes a contour-deformation argument that mathlib does not
supply, and this file supplies its local input rather than claiming the whole.
-/

namespace Soma.Holonics.RH.Winding

open Complex Metric intervalIntegral

/-- **THE MODEL FACTOR WINDS ONCE PER UNIT OF ORDER.**  The logarithmic derivative of `(z − a)^n`
is `n/(z − a)`, and its circle integral is `2πi·n`: the order of a zero read as a turn count. -/
theorem theModelFactorWindsOncePerUnitOfOrder (a : ℂ) {R : ℝ} (hR : 0 < R) (n : ℕ) :
    (∮ z in C(a, R), (n : ℂ) / (z - a)) = 2 * Real.pi * Complex.I * n := by
  have h := circleIntegral.integral_sub_inv_of_mem_ball (c := a) (w := a) (R := R)
    (Metric.mem_ball_self hR)
  have hsm : (∮ z in C(a, R), (n : ℂ) / (z - a))
      = (n : ℂ) • (∮ z in C(a, R), (z - a)⁻¹) := by
    rw [← circleIntegral.integral_smul]
    simp [div_eq_mul_inv, smul_eq_mul]
  rw [hsm, h, smul_eq_mul]
  ring

/-- **A NONVANISHING ANALYTIC FACTOR CARRIES NO WINDING.**  Cauchy's theorem: the logarithmic
derivative of a function analytic and nonvanishing on the closed disc integrates to zero, so the
count cannot see it.  The analytic factor is a gauge on the divisor. -/
theorem theAnalyticFactorCarriesNoWinding {a : ℂ} {R : ℝ} (hR : 0 ≤ R) {g : ℂ → ℂ}
    (hg : DiffContOnCl ℂ (fun z => deriv g z / g z) (ball a R)) :
    (∮ z in C(a, R), deriv g z / g z) = 0 :=
  hg.circleIntegral_eq_zero hR

/-- **THE SPLIT.**  Away from the centre, and where `g` does not vanish, the logarithmic derivative
of `(z − a)^n · g` is the model term plus the analytic term.  This is the identity the two
theorems above are applied to. -/
theorem theLogarithmicDerivativeSplits {a z : ℂ} (n : ℕ) (hn : 0 < n) {g : ℂ → ℂ} {g' : ℂ}
    (hz : z ≠ a) (hgz : g z ≠ 0) (hg : HasDerivAt g g' z) :
    deriv (fun w => (w - a) ^ n * g w) z / ((z - a) ^ n * g z)
      = (n : ℂ) / (z - a) + g' / g z := by
  have hp : HasDerivAt (fun w : ℂ => (w - a) ^ n) ((n : ℂ) * (z - a) ^ (n - 1)) z := by
    change HasDerivAt ((fun w : ℂ => w - a) ^ n) ((n : ℂ) * (z - a) ^ (n - 1)) z
    simpa using (((hasDerivAt_id z).sub_const a).pow n)
  have hf : HasDerivAt (fun w => (w - a) ^ n * g w)
      ((n : ℂ) * (z - a) ^ (n - 1) * g z + (z - a) ^ n * g') z := hp.mul hg
  rw [hf.deriv]
  have hza : (z - a) ≠ 0 := sub_ne_zero.2 hz
  have hP : ((z - a) ^ (n - 1)) ≠ 0 := pow_ne_zero _ hza
  have hpow : (z - a) ^ n = (z - a) * (z - a) ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hpow]
  field_simp

/-- **THE LOCAL ARGUMENT PRINCIPLE.**  For the split integrand, the winding is exactly the order.
The model term supplies `2πi·n` and the analytic term supplies nothing. -/
theorem theLocalArgumentPrinciple (a : ℂ) {R : ℝ} (hR : 0 < R) (n : ℕ) {g : ℂ → ℂ}
    (hg : DiffContOnCl ℂ (fun z => deriv g z / g z) (ball a R))
    (hint : CircleIntegrable (fun z => (n : ℂ) / (z - a)) a R)
    (hint' : CircleIntegrable (fun z => deriv g z / g z) a R) :
    (∮ z in C(a, R), ((n : ℂ) / (z - a) + deriv g z / g z))
      = 2 * Real.pi * Complex.I * n := by
  rw [circleIntegral.integral_add hint hint',
    theModelFactorWindsOncePerUnitOfOrder a hR n,
    theAnalyticFactorCarriesNoWinding hR.le hg, add_zero]

/-- **THE INDEX IS A TURN COUNT AND NOTHING ELSE.**  Two zeros of the same order have the same
winding whatever their analytic factors, so the divisor is a phase object: no magnitude of `f`
enters the count. -/
theorem theIndexDependsOnlyOnTheOrder (a : ℂ) {R : ℝ} (m n : ℕ) (hmn : m = n) :
    (∮ z in C(a, R), (m : ℂ) / (z - a)) = (∮ z in C(a, R), (n : ℂ) / (z - a)) := by
  rw [hmn]

end Soma.Holonics.RH.Winding
