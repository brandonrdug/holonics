import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

/-!
# A family of involutions and three elementary loci

Three familiar loci can be presented as fixed sets of anti-holomorphic involutions of the same
algebraic *shape*, on different carriers and under different hypotheses:

```text
unit circle        |z| = 1           Fix(z ↦ 1/z̄)
radius-√q circle   |α| = √q          Fix(α ↦ q/ᾱ)
critical line      Re s = ½          Fix(s ↦ 1 − s̄)
```

The circle and line fixed-set equivalences are proved explicitly. The complementary-power theorem
`q^s · q^{1−s} = q` is a separate exact identity for the principal complex power at positive real
`q`; it does not by itself prove a conjugacy between the two involutions.

The final theorem proves one degree-two algebraic fact: a real palindromic quadratic with negative
discriminant has its non-real roots on the unit circle. Calling that a finite Lee–Yang-shaped
instance is interpretation. No Ising transfer matrix, ferromagnetic hypothesis, Weil polynomial,
or Riemann zero is constructed here.
-/

namespace Soma.Holonics.Millennium.OneInvolution

open Complex

/-! ## Three fixed-locus equations in one algebraic family -/

/-- **The critical line is the fixed locus of `s ↦ 1 − s̄`.** -/
theorem theCriticalLineIsAFixedLocus (s : ℂ) : s.re = 1 / 2 ↔ s = 1 - (starRingEnd ℂ) s := by
  constructor
  · intro h
    apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im] <;> linarith [h]
  · intro h
    have := congrArg Complex.re h
    simp [Complex.sub_re] at this
    linarith [this]

/-- **The circle of radius `√q` is the fixed locus of `α ↦ q / ᾱ`.**

The nonzero hypothesis is exactly what makes the displayed division legal.  The equivalent
product equation is the elementary identity `α ᾱ = ‖α‖²`; no claim about a Weil polynomial is
made here. -/
theorem theWeilCircleIsAFixedLocus (q : ℝ) (al : ℂ) (hal : al ≠ 0) :
    Complex.normSq al = q ↔ al = (q : ℂ) / (starRingEnd ℂ) al := by
  have hconj : (starRingEnd ℂ) al ≠ 0 := by
    intro hz
    apply hal
    have hz' := congrArg (starRingEnd ℂ) hz
    simpa using hz'
  constructor
  · intro h
    apply (eq_div_iff hconj).2
    rw [Complex.mul_conj]
    exact_mod_cast h
  · intro h
    have hp := (eq_div_iff hconj).1 h
    have hr := congrArg Complex.re hp
    simpa using hr

/-- **Complementary positive powers multiply to the base.**

This is the precise chart statement proved here: for a positive real base, the principal complex
powers at complementary exponents multiply to `q`.  It does not assert that the complex power map
is injective, nor does it identify fixed loci without additional hypotheses. -/
theorem theComplementaryPowersMultiplyToTheBase (q : ℝ) (hq : 0 < q) (s : ℂ) :
    (q : ℂ) ^ s * (q : ℂ) ^ (1 - s) = (q : ℂ) := by
  rw [← Complex.cpow_add _ _ (by exact_mod_cast hq.ne')]
  simp

/-! ## Lee–Yang at degree two: a palindromic real quadratic puts its zeros on the circle -/

/-- **A palindromic real quadratic with a negative discriminant has both zeros on the unit
circle.**

`a z² + b z + a` has root product `a/a = 1`.  With real coefficients and no real root the two roots
are conjugate, so `z z̄ = 1` and `|z| = 1`.  *That is the Lee–Yang mechanism in miniature: the
palindrome is the inversion symmetry `z ↦ 1/z`, and the circle is its fixed locus.* -/
theorem thePalindromicQuadraticPutsItsZerosOnTheCircle
    (a b : ℝ) (ha : a ≠ 0) (hdisc : b ^ 2 < 4 * a ^ 2) (z : ℂ)
    (hz : (a : ℂ) * z ^ 2 + (b : ℂ) * z + (a : ℂ) = 0) :
    Complex.normSq z = 1 := by
  have hre : a * (z.re * z.re - z.im * z.im) + b * z.re + a = 0 := by
    have h := congrArg Complex.re hz
    simpa [pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im] using h
  have him : a * (z.re * z.im + z.im * z.re) + b * z.im = 0 := by
    have h := congrArg Complex.im hz
    simpa [pow_two, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im] using h
  have hy : z.im ≠ 0 := by
    intro h
    rw [h] at hre
    have h2 : a * z.re * z.re + b * z.re = -a := by nlinarith [hre]
    have key : (2 * a * z.re + b) ^ 2 = b ^ 2 - 4 * a ^ 2 := by linear_combination (4 * a) * h2
    nlinarith [sq_nonneg (2 * a * z.re + b), key]
  have hx : 2 * a * z.re + b = 0 := by
    have hfac : z.im * (2 * a * z.re + b) = 0 := by linear_combination him
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd h hy
    · exact h
  have hcirc : a * (1 - (z.re * z.re + z.im * z.im)) = 0 := by
    linear_combination hre - z.re * hx
  rcases mul_eq_zero.mp hcirc with h | h
  · exact absurd h ha
  · rw [Complex.normSq_apply]
    linarith [h]


end Soma.Holonics.Millennium.OneInvolution
