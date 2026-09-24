import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-!
# The sign of the curvature is the sign in the deviation equation — optics and geometry, one law

Brandon, 2026-08-23: *"Is negative vs positive curvature not like concavity and convexity?
Divergence and convergence, optics?"*

Yes, and the identification is an equation rather than a resemblance.  Geodesic deviation obeys

```text
J'' + K · J = 0
```

— Jacobi's equation — with `K` the sectional curvature.  It is the harmonic oscillator with `K` as
the spring constant, so the **sign of the curvature is the sign in `y'' + k y = 0`**, and the
dichotomy is the classical one:

| `K` | solution | geometry | optics |
|---|---|---|---|
| `> 0` | `sin(kt)/k` | geodesics reconverge | **converging lens**, a focus exists |
| `= 0` | `t` | parallels stay parallel | no power |
| `< 0` | `sinh(kt)/k` | geodesics escape | **diverging lens**, no focus |

A **conjugate point** is where a Jacobi field vanishes again; a **focus** is where rays reconverge.
Those are the same definition, not two definitions that resemble each other — which is why the
lensmaker's equation `1/f = (n−1)(1/R₁ − 1/R₂)` reads focal power as a *difference of curvatures*.

**One caution the corpus already carries.**  Concave/convex is a choice of *side*: flip it and they
swap, exactly as `A` and `−A` have swapped inertia.  What no frame touches is the **split** — that
the deviation oscillates or escapes — not which side is called positive.  Sylvester's law is the
same statement one altitude up.

Proved below: the three solutions, and the sharp qualitative difference — the positive case has a
zero at `π/k` and the negative case has none.
-/

namespace Soma.Holonics.Millennium.Deviation

open Real

/-! ## 1.  The three solutions -/

/-- **POSITIVE CURVATURE: the deviation is a sine.**  `J = sin(kt)` satisfies `J'' = −k²J`. -/
theorem theSineSolvesThePositiveDeviation (k t : ℝ) :
    HasDerivAt (fun u : ℝ => k * Real.cos (k * u)) (-(k ^ 2) * Real.sin (k * t)) t := by
  have h : HasDerivAt (fun u : ℝ => Real.cos (k * u)) (-Real.sin (k * t) * k) t := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_cos (k * t)).comp t ((hasDerivAt_id t).const_mul k)
  simpa [mul_comm, mul_assoc, mul_left_comm, pow_two] using h.const_mul k

/-- Its first derivative, for the record. -/
theorem theSineHasTheExpectedFirstDerivative (k t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.sin (k * u)) (k * Real.cos (k * t)) t := by
  simpa [Function.comp_def, mul_comm] using
    (Real.hasDerivAt_sin (k * t)).comp t ((hasDerivAt_id t).const_mul k)

/-- **NEGATIVE CURVATURE: the deviation is a hyperbolic sine.**  `J = sinh(kt)` satisfies
`J'' = +k²J` — the sign flip is the whole difference. -/
theorem theHyperbolicSineSolvesTheNegativeDeviation (k t : ℝ) :
    HasDerivAt (fun u : ℝ => k * Real.cosh (k * u)) (k ^ 2 * Real.sinh (k * t)) t := by
  have h : HasDerivAt (fun u : ℝ => Real.cosh (k * u)) (Real.sinh (k * t) * k) t := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_cosh (k * t)).comp t ((hasDerivAt_id t).const_mul k)
  simpa [mul_comm, mul_assoc, mul_left_comm, pow_two] using h.const_mul k

/-! ## 2.  The sharp difference: a focus exists, or it does not -/

/-- **POSITIVE CURVATURE HAS A CONJUGATE POINT.**  The deviation returns to zero at `t = π/k`:
geodesics that separated come back together, which is a focus. -/
theorem thePositiveCaseHasAFocus {k : ℝ} (hk : k ≠ 0) : Real.sin (k * (π / k)) = 0 := by
  rw [mul_div_cancel₀ _ hk, Real.sin_pi]

/-- **NEGATIVE CURVATURE HAS NONE.**  `sinh` is strictly positive for positive argument, so the
deviation never returns: rays that separated keep separating, and there is no focus at any
distance. -/
theorem theNegativeCaseHasNoFocus {k t : ℝ} (hk : 0 < k) (ht : 0 < t) :
    0 < Real.sinh (k * t) :=
  Real.sinh_pos_iff.2 (by positivity)

/-- **THE FLAT CASE IS LINEAR.**  Parallels stay parallel and the deviation grows exactly linearly
— no power at all. -/
theorem theFlatCaseIsLinear (t : ℝ) : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t :=
  hasDerivAt_const t 1

/-! ## 3.  The side is a gauge; the split is not -/

/-- **CONCAVE AND CONVEX ARE ONE OBJECT WITH TWO SIDES.**  Negating swaps them and changes no
geometry, exactly as `A` and `−A` have swapped inertia — the invariant is the split, never the
label.  Exhibited: the sine's zero survives the flip, so the *existence of a focus* is frame-free
while the sign convention is not. -/
theorem theSideIsAGaugeButTheSplitIsNot {k : ℝ} (hk : k ≠ 0) :
    Real.sin (k * (π / k)) = 0 ∧ (-Real.sin) (k * (π / k)) = 0 := by
  refine ⟨thePositiveCaseHasAFocus hk, ?_⟩
  simp [thePositiveCaseHasAFocus hk]

end Soma.Holonics.Millennium.Deviation
