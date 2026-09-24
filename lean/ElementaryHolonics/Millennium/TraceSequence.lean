import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The trace sequence, and where the Weil exponent comes from

`#X(F_{q^p}) = q^p + 1 − Σ αᵢ^p`.  For a genus-one curve there are two conjugate `αᵢ`, and their
power sums satisfy one integer recurrence:

```text
t₀ = 2,  t₁ = a,  t_{p+2} = a·t_{p+1} − q·t_p
```

**Everything about the Weil bound at this genus is a property of that recurrence.**  The root sits
on the circle of radius `√q` exactly when `a² ≤ 4q`; the trace is then twice the real part of a
power of that root; and `|t_p| ≤ 2q^{p/2}` follows at every level from the level-one hypothesis
alone, using only `Re(z)² ≤ |z|²`.  Beyond the bound the characteristic polynomial acquires a real
root past `√q` and the sequence goes hyperbolic — `cos` becomes `cosh`, the circle becomes a
hyperbola.

**And the genus-zero family is the same recurrence at `q = 1`.**  `a = 2` gives the constant `2`;
`a = −2` gives `2(−1)^p`.  Those are the `∓1` corrections that the moduli `2^p ∓ 1` carry, so the
sign-word family and the elliptic trace sequences differ only in `q`, and the Weil exponent is
`q`'s square root: `|α| = 1` against `|α| = √2`.

**At `q = 2` the bound is forced by integrality.**  Hasse allows `|a| ≤ 2√2 ≈ 2.828`, so an integer
trace has `a² ≤ 4 < 8 = 4q` — strictly.  No elliptic curve over `F₂` sits on the boundary.

Every `theorem` here is discharged and none depends on `sorryAx`.  Nothing here is a claim about any
named conjecture; the Weil conjectures are theorems and are not reproved here — what is proved is
the recurrence's own dichotomy.
-/

namespace Soma.Holonics.Millennium.TraceSequence

open Complex

/-- The **trace sequence** of a weight-one Frobenius: `t_p = α^p + ᾱ^p` for `α` a root of
`x² − a x + q`, as an integer recurrence. -/
def trace (a q : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => a
  | (n + 2) => a * trace a q (n + 1) - q * trace a q n

@[simp] theorem trace_zero (a q : ℤ) : trace a q 0 = 2 := rfl
@[simp] theorem trace_one (a q : ℤ) : trace a q 1 = a := rfl
theorem trace_succ_succ (a q : ℤ) (n : ℕ) :
    trace a q (n + 2) = a * trace a q (n + 1) - q * trace a q n := rfl

/-- The Frobenius root when the discriminant is negative. -/
noncomputable def alpha (a q : ℤ) : ℂ :=
  ⟨(a : ℝ) / 2, Real.sqrt (4 * (q : ℝ) - (a : ℝ) ^ 2) / 2⟩

/-- **The root sits on the circle of radius `√q` exactly when the level-one bound holds.** -/
theorem theRootHasSquaredModulusQ (a q : ℤ) (h : (a : ℝ) ^ 2 ≤ 4 * (q : ℝ)) :
    Complex.normSq (alpha a q) = (q : ℝ) := by
  have hnn : (0 : ℝ) ≤ 4 * (q : ℝ) - (a : ℝ) ^ 2 := by linarith
  have hs : Real.sqrt (4 * (q : ℝ) - (a : ℝ) ^ 2) * Real.sqrt (4 * (q : ℝ) - (a : ℝ) ^ 2)
      = 4 * (q : ℝ) - (a : ℝ) ^ 2 := Real.mul_self_sqrt hnn
  simp only [alpha, Complex.normSq_mk]
  nlinarith [hs]

/-- **The root satisfies its own characteristic equation.** -/
theorem theRootIsCharacteristic (a q : ℤ) (h : (a : ℝ) ^ 2 ≤ 4 * (q : ℝ)) :
    alpha a q * alpha a q = (a : ℂ) * alpha a q - (q : ℂ) := by
  have hnn : (0 : ℝ) ≤ 4 * (q : ℝ) - (a : ℝ) ^ 2 := by linarith
  have hs : Real.sqrt (4 * (q : ℝ) - (a : ℝ) ^ 2) * Real.sqrt (4 * (q : ℝ) - (a : ℝ) ^ 2)
      = 4 * (q : ℝ) - (a : ℝ) ^ 2 := Real.mul_self_sqrt hnn
  apply Complex.ext <;>
    simp only [alpha, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.intCast_re, Complex.intCast_im] <;> nlinarith [hs]

/-- **The trace sequence is twice the real part of the Frobenius power.** -/
theorem theTraceIsTwiceTheRealPart (a q : ℤ) (h : (a : ℝ) ^ 2 ≤ 4 * (q : ℝ)) (p : ℕ) :
    ((trace a q p : ℤ) : ℝ) = 2 * ((alpha a q) ^ p).re := by
  induction p using Nat.twoStepInduction with
  | zero => simp [trace, alpha]
  | one => simp [trace, alpha]; ring
  | more n ih1 ih2 =>
    have hpow : (alpha a q) ^ (n + 2)
        = (a : ℂ) * (alpha a q) ^ (n + 1) - (q : ℂ) * (alpha a q) ^ n := by
      calc (alpha a q) ^ (n + 2) = (alpha a q) ^ n * (alpha a q * alpha a q) := by ring
        _ = (alpha a q) ^ n * ((a : ℂ) * alpha a q - (q : ℂ)) := by
              rw [theRootIsCharacteristic a q h]
        _ = (a : ℂ) * (alpha a q) ^ (n + 1) - (q : ℂ) * (alpha a q) ^ n := by ring
    rw [trace_succ_succ, hpow]
    simp only [Complex.sub_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
      zero_mul, sub_zero]
    push_cast
    rw [ih1, ih2]
    ring

/-- **The Weil bound at every level follows from the bound at level one.**

`t_p² ≤ 4 q^p`, i.e. `|t_p| ≤ 2 q^{p/2}` — because the root sits on the circle of radius `√q`, so
only `Re(z)² ≤ |z|²` is used.  *The level-one hypothesis `a² ≤ 4q` is the whole input; every higher
level is free.* -/
theorem theLevelOneBoundGivesEveryLevel (a q : ℤ) (h : (a : ℝ) ^ 2 ≤ 4 * (q : ℝ)) (p : ℕ) :
    ((trace a q p : ℤ) : ℝ) ^ 2 ≤ 4 * (q : ℝ) ^ p := by
  rw [theTraceIsTwiceTheRealPart a q h p]
  have hns : Complex.normSq ((alpha a q) ^ p) = (q : ℝ) ^ p := by
    rw [map_pow, theRootHasSquaredModulusQ a q h]
  have hre : ((alpha a q) ^ p).re ^ 2 ≤ Complex.normSq ((alpha a q) ^ p) := by
    rw [Complex.normSq_apply]; nlinarith [sq_nonneg ((alpha a q) ^ p).im]
  nlinarith [hre, hns]

/-! ## Where the genus-zero family sits: it is the same recurrence at `q = 1` -/

/-- **The two genus-zero moduli are the trace sequence at `q = 1`.**
`a = 2` gives the constant `2` (root `1`); `a = −2` gives `2(−1)^p` (root `−1`).  So `2^p ∓ 1` and
the elliptic trace sequences are **one recurrence at different `q`**, and the Weil exponent is
`q`'s square root: `|α| = 1` at `q = 1`, `|α| = √2` at `q = 2`. -/
theorem theGenusZeroFamilyIsTheRecurrenceAtOne :
    (trace 2 1 0 = 2 ∧ trace 2 1 1 = 2 ∧ trace 2 1 2 = 2 ∧ trace 2 1 3 = 2)
      ∧ (trace (-2) 1 0 = 2 ∧ trace (-2) 1 1 = -2 ∧ trace (-2) 1 2 = 2 ∧ trace (-2) 1 3 = -2)
      ∧ (trace 0 1 0 = 2 ∧ trace 0 1 1 = 0 ∧ trace 0 1 2 = -2 ∧ trace 0 1 3 = 0) := by
  refine ⟨⟨rfl, rfl, by decide, by decide⟩, ⟨rfl, rfl, by decide, by decide⟩,
    ⟨rfl, rfl, by decide, by decide⟩⟩

/-! ## Genus one over `F₂`: the bound is forced by integrality -/

/-- **At `q = 2` the Weil bound holds for every integer trace the Hasse interval admits.**
`|a| ≤ 2√2 ≈ 2.828` forces `a ∈ {−2,−1,0,1,2}`, and then `a² ≤ 4 < 8 = 4q`.  **The inequality is
strict for every admissible integer**, so no elliptic curve over `F₂` sits on the boundary. -/
theorem theHasseIntervalAtTwoIsStrict (a : ℤ) (h : a ^ 2 ≤ 8) : a ^ 2 ≤ 4 := by
  have hb1 : -2 ≤ a := by nlinarith
  have hb2 : a ≤ 2 := by nlinarith
  interval_cases a <;> decide

/-- The five admissible integer traces over `F₂` and their sequences to depth four. -/
theorem theFiveTracesOverTheBinaryField :
    (trace 0 2 2 = -4 ∧ trace 0 2 3 = 0 ∧ trace 0 2 4 = 8)
      ∧ (trace 1 2 2 = -3 ∧ trace 1 2 3 = -5 ∧ trace 1 2 4 = 1)
      ∧ (trace 2 2 2 = 0 ∧ trace 2 2 3 = -4 ∧ trace 2 2 4 = -8)
      ∧ (trace (-1) 2 2 = -3 ∧ trace (-1) 2 3 = 5 ∧ trace (-1) 2 4 = 1)
      ∧ (trace (-2) 2 2 = 0 ∧ trace (-2) 2 3 = 4 ∧ trace (-2) 2 4 = -8) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩⟩

/-! ## The dichotomy: circular or hyperbolic -/

/-- **Beyond the bound the characteristic polynomial has a real root outside the circle.**

This is only a quadratic-root statement; no assertion about a Weil family or a higher-level trace
bound is made here. -/
theorem theOvershootProducesARealRootBeyondTheCircle (a q : ℝ) (h : 4 * q < a ^ 2)
    (ha : 0 < a) :
    ∃ x : ℝ, x ^ 2 - a * x + q = 0 ∧ q < x ^ 2 := by
  have hd : 0 ≤ a ^ 2 - 4 * q := by linarith
  refine ⟨(a + Real.sqrt (a ^ 2 - 4 * q)) / 2, ?_, ?_⟩
  · have hs : Real.sqrt (a ^ 2 - 4 * q) * Real.sqrt (a ^ 2 - 4 * q) = a ^ 2 - 4 * q :=
      Real.mul_self_sqrt hd
    nlinarith [hs]
  · have hpos : 0 < Real.sqrt (a ^ 2 - 4 * q) := by
      apply Real.sqrt_pos.mpr; linarith
    have hs : Real.sqrt (a ^ 2 - 4 * q) * Real.sqrt (a ^ 2 - 4 * q) = a ^ 2 - 4 * q :=
      Real.mul_self_sqrt hd
    nlinarith [hs, hpos]


end Soma.Holonics.Millennium.TraceSequence
