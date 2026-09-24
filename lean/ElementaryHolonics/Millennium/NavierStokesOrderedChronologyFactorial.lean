import ElementaryHolonics.Millennium.NavierStokesSmoothMildSourceChronology
import Mathlib.Analysis.ODE.PicardLindelof

/-!
# Ordered chronology and factorial suppression

**[proved-derived; formal-checked]**  The scalar Volterra return below isolates the ordered-time
simplex mechanism used in the Picard--Lindelöf argument.  Its successor integrates only over the
unoriented interval between the source clock and the current clock.  For a forward causal history
`s ≤ t`, this is exactly the ordered interval `(s,t]`.

Mathlib's exact `integral_pow_abs_sub_uIoc` identity supplies the simplex volume.  Consequently the
`n`-fold return is exactly `(K * |t - s|)^n / n!`.  A generic comparison theorem then pays any
continuous scalar return population satisfying the same Volterra Lipschitz recurrence.

The final receiver records that factorial suppression survives an arbitrary fixed exponential
weight per generation.  This is only a combinatorial and integral statement: no Navier--Stokes
interaction population is asserted to satisfy the recurrence, and no convergence, continuation,
or regularity consequence is claimed here.
-/

noncomputable section

open Function MeasureTheory Metric Set
open scoped BigOperators Nat NNReal Topology

namespace Soma.Holonics.Millennium.NavierStokesOrderedChronologyFactorial

/-! ## The exact ordered Volterra population -/

/-- The scalar population produced by `n` ordered Volterra returns with Lipschitz rate `K` from
the source clock `s`.  The zero-depth population is one. -/
def orderedVolterraReturn (K s : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n + 1, t => K * ∫ sourceTime in uIoc s t,
      orderedVolterraReturn K s n sourceTime

/-- The exact factorial weight carried by an ordered chronology of depth `n`. -/
def orderedChronologyFactorialWeight (K s t : ℝ) (n : ℕ) : ℝ :=
  (K * |t - s|) ^ n / n !

/-- **Exact ordered-time simplex law.**  Repeating the Volterra return `n` times produces the
factorial denominator, with no estimate or discarded chronology. -/
theorem orderedVolterraReturn_eq_factorialWeight
    (K s t : ℝ) (n : ℕ) :
    orderedVolterraReturn K s n t =
      orderedChronologyFactorialWeight K s t n := by
  induction n generalizing t with
  | zero => simp [orderedVolterraReturn, orderedChronologyFactorialWeight]
  | succ n ih =>
    rw [orderedVolterraReturn]
    simp_rw [ih, orderedChronologyFactorialWeight, mul_pow]
    rw [MeasureTheory.integral_div]
    rw [MeasureTheory.integral_const_mul]
    rw [integral_pow_abs_sub_uIoc]
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    field_simp
    ring

theorem continuous_orderedVolterraReturn (K s : ℝ) (n : ℕ) :
    Continuous (orderedVolterraReturn K s n) := by
  rw [show orderedVolterraReturn K s n =
      (fun t : ℝ => orderedChronologyFactorialWeight K s t n) from
    funext fun t => orderedVolterraReturn_eq_factorialWeight K s t n]
  unfold orderedChronologyFactorialWeight
  fun_prop

/-! ## Generic Lipschitz-return comparison -/

/-- A continuous scalar family satisfying the Volterra Lipschitz recurrence is paid at every
depth and target clock by the exact ordered population.  `C` is the zero-depth payment. -/
theorem lipschitzReturns_le_orderedVolterraReturn
    (returns : ℕ → ℝ → ℝ) (K C s : ℝ) (hK : 0 ≤ K)
    (hcontinuous : ∀ n, Continuous (returns n))
    (hzero : ∀ t, returns 0 t ≤ C)
    (hsucc : ∀ n t, returns (n + 1) t ≤
      K * ∫ sourceTime in uIoc s t, returns n sourceTime) :
    ∀ n t, returns n t ≤ C * orderedVolterraReturn K s n t := by
  intro n
  induction n with
  | zero =>
    intro t
    simpa [orderedVolterraReturn] using hzero t
  | succ n ih =>
    intro t
    have hmono :
        (∫ sourceTime in uIoc s t, returns n sourceTime) ≤
          ∫ sourceTime in uIoc s t,
            C * orderedVolterraReturn K s n sourceTime := by
      apply MeasureTheory.integral_mono
      · exact (hcontinuous n).integrableOn_uIoc
      · exact (continuous_const.mul
          (continuous_orderedVolterraReturn K s n)).integrableOn_uIoc
      · exact fun sourceTime => ih sourceTime
    calc
      returns (n + 1) t ≤
          K * ∫ sourceTime in uIoc s t, returns n sourceTime := hsucc n t
      _ ≤ K * ∫ sourceTime in uIoc s t,
          C * orderedVolterraReturn K s n sourceTime :=
        mul_le_mul_of_nonneg_left hmono hK
      _ = C * orderedVolterraReturn K s (n + 1) t := by
        rw [orderedVolterraReturn, MeasureTheory.integral_const_mul]
        ring

/-- Direct factorial form of `lipschitzReturns_le_orderedVolterraReturn`. -/
theorem lipschitzReturns_le_orderedChronologyFactorial
    (returns : ℕ → ℝ → ℝ) (K C s : ℝ) (hK : 0 ≤ K)
    (hcontinuous : ∀ n, Continuous (returns n))
    (hzero : ∀ t, returns 0 t ≤ C)
    (hsucc : ∀ n t, returns (n + 1) t ≤
      K * ∫ sourceTime in uIoc s t, returns n sourceTime)
    (n : ℕ) (t : ℝ) :
    returns n t ≤ C * orderedChronologyFactorialWeight K s t n := by
  calc
    returns n t ≤ C * orderedVolterraReturn K s n t :=
      lipschitzReturns_le_orderedVolterraReturn
        returns K C s hK hcontinuous hzero hsucc n t
    _ = C * orderedChronologyFactorialWeight K s t n := by
      rw [orderedVolterraReturn_eq_factorialWeight]

/-! ## Exponentially weighted scale tails -/

/-- Factorial chronology dominates every fixed exponential generation weight. -/
theorem summable_exponentiallyWeighted_orderedChronologyFactorial
    (scaleGrowth K s t : ℝ) :
    Summable (fun n : ℕ => scaleGrowth ^ n *
      orderedChronologyFactorialWeight K s t n) := by
  have heq :
      (fun n : ℕ => scaleGrowth ^ n *
        orderedChronologyFactorialWeight K s t n) =
      (fun n : ℕ =>
        (scaleGrowth * (K * |t - s|)) ^ n / n !) := by
    funext n
    rw [mul_pow]
    simp only [orderedChronologyFactorialWeight, mul_pow]
    ring
  rw [heq]
  exact Real.summable_pow_div_factorial _

/-- An NS-facing receiver for a generation-indexed interaction mass.  Once a concrete nonlinear
ancestry construction supplies the displayed factorial bound, every fixed exponential scale cost
is summable.  The premise is deliberately visible and is not asserted for the current PDE source. -/
theorem navierStokesOrderedGenerationScaleTail_summable
    (generationMass : ℕ → ℝ) (scaleGrowth K C s t : ℝ)
    (hscaleGrowth : 0 ≤ scaleGrowth)
    (hmass_nonneg : ∀ n, 0 ≤ generationMass n)
    (hmass : ∀ n, generationMass n ≤
      C * orderedChronologyFactorialWeight K s t n) :
    Summable (fun n : ℕ => scaleGrowth ^ n * generationMass n) := by
  apply Summable.of_nonneg_of_le
  · intro n
    exact mul_nonneg (pow_nonneg hscaleGrowth n) (hmass_nonneg n)
  · intro n
    calc
      scaleGrowth ^ n * generationMass n ≤
          scaleGrowth ^ n *
            (C * orderedChronologyFactorialWeight K s t n) :=
        mul_le_mul_of_nonneg_left (hmass n) (pow_nonneg hscaleGrowth n)
      _ = C * (scaleGrowth ^ n *
          orderedChronologyFactorialWeight K s t n) := by ring
  · exact Summable.mul_left C
      (summable_exponentiallyWeighted_orderedChronologyFactorial
        scaleGrowth K s t)

/-- Fully composed abstract receiver: a nonnegative continuous return population satisfying the
ordered Volterra recurrence has a summable exponentially weighted target-clock tail. -/
theorem navierStokesOrderedVolterraScaleTail_summable
    (returns : ℕ → ℝ → ℝ) (scaleGrowth K C s t : ℝ)
    (hscaleGrowth : 0 ≤ scaleGrowth) (hK : 0 ≤ K)
    (hcontinuous : ∀ n, Continuous (returns n))
    (hreturns_nonneg : ∀ n targetTime, 0 ≤ returns n targetTime)
    (hzero : ∀ targetTime, returns 0 targetTime ≤ C)
    (hsucc : ∀ n targetTime, returns (n + 1) targetTime ≤
      K * ∫ sourceTime in uIoc s targetTime, returns n sourceTime) :
    Summable (fun n : ℕ => scaleGrowth ^ n * returns n t) :=
  navierStokesOrderedGenerationScaleTail_summable
    (fun n => returns n t) scaleGrowth K C s t hscaleGrowth
    (fun n => hreturns_nonneg n t)
    (fun n => lipschitzReturns_le_orderedChronologyFactorial
      returns K C s hK hcontinuous hzero hsucc n t)

section Audit

#print axioms orderedVolterraReturn_eq_factorialWeight
#print axioms lipschitzReturns_le_orderedVolterraReturn
#print axioms lipschitzReturns_le_orderedChronologyFactorial
#print axioms summable_exponentiallyWeighted_orderedChronologyFactorial
#print axioms navierStokesOrderedGenerationScaleTail_summable
#print axioms navierStokesOrderedVolterraScaleTail_summable

end Audit

end Soma.Holonics.Millennium.NavierStokesOrderedChronologyFactorial
