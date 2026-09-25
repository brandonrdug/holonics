import HolonicsResearch.Zeta.ThetaMellin
import Mathlib.Tactic

/-!
# The theta source has a positive Hankel face

The positive lattice coefficients of LandenLattice.T3 give a genuine Gram
factorization for each finite theta section. This is a source-derived
positive face on the half-line, not an identification with the complete
Weil receiver. Its Mellin chart is identified with completed zeta in
Zeta.ThetaMellin only where the Mellin integral converges absolutely.
-/

noncomputable section

namespace Holonics.Zeta.ThetaHankelPositive

open Real

/-- The positive n + 1 theta mode in the actual T3 - 1 series. -/
def thetaMode (n : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t)

/-- A finite, source-derived theta section, without floating approximation. -/
def finiteThetaSection (N : ℕ) (t : ℝ) : ℝ :=
  2 * ∑ n ∈ Finset.range N, thetaMode n t

theorem thetaMode_add (n : ℕ) (x y : ℝ) :
    thetaMode n (x + y) = thetaMode n x * thetaMode n y := by
  unfold thetaMode
  rw [show -Real.pi * ((n : ℝ) + 1) ^ 2 * (x + y) =
      (-Real.pi * ((n : ℝ) + 1) ^ 2 * x) +
      (-Real.pi * ((n : ℝ) + 1) ^ 2 * y) by ring, Real.exp_add]

/-- Every finite theta Hankel quadratic form is a sum of squares. The
coordinates are the actual exponential lattice modes, not a Gram form
defined by the Weil zero receiver. -/
theorem finiteThetaSection_gram
    {I : Type*} [DecidableEq I] (S : Finset I) (N : ℕ)
    (t c : I → ℝ) :
    (∑ i ∈ S, ∑ j ∈ S,
      c i * c j * finiteThetaSection N (t i + t j)) =
    2 * ∑ n ∈ Finset.range N,
      (∑ i ∈ S, c i * thetaMode n (t i)) ^ 2 := by
  classical
  simp only [finiteThetaSection, thetaMode_add]
  simp_rw [Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext x
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  rw [pow_two, Finset.sum_mul_sum]
  conv_rhs => rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  conv_rhs => rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  ring

theorem finiteThetaSection_nonneg
    {I : Type*} [DecidableEq I] (S : Finset I) (N : ℕ)
    (t c : I → ℝ) :
    0 ≤ ∑ i ∈ S, ∑ j ∈ S,
      c i * c j * finiteThetaSection N (t i + t j) := by
  rw [finiteThetaSection_gram]
  positivity

#print axioms finiteThetaSection_gram
#print axioms finiteThetaSection_nonneg

end Holonics.Zeta.ThetaHankelPositive
