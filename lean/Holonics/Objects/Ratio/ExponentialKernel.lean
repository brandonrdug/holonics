import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The exponential kernel in the ratio's lifted chart

The complex exponential forgets exactly the integer full-turn component of its additive chart.
This generic kernel law belongs with the ratio's winding-bearing logarithm; geometric turn
calibration and its source-specific applications remain in Research.
-/

namespace Holonics.Objects.Ratio.ExponentialKernel

/-- The kernel of the complex exponential is the lattice of integer full turns. -/
theorem exp_eq_one_iff_integer_period (x : ℂ) :
    Complex.exp x = 1 ↔ ∃ n : ℤ, x = n * (2 * Real.pi * Complex.I) :=
  Complex.exp_eq_one_iff

#print axioms exp_eq_one_iff_integer_period

end Holonics.Objects.Ratio.ExponentialKernel
