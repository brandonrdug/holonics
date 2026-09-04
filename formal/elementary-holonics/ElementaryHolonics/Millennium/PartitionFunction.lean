import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# The finite transfer trace recurrence

For a finite two-state transfer matrix, the trace of powers obeys a two-term recurrence.  This file
proves the recurrence directly from the size-two Cayley–Hamilton identity:

```text
Z_0 = 2,  Z_1 = tr T,  Z_{N+2} = (tr T)·Z_{N+1} − (det T)·Z_N
```

by Cayley–Hamilton, computed rather than cited.  The result is a finite matrix identity.  It does
not identify this recurrence with a Frobenius trace, a Weil bound, a thermodynamic limit, a phase
transition, or a spectral-gap statement.
-/

namespace Soma.Holonics.Millennium.PartitionFunction

open Matrix

variable {R : Type*} [CommRing R]

/-- **Cayley–Hamilton at size two, by computation.** -/
theorem theSquareIsTheTraceMinusTheDeterminant (T : Matrix (Fin 2) (Fin 2) R) :
    T * T = (Matrix.trace T) • T - (Matrix.det T) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.trace, Matrix.det_fin_two, Fin.sum_univ_two,
      ] <;> ring

/-- **So the powers obey the trace recurrence.** -/
theorem thePowerObeysTheRecurrence (T : Matrix (Fin 2) (Fin 2) R) (n : ℕ) :
    T ^ (n + 2) = (Matrix.trace T) • T ^ (n + 1) - (Matrix.det T) • T ^ n := by
  have h := theSquareIsTheTraceMinusTheDeterminant T
  calc T ^ (n + 2) = T ^ n * (T * T) := by rw [pow_add, pow_two]
    _ = T ^ n * ((Matrix.trace T) • T - (Matrix.det T) • (1 : Matrix (Fin 2) (Fin 2) R)) := by
          rw [h]
    _ = (Matrix.trace T) • T ^ (n + 1) - (Matrix.det T) • T ^ n := by
          rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]
          congr 1

/-- **The trace of powers of a finite two-by-two matrix obeys its trace recurrence.**

`Z_N = Tr(Tᴺ)` satisfies `Z_{N+2} = (tr T)·Z_{N+1} − (det T)·Z_N` with `Z_0 = 2`, `Z_1 = tr T`.
A separately declared transfer matrix or Frobenius operator may instantiate the identity; neither
interpretation is part of this theorem. -/
theorem theFiniteTransferTraceObeysItsRecurrence (T : Matrix (Fin 2) (Fin 2) R) (n : ℕ) :
    Matrix.trace (T ^ (n + 2))
      = (Matrix.trace T) * Matrix.trace (T ^ (n + 1)) - (Matrix.det T) * Matrix.trace (T ^ n) := by
  rw [thePowerObeysTheRecurrence T n, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul]
  simp [smul_eq_mul]

/-- **And the base cases match.** -/
theorem theBaseCasesMatch (T : Matrix (Fin 2) (Fin 2) R) :
    Matrix.trace (T ^ 0) = 2 ∧ Matrix.trace (T ^ 1) = Matrix.trace T := by
  refine ⟨?_, by rw [pow_one]⟩
  simp [Matrix.trace]

/-- **A real quadratic with zero discriminant has only the repeated root `a/2`.** -/
theorem theZeroDiscriminantQuadraticHasTheRepeatedRoot (a q : ℝ) (h : a ^ 2 = 4 * q) (x : ℝ)
    (hx : x ^ 2 - a * x + q = 0) : x = a / 2 := by
  nlinarith [sq_nonneg (x - a / 2)]


end Soma.Holonics.Millennium.PartitionFunction
