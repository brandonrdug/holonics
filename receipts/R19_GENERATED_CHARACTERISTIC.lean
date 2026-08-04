import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open Polynomial Matrix
namespace Soma.Holonics.R19

noncomputable def diagonalCharacteristic (m n : Nat) : Polynomial ℤ :=
  (X ^ Nat.lcm m n - 1) ^ Nat.gcd m n

theorem generated_diagonal_characteristic_degree (m n : Nat)
    (hm : m ≠ 0) (hn : n ≠ 0) :
    (diagonalCharacteristic m n).natDegree = m * n := by
  unfold diagonalCharacteristic
  change ((X ^ Nat.lcm m n - C (1 : ℤ)) ^ Nat.gcd m n).natDegree = m * n
  rw [(monic_X_pow_sub_C (1 : ℤ) (Nat.lcm_ne_zero hm hn)).natDegree_pow]
  rw [natDegree_X_pow_sub_C, Nat.gcd_mul_lcm]

def weightedTwoCycle (u v : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, v; u, 0]

theorem generated_weighted_two_cycle (u v : ℤ) :
    (weightedTwoCycle u v).charpoly = X ^ 2 - C (u * v) := by
  rw [Matrix.charpoly_fin_two]
  simp [weightedTwoCycle, Matrix.trace, Matrix.det_fin_two]
  ring

def sourceReturn : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; 1, 1]
def rechart : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 0, 1]
def rechartInv : Matrix (Fin 2) (Fin 2) ℤ := !![1, -1; 0, 1]

theorem generated_rechart_characteristic :
    (rechart * sourceReturn * rechartInv).charpoly = sourceReturn.charpoly := by
  simp [Matrix.charpoly_fin_two, sourceReturn, rechart, rechartInv, Matrix.trace]

def gaussZeroIndicial (rho : ℚ) := rho * (rho - 1) + 2 * rho
def gaussOneIndicial (rho : ℚ) := rho * (rho + 1 + 1 - 2)
def gaussInfinityIndicial (rho : ℚ) := (rho - 1) * (rho - 1)

theorem generated_gauss_indicial (rho : ℚ) :
    gaussZeroIndicial rho = rho * (rho + 1) ∧
    gaussOneIndicial rho = rho ^ 2 ∧
    gaussInfinityIndicial rho = (rho - 1) ^ 2 := by
  constructor
  · simp [gaussZeroIndicial]
    ring
  constructor
  · simp [gaussOneIndicial]
    ring
  · simp [gaussInfinityIndicial, pow_two]

end Soma.Holonics.R19

#check Soma.Holonics.R19.generated_diagonal_characteristic_degree
