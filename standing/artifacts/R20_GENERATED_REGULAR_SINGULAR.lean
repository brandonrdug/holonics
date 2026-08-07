import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

open Matrix
namespace Soma.Holonics.R20

def residueZero : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, -1]
def residueOne : Matrix (Fin 2) (Fin 2) ℤ := !![0, 0; -1, -1]
def residueInfinity : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 2]

theorem generated_residue_algebra :
    residueInfinity = -(residueZero + residueOne) ∧
    (residueInfinity - 1) * (residueInfinity - 1) = 0 := by
  native_decide

def zeroCoefficient (n : ℕ) : ℚ := 1 / (n + 1)

theorem generated_zero_frobenius_step (n : ℕ) :
    ((n : ℚ) + 1) * ((n : ℚ) + 2) * zeroCoefficient (n + 1) =
      ((n : ℚ) + 1) ^ 2 * zeroCoefficient n := by
  simp [zeroCoefficient]
  field_simp
  ring

def oneCoefficient (_n : ℕ) : ℚ := 1

theorem generated_one_frobenius_step (n : ℕ) :
    ((n : ℚ) + 1) ^ 2 * (oneCoefficient (n + 1) - oneCoefficient n) = 0 := by
  simp [oneCoefficient]

def oneResonantVector : Fin 2 → ℤ := ![0, 1]
def oneResonantSource : Fin 2 → ℤ := ![1, -1]
def oneCokernel : Fin 2 → ℤ := ![1, 0]

theorem generated_resonance_obstruction :
    residueZero *ᵥ oneResonantVector = oneResonantSource ∧
    dotProduct oneCokernel oneResonantSource = 1 := by
  native_decide

def monodromyZero : Matrix (Fin 2) (Fin 2) ℤ := 1
def monodromyOne (omega : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, -omega; 0, 1]
def monodromyInfinity (omega : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, omega; 0, 1]
def chamberSwap : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]
def zeroBasisLoop (omega : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; -omega, 1]

theorem generated_connection_and_loop (omega : ℤ) :
    monodromyZero * monodromyOne omega * monodromyInfinity omega = 1 ∧
    chamberSwap * monodromyOne omega * chamberSwap = zeroBasisLoop omega := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [monodromyZero, monodromyOne, monodromyInfinity, chamberSwap, zeroBasisLoop]

end Soma.Holonics.R20

#check Soma.Holonics.R20.generated_connection_and_loop
