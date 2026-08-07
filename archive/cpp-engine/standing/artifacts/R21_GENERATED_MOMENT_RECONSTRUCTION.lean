import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Matrix
namespace Soma.Holonics.R21.Moment

def det3 (m : Matrix (Fin 3) (Fin 3) ℤ) : ℤ :=
  m 0 0 * (m 1 1 * m 2 2 - m 1 2 * m 2 1) -
  m 0 1 * (m 1 0 * m 2 2 - m 1 2 * m 2 0) +
  m 0 2 * (m 1 0 * m 2 1 - m 1 1 * m 2 0)

def h0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3,7,21],![7,21,73],![21,73,273]]
def h1 : Matrix (Fin 3) (Fin 3) ℤ := ![![7,21,73],![21,73,273],![73,273,1057]]
def pencil (x : ℤ) : ℤ := det3 (fun i j => x * h0 i j - h1 i j)
def recovered (x : ℤ) : ℤ := (-8) * x ^ 0 + (14) * x ^ 1 + (-7) * x ^ 2 + (1) * x ^ 3

theorem generated_hankel_pencil (x : ℤ) : pencil x = 36 * recovered x := by
  simp [pencil, det3, h0, h1, recovered]
  ring

def cubicDiscriminant (a b c : ℤ) : ℤ :=
  a^2*b^2 - 4*b^3 - 4*a^3*c - 27*c^2 + 18*a*b*c

theorem generated_vandermonde_discriminant : det3 h0 = 36 ∧ cubicDiscriminant (-7) (14) (-8) = 36 := by
  native_decide

theorem generated_recovered_roots : recovered 1 = 0 ∧ recovered 2 = 0 ∧ recovered 4 = 0 := by
  native_decide

def collisionH0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3,6,18],![6,18,66],![18,66,258]]

theorem generated_collision_obstruction : det3 collisionH0 = 0 := by
  native_decide

end Soma.Holonics.R21.Moment

#check Soma.Holonics.R21.Moment.generated_hankel_pencil
