import HolonicsResearch.Geometry.CyclicGrover.CyclicShift

/-! Refs #62. The Grover operator is derived from dart incidence and reversal.
At every cycle vertex its two outgoing contact ports have coin 2/2=1.
The simple-graph neighbor count for N>=3 is a separate certificate below.
Columns carry the input dart; rows carry the output dart. -/
namespace Holonics.Epime.GroverCycle
open Matrix
open Holonics.Epime.CyclicShift
variable {R : Type*} [CommRing R]

abbrev Vertex (n : ℕ) := Fin (n+2)
abbrev Dart (n : ℕ) := Vertex n × Bool

def target (n : ℕ) (d : Dart n) : Vertex n :=
  if d.2 then finRotate (n+2) d.1 else (finRotate (n+2)).symm d.1

def reverse (n : ℕ) (d : Dart n) : Dart n := (target n d, !d.2)

/-- Degree-two scattering: arrival incidence, then coin minus reversal. -/
def grover (n : ℕ) : Matrix (Dart n) (Dart n) R :=
  fun e d => if e.1 = target n d then 1 - (if e = reverse n d then 1 else 0) else 0

def orientationBlock (n : ℕ) (b : Bool) : Matrix (Vertex n) (Vertex n) R :=
  if b then shift n else (shift n).transpose

theorem grover_decomposition (n : ℕ) :
    (grover n : Matrix (Dart n) (Dart n) R) = Matrix.blockDiagonal (orientationBlock n) := by
  funext ⟨i,b⟩ ⟨j,c⟩
  cases b with
  | false =>
    cases c with
    | false =>
      change (if i=(finRotate (n+2)).symm j then
        1-(if (i,false)=((finRotate (n+2)).symm j,true) then 1 else 0) else 0) =
        (if j=finRotate (n+2) i then 1 else 0)
      simp only [Prod.mk.injEq, Bool.false_eq_true, and_false, if_false, sub_zero]
      have he : i=(finRotate (n+2)).symm j ↔ j=finRotate (n+2) i := by
        rw [Equiv.eq_symm_apply]; exact eq_comm
      by_cases h : i=(finRotate (n+2)).symm j
      · rw [if_pos h, if_pos (he.mp h)]
      · rw [if_neg h, if_neg (he.not.mp h)]
    | true =>
      change (if i=finRotate (n+2) j then
        1-(if (i,false)=(finRotate (n+2) j,false) then 1 else 0) else 0) = 0
      by_cases h : i=finRotate (n+2) j
      · have hp : (i,false)=(finRotate (n+2) j,false) := by rw [h]
        rw [if_pos h, if_pos hp, sub_self]
      · rw [if_neg h]
  | true =>
    cases c with
    | false =>
      change (if i=(finRotate (n+2)).symm j then
        1-(if (i,true)=((finRotate (n+2)).symm j,true) then 1 else 0) else 0) = 0
      by_cases h : i=(finRotate (n+2)).symm j
      · have hp : (i,true)=((finRotate (n+2)).symm j,true) := by rw [h]
        rw [if_pos h, if_pos hp, sub_self]
      · rw [if_neg h]
    | true =>
      change (if i=finRotate (n+2) j then
        1-(if (i,true)=(finRotate (n+2) j,false) then 1 else 0) else 0) =
        (if i=finRotate (n+2) j then 1 else 0)
      simp only [Prod.mk.injEq, Bool.true_eq_false, and_false, if_false, sub_zero]

theorem backward_determinant (n : ℕ) (a : R) :
    (Matrix.scalar (Vertex n) a - (shift n).transpose).det = a^(n+2)-1 := by
  have he : Matrix.scalar (Vertex n) a - (shift n).transpose =
      (Matrix.scalar (Vertex n) a - shift n).transpose := by
    funext i j
    simp [Matrix.transpose, Matrix.scalar, Matrix.diagonal, eq_comm]
  rw [he, Matrix.det_transpose, shift_determinant]

theorem scalar_sub_decomposition (n : ℕ) (a : R) :
    Matrix.scalar (Dart n) a - grover n =
      Matrix.blockDiagonal (fun b => Matrix.scalar (Vertex n) a - orientationBlock n b) := by
  rw [grover_decomposition]
  funext ⟨i,b⟩ ⟨j,c⟩
  by_cases h : b=c
  · subst c
    simp [Matrix.scalar, Matrix.diagonal, Matrix.blockDiagonal]
  · simp [Matrix.scalar, Matrix.diagonal, Matrix.blockDiagonal, h]

theorem grover_determinant (n : ℕ) (a : R) :
    (Matrix.scalar (Dart n) a - grover n).det = (a^(n+2)-1)^2 := by
  rw [scalar_sub_decomposition, Matrix.det_blockDiagonal]
  have hd : ∀ b : Bool, (Matrix.scalar (Vertex n) a - orientationBlock n b).det = a^(n+2)-1 := by
    intro b
    cases b with
    | false => exact backward_determinant n a
    | true => exact shift_determinant n a
  simp only [hd]
  simp

end Holonics.Epime.GroverCycle

#print axioms Holonics.Epime.GroverCycle.grover_determinant
#print axioms Holonics.Epime.GroverCycle.grover_decomposition
