import HolonicsResearch.Geometry.CyclicGrover.GroverGraphChart

namespace Holonics.Epime.GroverCycle
open Matrix
variable {R : Type*} [CommRing R]

def predecessor (n : ℕ) (d : Dart n) : Dart n :=
  (if d.2 then (finRotate (n+2)).symm d.1 else finRotate (n+2) d.1, d.2)

def motion (n : ℕ) : Equiv.Perm (Dart n) where
  toFun d := (target n d, d.2)
  invFun := predecessor n
  left_inv := by rintro ⟨i,b⟩; cases b <;> simp [target, predecessor]
  right_inv := by rintro ⟨i,b⟩; cases b <;> simp [target, predecessor]

theorem row_is_predecessor (n : ℕ) (e d : Dart n) :
    (grover n : Matrix (Dart n) (Dart n) R) e d =
      if d = predecessor n e then 1 else 0 := by
  rw [grover_decomposition]
  rcases e with ⟨i,b⟩
  rcases d with ⟨j,c⟩
  cases b with
  | false =>
    cases c with
    | false =>
      change (if j=finRotate (n+2) i then 1 else 0) =
        if (j,false)=(finRotate (n+2) i,false) then 1 else 0
      simp only [Prod.mk.injEq, and_true]
    | true =>
      change (0:R) = if (j,true)=(finRotate (n+2) i,false) then 1 else 0
      simp only [Prod.mk.injEq, Bool.true_eq_false, and_false, if_false]
  | true =>
    cases c with
    | false =>
      change (0:R) = if (j,false)=((finRotate (n+2)).symm i,true) then 1 else 0
      simp only [Prod.mk.injEq, Bool.false_eq_true, and_false, if_false]
    | true =>
      change (if i=finRotate (n+2) j then 1 else 0) =
        if (j,true)=((finRotate (n+2)).symm i,true) then 1 else 0
      simp only [Prod.mk.injEq, and_true]
      have he : i=finRotate (n+2) j ↔ j=(finRotate (n+2)).symm i := by
        rw [Equiv.eq_symm_apply]; exact eq_comm
      simp only [he]

theorem actual_mulVec (n : ℕ) (f : Dart n → R) :
    (grover n : Matrix (Dart n) (Dart n) R).mulVec f =
      fun e => f ((motion n).symm e) := by
  funext e
  change (∑ d, (grover n : Matrix (Dart n) (Dart n) R) e d * f d) = f (predecessor n e)
  simp only [row_is_predecessor, ite_mul, one_mul, zero_mul]
  simp

end Holonics.Epime.GroverCycle

#print axioms Holonics.Epime.GroverCycle.actual_mulVec
