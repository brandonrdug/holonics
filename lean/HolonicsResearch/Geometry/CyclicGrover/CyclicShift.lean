import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Lean.Elab.Tactic.Omega

/-! Refs #62. Cyclic-shift determinant from two triangular minors.
No determinant or characteristic polynomial is supplied as a hypothesis. -/
namespace Holonics.Epime.CyclicShift
open Matrix
variable {R : Type*} [CommRing R]

def cycle (n : ℕ) (a : R) : Matrix (Fin (n+2)) (Fin (n+2)) R :=
  fun i j => if i = j then a else
    if i.val = j.val + 1 ∨ (i.val = 0 ∧ j.val = n+1) then -1 else 0

def shift (n : ℕ) : Matrix (Fin (n+2)) (Fin (n+2)) R :=
  fun i j => if i = finRotate (n+2) j then 1 else 0

lemma cycle_minor_zero (n : ℕ) (a : R) :
    ((cycle n a).submatrix Fin.succ Fin.succ).det = a^(n+1) := by
  have ht : ((cycle n a).submatrix Fin.succ Fin.succ).IsLowerTriangular := by
    intro i j h
    have hij : i.val < j.val := h
    have hne : i.succ ≠ j.succ := by intro hh; have := congrArg Fin.val hh; simp at this; omega
    change cycle n a i.succ j.succ = 0
    have hnot : ¬ (i.succ.val = j.succ.val + 1 ∨
        (i.succ.val = 0 ∧ j.succ.val = n+1)) := by
      change ¬ (i.val+1 = (j.val+1)+1 ∨ (i.val+1=0 ∧ j.val+1=n+1))
      omega
    simp only [cycle, if_neg hne, if_neg hnot]
  rw [Matrix.det_of_isLowerTriangular _ ht]
  simp [Matrix.submatrix, cycle]

lemma cycle_minor_last (n : ℕ) (a : R) :
    ((cycle n a).submatrix Fin.succ (Fin.last (n+1)).succAbove).det = (-1:R)^(n+1) := by
  rw [Fin.succAbove_last]
  have ht : ((cycle n a).submatrix Fin.succ Fin.castSucc).IsUpperTriangular := by
    intro i j h
    have hij : j.val < i.val := h
    have hne : i.succ ≠ j.castSucc := by intro hh; have := congrArg Fin.val hh; simp at this; omega
    simp [Matrix.submatrix, cycle, hne, Fin.val_succ, Fin.val_castSucc]
    omega
  rw [Matrix.det_of_isUpperTriangular ht]
  have hd : ∀ i : Fin (n+1), cycle n a i.succ i.castSucc = (-1:R) := by
    intro i
    have hne : i.succ ≠ i.castSucc := by intro hh; have := congrArg Fin.val hh; simp at this
    simp [cycle, hne, Fin.val_succ]
  simp [Matrix.submatrix, hd]

lemma cycle_det (n : ℕ) (a : R) : (cycle n a).det = a^(n+2)-1 := by
  rw [Matrix.det_succ_row_zero]
  let f := fun j : Fin (n+2) => (-1:R)^j.val * cycle n a 0 j *
    ((cycle n a).submatrix Fin.succ j.succAbove).det
  change (∑ j, f j) = _
  have hsum : (∑ j, f j) = ∑ j ∈ ({0,Fin.last (n+1)} : Finset (Fin (n+2))), f j := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hz : j ≠ 0 := by intro h; subst j; simp at hj
    have hl : j ≠ Fin.last (n+1) := by intro h; subst j; simp at hj
    have hjv : j.val ≠ n+1 := by intro h; apply hl; apply Fin.ext; simpa using h
    simp [f, cycle, hz.symm, hjv]
  rw [hsum]
  have hn : (0 : Fin (n+2)) ≠ Fin.last (n+1) := by intro h; have := congrArg Fin.val h; simp at this
  simp only [Finset.sum_pair hn, f, Fin.val_zero, pow_zero, one_mul, Fin.val_last]
  have hlast : cycle n a 0 (Fin.last (n+1)) = (-1:R) := by simp [cycle, hn]
  rw [hlast]
  simp only [cycle, ite_true, Fin.succAbove_zero]
  rw [cycle_minor_zero, cycle_minor_last]
  have hp : (-1:R)^(n+1) * (-1:R)^(n+1) = 1 := by rw [← mul_pow]; simp
  calc
    a * a^(n+1) + (-1:R)^(n+1) * -1 * (-1:R)^(n+1)
      = a^(n+2)-1 := by
        rw [mul_right_comm ((-1:R)^(n+1)) (-1) _, hp, one_mul, ← pow_succ']
        simp [Nat.add_assoc, sub_eq_add_neg]

lemma cycle_scalar_sub_shift (n : ℕ) (a : R) :
    Matrix.scalar (Fin (n+2)) a - shift n = cycle n a := by
  funext i j
  have hr : i = finRotate (n+2) j ↔
      i.val = j.val+1 ∨ (i.val=0 ∧ j.val=n+1) := by
    rw [Fin.ext_iff, coe_finRotate]
    by_cases hj : j = Fin.last (n+1)
    · have hv : j.val=n+1 := by simp [hj]
      simp [hj, hv]
      have hi := i.isLt
      omega
    · have hv : j.val≠n+1 := by intro h; apply hj; exact Fin.ext h
      simp [hj, hv]
  have hfix : i = j → ¬ (i.val=j.val+1 ∨ (i.val=0 ∧ j.val=n+1)) := by
    intro hij; subst j; have hi := i.isLt; omega
  change (if i=j then a else 0) - (if i=finRotate (n+2) j then 1 else 0) =
    if i=j then a else if i.val=j.val+1 ∨ (i.val=0 ∧ j.val=n+1) then -1 else 0
  by_cases hij : i=j
  · rw [if_pos hij, if_pos hij, if_neg (hr.not.mpr (hfix hij))]
    simp
  · rw [if_neg hij, if_neg hij]
    by_cases hrot : i=finRotate (n+2) j
    · rw [if_pos hrot, if_pos (hr.mp hrot)]; simp
    · rw [if_neg hrot, if_neg (hr.not.mp hrot)]; simp

lemma shift_determinant (n : ℕ) (a : R) :
    (Matrix.scalar (Fin (n+2)) a - shift n).det = a^(n+2)-1 := by
  rw [cycle_scalar_sub_shift, cycle_det]

end Holonics.Epime.CyclicShift

#print axioms Holonics.Epime.CyclicShift.shift_determinant
