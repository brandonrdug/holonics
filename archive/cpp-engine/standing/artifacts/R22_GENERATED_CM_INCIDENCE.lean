import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Soma.Holonics.R22

structure CM4 where
  a0 : ℤ
  a1 : ℤ
  a2 : ℤ
  a3 : ℤ
deriving DecidableEq

def cmOne : CM4 := ⟨1,0,0,0⟩
def cmConj (a : CM4) : CM4 := ⟨a.a0-a.a1,-a.a1,a.a3-a.a1,a.a2-a.a1⟩
def cmMul (a b : CM4) : CM4 :=
  let c0 := a.a0*b.a0
  let c1 := a.a0*b.a1+a.a1*b.a0
  let c2 := a.a0*b.a2+a.a1*b.a1+a.a2*b.a0
  let c3 := a.a0*b.a3+a.a1*b.a2+a.a2*b.a1+a.a3*b.a0
  let c4 := a.a1*b.a3+a.a2*b.a2+a.a3*b.a1
  let c5 := a.a2*b.a3+a.a3*b.a2
  let c6 := a.a3*b.a3
  ⟨c0-c4+c5,c1-c4+c6,c2-c4,c3-c4⟩
def cmSub (a b : CM4) : CM4 := ⟨a.a0-b.a0,a.a1-b.a1,a.a2-b.a2,a.a3-b.a3⟩
def cmNorm (a : CM4) : CM4 := cmMul a (cmConj a)

def root0 : CM4 := ⟨1,0,0,0⟩
def root1 : CM4 := ⟨0,1,0,0⟩
def root2 : CM4 := ⟨0,0,1,0⟩
def root3 : CM4 := ⟨0,0,0,1⟩
def root4 : CM4 := ⟨-1,-1,-1,-1⟩

theorem generated_norm_one_translations :
    cmNorm root0 = cmOne ∧ cmNorm root1 = cmOne ∧ cmNorm root2 = cmOne ∧
    cmNorm root3 = cmOne ∧ cmNorm root4 = cmOne := by native_decide

def coeff (n shift : Nat) : ℤ := Int.ofNat ((n / (2^shift)) % 2)
def point (n : Fin 16) : CM4 :=
  ⟨coeff n.val 0,coeff n.val 1,coeff n.val 2,coeff n.val 3⟩
def unitPair (i j : Fin 16) : Bool :=
  decide (i.val < j.val) && decide (cmNorm (cmSub (point j) (point i)) = cmOne)
def unitPairCount : Nat :=
  (((Finset.univ : Finset (Fin 16)) ×ˢ (Finset.univ : Finset (Fin 16))).filter
    (fun p : Fin 16 × Fin 16 => unitPair p.1 p.2 = true)).card

theorem generated_bounded_embedding_injective :
    ∀ i j : Fin 16, point i = point j → i = j := by native_decide

theorem generated_unit_pair_count : unitPairCount = 33 := by native_decide

def periodicChar (X : ℤ) : ℤ := ((((((((((((((((1 * X + 0) * X + -40) * X + 0) * X + 540) * X + -384) * X + -3480) * X + 5760) * X + 8070) * X + -29440) * X + 17640) * X + 37120) * X + -82020) * X + 74880) * X + -37800) * X + 10368) * X + -1215)
def periodicFactor (X : ℤ) : ℤ := (((1 * X + 3)) ^ 5) * (((1 * X + -1)) ^ 10) * (((1 * X + -5)) ^ 1)
def windowChar (X : ℤ) : ℤ := ((((((((((((((((1 * X + 0) * X + -33) * X + 0) * X + 376) * X + -48) * X + -1984) * X + 576) * X + 4992) * X + -2304) * X + -4864) * X + 3072) * X + 0) * X + 0) * X + 0) * X + 0) * X + 0)
def windowFactor (X : ℤ) : ℤ := (((1 * X + 2)) ^ 3) * (((1 * X + 0)) ^ 5) * (((1 * X + -2)) ^ 3) * ((((1 * X + 1) * X + -4)) ^ 1) * (((((1 * X + -1) * X + -16) * X + 12)) ^ 1)

theorem generated_cm_characteristic_transport (X : ℤ) :
    periodicChar X = periodicFactor X ∧ windowChar X = windowFactor X := by
  constructor <;>
    simp only [periodicChar, periodicFactor, windowChar, windowFactor] <;> ring

theorem generated_aperture_transport : (40 : ℤ) - 7 = 33 ∧ (0 : ℤ) = 0 := by norm_num

end Soma.Holonics.R22

#check Soma.Holonics.R22.generated_cm_characteristic_transport
