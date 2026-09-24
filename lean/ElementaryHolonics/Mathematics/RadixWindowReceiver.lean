import Mathlib

noncomputable section

namespace Soma.Holonics.Mathematics.RadixWindowReceiver

/-! A radix window is the residue seen by a receiver after an exact scaling.
The integer floor is retained until the final, explicitly declared residue. -/

def window (b k l : ℕ) (x : ℝ) : ℤ :=
  ⌊(b : ℝ) ^ (k + l) * x⌋ % (b ^ l : ℤ)

def scaledWindow (b l : ℕ) (y : ℝ) : ℤ :=
  ⌊(b : ℝ) ^ l * y⌋ % (b ^ l : ℤ)

theorem floor_scaled_eq_of_endpoint_floors_eq
    {b k l : ℕ} (hb : 0 < b) {L U x : ℝ} {K : ℤ}
    (hLU : L ≤ x) (hxU : x ≤ U)
    (hL : ⌊(b : ℝ) ^ (k + l) * L⌋ = K)
    (hU : ⌊(b : ℝ) ^ (k + l) * U⌋ = K) :
    ⌊(b : ℝ) ^ (k + l) * x⌋ = K := by
  have hs : 0 < (b : ℝ) ^ (k + l) := by positivity
  have hLx : (b : ℝ) ^ (k + l) * L ≤ (b : ℝ) ^ (k + l) * x :=
    mul_le_mul_of_nonneg_left hLU hs.le
  have hxU' : (b : ℝ) ^ (k + l) * x ≤ (b : ℝ) ^ (k + l) * U :=
    mul_le_mul_of_nonneg_left hxU hs.le
  have hfloorL : K ≤ ⌊(b : ℝ) ^ (k + l) * x⌋ := by
    rw [← hL]
    exact Int.floor_mono hLx
  have hfloorU : ⌊(b : ℝ) ^ (k + l) * x⌋ ≤ K := by
    rw [← hU]
    exact Int.floor_mono hxU'
  exact le_antisymm hfloorU hfloorL

theorem window_eq_of_endpoint_floors_eq
    {b k l : ℕ} (hb : 0 < b) {L U x : ℝ} {K : ℤ}
    (hLU : L ≤ x) (hxU : x ≤ U)
    (hL : ⌊(b : ℝ) ^ (k + l) * L⌋ = K)
    (hU : ⌊(b : ℝ) ^ (k + l) * U⌋ = K) :
    window b k l x = K % (b ^ l : ℤ) := by
  unfold window
  rw [floor_scaled_eq_of_endpoint_floors_eq hb hLU hxU hL hU]

theorem scaledWindow_int_translate (b l : ℕ) (y : ℝ) (j : ℤ) :
    scaledWindow b l (y + j) = scaledWindow b l y := by
  unfold scaledWindow
  have hpow : ((b : ℝ) ^ l) * (j : ℝ) = ((b ^ l : ℤ) * j : ℤ) := by
    norm_num
  rw [mul_add, hpow, Int.floor_add_intCast]
  exact Int.add_mul_emod_self_left _ _ _

theorem scaledWindow_eq_fract_floor (b l : ℕ) (y : ℝ) :
    scaledWindow b l y =
      ⌊(b : ℝ) ^ l * Int.fract y⌋ % (b ^ l : ℤ) := by
  unfold scaledWindow
  have hpow : ((b : ℝ) ^ l) * (Int.floor y : ℝ) =
      ((b ^ l : ℤ) * Int.floor y : ℤ) := by
    norm_num
  have hy : y = Int.fract y + (Int.floor y : ℝ) := by
    change y = (y - (Int.floor y : ℝ)) + (Int.floor y : ℝ)
    ring
  conv_lhs =>
    rw [hy, mul_add, hpow, Int.floor_add_intCast]
  exact Int.add_mul_emod_self_left _ _ _

theorem scaledWindow_eq_fract_floor_of_pos (b l : ℕ) (hb : 0 < b) (y : ℝ) :
    scaledWindow b l y = ⌊(b : ℝ) ^ l * Int.fract y⌋ := by
  rw [scaledWindow_eq_fract_floor]
  apply Int.emod_eq_of_lt
  · positivity
  · have hs : 0 < (b : ℝ) ^ l := by positivity
    have hlt : Int.fract y < 1 := Int.fract_lt_one y
    have hreal : (b : ℝ) ^ l * Int.fract y < (b : ℝ) ^ l :=
      by simpa using (mul_lt_mul_of_pos_left hlt hs)
    rw [Int.floor_lt]
    exact_mod_cast hreal

theorem window_eq_scaledWindow (b k l : ℕ) (x : ℝ) :
    window b k l x = scaledWindow b l ((b : ℝ) ^ k * x) := by
  unfold window scaledWindow
  congr 2
  rw [pow_add]
  ring

theorem endpoint_residue_agreement_wraparound :
    ((9 : ℤ) % (10 : ℤ)) = ((19 : ℤ) % (10 : ℤ)) ∧ (9 : ℤ) ≠ 19 := by
  norm_num

end Soma.Holonics.Mathematics.RadixWindowReceiver
