import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# The ring's hand: a pumped move keeps, reverses or collapses the plane's orientation

The tower's ring is carried by the moves `h ↦ λ h + β·conj(h)` of its mode
(`hnn::tower::{ring_carry, ring_carry_adjoint, hand_after}`, `RingFace::with_restarts`; record
`2026-10-24_THE_TOWER_HEARS_THE_HOLONICS_TEXT_AND_EVERY_LOOK_IS_READ_BY_ITS_LOCK.md`, section "`−` is
`+` reversed", PR #471). The ring is read in its own hand, `(Re h, o·Im h)`, with `o` the product of
the moves' determinant signs since its last restart. #410 owes the hand's law; this file proves it.

[proved-standard; formal-checked] What is proved.

1. **The move in the chart `(Re h, Im h)`** (`handMatrix`, `handMatrix_mulVec`): with
   `m = [Re λ, Im λ, Re β, Im β]` it is `[[Re λ + Re β, Im β − Im λ], [Im λ + Im β, Re λ − Re β]]`,
   Rust's `ring_carry`.
2. **Its determinant is `|λ|² − |β|²`** (`det_handMatrix`), so it keeps the plane's orientation
   where `|λ| > |β|` (`handMatrix_keeps`), reverses it where `|λ| < |β|` (`handMatrix_reverses`) and
   is singular where they are equal (`handMatrix_singular`): the ring collapses onto a line or the
   origin. With `λ = 0` and `|β| = 1` it is a reflection: it squares to `1` and has determinant
   `−1` (`handMatrix_reflection`).
3. **The covector goes back through the transpose** (`transpose_handMatrix`): `Mᵀ` is the move of
   `(conj λ, β)`, Rust's `ring_carry_adjoint`, the adjoint `G ↦ conj(λ) G + β conj(G)` of the
   pumped mode.
4. **Re-basing a reversed ring** (`flipY`, `handMatrix_zero_one`, `flipY_mul_self`,
   `flipY_transpose`, `flipY_mulVec`, `flipY_adjoint`, `det_flipY`): `(x, y) ↦ (x, −y)` is the move
   `conj`, an involution of determinant `−1`, and the covector carried back through it is
   `(g_x, −g_y)`.
5. **The ring reads in its own hand** (`handAfter`, `handSign`, `hand_reads_positive`,
   `hand_from_rest_reads_positive`). `handAfter` is Rust's `hand_after`: the hand is kept by a move of
   positive determinant, flipped by one of negative determinant, and restarts unreversed at a
   singular move. Along any moves since the last restart, the hand `o` reached from rest makes
   `o · ∏ det M_i > 0`: the read `(Re h, o·Im h)` composed with the moves always keeps the
   orientation, so a turn met after a reflection is read turning the other way.

Consumers: the atlas rows `hnn.tower-ring-face`, `hnn.tower-ring-closure` and
`hnn.tower-pumped-mode`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.RingHand

open Complex ComplexConjugate Matrix

/-- [definition] The move `h ↦ λ h + β·conj(h)` in the chart `(Re h, Im h)`. -/
def handMatrix (l b : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![l.re + b.re, b.im - l.im; l.im + b.im, l.re - b.re]

/-- [proved-standard; formal-checked] **The matrix is the move** in the chart `(Re h, Im h)`. -/
theorem handMatrix_mulVec (l b h : ℂ) :
    handMatrix l b *ᵥ ![h.re, h.im] = ![(l * h + b * conj h).re, (l * h + b * conj h).im] := by
  ext i
  fin_cases i <;> simp [handMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- [proved-standard; formal-checked] **The move's determinant is `|λ|² − |β|²`.** -/
theorem det_handMatrix (l b : ℂ) : (handMatrix l b).det = normSq l - normSq b := by
  rw [handMatrix, Matrix.det_fin_two_of, normSq_apply, normSq_apply]
  ring

/-- [proved-standard; formal-checked] Where `|λ| > |β|` the move keeps the orientation. -/
theorem handMatrix_keeps {l b : ℂ} (h : normSq b < normSq l) : 0 < (handMatrix l b).det := by
  rw [det_handMatrix]
  linarith

/-- [proved-standard; formal-checked] Where `|λ| < |β|` the move reverses the orientation. -/
theorem handMatrix_reverses {l b : ℂ} (h : normSq l < normSq b) : (handMatrix l b).det < 0 := by
  rw [det_handMatrix]
  linarith

/-- [proved-standard; formal-checked] Where `|λ| = |β|` the move is singular. -/
theorem handMatrix_singular {l b : ℂ} (h : normSq l = normSq b) : (handMatrix l b).det = 0 := by
  rw [det_handMatrix, h, sub_self]

/-- [proved-standard; formal-checked] **With `λ = 0` and `|β| = 1` the move is a reflection:** it
squares to `1` and has determinant `−1`. -/
theorem handMatrix_reflection {b : ℂ} (hb : normSq b = 1) :
    handMatrix 0 b * handMatrix 0 b = 1 ∧ (handMatrix 0 b).det = -1 := by
  refine ⟨?_, by rw [det_handMatrix, map_zero, hb]; norm_num⟩
  rw [normSq_apply] at hb
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [handMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> linarith

/-- [proved-standard; formal-checked] **The covector goes back through the transpose**, the move of
`(conj λ, β)`. -/
theorem transpose_handMatrix (l b : ℂ) : (handMatrix l b)ᵀ = handMatrix (conj l) b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [handMatrix] <;> ring

/-- [definition] The re-basing `(x, y) ↦ (x, −y)`. -/
def flipY : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- [proved-standard; formal-checked] The re-basing is the move `conj`. -/
theorem handMatrix_zero_one : handMatrix 0 1 = flipY := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [handMatrix, flipY]

/-- [proved-standard; formal-checked] **The re-basing is an involution.** -/
theorem flipY_mul_self : flipY * flipY = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flipY, Matrix.mul_apply, Fin.sum_univ_two]

/-- [proved-standard; formal-checked] The re-basing is its own transpose. -/
theorem flipY_transpose : flipYᵀ = flipY := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flipY]

/-- [proved-standard; formal-checked] The re-basing reads `(x, −y)`. -/
theorem flipY_mulVec (x y : ℝ) : flipY *ᵥ ![x, y] = ![x, -y] := by
  ext i
  fin_cases i <;> simp [flipY, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- [proved-standard; formal-checked] **The covector carried back through the re-basing is
`(g_x, −g_y)`:** `⟨g, flipY v⟩ = ⟨flipY g, v⟩`. -/
theorem flipY_adjoint (g v : Fin 2 → ℝ) : g ⬝ᵥ (flipY *ᵥ v) = (flipY *ᵥ g) ⬝ᵥ v := by
  simp [flipY, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- [proved-standard; formal-checked] The re-basing reverses the orientation. -/
theorem det_flipY : flipY.det = -1 := by
  rw [flipY, Matrix.det_fin_two_of]
  norm_num

/-- [definition] Rust's `hand_after`: `true` is a reversed hand. A move of positive determinant
keeps the hand, one of negative determinant flips it, and a singular move restarts the ring
unreversed. -/
noncomputable def handAfter (l b : ℂ) (hand : Bool) : Bool :=
  if normSq b < normSq l then hand else if normSq l < normSq b then !hand else false

/-- [definition] The sign `o` of a hand: `−1` reversed, `1` not. -/
def handSign (o : Bool) : ℝ := if o then -1 else 1

theorem handSign_mul_self (o : Bool) : handSign o * handSign o = 1 := by
  cases o <;> simp [handSign]

theorem handSign_not (o : Bool) : handSign (!o) = -handSign o := by
  cases o <;> simp [handSign]

/-- [proved-standard; formal-checked] **The ring reads in its own hand:** along nonsingular moves
from a hand `o₀`, the hand `o` reached makes `o · o₀ · ∏ det M_i > 0`. -/
theorem hand_reads_positive (ms : List (ℂ × ℂ)) (hms : ∀ m ∈ ms, normSq m.1 ≠ normSq m.2)
    (o : Bool) :
    0 < handSign (ms.foldl (fun o m => handAfter m.1 m.2 o) o) * handSign o *
      (ms.map fun m => (handMatrix m.1 m.2).det).prod := by
  induction ms generalizing o with
  | nil => simp [handSign_mul_self]
  | cons m ms ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons]
    have hm := hms m (by simp)
    have ih' := ih (fun x hx => hms x (by simp [hx])) (handAfter m.1 m.2 o)
    rcases lt_or_gt_of_ne hm with hlt | hgt
    · have hd : (handMatrix m.1 m.2).det < 0 := handMatrix_reverses hlt
      have hf : handAfter m.1 m.2 o = !o := by
        simp only [handAfter, if_neg (not_lt.2 hlt.le), if_pos hlt]
      rw [hf, handSign_not] at ih'
      rw [hf]
      have e : handSign ((ms.foldl (fun o m => handAfter m.1 m.2 o) (!o))) * handSign o *
            ((handMatrix m.1 m.2).det * (ms.map fun m => (handMatrix m.1 m.2).det).prod) =
          (-(handMatrix m.1 m.2).det) *
            (handSign ((ms.foldl (fun o m => handAfter m.1 m.2 o) (!o))) * -handSign o *
              (ms.map fun m => (handMatrix m.1 m.2).det).prod) := by ring
      rw [e]
      exact mul_pos (neg_pos.2 hd) ih'
    · have hd : 0 < (handMatrix m.1 m.2).det := handMatrix_keeps hgt
      have hf : handAfter m.1 m.2 o = o := by
        simp only [handAfter, if_pos hgt]
      rw [hf] at ih'
      rw [hf]
      have e : handSign ((ms.foldl (fun o m => handAfter m.1 m.2 o) o)) * handSign o *
            ((handMatrix m.1 m.2).det * (ms.map fun m => (handMatrix m.1 m.2).det).prod) =
          (handMatrix m.1 m.2).det *
            (handSign ((ms.foldl (fun o m => handAfter m.1 m.2 o) o)) * handSign o *
              (ms.map fun m => (handMatrix m.1 m.2).det).prod) := by ring
      rw [e]
      exact mul_pos hd ih'

/-- [proved-standard; formal-checked] **From rest, the hand reached reads the moves positively:**
`o · ∏ det M_i > 0`, so `(Re h, o·Im h)` composed with the moves keeps the orientation. -/
theorem hand_from_rest_reads_positive (ms : List (ℂ × ℂ))
    (hms : ∀ m ∈ ms, normSq m.1 ≠ normSq m.2) :
    0 < handSign (ms.foldl (fun o m => handAfter m.1 m.2 o) false) *
      (ms.map fun m => (handMatrix m.1 m.2).det).prod := by
  have h := hand_reads_positive ms hms false
  simpa [handSign] using h

end Holonics.HNN.RingHand
