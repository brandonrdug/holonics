import Holonics.Objects.Ratio

/-!
# The native face joined to its receiving tree: the covector stays `F − e_t`

The record `research/records/2026-10-22_THE_NATIVE_FACE_READS_ITS_OWN_RECEIVING_TREE.md` (atlas
`hnn.native-tree-join`) joins the native face to the receiving tree's face `q` read at the cell's
address: `weight_c = q_c · 2^(w_c − top)`, `F = weight / Σ weight`
(`hnn::receiving::native_current::NativeCurrentFace::joined`, with `w_c` the wave's real part at
class `c`). Its item 4 says the covector `F − e_t` is the logit gradient of `−log₂ F_t` with the tree
mass held fixed, so the readout's covector law is unchanged; #410 owes that statement. This file
proves it on the owner's normalized exponential
(`Computation/HolonicAdjointNormalization.NormalizedExponential.face`), through the logit covector
of `Objects/Ratio`.

[proved-derived; formal-checked] What is proved.

1. **The joined face is the record's** (`joinedFace_mass`): with the joined potential
   `s_c = ln q_c + w_c ln 2`, the face of `s` is `F_c = q_c 2^(w_c) / Σ_d q_d 2^(w_d)` for a positive
   tree face; subtracting the chart's common `top` from the wave leaves it unchanged
   (`joinedFace_sub_top`).
2. **The tree is a shift of the wave in the base-two chart** (`joinedPotential_eq_shift`): the joined
   face at `(q, w)` is the tree-free face at the wave `w + log₂ q`; with one common tree mass (such as
   `1/|A|` without a tree) it is the wave's own base-two face (`joinedFace_const`). The readout's
   wave is the correction to what the tree already predicts.
3. **The code** (`joinedCode_eq`): `−log₂ F_t = −log₂ q_t − w_t + log₂ Σ_d q_d 2^(w_d)`.
4. **The covector** (`hasDerivAt_joinedCode_line`, `hasDerivAt_joinedCode_coordinate`): with `q`
   held fixed, `−log₂ F_t` moves along the wave line `w + x d` at rate `E_F[d] − d_t`, so its
   gradient in `w` is `F − e_t`: the `ln 2` of the base-two power cancels the `ln 2` of the base-two
   code, and the tree enters only through `F`. The covector carries no total current
   (`sum_joinedCovector`).

The computational object is the helical pair interaction's receiving face: the tree's mass and the
wave's power meet once per class at the receiver's section, and the covector is read on the joined
face that is emitted. Of the winding guide's six general objects this touches faces and placement
(the face at the cell's address); the helix, the pair, the cell holonomy, the tube and the tower
thread stay attached.

Consumers: the atlas row `hnn.native-tree-join` and #410.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.NativeTreeJoin

open scoped BigOperators
open Holonics.Computation.HolonicInformationTheory
open Holonics.Computation.HolonicAdjointNormalization
open Holonics.Computation.HolonicAdjointNormalization.NormalizedExponential
open Holonics.Objects.Ratio

variable {A : Type*} [Fintype A] [Nonempty A]

/-! ## 1. The joined face -/

/-- [definition] The joined potential: the tree's mass in the natural chart beside the wave's
base-two power, `s_c = ln q_c + w_c ln 2`. -/
def joinedPotential (q w : A → ℝ) : A → ℝ := fun c => Real.log (q c) + w c * Real.log 2

/-- [definition] The native face joined to the receiving tree, `F = face(s)`. -/
def joinedFace (q w : A → ℝ) : PositiveProbabilitySection A := face (joinedPotential q w)

/-- [proved-derived; formal-checked] A class's weight is its tree mass times the wave's power,
`e^(s_c) = q_c 2^(w_c)`. -/
theorem exp_joinedPotential {q : A → ℝ} (hq : ∀ c, 0 < q c) (w : A → ℝ) (c : A) :
    Real.exp (joinedPotential q w c) = q c * (2 : ℝ) ^ (w c) := by
  rw [joinedPotential, Real.exp_add, Real.exp_log (hq c), Real.rpow_def_of_pos two_pos,
    mul_comm (w c)]

/-- [proved-derived; formal-checked] **The joined face is the record's**:
`F_c = q_c 2^(w_c) / Σ_d q_d 2^(w_d)`. -/
theorem joinedFace_mass {q : A → ℝ} (hq : ∀ c, 0 < q c) (w : A → ℝ) (c : A) :
    (joinedFace q w).mass c = q c * (2 : ℝ) ^ (w c) / ∑ d, q d * (2 : ℝ) ^ (w d) := by
  simp only [joinedFace, face, partition, exp_joinedPotential hq]

/-- [proved-derived; formal-checked] **The top is invisible**: subtracting a common `top` from the
wave (the Rust chart's `w − top`) leaves the joined face unchanged. -/
theorem joinedFace_sub_top (q w : A → ℝ) (top : ℝ) :
    (joinedFace q (fun c => w c - top)).mass = (joinedFace q w).mass := by
  have h : joinedPotential q (fun c => w c - top) =
      fun c => joinedPotential q w c + (-(top * Real.log 2)) := by
    funext c
    simp only [joinedPotential]
    ring
  simp only [joinedFace]
  rw [h, face_add_common]

/-! ## 2. The tree is a shift of the wave -/

/-- [proved-derived; formal-checked] **The tree is a shift of the wave in the base-two chart**: the
joined potential at `(q, w)` is the tree-free potential at the wave `w + log₂ q`. -/
theorem joinedPotential_eq_shift (q w : A → ℝ) :
    joinedPotential q w =
      joinedPotential (fun _ => 1) (fun c => w c + Real.logb 2 (q c)) := by
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  funext c
  simp only [joinedPotential, Real.log_one, zero_add, Real.logb]
  rw [add_mul, div_mul_cancel₀ _ h2]
  ring

/-- [proved-derived; formal-checked] **Without a tree**: with one common tree mass `m` (such as
`1/|A|`), the joined face is the wave's own base-two face `face(w ln 2)`. -/
theorem joinedFace_const (m : ℝ) (w : A → ℝ) :
    (joinedFace (fun _ => m) w).mass = (face (fun c => w c * Real.log 2)).mass := by
  have h : joinedPotential (fun _ => m) w = fun c => w c * Real.log 2 + Real.log m := by
    funext c
    simp only [joinedPotential]
    ring
  simp only [joinedFace]
  rw [h, face_add_common]

/-! ## 3. The code -/

/-- [proved-derived; formal-checked] **The code**: `−log₂ F_t = −log₂ q_t − w_t + log₂ Σ_d q_d 2^(w_d)`. -/
theorem joinedCode_eq {q : A → ℝ} (hq : ∀ c, 0 < q c) (w : A → ℝ) (t : A) :
    -Real.logb 2 ((joinedFace q w).mass t) =
      -Real.logb 2 (q t) - w t + Real.logb 2 (∑ d, q d * (2 : ℝ) ^ (w d)) := by
  have hpow : ∀ c, 0 < (2 : ℝ) ^ (w c) := fun c => Real.rpow_pos_of_pos two_pos _
  have hZ : 0 < ∑ d, q d * (2 : ℝ) ^ (w d) :=
    Finset.sum_pos (fun d _ => mul_pos (hq d) (hpow d)) Finset.univ_nonempty
  rw [joinedFace_mass hq, Real.logb_div (mul_pos (hq t) (hpow t)).ne' hZ.ne',
    Real.logb_mul (hq t).ne' (hpow t).ne', Real.logb_rpow two_pos (by norm_num)]
  ring

/-! ## 4. The covector -/

/-- [proved-derived; formal-checked] The joined potential moves along a wave line by the direction
times `ln 2`. -/
theorem joinedPotential_line (q w d : A → ℝ) (x : ℝ) :
    joinedPotential q (fun c => w c + x * d c) =
      fun c => joinedPotential q w c + x * (Real.log 2 * d c) := by
  funext c
  simp only [joinedPotential]
  ring

/-- [proved-derived; formal-checked] **The code along a wave line**: with the tree mass held fixed,
`−log₂ F_t` moves along `w + x d` at rate `E_F[d] − d_t`. -/
theorem hasDerivAt_joinedCode_line (q w d : A → ℝ) (t : A) :
    HasDerivAt (fun x => -Real.logb 2 ((joinedFace q (fun c => w c + x * d c)).mass t))
      (expectation (joinedFace q w) d - d t) 0 := by
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have h := (hasDerivAt_targetSurprisal_sectionLine (joinedPotential q w)
    (fun c => Real.log 2 * d c) t).div_const (Real.log 2)
  have hfun : (fun x => -Real.logb 2 ((joinedFace q (fun c => w c + x * d c)).mass t)) =
      fun x => targetSurprisal (fun c => joinedPotential q w c + x * (Real.log 2 * d c)) t /
        Real.log 2 := by
    funext x
    simp only [joinedFace, joinedPotential_line, targetSurprisal, Real.logb, neg_div]
  rw [hfun]
  refine h.congr_deriv ?_
  have hs : ∑ i, (face (joinedPotential q w)).mass i * (Real.log 2 * d i) =
      Real.log 2 * ∑ i, (face (joinedPotential q w)).mass i * d i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [expectation, joinedFace]
  rw [hs, ← mul_sub, mul_div_cancel_left₀ _ h2]

/-- [proved-derived; formal-checked] **The covector is `F − e_t`**: along wave coordinate `j`, with
the tree mass held fixed, `∂/∂w_j (−log₂ F_t) = F_j − [t = j]`. -/
theorem hasDerivAt_joinedCode_coordinate [DecidableEq A] (q w : A → ℝ) (t j : A) :
    HasDerivAt
      (fun x => -Real.logb 2
        ((joinedFace q (fun c => w c + x * (Pi.single j (1 : ℝ) : A → ℝ) c)).mass t))
      ((joinedFace q w).mass j - if t = j then 1 else 0) 0 := by
  refine (hasDerivAt_joinedCode_line q w (Pi.single j 1) t).congr_deriv ?_
  congr 1
  · simp [expectation, Pi.single_apply]
  · simp [Pi.single_apply]

/-- [proved-derived; formal-checked] The covector `F − e_t` carries no total current. -/
theorem sum_joinedCovector [DecidableEq A] (q w : A → ℝ) (t : A) :
    ∑ j, ((joinedFace q w).mass j - if t = j then 1 else 0) = 0 := by
  rw [Finset.sum_sub_distrib, (joinedFace q w).normalized]
  simp

end Holonics.HNN.NativeTreeJoin
