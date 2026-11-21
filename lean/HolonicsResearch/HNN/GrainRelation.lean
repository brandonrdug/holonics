import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Tactic
import HolonicsResearch.HNN.WidthTolerance

/-!
# A grain is a relation between grains: the point a place is counted from is a gauge, a place is priced by a ratio, and coarse channels pin a value by agreeing

Atlas: `radix.grain-is-a-relation`, `code.common-mode-unread`. Record:
`research/records/2026-11-21_A_GRAIN_IS_A_RELATION_BETWEEN_GRAINS_…` (§4, §9).

The first record of November 21 stated a word's bottom as a count of places under a point, for a tolerance handed in by number, and E5 of
#1088 built it so. This module holds the statements that show what such a count leaves unsaid. Most of the law already has its
owners, and they are named where each is used:

* a word's read part and its carried rest, and the carries that hold a flux: `Holonics/HNN/LatticeDeposit` and
  `Foundation/CarriedRelease` (`release_conserves`, `release_tracks`, `plain_rounding_silences`);
* a total read from its low places and a coarse reading at the real place: `Foundation/SectionGauge` (`intervalSection_reads`);
* a defect located by loop closure only where the circuit menu separates it: `Holon/Syndrome` (`locates_iff_separates`);
* the pantograph, whose scales multiply, and the gyrogroup: `Geometry/HolonicPantographicSwingJets`, `Geometry/Gyrogroup`.

1. **The point is a gauge** (`face_shift`, `lane_ratio_scale`). A face is unchanged when every exponent takes one common offset, and
   a lane read as a ratio to its own power is unchanged when the lane is scaled. A place counted from a fixed point under either
   carrier names nothing its reader reads.
2. **A common mode is unread** (`face_tail_common_mode`). Where the unread tails of a face's exponents all stand within `B` of one
   common value `c`, every symbol's code moves by at most `2B`, whatever `c` is. The tail's spread over the symbols is read and its
   mean is not. This sharpens `WidthTolerance.face_tail_moves_code`, which is the case `c = 0`.
3. **Equal rents cost least** (`total_rent_ge`, `equal_rent_attains`). Entries of stiffness `h i` held at grains `u i` pay rents
   `h i * u i ^ 2`. At a fixed product of the grains, which is a fixed count of places kept over all entries, the total rent is at
   least the count of entries times the geometric mean of the rents, and it equals that where every entry pays the same rent. A
   grain proportional to each entry's own unit is the least cost, and one grain for every entry is that only where every entry is
   as stiff as every other.
4. **Two coarse channels pin a value, and a third sees a disagreement** (`two_channels_pin`, `third_channel_detects`). Two values of
   a declared range that agree on two coprime channels whose product covers the range are one value, so they agree on every third
   channel. A reading that agrees with a value on two channels and differs on a third is the reading of no value of the range, and
   that is seen from the three channels alone.
5. **One place read at two cuts** (`place_two_cuts`). A power of two is as small at the real place as it is large at the place of
   two, and the two sizes multiply to one. The sign of an exponent names which of the two cuts a word is read at.

The computational object is the helical pair interaction's receiving face and the store its deposit moves. Of the winding guide's
six objects this touches the helix (a word is a count above a turn), faces and placement (the place a read part ends at) and the
tower thread (a unit is a level's); the pair, cell holonomy and the tube stay attached through the owners above.
-/

namespace Holonics.HNN.GrainRelation

open Finset

/-- **The point is a gauge, on the face.** One common offset of every exponent leaves every symbol's share as it was. -/
theorem face_shift {ι : Type*} [Fintype ι] (z : ι → ℝ) (c : ℝ) (a : ι) :
    Real.exp (z a + c) / ∑ b, Real.exp (z b + c) = Real.exp (z a) / ∑ b, Real.exp (z b) := by
  have h : ∀ b, Real.exp (z b + c) = Real.exp (z b) * Real.exp c := fun b => Real.exp_add _ _
  simp only [h, ← Finset.sum_mul]
  rw [mul_div_mul_right _ _ (Real.exp_pos c).ne']

/-- **A common mode is unread.** Tails that stand within `B` of one common value `c` at every symbol move every symbol's code by at
most `2B`, whatever `c` is. -/
theorem face_tail_common_mode {ι : Type*} [Fintype ι] [Nonempty ι] (z z' : ι → ℝ) (B c : ℝ)
    (h : ∀ b, |z' b - z b - c| ≤ B) (a : ι) :
    |Real.log (Real.exp (z' a) / ∑ b, Real.exp (z' b)) - Real.log (Real.exp (z a) / ∑ b, Real.exp (z b))|
      ≤ 2 * B := by
  have key := WidthTolerance.face_tail_moves_code z (fun b => z' b + -c) B
    (fun b => by have := h b; rwa [show z' b + -c - z b = z' b - z b - c by ring]) a
  rwa [face_shift z' (-c) a] at key

/-- **The point is a gauge, on a lane.** A coordinate's share of its lane's power is unchanged when the lane is scaled. -/
theorem lane_ratio_scale {ι : Type*} [Fintype ι] (x : ι → ℝ) (l : ℝ) (hl : l ≠ 0) (i : ι) :
    (l * x i) ^ 2 / ∑ j, (l * x j) ^ 2 = x i ^ 2 / ∑ j, x j ^ 2 := by
  have h : ∀ j, (l * x j) ^ 2 = l ^ 2 * x j ^ 2 := fun j => mul_pow _ _ _
  simp only [h, ← Finset.mul_sum]
  rw [mul_div_mul_left _ _ (pow_ne_zero 2 hl)]

/-- **The total rent is at least the count of entries times the geometric mean of the rents.** The product of the rents is the
product of the stiffnesses times the square of the product of the grains, so at a fixed count of places kept it is fixed. -/
theorem total_rent_ge {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (h u : ι → ℝ) (hh : ∀ i ∈ s, 0 ≤ h i) :
    (s.card : ℝ) * (∏ i ∈ s, h i * u i ^ 2) ^ ((s.card : ℝ)⁻¹) ≤ ∑ i ∈ s, h i * u i ^ 2 := by
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hr : ∀ i ∈ s, 0 ≤ h i * u i ^ 2 := fun i hi => mul_nonneg (hh i hi) (sq_nonneg _)
  have hw : ∑ _i ∈ s, (s.card : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hn.ne']
  have am := Real.geom_mean_le_arith_mean_weighted s (fun _ => (s.card : ℝ)⁻¹) (fun i => h i * u i ^ 2)
    (fun _ _ => inv_nonneg.mpr hn.le) hw hr
  rw [Real.finsetProd_rpow s _ hr, ← Finset.mul_sum] at am
  calc (s.card : ℝ) * (∏ i ∈ s, h i * u i ^ 2) ^ ((s.card : ℝ)⁻¹)
      ≤ (s.card : ℝ) * ((s.card : ℝ)⁻¹ * ∑ i ∈ s, h i * u i ^ 2) := mul_le_mul_of_nonneg_left am hn.le
    _ = ∑ i ∈ s, h i * u i ^ 2 := by rw [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]

/-- **Equal rents attain it.** Where every entry pays one rent `c`, the total is the bound of `total_rent_ge`. -/
theorem equal_rent_attains {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (h u : ι → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (heq : ∀ i ∈ s, h i * u i ^ 2 = c) :
    ∑ i ∈ s, h i * u i ^ 2 = (s.card : ℝ) * (∏ i ∈ s, h i * u i ^ 2) ^ ((s.card : ℝ)⁻¹) := by
  rw [Finset.sum_congr rfl heq, Finset.prod_congr rfl heq, Finset.sum_const, Finset.prod_const, nsmul_eq_mul,
    Real.pow_rpow_inv_natCast hc hs.card_pos.ne']

/-- **Two coarse channels pin a value.** Two values under the product of two coprime moduli that agree on both channels are one. -/
theorem two_channels_pin {a b : ℕ} (hab : a.Coprime b) {x y : ℕ} (hx : x < a * b) (hy : y < a * b)
    (ha : x % a = y % a) (hb : x % b = y % b) : x = y :=
  Nat.ModEq.eq_of_lt_of_lt ((Nat.modEq_and_modEq_iff_modEq_mul hab).mp ⟨ha, hb⟩) hx hy

/-- **A third channel sees a disagreement.** Two values of a range that two coprime channels cover, agreeing on those two, agree on
every third channel: a reading that agrees on two and differs on the third is the reading of no value of the range. -/
theorem third_channel_detects {a b c R : ℕ} (hab : a.Coprime b) (hR : R ≤ a * b) {x y : ℕ} (hx : x < R) (hy : y < R)
    (ha : x % a = y % a) (hb : x % b = y % b) : x % c = y % c := by
  rw [two_channels_pin hab (hx.trans_le hR) (hy.trans_le hR) ha hb]

/-- **One place read at two cuts.** A power of two is as small at the real place as it is large at the place of two. -/
theorem place_two_cuts (k : ℤ) : padicNorm 2 ((2 : ℚ) ^ k) * |(2 : ℚ) ^ k| = 1 := by
  have h0 : (2 : ℚ) ^ k ≠ 0 := zpow_ne_zero k (by norm_num)
  have h1 : padicValRat 2 (2 : ℚ) = 1 := by exact_mod_cast padicValRat.self (p := 2) (by norm_num)
  have hv : padicValRat 2 ((2 : ℚ) ^ k) = k := by
    rw [padicValRat.zpow (p := 2) (2 : ℚ) (k := k), h1, mul_one]
  rw [padicNorm.eq_zpow_of_nonzero h0, hv, abs_of_pos (zpow_pos (by norm_num) k)]
  simp only [Nat.cast_ofNat]
  rw [zpow_neg]
  exact inv_mul_cancel₀ h0

end Holonics.HNN.GrainRelation
