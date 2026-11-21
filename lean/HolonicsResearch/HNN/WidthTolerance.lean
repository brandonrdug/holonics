import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Tactic

/-!
# A width is a tolerance: an unread tail moves a code by at most twice its bound, and coprime channels add without a carry

Atlas: `code.tail-bound-moves-code-by-twice`, `radix.width-is-a-tolerance`. Record:
`research/records/2026-11-21_A_WIDTH_IS_A_TOLERANCE_…` (§4, §11).

The engine's grains are declared numbers (`crates/engine/src/width.rs`, counted by `tools/width_census.py`). The record
states where a width comes from instead: a word's top grows by its carry or by the need of its operation, and its
bottom stands where what is left unread no longer moves its receiver's code. Most of that law already has its owners,
and this module adds only the two statements they lacked:

* the need of a sum and a product: `Mathematics/PlaceComplex` (`sum_n_width`, `product_width`);
* a receiver's grain from its tolerance, the lattice a store's entries live on, and the guard of a sum, which is the
  receiver's places and the fan-in's: `HNN/FinestGrain` (`receiverGrain_spec`, `latticeExponent_le_of_reach_le`,
  `remainder_below_every_tolerance`) and `Holonics/HNN/LatticeDeposit` (`remainder_below_grain`, `rem_bounds`: a word is a
  read part on its lattice and a carried part under half a unit);
* the carried release: `Foundation/CarriedRelease` (`release_conserves`, `release_tracks`, `plain_rounding_silences`,
  `release_keeps_constant_rate`);
* the code's move to second order, the mean's side: `Holonics/HNN/Ratio/Certificate` (`codeLength_add_le`) and
  `Holonics/HNN/Ratio/Resolution` (`grain_lemma`).

1. **A tail moves a code by at most twice its bound** (`face_tail_moves_code`, `face_tail_within`): a face
   `p(a) = e^(z_a) / Σ_b e^(z_b)` whose every exponent is known to within `B` has every symbol's code `−log p(a)`
   within `2B`. So a series, a chain of ticks or a word read from its top place down is released at the first place
   where twice its tail's bound is under the receiver's tolerance in code. The statement is on the density at every
   symbol: no symbol's rank and no top of the face enters it. It is the first-order bound at each symbol, beside the
   second-order bound on the mean that the certificate owns.
2. **A sum is formed channel by channel** (`channels_add`): a state whose residue on each of two coprime rings is the
   sum of the operands' residues there is the operands' sum on the ring of the product. No carry passes between the
   channels, so resolution multiplies across channels that meet while each stays as narrow as its own ring. That two
   coprime residues pin the state on the product ring is Mathlib's `Nat.modEq_and_modEq_iff_modEq_mul`, used as it stands.

The computational object is the helical pair interaction's receiving face read at a receiver's tolerance. Of the winding
guide's six objects this touches the helix (a word is a circle with its carry) and faces and placement (the place a tail
is released at); the pair, cell holonomy, the tube and the tower thread stay attached through the owners above.
-/

namespace Holonics.HNN.WidthTolerance

open Finset

/-- **A tail moves a code by at most twice its bound.** Two faces whose exponents differ by at most `B` at every
symbol give every symbol log-probabilities within `2B`: `B` from the symbol's own exponent and `B` from the
normalizer. -/
theorem face_tail_moves_code {ι : Type*} [Fintype ι] [Nonempty ι] (z z' : ι → ℝ) (B : ℝ)
    (h : ∀ b, |z' b - z b| ≤ B) (a : ι) :
    |Real.log (Real.exp (z' a) / ∑ b, Real.exp (z' b)) - Real.log (Real.exp (z a) / ∑ b, Real.exp (z b))|
      ≤ 2 * B := by
  have hS : 0 < ∑ b, Real.exp (z b) := Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty
  have hS' : 0 < ∑ b, Real.exp (z' b) := Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty
  have h1 : ∑ b, Real.exp (z' b) ≤ Real.exp B * ∑ b, Real.exp (z b) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have := (abs_le.mp (h b)).2
    linarith
  have h2 : ∑ b, Real.exp (z b) ≤ Real.exp B * ∑ b, Real.exp (z' b) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have := (abs_le.mp (h b)).1
    linarith
  have l1 : Real.log (∑ b, Real.exp (z' b)) ≤ B + Real.log (∑ b, Real.exp (z b)) := by
    have := Real.log_le_log hS' h1
    rwa [Real.log_mul (Real.exp_pos B).ne' hS.ne', Real.log_exp] at this
  have l2 : Real.log (∑ b, Real.exp (z b)) ≤ B + Real.log (∑ b, Real.exp (z' b)) := by
    have := Real.log_le_log hS h2
    rwa [Real.log_mul (Real.exp_pos B).ne' hS'.ne', Real.log_exp] at this
  rw [Real.log_div (Real.exp_pos _).ne' hS'.ne', Real.log_div (Real.exp_pos _).ne' hS.ne', Real.log_exp,
    Real.log_exp]
  have ha := abs_le.mp (h a)
  rw [abs_le]
  constructor <;> linarith [ha.1, ha.2]

/-- **The release of a tail.** Where twice the tail's bound is under the receiver's tolerance `ε` in code, no
symbol's code moves by more than `ε` when the tail is read. -/
theorem face_tail_within {ι : Type*} [Fintype ι] [Nonempty ι] (z z' : ι → ℝ) (B ε : ℝ)
    (h : ∀ b, |z' b - z b| ≤ B) (hB : 2 * B ≤ ε) (a : ι) :
    |Real.log (Real.exp (z' a) / ∑ b, Real.exp (z' b)) - Real.log (Real.exp (z a) / ∑ b, Real.exp (z b))|
      ≤ ε :=
  (face_tail_moves_code z z' B h a).trans hB

/-- **A sum is formed channel by channel.** A state whose residue on each of two coprime rings is the sum of the
operands' residues there is the operands' sum on the ring of the product: no carry passes between the channels. -/
theorem channels_add {m n : ℕ} (h : m.Coprime n) (x y s : ℕ) (hm : s % m = (x % m + y % m) % m)
    (hn : s % n = (x % n + y % n) % n) : s % (m * n) = (x + y) % (m * n) := by
  refine (Nat.modEq_and_modEq_iff_modEq_mul h).mp ⟨?_, ?_⟩
  · show s % m = (x + y) % m
    rw [hm]
    exact (Nat.add_mod x y m).symm
  · show s % n = (x + y) % n
    rw [hn]
    exact (Nat.add_mod x y n).symm

end Holonics.HNN.WidthTolerance
