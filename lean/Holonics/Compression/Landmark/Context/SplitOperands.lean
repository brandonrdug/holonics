import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Compression.Landmark.Context.SplitOperands: the lattice mixture read in split operands

[definition] A mixing node of the receiving tree reads its face on the lattice `2^(−M)ℤ` as the
nearest lattice numerator (ties up) of `λ̂ u/v + (1 − λ̂) x`, with the stop weight `λ̂ = stop/2^M`,
the node's KT face `u/v` and the deeper face `x/2^M` (module header of
`compression::landmark::context`, "The lattice mixture and the stop weight read split operands";
`Context/Tree`'s lattice path). Written over one denominator it is the single division

```text
N = stop·u·2^M + (2^M − stop)·x·v,   D = v·2^M,   ⟦N/D⟧ = ⌊(2N + D)/(2D)⌋
```

whose numerator needs `2M + κ + 3` bits (`u ≤ v < 2^κ`, `stop ≤ 2^M`, `x < 2^M`). That was the
card kernel's realization before #335. The host (`lattice_mix`, `context.rs`) and, since #335, the
card (`holonics-cuda`, `kernels/tree.cu`, `tree_mix`) divide each part with its remainder,

```text
a = stop·u = q_a v + r_a,   b = (2^M − stop)·x = q_b 2^M + r_b,
⟦N/D⟧ = q_a + q_b + ⌊(2 r_a 2^M + 2 r_b v + v 2^M)/(2 v 2^M)⌋,
```

and no operand passes `max(2M, M + κ + 3)` bits.

[proved-derived; formal-checked] This file proves both, for all naturals:
* **The split is the single division** (`split_round`, `latticeSplit_eq_single`): the two parts'
  quotients add to the rounding of their remainders' sum, which is the single division's rounding,
  for every `v > 0`, every `M` and every stop, KT face and deeper face, with no bound on any of
  them. The clamp into `[1, 2^M − 1]` is applied to the same integer on both sides
  (`latticeMix_eq_single`).
* **The split's operands fit `max(2M, M + κ + 3)` bits** (`split_operands_lt`): under the node's
  ranges, `a < 2^(M+κ)`, `b < 2^(2M)`, the half part's numerator `< 2^(M+κ+3)`, its denominator
  `< 2^(M+κ+1)` and the whole part `< 2^(M+1)`; the single division's numerator stays
  `< 2^(2M+κ+3)` (`single_numerator_lt`), which is the width the split avoids.

The Rust join is the host test `landmark_split_operands_are_the_single_division`
(`context/tests.rs`), which draws the operands at the declared widths and compares `lattice_mix`
with the single division in big integers. The computational object is the helical pair
interaction's receiving tree; of the winding guide's six general objects this touches **faces and
placement** (the lattice face) and the **helix** (the division's carry, the quotient, beside its
remainder); the pair, the cell holonomy, the tube and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Compression.Landmark.Context.SplitOperands

/-- [definition] **The single division** (`tree_round` on the card's one numerator): the integer
nearest `stop·u/v + (2^M − stop)·x/2^M` (ties up), the lattice numerator before the clamp. -/
def singleRound (M stop u v x : ℕ) : ℕ :=
  (2 * (stop * u * 2 ^ M + (2 ^ M - stop) * x * v) + v * 2 ^ M) / (2 * (v * 2 ^ M))

/-- [definition] **The split operands** (`lattice_mix` before its clamp): the whole part
`a/v + b/2^M` and the half part, the rounding of the two remainders' sum. -/
def latticeSplit (M stop u v x : ℕ) : ℕ :=
  stop * u / v + (2 ^ M - stop) * x / 2 ^ M +
    (2 * (stop * u % v) * 2 ^ M + 2 * ((2 ^ M - stop) * x % 2 ^ M) * v + v * 2 ^ M) /
      (2 * (v * 2 ^ M))

/-- [definition] The clamp into `[1, 2^M − 1]` (`clamp(1, (1 << face) − 1)`). -/
def clampFace (M n : ℕ) : ℕ := min (max n 1) (2 ^ M - 1)

/-- [definition] **The lattice mixture** (`lattice_mix`): the split operands, clamped. -/
def latticeMix (M stop u v x : ℕ) : ℕ := clampFace M (latticeSplit M stop u v x)

/-- [proved-derived; formal-checked] **A rounding divided in two parts**: for `v, F > 0`, each part
divided with its remainder, the quotients add to the rounding of the remainders' sum. -/
theorem split_round (a b v F : ℕ) (hv : 0 < v) (hF : 0 < F) :
    (2 * (a * F + b * v) + v * F) / (2 * (v * F)) =
      a / v + b / F + (2 * (a % v) * F + 2 * (b % F) * v + v * F) / (2 * (v * F)) := by
  have hD : 0 < 2 * (v * F) := by positivity
  conv_lhs => rw [← Nat.div_add_mod a v, ← Nat.div_add_mod b F]
  have h : 2 * ((v * (a / v) + a % v) * F + (F * (b / F) + b % F) * v) + v * F =
      (2 * (a % v) * F + 2 * (b % F) * v + v * F) + (a / v + b / F) * (2 * (v * F)) := by ring
  rw [h, Nat.add_mul_div_right _ _ hD]
  ring

/-- [proved-derived; formal-checked] **The split is the single division**, for every `v > 0` and
all naturals `M`, `stop`, `u`, `x`. -/
theorem latticeSplit_eq_single (M stop u x : ℕ) {v : ℕ} (hv : 0 < v) :
    latticeSplit M stop u v x = singleRound M stop u v x := by
  have h := split_round (stop * u) ((2 ^ M - stop) * x) v (2 ^ M) hv (by positivity)
  rw [singleRound, latticeSplit, ← h]

/-- [proved-derived; formal-checked] **The lattice mixture is the clamped single division**
(`lattice_mix` against the card's `tree_round`). -/
theorem latticeMix_eq_single (M stop u x : ℕ) {v : ℕ} (hv : 0 < v) :
    latticeMix M stop u v x = clampFace M (singleRound M stop u v x) := by
  rw [latticeMix, latticeSplit_eq_single M stop u x hv]

/-- [proved-derived; formal-checked] **The split's operands** under the node's ranges
(`stop ≤ 2^M`, `0 < v`, `u ≤ v < 2^κ`, `x < 2^M`): `a < 2^(M+κ)`, `b < 2^(2M)`, the half part's
numerator `< 2^(M+κ+3)` and denominator `< 2^(M+κ+1)`, the whole part `< 2^(M+1)`. -/
theorem split_operands_lt (M κ stop u v x : ℕ) (hs : stop ≤ 2 ^ M) (hv : 0 < v) (huv : u ≤ v)
    (hvk : v < 2 ^ κ) (hx : x < 2 ^ M) :
    stop * u < 2 ^ (M + κ) ∧ (2 ^ M - stop) * x < 2 ^ (2 * M) ∧
      2 * (stop * u % v) * 2 ^ M + 2 * ((2 ^ M - stop) * x % 2 ^ M) * v + v * 2 ^ M <
        2 ^ (M + κ + 3) ∧
      2 * (v * 2 ^ M) < 2 ^ (M + κ + 1) ∧
      stop * u / v + (2 ^ M - stop) * x / 2 ^ M < 2 ^ (M + 1) := by
  have hF : 0 < 2 ^ M := by positivity
  have hsub : 2 ^ M - stop ≤ 2 ^ M := Nat.sub_le _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc stop * u ≤ 2 ^ M * v := Nat.mul_le_mul hs huv
      _ < 2 ^ M * 2 ^ κ := Nat.mul_lt_mul_of_pos_left hvk hF
      _ = 2 ^ (M + κ) := (pow_add 2 M κ).symm
  · calc (2 ^ M - stop) * x ≤ 2 ^ M * x := Nat.mul_le_mul_right _ hsub
      _ < 2 ^ M * 2 ^ M := Nat.mul_lt_mul_of_pos_left hx hF
      _ = 2 ^ (2 * M) := by rw [two_mul, pow_add]
  · have hra : stop * u % v < v := Nat.mod_lt _ hv
    have hrb : (2 ^ M - stop) * x % 2 ^ M < 2 ^ M := Nat.mod_lt _ hF
    have h1 : 2 * (stop * u % v) * 2 ^ M ≤ 2 * v * 2 ^ M := by
      have := Nat.mul_le_mul_right (2 ^ M) (Nat.mul_le_mul_left 2 hra.le); linarith
    have h2 : 2 * ((2 ^ M - stop) * x % 2 ^ M) * v ≤ 2 * 2 ^ M * v := by
      have := Nat.mul_le_mul_right v (Nat.mul_le_mul_left 2 hrb.le); linarith
    have hvF : v * 2 ^ M < 2 ^ κ * 2 ^ M := Nat.mul_lt_mul_of_pos_right hvk hF
    have hpow : 2 ^ (M + κ + 3) = 8 * (2 ^ κ * 2 ^ M) := by rw [pow_add, pow_add]; ring
    rw [hpow]
    nlinarith
  · have hvF : v * 2 ^ M < 2 ^ κ * 2 ^ M := Nat.mul_lt_mul_of_pos_right hvk hF
    have hpow : 2 ^ (M + κ + 1) = 2 * (2 ^ κ * 2 ^ M) := by rw [pow_add, pow_add]; ring
    rw [hpow]
    omega
  · have ha : stop * u / v ≤ stop := by
      rw [Nat.div_le_iff_le_mul_add_pred hv]
      calc stop * u ≤ stop * v := Nat.mul_le_mul_left _ huv
        _ ≤ v * stop + (v - 1) := by rw [Nat.mul_comm]; exact Nat.le_add_right _ _
    have hb : (2 ^ M - stop) * x / 2 ^ M < 2 ^ M := by
      rw [Nat.div_lt_iff_lt_mul hF]
      calc (2 ^ M - stop) * x ≤ 2 ^ M * x := Nat.mul_le_mul_right _ hsub
        _ < 2 ^ M * 2 ^ M := Nat.mul_lt_mul_of_pos_left hx hF
    have hpow : 2 ^ (M + 1) = 2 * 2 ^ M := by rw [pow_succ]; ring
    rw [hpow]
    omega

/-- [proved-derived; formal-checked] **The split fits `max(2M, M + κ + 3)` bits**: every operand
of `split_operands_lt` is below `2^max(2M, M + κ + 3)`. -/
theorem split_operands_lt_max (M κ stop u v x : ℕ) (hs : stop ≤ 2 ^ M) (hv : 0 < v)
    (huv : u ≤ v) (hvk : v < 2 ^ κ) (hx : x < 2 ^ M) :
    stop * u < 2 ^ max (2 * M) (M + κ + 3) ∧
      (2 ^ M - stop) * x < 2 ^ max (2 * M) (M + κ + 3) ∧
      2 * (stop * u % v) * 2 ^ M + 2 * ((2 ^ M - stop) * x % 2 ^ M) * v + v * 2 ^ M <
        2 ^ max (2 * M) (M + κ + 3) ∧
      2 * (v * 2 ^ M) < 2 ^ max (2 * M) (M + κ + 3) ∧
      stop * u / v + (2 ^ M - stop) * x / 2 ^ M < 2 ^ max (2 * M) (M + κ + 3) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := split_operands_lt M κ stop u v x hs hv huv hvk hx
  have up : ∀ {n e : ℕ}, e ≤ max (2 * M) (M + κ + 3) → n < 2 ^ e →
      n < 2 ^ max (2 * M) (M + κ + 3) := fun he hn =>
    lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) he)
  exact ⟨up (by omega) h1, up (le_max_left _ _) h2, up (le_max_right _ _) h3, up (by omega) h4,
    up (by omega) h5⟩

/-- [proved-derived; formal-checked] **The single division's numerator** under the same ranges is
below `2^(2M + κ + 3)`: the width the card's one division needs and the split avoids. -/
theorem single_numerator_lt (M κ stop u v x : ℕ) (hs : stop ≤ 2 ^ M) (huv : u ≤ v)
    (hvk : v < 2 ^ κ) (hx : x < 2 ^ M) :
    2 * (stop * u * 2 ^ M + (2 ^ M - stop) * x * v) + v * 2 ^ M < 2 ^ (2 * M + κ + 3) := by
  have hF : 0 < 2 ^ M := by positivity
  have hsub : 2 ^ M - stop ≤ 2 ^ M := Nat.sub_le _ _
  have ha : stop * u * 2 ^ M ≤ 2 ^ M * 2 ^ κ * 2 ^ M :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul hs (huv.trans hvk.le))
  have hb : (2 ^ M - stop) * x * v ≤ 2 ^ M * 2 ^ M * 2 ^ κ :=
    Nat.mul_le_mul (Nat.mul_le_mul hsub hx.le) hvk.le
  have hc : v * 2 ^ M < 2 ^ κ * 2 ^ M := Nat.mul_lt_mul_of_pos_right hvk hF
  have hc' : 2 ^ κ * 2 ^ M ≤ 2 ^ M * 2 ^ κ * 2 ^ M := by
    have : 1 ≤ 2 ^ M := hF
    nlinarith [Nat.zero_le (2 ^ κ * 2 ^ M)]
  have hpow : 2 ^ (2 * M + κ + 3) = 8 * (2 ^ M * 2 ^ κ * 2 ^ M) := by
    rw [pow_add, pow_add, two_mul, pow_add]; ring
  rw [hpow]
  nlinarith

end Holonics.Compression.Landmark.Context.SplitOperands

#print axioms Holonics.Compression.Landmark.Context.SplitOperands.split_round
#print axioms Holonics.Compression.Landmark.Context.SplitOperands.latticeSplit_eq_single
#print axioms Holonics.Compression.Landmark.Context.SplitOperands.latticeMix_eq_single
#print axioms Holonics.Compression.Landmark.Context.SplitOperands.split_operands_lt
#print axioms Holonics.Compression.Landmark.Context.SplitOperands.split_operands_lt_max
#print axioms Holonics.Compression.Landmark.Context.SplitOperands.single_numerator_lt
