import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Compression.Landmark.Context.SplitOperands: the lattice mixture and stop weight in split operands

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
* **The stop weight is the exact rounding** (`stopWeightAbove_eq`, `stopWeightBelow_eq`): the
  host's `Beta::stop_weight` and the card's `tree_stop_weight` return `⟦2^M β/(1 + β)⟧` for
  `β = (a/b)·2^e`, every `M`, `e` and positive `a`, `b`. Where one side of `1 + β` passes the other
  by `2^(M+1)`, read from the sides' bits (`Nat.size`, the Rust's `bits128`) before any division,
  the weight is decided at `2^M` or `0`: the other side's share is below half a lattice step, so
  the decided value is the rounding. Otherwise the division is the rounding itself, written at
  `e ≥ 0` as `2^M − ⌈(2^(M+1) b − g)/(2g)⌉` (`round_above`). Its operands stay below
  `2^(M+3+bits b)` at `e ≥ 0` and `2^(M+3+bits a)` at `e < 0` (`stop_operands_above_lt`,
  `stop_operands_below_lt`): `M + W + 3` bits on the carrier.

The Rust joins are the host tests `landmark_split_operands_are_the_single_division`
(`context/tests.rs`), which draws the operands at the declared widths and compares `lattice_mix`
with the single division in big integers, and `landmark_stop_weight_rounds_exactly`, which compares
`stop_weight` with the rounding in ℚ for exponents past `±(M + W)`. The computational object is
the helical pair interaction's receiving tree; of the winding guide's six general objects this
touches **faces and placement** (the lattice face) and the **helix** (the division's carry, the
quotient, beside its remainder); the pair, the cell holonomy, the tube and the tower thread stay
attached.

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

/-! ## The stop weight's bits decision -/

/-- [definition] **The exact rounding** `⟦p/q⟧ = ⌊p/q + ½⌋`, nearest with ties up, for `q > 0`. -/
def roundUp (p q : ℕ) : ℕ := (2 * p + q) / (2 * q)

/-- [definition] **The stop weight at `e ≥ 0`** (`Beta::stop_weight`, `context.rs`, and the card's
`tree_stop_weight`): `β = (a/b)·2^e`. When `e + bits a ≥ M + 2 + bits b` the weight is decided at
`2^M` before any division; otherwise `2^M − ⌈(t − g)/(2g)⌉`, `t = 2^(M+1) b`, `g = a 2^e + b`, the
ceiling `0` when `t ≤ g`. `bits` is `Nat.size`, the Rust's `bits128`. -/
def stopWeightAbove (M a b e : ℕ) : ℕ :=
  if M + 2 + Nat.size b ≤ e + Nat.size a then 2 ^ M
  else
    2 ^ M - (if 2 ^ (M + 1) * b ≤ a * 2 ^ e + b then 0
      else (2 ^ (M + 1) * b - (a * 2 ^ e + b) + (2 * (a * 2 ^ e + b) - 1)) /
        (2 * (a * 2 ^ e + b)))

/-- [definition] **The stop weight at `e = −s < 0`**: `β = a/(b 2^s)`. When
`s + bits b ≥ M + 2 + bits a` the weight is decided at `0`; otherwise
`⌊(2^(M+1) a + h)/(2h)⌋`, `h = a + b 2^s`. -/
def stopWeightBelow (M a b s : ℕ) : ℕ :=
  if M + 2 + Nat.size a ≤ s + Nat.size b then 0
  else (2 ^ (M + 1) * a + (a + b * 2 ^ s)) / (2 * (a + b * 2 ^ s))

/-- [proved-derived; formal-checked] A positive natural is at least `2^(bits n − 1)`. -/
theorem two_pow_pred_size_le {n : ℕ} (hn : 0 < n) : 2 ^ (Nat.size n - 1) ≤ n := by
  have h : Nat.size n - 1 < Nat.size n := Nat.sub_lt (Nat.size_pos.mpr hn) one_pos
  exact Nat.lt_size.mp h

/-- [proved-derived; formal-checked] **The undecided rounding above one**: with `g = A + b > 0`,
`⟦2^M A/g⟧ = 2^M − ⌈(2^(M+1) b − g)/(2g)⌉`, the ceiling `0` when `2^(M+1) b ≤ g`. -/
theorem round_above (M A b : ℕ) (hg : 0 < A + b) :
    roundUp (2 ^ M * A) (A + b) =
      2 ^ M - (if 2 ^ (M + 1) * b ≤ A + b then 0
        else (2 ^ (M + 1) * b - (A + b) + (2 * (A + b) - 1)) / (2 * (A + b))) := by
  unfold roundUp
  set g := A + b with hgdef
  set n := 2 * g with hn
  have hnpos : 0 < n := by omega
  have hY : 2 * (2 ^ M * A) + 2 ^ (M + 1) * b = 2 ^ M * n := by
    rw [hn, hgdef, pow_succ]; ring
  split_ifs with ht
  · rw [Nat.sub_zero]
    apply Nat.div_eq_of_lt_le
    · generalize 2 * (2 ^ M * A) = X at hY ⊢
      generalize 2 ^ M * n = Y at hY ⊢
      omega
    · rw [add_mul, one_mul]
      generalize 2 * (2 ^ M * A) = X at hY ⊢
      generalize 2 ^ M * n = Y at hY ⊢
      omega
  · set t := 2 ^ (M + 1) * b with htdef
    set d := t - g with hd
    set c := (d + (n - 1)) / n with hc
    have hcn1 : n * c ≤ d + (n - 1) := Nat.mul_div_le _ _
    have hcn2 : d + (n - 1) < n * (c + 1) := by
      rw [hc]; exact Nat.lt_mul_div_succ _ hnpos
    rw [mul_add, mul_one] at hcn2
    have htle : t ≤ 2 ^ M * n := by omega
    have hcle : c ≤ 2 ^ M := by
      have : n * c < n * (2 ^ M + 1) := by
        rw [mul_add, mul_one, mul_comm n (2 ^ M)]; omega
      have := Nat.lt_of_mul_lt_mul_left this
      omega
    obtain ⟨k, hk⟩ : ∃ k, 2 ^ M = k + c := ⟨2 ^ M - c, by omega⟩
    generalize 2 * (2 ^ M * A) = X at hY ⊢
    rw [hk, Nat.add_sub_cancel]
    rw [hk, add_mul, mul_comm c n] at hY
    apply Nat.div_eq_of_lt_le
    · generalize k * n = K at hY ⊢
      generalize n * c = C at hY hcn1 hcn2 ⊢
      omega
    · rw [add_mul, one_mul]
      generalize k * n = K at hY ⊢
      generalize n * c = C at hY hcn1 hcn2 ⊢
      omega

/-- [proved-derived; formal-checked] **The stop weight is the exact rounding at `e ≥ 0`**:
`stopWeightAbove = ⟦2^M β/(1 + β)⟧ = ⟦2^M a 2^e/(a 2^e + b)⟧` for every `M`, `e` and positive
`a`, `b`. In the decided case `a 2^e > 2^(M+1) b`, so the discarded share `2^M b/g` is below half
a lattice step. -/
theorem stopWeightAbove_eq (M a b e : ℕ) (ha : 0 < a) (hb : 0 < b) :
    stopWeightAbove M a b e = roundUp (2 ^ M * (a * 2 ^ e)) (a * 2 ^ e + b) := by
  have hg : 0 < a * 2 ^ e + b := by positivity
  rw [round_above M (a * 2 ^ e) b hg]
  unfold stopWeightAbove
  by_cases hdec : M + 2 + Nat.size b ≤ e + Nat.size a
  · rw [if_pos hdec]
    have h1 : 2 ^ (M + 1 + Nat.size b) ≤ a * 2 ^ e := by
      calc 2 ^ (M + 1 + Nat.size b) ≤ 2 ^ (Nat.size a - 1 + e) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 ^ (Nat.size a - 1) * 2 ^ e := pow_add _ _ _
        _ ≤ a * 2 ^ e := Nat.mul_le_mul_right _ (two_pow_pred_size_le ha)
    have h2 : 2 ^ (M + 1) * b < 2 ^ (M + 1 + Nat.size b) := by
      rw [pow_add 2 (M + 1)]
      exact Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self _) (by positivity : 0 < 2 ^ (M + 1))
    rw [if_pos (by omega), Nat.sub_zero]
  · rw [if_neg hdec]

/-- [proved-derived; formal-checked] **The stop weight is the exact rounding at `e = −s`**:
`stopWeightBelow = ⟦2^M a/(a + b 2^s)⟧` for every `M`, `s`, `a` and positive `b`. In the decided
case `b 2^s > 2^(M+1) a`, so the share `2^M a/h` is below half a lattice step. -/
theorem stopWeightBelow_eq (M a b s : ℕ) (hb : 0 < b) :
    stopWeightBelow M a b s = roundUp (2 ^ M * a) (a + b * 2 ^ s) := by
  unfold stopWeightBelow roundUp
  split_ifs with hdec
  · symm; apply Nat.div_eq_of_lt
    have h1 : 2 ^ (M + 1 + Nat.size a) ≤ b * 2 ^ s := by
      calc 2 ^ (M + 1 + Nat.size a) ≤ 2 ^ (Nat.size b - 1 + s) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 ^ (Nat.size b - 1) * 2 ^ s := pow_add _ _ _
        _ ≤ b * 2 ^ s := Nat.mul_le_mul_right _ (two_pow_pred_size_le hb)
    have h2 : 2 ^ (M + 1) * a < 2 ^ (M + 1 + Nat.size a) ∨ a = 0 := by
      rcases Nat.eq_zero_or_pos a with h | h
      · right; exact h
      · left
        rw [pow_add 2 (M + 1)]
        exact Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self _) (by positivity : 0 < 2 ^ (M + 1))
    have h3 : 2 * (2 ^ M * a) = 2 ^ (M + 1) * a := by rw [pow_succ]; ring
    have h4 : 0 < b * 2 ^ s := by positivity
    rcases h2 with h2 | h2
    · omega
    · subst h2; simp; omega
  · congr 1; rw [pow_succ]; ring

/-- [proved-derived; formal-checked] **The stop weight's operands at `e ≥ 0`**: undecided, with
`a 2^e + b = g`, the target `t = 2^(M+1) b < 2^(M+1+bits b)`, the ceiling's numerator, at most
`t + g`, and its denominator `2g` stay below `2^(M+3+bits b)`: `M + W + 3` bits for `b < 2^W`. -/
theorem stop_operands_above_lt (M a b e : ℕ) (hdec : ¬M + 2 + Nat.size b ≤ e + Nat.size a) :
    2 ^ (M + 1) * b < 2 ^ (M + 1 + Nat.size b) ∧
      2 ^ (M + 1) * b + (a * 2 ^ e + b) < 2 ^ (M + 3 + Nat.size b) ∧
      2 * (a * 2 ^ e + b) < 2 ^ (M + 3 + Nat.size b) := by
  have hb : b < 2 ^ Nat.size b := Nat.lt_size_self _
  have ha : a * 2 ^ e < 2 ^ (M + 1 + Nat.size b) := by
    calc a * 2 ^ e < 2 ^ Nat.size a * 2 ^ e :=
          Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self _) (by positivity)
      _ = 2 ^ (Nat.size a + e) := (pow_add _ _ _).symm
      _ ≤ 2 ^ (M + 1 + Nat.size b) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have ht : 2 ^ (M + 1) * b < 2 ^ (M + 1 + Nat.size b) := by
    rw [pow_add 2 (M + 1)]
    exact Nat.mul_lt_mul_of_pos_left hb (by positivity : 0 < 2 ^ (M + 1))
  have hsb : 2 ^ Nat.size b ≤ 2 ^ (M + 1 + Nat.size b) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ (M + 3 + Nat.size b) = 4 * 2 ^ (M + 1 + Nat.size b) := by
    rw [show M + 3 + Nat.size b = (M + 1 + Nat.size b) + 2 by omega, pow_add]; ring
  refine ⟨ht, ?_, ?_⟩ <;> omega

/-- [proved-derived; formal-checked] **The stop weight's operands at `e = −s`**: undecided, with
`h = a + b 2^s`, the numerator `2^(M+1) a + h` and the denominator `2h` stay below
`2^(M+3+bits a)`. -/
theorem stop_operands_below_lt (M a b s : ℕ) (hdec : ¬M + 2 + Nat.size a ≤ s + Nat.size b) :
    2 ^ (M + 1) * a + (a + b * 2 ^ s) < 2 ^ (M + 3 + Nat.size a) ∧
      2 * (a + b * 2 ^ s) < 2 ^ (M + 3 + Nat.size a) := by
  have ha : a < 2 ^ Nat.size a := Nat.lt_size_self _
  have hb : b * 2 ^ s < 2 ^ (M + 1 + Nat.size a) := by
    calc b * 2 ^ s < 2 ^ Nat.size b * 2 ^ s :=
          Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self _) (by positivity)
      _ = 2 ^ (Nat.size b + s) := (pow_add _ _ _).symm
      _ ≤ 2 ^ (M + 1 + Nat.size a) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have ht : 2 ^ (M + 1) * a < 2 ^ (M + 1 + Nat.size a) := by
    rw [pow_add 2 (M + 1)]
    exact Nat.mul_lt_mul_of_pos_left ha (by positivity : 0 < 2 ^ (M + 1))
  have hsa : 2 ^ Nat.size a ≤ 2 ^ (M + 1 + Nat.size a) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ (M + 3 + Nat.size a) = 4 * 2 ^ (M + 1 + Nat.size a) := by
    rw [show M + 3 + Nat.size a = (M + 1 + Nat.size a) + 2 by omega, pow_add]; ring
  constructor <;> omega

end Holonics.Compression.Landmark.Context.SplitOperands

#print axioms Holonics.Compression.Landmark.Context.SplitOperands.split_round
#print axioms Holonics.Compression.Landmark.Context.SplitOperands.latticeSplit_eq_single
#print axioms Holonics.Compression.Landmark.Context.SplitOperands.latticeMix_eq_single
#print axioms Holonics.Compression.Landmark.Context.SplitOperands.split_operands_lt
#print axioms Holonics.Compression.Landmark.Context.SplitOperands.split_operands_lt_max
#print axioms Holonics.Compression.Landmark.Context.SplitOperands.single_numerator_lt
#print axioms Holonics.Compression.Landmark.Context.SplitOperands.round_above
#print axioms Holonics.Compression.Landmark.Context.SplitOperands.stopWeightAbove_eq
#print axioms Holonics.Compression.Landmark.Context.SplitOperands.stopWeightBelow_eq
#print axioms Holonics.Compression.Landmark.Context.SplitOperands.stop_operands_above_lt
#print axioms Holonics.Compression.Landmark.Context.SplitOperands.stop_operands_below_lt
