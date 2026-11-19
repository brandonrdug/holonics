import HolonicsResearch.Landmarks.ClosureKeyTorsion

/-!
# The closure key's menus: operands below `b³`, the reflected difference, and one key for sums and differences

[proved-derived; formal-checked] Formal obligations (#410), the box "The closure key's torsion (#405)". Sources: the
record of October 25 on the newline closure (`research/records/2026-10-25_THE_NEWLINE_CLOSURE_HAS_TORSION_B_TIMES_B_*`,
§§4, 5, 6, 10, 11 and "Owed"; its receipt `closure_reflection.py`, whose `hands` the hands here follow); atlas
`key.newline-closure-torsion`, `key.newline-closure-differences`, `key.newline-closure-reflection`. It continues
`Landmarks/ClosureKeyTorsion` and reuses its `SumKey`, `DiffKey`, their readings and §5's solution.

What is proved, for keys linear in the digit values, in §5's gauge (`ψ(d) = s d`) and line-shape reading.

1. **Operands below `b³` (§6).** `wideOperand`, `wideResult` and `wideClosure` read an operand of up to three places,
   `(seam, d₂)(d₂, d₁)(d₁, d₀)(d₀, sep)`, and a result of up to four, with `SumKey`'s shared moves; below `b²` the
   reading is §5's (`wideClosure_of_lt`). A key closing every true line `x + y = c` with `x, y < b³` has `2 s b = 0`
   beside `s b (b + 1) = 0`, so `s b (b − 1) = 0` (`wide_necessity`). Where `b(b − 1) = 0` and `b(b + 1) = 0`, §5's
   solution closes every such line to `s (x + y − c)` (`wide_ofScale_closure`, through `ofScale_operand`,
   `ofScale_result`, `three_places`, `four_places`). So a key with `s` a unit exists exactly where both vanish
   (`wide_exists_iff`); modulo `q` exactly when `q ∣ b·gcd(2, b + 1)` (`wide_zmod_exists_iff`, through
   `gcd(b − 1, b + 1) = gcd(2, b + 1)`, `gcd_pred_succ`), which is `q ∣ b` in an even base and `q ∣ 2b` in an odd
   one; and modulo a prime `p` exactly when `p ∣ 2b` (`wide_prime_exists_iff`). In base 10 the key modulo 10 closes
   every line to `x + y − c`, and no key exists modulo 11 or modulo 20 (`wide_ten`).
2. **Differences with the hand reversible (§11).** `Hands` holds the hands a difference line's pairs are counted
   in: the subtrahend's (from the seam `−` to the pair into `=`), the result's (from the seam `=`) and `c₀`'s, with
   §11's (`Hands.plain`, `Hands.minus`, `Hands.minusInForce`, `Hands.minusRestart`, `Hands.equals`); `diffClosure`
   reads `DiffKey`'s moves in them, and with no reflector it is §10's reading (`diffClosure_plain`). With `−`
   reflecting, whatever the hands at `=` and of `c₀`, a key closing every true difference with `y ≤ x < b²` closes
   every line `x − y = c` it reads to `fin · s (x − y − c)` (`minus_forced`, six lines), so in characteristic zero,
   with `s` and `fin` units, it closes `x − y = c` exactly when `x = y + c` (`minus_tells_apart`): every result is
   told apart. The key `minusKey s r b` (`u ≡ u⁻ ≡ w ≡ 0`, `z ≡ z⁼ ≡ s`, `v ≡ s b`, `u′ ≡ −r s b`, `r` the result's
   hand) closes every line to `s (x − y − c)` over any ring and base (`minusKey_closure`), so a key with `s = 1`
   exists over every ring, restarted at `=` or not (`minus_exists`, `minus_exists_both`): no torsion. With `=`
   reflecting instead, a line reads as §10's with `u′` reversed (`diffClosure_equals`), so a key exists modulo `q`
   exactly when `q ∣ 2b`, as with no reflector (`equals_zmod_exists_iff`).
3. **One menu, `−` reflecting and `=` restarting (§11).** `MenuKey` extends `DiffKey` with `u⁺` after `+` and `z⁺`
   before `+`, every separator its own moves; a sum line is read through two `SumKey`s (`first`, `second`,
   `sumClosure`) in the starting hand, a difference line by `diffClosure`, and `Closes` asks every true line of both
   families. On the sum lines alone §4's shared moves are forced and `s b (b + 1) = 0` (`sum_moves`, eight lines), so
   §5's necessity needs no shared move. The menu's solution `MenuKey.ofScale` closes every sum to `s (x + y − c)`
   where `b(b + 1) = 0` (`ofScale_sumClosure`) and, with `−` reflecting and `=` restarting, every difference to
   `s (x − y − c)` over any ring (`ofScale_restart_closure`). So a key with `s` a unit exists exactly where
   `b(b + 1) = 0` (`restart_exists_iff`), modulo `q` exactly when `q ∣ b(b + 1)` (`restart_zmod_exists_iff`); modulo
   `b(b + 1)` the key closes `x + y = c` exactly when `x + y ≡ c` and `x − y = c` exactly when `x ≡ y + c`: it reads
   `c mod b(b + 1)` in both families (`restart_reads`), in base 10 modulo 110 (`torsion110_menu`).
4. **The menu's other hands (§11's table).** With no reflector, `2 s = 0` (`plain_necessity`: the shared `(y, =)`
   takes an addend's units `+s` and a subtrahend's `−s`), and a key exists exactly where `2 = 0`, modulo `q` when
   `q ∣ 2` (`plain_exists_iff`, `plain_zmod_exists_iff`, through `ofScale_plain_closure` and `two_mul_succ_cast`).
   With `−` reflecting alone and `c₀` in the starting hand, `2 s b = 0` beside `s b (b + 1) = 0` (`minus_necessity`),
   and a key exists exactly where `b(b + 1) = 0` and `2b = 0` (`minus_exists_iff`, through `ofScale_minus_closure`),
   modulo `q` when `q ∣ b·gcd(2, b + 1)`, `q ∣ 10` in base 10 (`minus_zmod_exists_iff`). With `−` reflecting and
   `c₀` in the hand in force, `2 s = 0` (`inForce_necessity`), and a key exists exactly where `2 = 0`, modulo `q`
   when `q ∣ 2` (`inForce_exists_iff`, `inForce_zmod_exists_iff`, through `ofScale_inForce_closure`).

Where the record's statement and the one proved here differ.
- Operands below `b³`: the record's "exactly when `p ∣ 2b`" (Owed) and "the torsion primes are those of `2b`" (§6)
  hold for a prime modulus (`wide_prime_exists_iff`). For a modulus `q` the condition is `q ∣ b·gcd(2, b + 1)`, not
  `q ∣ 2b`: in base 10 no key exists modulo 20 (`wide_ten`) or 4, where §10's differences have one modulo 20.
- §5 derives `s b (b + 1) = 0` with §4's shared moves; `sum_moves` derives the shared moves from the sum lines, so the
  condition holds for linear keys with every separator its own moves, in the two-place menu and in the mixed one.
- With `−` reflecting and no restart the result's pair `(=, c₁)` is in the reversed hand too, so the key's `u′` is
  `+s b` there and `−s b` with `=` restarting (`minusKey`); §11 states the subtrahend's reversal, and both hands close
  every line to `s (x − y − c)`.

What is not claimed.
- The torsion of a general pair key, every pair its own move: §6's and §11's tables are computations over the finite
  line sets (§6 in bases 3 to 8 and 10, §11's menus in base 10). The theorems here are for keys linear in the digit
  values.
- The mixed menu and the reflecting hands with operands below `b³`, and §9's split by each operand's length at three
  places, which the record owes as a check.
- That a closure is read from a line's bytes: the closures are the pair sums read by the line's shape, as in
  `ClosureKeyTorsion`; `minus_forced` and the closure formulas are statements about those readings.
- The pair into the reflector, `(x₀, −)`, is counted in the starting hand (a reflector reverses the hand where it is
  met as a seam, the receipt's `hands`); its move `z` meets no other pair, so the reading that reverses it changes no
  statement here but the sign of `z`.
- §8's and §11's readings (the missing move as the reflection, the inverse chart, the antilinear involutions), which
  the record marks agent-inferred.

The computational object is the helical pair interaction read on a closure's menu: each (seam, arriving class) pair
is a contact whose move turns a ring, counted in the hand in force at its seam; a reflector byte reverses the hand
(the ring read through the conjugation, `HNN/RingHand`), a restart returns it, and the two compose into a turn, so that
with `−` reflecting and `=` restarting a difference is read as a sum and one key carries both families. Of the winding
guide's six general objects this touches the pair (the contacts' moves, each separator its own), the helix (a ring's
residue and its hand) and faces and placement (a digit's place weight `bᵏ`; at three places the weight must read
`b² = b` and `b² = −b` at once, which leaves `b` and the parity); the cell holonomy, the tube and the tower thread stay
attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

open Holonics.Landmarks.ClosureKeyTorsion

namespace Holonics.Landmarks.ClosureKeyMenus

/-! ## 1. Operands below `b³` -/

section Wide

/-- [proved-derived; formal-checked] `gcd(b − 1, b + 1) = gcd(2, b + 1)`: the base's two neighbours share at most the
parity. -/
theorem gcd_pred_succ {b : ℕ} (hb : 1 ≤ b) : Nat.gcd (b - 1) (b + 1) = Nat.gcd 2 (b + 1) := by
  have e1 : b + 1 = 2 + (b - 1) := by omega
  rw [e1, Nat.gcd_add_self_right, Nat.gcd_comm, Nat.gcd_self_add_right]

/-- [proved-derived; formal-checked] A number's places, three read: `c = b² (c / b²) + b (c / b mod b) + c mod b`. -/
theorem three_places (b c : ℕ) : c = b ^ 2 * (c / b ^ 2) + b * (c / b % b) + c % b := by
  have h1 := Nat.div_add_mod c b
  have h2 := Nat.div_add_mod (c / b) b
  rw [Nat.div_div_eq_div_mul, ← pow_two] at h2
  nlinarith [h1, h2]

/-- [proved-derived; formal-checked] A number's places, four read. -/
theorem four_places (b c : ℕ) :
    c = b ^ 3 * (c / b ^ 3) + b ^ 2 * (c / b ^ 2 % b) + b * (c / b % b) + c % b := by
  have h1 := Nat.div_add_mod c b
  have h2 := Nat.div_add_mod (c / b) b
  have h3 := Nat.div_add_mod (c / b ^ 2) b
  rw [Nat.div_div_eq_div_mul, ← pow_two] at h2
  rw [Nat.div_div_eq_div_mul, ← pow_succ] at h3
  nlinarith [h1, h2, h3]

variable {R : Type*} [CommRing R] (κ : SumKey R) (b : ℕ)

/-- [definition] An operand of one to three places; `d₂d₁d₀` meets `(seam, d₂)(d₂, d₁)(d₁, d₀)(d₀, sep)`. -/
def wideOperand (x : ℕ) : R :=
  if x < b ^ 2 then κ.operand b x
  else (κ.u + κ.v) * ((x / b ^ 2 : ℕ) : R) + (κ.v + κ.w) * ((x / b % b : ℕ) : R) +
    (κ.w + κ.z) * ((x % b : ℕ) : R)

/-- [definition] A result of one to four places; `c₃c₂c₁c₀` meets `(=, c₃)(c₃, c₂)(c₂, c₁)`, less `ψ(c₀)`. -/
def wideResult (c : ℕ) : R :=
  if c < b ^ 3 then κ.result b c
  else (κ.u' + κ.v) * ((c / b ^ 3 : ℕ) : R) + (κ.v + κ.w) * ((c / b ^ 2 % b : ℕ) : R) +
    κ.w * ((c / b % b : ℕ) : R) - κ.s * ((c % b : ℕ) : R)

/-- [definition] A sum line's closure with operands of up to three places. -/
def wideClosure (x y c : ℕ) : R := wideOperand κ b x + wideOperand κ b y + wideResult κ b c

/-- [proved-derived; formal-checked] With operands below `b²` and a result below `b³` the wide reading is §5's. -/
theorem wideClosure_of_lt {x y c : ℕ} (hx : x < b ^ 2) (hy : y < b ^ 2) (hc : c < b ^ 3) :
    wideClosure κ b x y c = κ.closure b x y c := by
  rw [wideClosure, wideOperand, wideOperand, wideResult, if_pos hx, if_pos hy, if_pos hc]
  rfl

/-- [proved-derived; formal-checked] A three-place operand `b² d₂ + b d₁ + d₀`. -/
theorem wideOperand_three {d₂ d₁ d₀ : ℕ} (h₀ : d₀ < b) (h₁ : d₁ < b) (h₂ : 1 ≤ d₂) :
    wideOperand κ b (b ^ 2 * d₂ + b * d₁ + d₀) =
      (κ.u + κ.v) * (d₂ : R) + (κ.v + κ.w) * (d₁ : R) + (κ.w + κ.z) * (d₀ : R) := by
  have hlt : ¬ b ^ 2 * d₂ + b * d₁ + d₀ < b ^ 2 := by nlinarith
  obtain ⟨e2, e1, e0⟩ := SumKey.div_mod_three b (d₂ := d₂) h₀ h₁
  rw [wideOperand, if_neg hlt, e2, e1, e0]

/-- [proved-derived; formal-checked] A three-place result `b² d₂ + b d₁ + d₀`. -/
theorem wideResult_three {d₂ d₁ d₀ : ℕ} (h₀ : d₀ < b) (h₁ : d₁ < b) (h₂ : 1 ≤ d₂) (h₂' : d₂ < b) :
    wideResult κ b (b ^ 2 * d₂ + b * d₁ + d₀) =
      (κ.u' + κ.v) * (d₂ : R) + κ.w * (d₁ : R) - κ.s * (d₀ : R) := by
  have hlt : b ^ 2 * d₂ + b * d₁ + d₀ < b ^ 3 := by
    have : b * d₁ + d₀ < b ^ 2 := by nlinarith
    have : b ^ 2 * d₂ + b ^ 2 ≤ b ^ 3 := by nlinarith
    omega
  rw [wideResult, if_pos hlt, SumKey.result_three κ b h₀ h₁ h₂]

/-- [proved-derived; formal-checked] Statement 1: a key closing every true sum with operands below `b³` has `2 s b = 0`,
`s b (b + 1) = 0` and so `s b (b − 1) = 0` (lines `1 + 0`, `(b − 1) + 1`, `(b + 1) + 0`, `b + 0`, `(b² + b) + 0`). -/
theorem wide_necessity (hb : 2 ≤ b)
    (h : ∀ x y, x < b ^ 3 → y < b ^ 3 → wideClosure κ b x y (x + y) = 0) :
    2 * κ.s * (b : R) = 0 ∧ κ.s * (b : R) * ((b : R) + 1) = 0 ∧ κ.s * (b : R) * ((b : R) - 1) = 0 := by
  have hb3 : b ^ 2 * 2 ≤ b ^ 3 := by rw [pow_succ]; exact Nat.mul_le_mul_left _ hb
  have hn : ∀ x y, x < b ^ 2 → y < b ^ 2 → κ.closure b x y (x + y) = 0 := by
    intro x y hx hy
    rw [← wideClosure_of_lt κ b hx hy (by omega)]
    exact h x y (by omega) (by omega)
  have hS := κ.sum_necessity b hb hn
  have h' : ∀ x y c, x < b ^ 2 → y < b ^ 2 → c = x + y → κ.closure b x y c = 0 :=
    fun x y c hx hy hc => hc ▸ hn x y hx hy
  have hw : ∀ x y c, x < b ^ 3 → y < b ^ 3 → c = x + y → wideClosure κ b x y c = 0 :=
    fun x y c hx hy hc => hc ▸ h x y hx hy
  have h2 : 2 * κ.s * (b : R) = 0 := by
    obtain ⟨k, rfl⟩ : ∃ k, b = k + 2 := ⟨b - 2, by omega⟩
    have A := h' 1 0 1 (by nlinarith) (by nlinarith) rfl
    rw [SumKey.closure, SumKey.operand_one κ (k + 2) (by omega : 1 < k + 2),
      SumKey.operand_one κ (k + 2) (by omega : 0 < k + 2), SumKey.result_one κ (k + 2) (by omega : 1 < k + 2)] at A
    have B := h' (k + 1) 1 ((k + 2) * 1 + 0) (by nlinarith) (by nlinarith) (by ring)
    rw [SumKey.closure, SumKey.operand_one κ (k + 2) (by omega : k + 1 < k + 2),
      SumKey.operand_one κ (k + 2) (by omega : 1 < k + 2),
      SumKey.result_two κ (k + 2) (by omega) le_rfl (by omega)] at B
    have C := h' ((k + 2) * 1 + 1) 0 ((k + 2) * 1 + 1) (by nlinarith) (by nlinarith) (by ring)
    rw [SumKey.closure, SumKey.operand_two κ (k + 2) (by omega) le_rfl,
      SumKey.operand_one κ (k + 2) (by omega : 0 < k + 2),
      SumKey.result_two κ (k + 2) (by omega) le_rfl (by omega)] at C
    have G := h' ((k + 2) * 1 + 0) 0 ((k + 2) * 1 + 0) (by nlinarith) (by nlinarith) (by ring)
    rw [SumKey.closure, SumKey.operand_two κ (k + 2) (by omega) le_rfl,
      SumKey.operand_one κ (k + 2) (by omega : 0 < k + 2),
      SumKey.result_two κ (k + 2) (by omega) le_rfl (by omega)] at G
    have H := hw ((k + 2) ^ 2 * 1 + (k + 2) * 1 + 0) 0 ((k + 2) ^ 2 * 1 + (k + 2) * 1 + 0)
      (by nlinarith) (by positivity) (by ring)
    have h0 : wideOperand κ (k + 2) 0 = 0 := by
      rw [wideOperand, if_pos (by positivity), SumKey.operand_one κ (k + 2) (by omega : 0 < k + 2)]
      simp
    rw [wideClosure, wideOperand_three κ (k + 2) (by omega) (by omega) le_rfl, h0,
      wideResult_three κ (k + 2) (by omega) (by omega) le_rfl (by omega)] at H
    push_cast at A B C G H ⊢
    linear_combination H - G + 2 * B - 2 * C - 2 * ((k : R) + 1) * A
  refine ⟨h2, hS, ?_⟩
  linear_combination hS - h2

/-- [proved-derived; formal-checked] §5's solution reads every operand as `s x`, over any ring. -/
theorem ofScale_operand (s : R) (t : ℕ) : (SumKey.ofScale s b).operand b t = s * t := by
  unfold SumKey.operand
  split_ifs
  · simp only [SumKey.ofScale]; ring
  · conv_rhs => rw [← Nat.div_add_mod t b]
    simp only [SumKey.ofScale]; push_cast; ring

/-- [proved-derived; formal-checked] Where `b(b + 1) = 0`, §5's solution reads every result as `−s c`. -/
theorem ofScale_result (s : R) (hR : ((b * (b + 1) : ℕ) : R) = 0) (c : ℕ) :
    (SumKey.ofScale s b).result b c = -(s * c) := by
  have hp : (b : R) * b = -b := by push_cast at hR; linear_combination hR
  unfold SumKey.result
  split_ifs
  · rfl
  · conv_rhs => rw [← Nat.div_add_mod c b]
    simp only [SumKey.ofScale]; push_cast; ring
  · conv_rhs => rw [three_places b c]
    simp only [SumKey.ofScale]; push_cast
    linear_combination (s * ((c / b ^ 2 : ℕ) : R)) * hp

/-- [proved-derived; formal-checked] Statement 1: where `b(b − 1) = 0` and `b(b + 1) = 0`, §5's solution closes every
line `x + y = c` read with operands of up to three places to `s (x + y − c)`. -/
theorem wide_ofScale_closure (s : R) (h1 : ((b * (b - 1) : ℕ) : R) = 0) (h2 : ((b * (b + 1) : ℕ) : R) = 0)
    (x y c : ℕ) : wideClosure (SumKey.ofScale s b) b x y c = s * ((x : R) + y - c) := by
  have hp : (b : R) * b = -b := by push_cast at h2; linear_combination h2
  have hm : (b : R) * b = b := by
    rcases Nat.eq_zero_or_pos b with hb0 | hb0
    · subst hb0; simp
    · have : ((b - 1 : ℕ) : R) = (b : R) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [Nat.cast_mul, this] at h1
      linear_combination h1
  have h2b : 2 * (b : R) = 0 := by linear_combination hp - hm
  have hop : ∀ t : ℕ, wideOperand (SumKey.ofScale s b) b t = s * t := by
    intro t
    unfold wideOperand
    split_ifs
    · exact ofScale_operand b s t
    · conv_rhs => rw [three_places b t]
      simp only [SumKey.ofScale]; push_cast
      linear_combination (-(s * ((t / b ^ 2 : ℕ) : R))) * hm
  have hres : wideResult (SumKey.ofScale s b) b c = -(s * c) := by
    unfold wideResult
    split_ifs
    · exact ofScale_result b s h2 c
    · conv_rhs => rw [four_places b c]
      simp only [SumKey.ofScale]; push_cast
      linear_combination (s * ((c / b ^ 2 % b : ℕ) : R) + s * ((c / b ^ 3 : ℕ) : R) * ((b : R) - 1)) * hp +
        (s * ((c / b ^ 3 : ℕ) : R)) * h2b
  rw [wideClosure, hop, hop, hres]
  ring

/-- [proved-derived; formal-checked] Statement 1: a key with `s` a unit closes every true sum with operands below `b³`
exactly where `b(b − 1) = 0` and `b(b + 1) = 0`. -/
theorem wide_exists_iff (hb : 2 ≤ b) :
    (∃ κ : SumKey R, IsUnit κ.s ∧ ∀ x y, x < b ^ 3 → y < b ^ 3 → wideClosure κ b x y (x + y) = 0) ↔
      ((b * (b - 1) : ℕ) : R) = 0 ∧ ((b * (b + 1) : ℕ) : R) = 0 := by
  have hc : ((b - 1 : ℕ) : R) = (b : R) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  constructor
  · rintro ⟨κ, hs, h⟩
    obtain ⟨-, hp, hm⟩ := wide_necessity κ b hb h
    rw [mul_assoc, hs.mul_right_eq_zero] at hp hm
    rw [Nat.cast_mul, hc, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    exact ⟨hm, hp⟩
  · rintro ⟨h1, h2⟩
    refine ⟨SumKey.ofScale 1 b, isUnit_one, fun x y _ _ => ?_⟩
    rw [wide_ofScale_closure b 1 h1 h2]
    push_cast
    ring

/-- [proved-derived; formal-checked] Statement 1: modulo `q`, exactly when `q ∣ b · gcd(2, b + 1)` (`q ∣ b` in an even
base, `q ∣ 2b` in an odd one). -/
theorem wide_zmod_exists_iff (q : ℕ) (hb : 2 ≤ b) :
    (∃ κ : SumKey (ZMod q), IsUnit κ.s ∧
        ∀ x y, x < b ^ 3 → y < b ^ 3 → wideClosure κ b x y (x + y) = 0) ↔ q ∣ b * Nat.gcd 2 (b + 1) := by
  rw [wide_exists_iff b hb, ZMod.natCast_eq_zero_iff, ZMod.natCast_eq_zero_iff, ← Nat.dvd_gcd_iff,
    Nat.gcd_mul_left, gcd_pred_succ (by omega)]

/-- [proved-derived; formal-checked] Statement 1, the prime form: modulo a prime `p`, exactly when `p ∣ 2b`. -/
theorem wide_prime_exists_iff (p : ℕ) [hp : Fact p.Prime] (hb : 2 ≤ b) :
    (∃ κ : SumKey (ZMod p), IsUnit κ.s ∧
        ∀ x y, x < b ^ 3 → y < b ^ 3 → wideClosure κ b x y (x + y) = 0) ↔ p ∣ 2 * b := by
  rw [wide_zmod_exists_iff b p hb]
  constructor
  · intro h
    rw [mul_comm 2 b]
    exact h.trans (Nat.mul_dvd_mul_left b (Nat.gcd_dvd_left 2 (b + 1)))
  · intro h
    rcases (Nat.Prime.dvd_mul hp.out).mp h with h2 | h2
    · have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h2
      subst hp2
      rcases Nat.even_or_odd b with he | ho
      · exact Dvd.dvd.mul_right (even_iff_two_dvd.mp he) _
      · have : Nat.gcd 2 (b + 1) = 2 := Nat.gcd_eq_left (even_iff_two_dvd.mp ho.add_one)
        rw [this]
        exact Dvd.intro_left b rfl
    · exact Dvd.dvd.mul_right h2 _

/-- [proved-derived; formal-checked] Statement 1 in base 10: modulo 10 the key closes every line to `x + y − c` (the
units), and no key closes every true sum with operands below `10³` modulo 11 (casting out elevens goes, §6) or
modulo 20. -/
theorem wide_ten : (∀ x y c : ℕ, wideClosure (SumKey.ofScale (1 : ZMod 10) 10) 10 x y c = (x : ZMod 10) + y - c) ∧
    (¬ ∃ κ : SumKey (ZMod 11), IsUnit κ.s ∧
        ∀ x y, x < 10 ^ 3 → y < 10 ^ 3 → wideClosure κ 10 x y (x + y) = 0) ∧
    ¬ ∃ κ : SumKey (ZMod 20), IsUnit κ.s ∧
        ∀ x y, x < 10 ^ 3 → y < 10 ^ 3 → wideClosure κ 10 x y (x + y) = 0 := by
  refine ⟨fun x y c => ?_, ?_, ?_⟩
  · rw [wide_ofScale_closure 10 1 (by decide) (by decide)]
    ring
  · rw [wide_prime_exists_iff 10 11 (hp := ⟨by norm_num⟩) (by norm_num)]
    decide
  · rw [wide_zmod_exists_iff 10 20 (by norm_num)]
    decide

end Wide

/-! ## 2. Differences with the hand reversible -/

section Hands

/-- [definition] The hands a difference line's pairs are counted in (§11): `sub` for the subtrahend's pairs (from the
seam `−` to the pair into `=`), `res` for the result's pairs from the seam `=`, `fin` for `c₀`; each `1` (the starting
hand) or `−1` (reversed). The minuend's pairs, `(x₀, −)` among them, are in the starting hand. -/
structure Hands (R : Type*) where
  sub : R
  res : R
  fin : R

variable {R : Type*} [CommRing R]

/-- [definition] No reflector: every pair in the starting hand. -/
def Hands.plain : Hands R := ⟨1, 1, 1⟩

/-- [definition] `−` reflects, nothing restarts: the subtrahend and the result reversed, `c₀` in the starting hand. -/
def Hands.minus : Hands R := ⟨-1, -1, 1⟩

/-- [definition] `−` reflects, nothing restarts, `c₀` read in the hand in force. -/
def Hands.minusInForce : Hands R := ⟨-1, -1, -1⟩

/-- [definition] `−` reflects and `=` restarts: the subtrahend reversed, everything from `=` on in the starting hand. -/
def Hands.minusRestart : Hands R := ⟨-1, 1, 1⟩

/-- [definition] `=` reflects: the result's pairs reversed, the subtrahend and `c₀` in the starting hand. -/
def Hands.equals : Hands R := ⟨1, -1, 1⟩

variable (κ : DiffKey R) (b : ℕ) (h : Hands R)

/-- [definition] The result after `=`, of one or two places: `(=, c₁)` in the hand `res`, `c₀` in the hand `fin`. -/
def diffResult (c : ℕ) : R :=
  if c < b then -(h.fin * κ.s * (c : R)) else h.res * κ.u' * ((c / b : ℕ) : R) - h.fin * κ.s * ((c % b : ℕ) : R)

/-- [definition] A difference line's closure `x − y = c`, each pair counted in the hand in force at its seam. -/
def diffClosure (x y c : ℕ) : R := κ.minuend b x + h.sub * κ.subtrahend b y + diffResult κ b h c

/-- [proved-derived; formal-checked] With no reflector the hand reading is §10's. -/
theorem diffClosure_plain (x y c : ℕ) : diffClosure κ b Hands.plain x y c = κ.closure b x y c := by
  simp only [diffClosure, diffResult, Hands.plain, DiffKey.closure, DiffKey.result, one_mul]

/-- [proved-derived; formal-checked] A one-place result in the hands `h`. -/
theorem diffResult_one {c : ℕ} (hc : c < b) : diffResult κ b h c = -(h.fin * κ.s * (c : R)) := if_pos hc

/-- [proved-derived; formal-checked] A two-place result in the hands `h`. -/
theorem diffResult_two {d₁ d₀ : ℕ} (h₀ : d₀ < b) (h₁ : 1 ≤ d₁) :
    diffResult κ b h (b * d₁ + d₀) = h.res * κ.u' * (d₁ : R) - h.fin * κ.s * (d₀ : R) := by
  have hlt : ¬ b * d₁ + d₀ < b := by nlinarith
  obtain ⟨e1, e2⟩ := SumKey.div_mod_two b (d₁ := d₁) h₀
  rw [diffResult, if_neg hlt, e1, e2]

/-- [proved-derived; formal-checked] Statement 2: with `−` reflecting, whatever the hands at `=` and of `c₀`, a key
closing every true difference with `y ≤ x < b²` closes every line `x − y = c` to `fin · s (x − y − c)` (lines `1 − 0`,
`1 − 1`, `b − 0`, `(b + 1) − 0`, `b − b`, `b − 1`). -/
theorem minus_forced (hs : h.sub = -1) (hb : 2 ≤ b)
    (hκ : ∀ x y, y ≤ x → x < b ^ 2 → diffClosure κ b h x y (x - y) = 0) (x y c : ℕ) :
    diffClosure κ b h x y c = h.fin * κ.s * ((x : R) - y - c) := by
  have h' : ∀ x y c, y ≤ x → x < b ^ 2 → c = x - y → diffClosure κ b h x y c = 0 :=
    fun x y c hxy hx hc => hc ▸ hκ x y hxy hx
  set f := h.fin
  set r := h.res
  have key : κ.u + κ.z = f * κ.s ∧ κ.um + κ.ze = f * κ.s ∧ κ.u + κ.v = f * κ.s * b ∧ κ.w + κ.z = f * κ.s ∧
      κ.um + κ.v = f * κ.s * b ∧ κ.w + κ.ze = f * κ.s ∧ r * κ.u' = -(f * κ.s * b) := by
    obtain ⟨k, rfl⟩ : ∃ k, b = k + 2 := ⟨b - 2, by omega⟩
    have D1 := h' 1 0 1 (by omega) (by nlinarith) (by omega)
    rw [diffClosure, DiffKey.minuend_one κ (k + 2) (by omega : 1 < k + 2),
      DiffKey.subtrahend_one κ (k + 2) (by omega : 0 < k + 2), diffResult_one κ (k + 2) h (by omega : 1 < k + 2)]
      at D1
    have D2 := h' 1 1 0 le_rfl (by nlinarith) (by omega)
    rw [diffClosure, DiffKey.minuend_one κ (k + 2) (by omega : 1 < k + 2),
      DiffKey.subtrahend_one κ (k + 2) (by omega : 1 < k + 2), diffResult_one κ (k + 2) h (by omega : 0 < k + 2)]
      at D2
    have D3 := h' ((k + 2) * 1 + 0) 0 ((k + 2) * 1 + 0) (by omega) (by nlinarith) (by omega)
    rw [diffClosure, DiffKey.minuend_two κ (k + 2) (by omega) le_rfl,
      DiffKey.subtrahend_one κ (k + 2) (by omega : 0 < k + 2), diffResult_two κ (k + 2) h (by omega) le_rfl] at D3
    have D4 := h' ((k + 2) * 1 + 1) 0 ((k + 2) * 1 + 1) (by omega) (by nlinarith) (by omega)
    rw [diffClosure, DiffKey.minuend_two κ (k + 2) (by omega) le_rfl,
      DiffKey.subtrahend_one κ (k + 2) (by omega : 0 < k + 2), diffResult_two κ (k + 2) h (by omega) le_rfl] at D4
    have D5 := h' ((k + 2) * 1 + 0) ((k + 2) * 1 + 0) 0 le_rfl (by nlinarith) (by omega)
    rw [diffClosure, DiffKey.minuend_two κ (k + 2) (by omega) le_rfl,
      DiffKey.subtrahend_two κ (k + 2) (by omega) le_rfl, diffResult_one κ (k + 2) h (by omega : 0 < k + 2)] at D5
    have D6 := h' ((k + 2) * 1 + 0) 1 (k + 1) (by omega) (by nlinarith) (by omega)
    rw [diffClosure, DiffKey.minuend_two κ (k + 2) (by omega) le_rfl,
      DiffKey.subtrahend_one κ (k + 2) (by omega : 1 < k + 2),
      diffResult_one κ (k + 2) h (by omega : k + 1 < k + 2)] at D6
    rw [hs] at D1 D2 D3 D4 D5 D6
    push_cast at D1 D2 D3 D4 D5 D6 ⊢
    have uz : κ.u + κ.z = f * κ.s := by linear_combination D1
    have ue : κ.um + κ.ze = f * κ.s := by linear_combination D1 - D2
    have uv : κ.u + κ.v = f * κ.s * ((k : R) + 2) := by linear_combination D6 + D1 - D2
    refine ⟨uz, ue, uv, by linear_combination D4 - D3, by linear_combination uv - D5,
      by linear_combination D4 - D3 - D1 + (D1 - D2) + D5, by linear_combination D3 - uv⟩
  obtain ⟨uz, ue, uv, wz, umv, we, ru⟩ := key
  have hm : κ.minuend b x = f * κ.s * x := by
    unfold DiffKey.minuend
    split_ifs
    · linear_combination (x : R) * uz
    · conv_rhs => rw [← Nat.div_add_mod x b]
      push_cast
      linear_combination ((x / b : ℕ) : R) * uv + ((x % b : ℕ) : R) * wz
  have hsub : κ.subtrahend b y = f * κ.s * y := by
    unfold DiffKey.subtrahend
    split_ifs
    · linear_combination (y : R) * ue
    · conv_rhs => rw [← Nat.div_add_mod y b]
      push_cast
      linear_combination ((y / b : ℕ) : R) * umv + ((y % b : ℕ) : R) * we
  have hr : diffResult κ b h c = -(f * κ.s * c) := by
    unfold diffResult
    split_ifs
    · rfl
    · conv_rhs => rw [← Nat.div_add_mod c b]
      push_cast
      linear_combination ((c / b : ℕ) : R) * ru
  rw [diffClosure, hm, hsub, hr, hs]
  ring

/-- [definition] The key for differences with `−` reflecting, the result's pair in the hand `r`: `u ≡ u⁻ ≡ w ≡ 0`,
`z ≡ z⁼ ≡ s`, `v ≡ s b`, `u′ ≡ −r s b`. -/
def minusKey (s r : R) (b : ℕ) : DiffKey R := ⟨0, 0, -(r * s * b), s, s, s * b, 0, s⟩

/-- [proved-derived; formal-checked] Statement 2: with `−` reflecting, `c₀` in the starting hand and the result's pair
in a hand `r` with `r² = 1`, `minusKey s r b` closes every line `x − y = c` to `s (x − y − c)` in any ring. -/
theorem minusKey_closure (hs : h.sub = -1) (hf : h.fin = 1) (hr : h.res * h.res = 1) (s : R) (x y c : ℕ) :
    diffClosure (minusKey s h.res b) b h x y c = s * ((x : R) - y - c) := by
  have hm : (minusKey s h.res b).minuend b x = s * x := by
    unfold DiffKey.minuend
    split_ifs
    · simp only [minusKey]; ring
    · conv_rhs => rw [← Nat.div_add_mod x b]
      simp only [minusKey]; push_cast; ring
  have hsub : (minusKey s h.res b).subtrahend b y = s * y := by
    unfold DiffKey.subtrahend
    split_ifs
    · simp only [minusKey]; ring
    · conv_rhs => rw [← Nat.div_add_mod y b]
      simp only [minusKey]; push_cast; ring
  have hres : diffResult (minusKey s h.res b) b h c = -(s * c) := by
    unfold diffResult
    split_ifs
    · simp only [minusKey, hf]; ring
    · conv_rhs => rw [← Nat.div_add_mod c b]
      simp only [minusKey, hf]; push_cast
      linear_combination (-(s * b * ((c / b : ℕ) : R))) * hr
  rw [diffClosure, hm, hsub, hres, hs]
  ring

/-- [proved-derived; formal-checked] Statement 2: with `−` reflecting, a key with `s = 1` closes every true difference
over every ring and in every base: no torsion. -/
theorem minus_exists (hs : h.sub = -1) (hf : h.fin = 1) (hr : h.res * h.res = 1) :
    ∃ κ : DiffKey R, κ.s = 1 ∧ ∀ x y, y ≤ x → diffClosure κ b h x y (x - y) = 0 := by
  refine ⟨minusKey 1 h.res b, rfl, fun x y hxy => ?_⟩
  rw [minusKey_closure b h hs hf hr, Nat.cast_sub hxy]
  ring

/-- [proved-derived; formal-checked] Statement 2: §11's two rows, `−` reflecting alone and `−` reflecting with `=`
restarting. -/
theorem minus_exists_both :
    (∃ κ : DiffKey R, κ.s = 1 ∧ ∀ x y, y ≤ x → diffClosure κ b Hands.minus x y (x - y) = 0) ∧
      ∃ κ : DiffKey R, κ.s = 1 ∧ ∀ x y, y ≤ x → diffClosure κ b Hands.minusRestart x y (x - y) = 0 :=
  ⟨minus_exists b _ rfl rfl (by simp [Hands.minus]), minus_exists b _ rfl rfl (by simp [Hands.minusRestart])⟩

/-- [proved-derived; formal-checked] Statement 2: in characteristic zero, with `s` and `c₀`'s hand units, a key closing
every true difference tells every result apart: it closes `x − y = c` exactly when `x = y + c`. -/
theorem minus_tells_apart [CharZero R] (hs : h.sub = -1) (hb : 2 ≤ b) (hsu : IsUnit κ.s) (hfu : IsUnit h.fin)
    (hκ : ∀ x y, y ≤ x → x < b ^ 2 → diffClosure κ b h x y (x - y) = 0) (x y c : ℕ) :
    diffClosure κ b h x y c = 0 ↔ x = y + c := by
  rw [minus_forced κ b h hs hb hκ, (hfu.mul hsu).mul_right_eq_zero, sub_sub, sub_eq_zero]
  exact_mod_cast Iff.rfl

/-- [proved-derived; formal-checked] With `=` reflecting a difference line reads as §10's with `u′` reversed. -/
theorem diffClosure_equals (x y c : ℕ) :
    diffClosure κ b Hands.equals x y c = ({ κ with u' := -κ.u' } : DiffKey R).closure b x y c := by
  simp only [diffClosure, diffResult, Hands.equals, DiffKey.closure, DiffKey.result, DiffKey.minuend,
    DiffKey.subtrahend, one_mul, neg_mul]

/-- [proved-derived; formal-checked] Statement 2, §11's row "`=` reflects": modulo `q` a key exists exactly when
`q ∣ 2b`, as with no reflector. -/
theorem equals_zmod_exists_iff (q : ℕ) (hb : 2 ≤ b) :
    (∃ κ : DiffKey (ZMod q), IsUnit κ.s ∧
        ∀ x y, y ≤ x → x < b ^ 2 → diffClosure κ b Hands.equals x y (x - y) = 0) ↔ q ∣ 2 * b := by
  rw [← DiffKey.zmod_exists_iff b q hb]
  constructor
  · rintro ⟨κ, hs, hκ⟩
    exact ⟨{ κ with u' := -κ.u' }, hs, fun x y hxy hx => by rw [← diffClosure_equals]; exact hκ x y hxy hx⟩
  · rintro ⟨κ, hs, hκ⟩
    refine ⟨{ κ with u' := -κ.u' }, hs, fun x y hxy hx => ?_⟩
    rw [diffClosure_equals]
    simpa using hκ x y hxy hx

end Hands

/-! ## 3. Sums and differences in one menu -/

section Menu

/-- [definition] A key on one menu of sums and differences, linear in the digit values, every separator its own moves:
`DiffKey`'s (`u` after the newline, `u⁻` after `−`, `u′` after `=`, `z` before `−`, `z⁼` before `=`,
`θ(x, y) = v x + w y`, `ψ(d) = s d`) with `u⁺` (`up`) after `+` and `z⁺` (`zp`) before `+`. The two families share the
pairs `(newline, x)`, `(x, y)`, `(y, =)` and `(=, c)`. -/
structure MenuKey (R : Type*) extends DiffKey R where
  up : R
  zp : R

namespace MenuKey

variable {R : Type*} [CommRing R] (κ : MenuKey R) (b : ℕ)

/-- [definition] The first operand's moves as a sum key: `u` after the newline, `z⁺` before `+`. -/
def first : SumKey R := ⟨κ.u, κ.v, κ.w, κ.zp, κ.u', κ.s⟩

/-- [definition] The second operand's moves as a sum key: `u⁺` after `+`, `z⁼` before `=`. -/
def second : SumKey R := ⟨κ.up, κ.v, κ.w, κ.ze, κ.u', κ.s⟩

/-- [definition] A sum line's closure `x + y = c`, every pair in the starting hand (a sum meets no reflector). -/
def sumClosure (x y c : ℕ) : R := κ.first.operand b x + κ.second.operand b y + κ.first.result b c

/-- [definition] The key closes every true line of the menu: sums with `x, y < b²`, and differences with `y ≤ x < b²`
read in the hands `h`. -/
def Closes (h : Hands R) : Prop :=
  (∀ x y, x < b ^ 2 → y < b ^ 2 → κ.sumClosure b x y (x + y) = 0) ∧
    ∀ x y, y ≤ x → x < b ^ 2 → diffClosure κ.toDiffKey b h x y (x - y) = 0

/-- [proved-derived; formal-checked] Statement 3: on the sum lines alone, no move shared, a closing key has §4's shared
moves forced (`u + z⁺ ≡ u⁺ + z⁼ ≡ w + z⁺ ≡ w + z⁼ ≡ s`, `u + v ≡ u⁺ + v ≡ s b`, `u′ ≡ −s b`) and `s b (b + 1) = 0`. -/
theorem sum_moves (hb : 2 ≤ b) (hS : ∀ x y, x < b ^ 2 → y < b ^ 2 → κ.sumClosure b x y (x + y) = 0) :
    κ.u + κ.zp = κ.s ∧ κ.up + κ.ze = κ.s ∧ κ.u' = -(κ.s * b) ∧ κ.u + κ.v = κ.s * b ∧ κ.w + κ.zp = κ.s ∧
      κ.up + κ.v = κ.s * b ∧ κ.w + κ.ze = κ.s ∧ κ.s * (b : R) * ((b : R) + 1) = 0 := by
  have h' : ∀ x y c, x < b ^ 2 → y < b ^ 2 → c = x + y → κ.sumClosure b x y c = 0 :=
    fun x y c hx hy hc => hc ▸ hS x y hx hy
  obtain ⟨k, rfl⟩ : ∃ k, b = k + 2 := ⟨b - 2, by omega⟩
  have L1 := h' 1 0 1 (by nlinarith) (by nlinarith) rfl
  rw [sumClosure, SumKey.operand_one _ (k + 2) (by omega : 1 < k + 2),
    SumKey.operand_one _ (k + 2) (by omega : 0 < k + 2), SumKey.result_one _ (k + 2) (by omega : 1 < k + 2)] at L1
  have L2 := h' 0 1 1 (by nlinarith) (by nlinarith) rfl
  rw [sumClosure, SumKey.operand_one _ (k + 2) (by omega : 0 < k + 2),
    SumKey.operand_one _ (k + 2) (by omega : 1 < k + 2), SumKey.result_one _ (k + 2) (by omega : 1 < k + 2)] at L2
  have L3 := h' ((k + 2) * 1 + 0) 0 ((k + 2) * 1 + 0) (by nlinarith) (by nlinarith) (by ring)
  rw [sumClosure, SumKey.operand_two _ (k + 2) (by omega) le_rfl,
    SumKey.operand_one _ (k + 2) (by omega : 0 < k + 2), SumKey.result_two _ (k + 2) (by omega) le_rfl (by omega)]
    at L3
  have L4 := h' ((k + 2) * 1 + 1) 0 ((k + 2) * 1 + 1) (by nlinarith) (by nlinarith) (by ring)
  rw [sumClosure, SumKey.operand_two _ (k + 2) (by omega) le_rfl,
    SumKey.operand_one _ (k + 2) (by omega : 0 < k + 2), SumKey.result_two _ (k + 2) (by omega) le_rfl (by omega)]
    at L4
  have L5 := h' (k + 1) 1 ((k + 2) * 1 + 0) (by nlinarith) (by nlinarith) (by ring)
  rw [sumClosure, SumKey.operand_one _ (k + 2) (by omega : k + 1 < k + 2),
    SumKey.operand_one _ (k + 2) (by omega : 1 < k + 2), SumKey.result_two _ (k + 2) (by omega) le_rfl (by omega)]
    at L5
  have L6 := h' 0 ((k + 2) * 1 + 0) ((k + 2) * 1 + 0) (by nlinarith) (by nlinarith) (by ring)
  rw [sumClosure, SumKey.operand_one _ (k + 2) (by omega : 0 < k + 2),
    SumKey.operand_two _ (k + 2) (by omega) le_rfl, SumKey.result_two _ (k + 2) (by omega) le_rfl (by omega)]
    at L6
  have L7 := h' 0 ((k + 2) * 1 + 1) ((k + 2) * 1 + 1) (by nlinarith) (by nlinarith) (by ring)
  rw [sumClosure, SumKey.operand_one _ (k + 2) (by omega : 0 < k + 2),
    SumKey.operand_two _ (k + 2) (by omega) le_rfl, SumKey.result_two _ (k + 2) (by omega) le_rfl (by omega)]
    at L7
  have L8 := h' ((k + 2) * (k + 1) + (k + 1)) ((k + 2) * 1 + 1) ((k + 2) ^ 2 * 1 + (k + 2) * 1 + 0)
    (by nlinarith) (by nlinarith) (by ring)
  rw [sumClosure, SumKey.operand_two _ (k + 2) (by omega) (by omega), SumKey.operand_two _ (k + 2) (by omega) le_rfl,
    SumKey.result_three _ (k + 2) (by omega) (by omega) le_rfl] at L8
  simp only [first, second] at L1 L2 L3 L4 L5 L6 L7 L8
  push_cast at L1 L2 L3 L4 L5 L6 L7 L8 ⊢
  have a : κ.u + κ.zp = κ.s := by linear_combination L1
  have b' : κ.up + κ.ze = κ.s := by linear_combination L2
  have c' : κ.u' = -(κ.s * ((k : R) + 2)) := by linear_combination L5 - ((k : R) + 1) * L1 - L2
  have d : κ.u + κ.v = κ.s * ((k : R) + 2) := by linear_combination L3 - c'
  have e : κ.w + κ.zp = κ.s := by linear_combination L4 - L3
  have f : κ.up + κ.v = κ.s * ((k : R) + 2) := by linear_combination L6 - c'
  have g : κ.w + κ.ze = κ.s := by linear_combination L7 - L6
  have hvw : κ.v + κ.w = κ.s * ((k : R) + 2) := by linear_combination d + e - a
  refine ⟨a, b', c', d, e, f, g, ?_⟩
  linear_combination L8 - ((k : R) + 1) * d - ((k : R) + 1) * e - f - g - c' - hvw

/-- [definition] The menu's solution, §5's moves in both families: `u ≡ u⁺ ≡ u⁻ ≡ w ≡ u′ ≡ −s b`, `v ≡ 2 s b`,
`z⁺ ≡ z ≡ z⁼ ≡ s + s b`. -/
def ofScale (s : R) (b : ℕ) : MenuKey R :=
  ⟨⟨-(s * b), -(s * b), -(s * b), s + s * b, s + s * b, 2 * s * b, -(s * b), s⟩, -(s * b), s + s * b⟩

/-- [proved-derived; formal-checked] Statement 3: on sum lines the menu's solution is §5's: where `b(b + 1) = 0` it
closes every line `x + y = c` to `s (x + y − c)`. -/
theorem ofScale_sumClosure (s : R) (hR : ((b * (b + 1) : ℕ) : R) = 0) (x y c : ℕ) :
    (ofScale s b).sumClosure b x y c = s * ((x : R) + y - c) := by
  have e1 : (ofScale s b).first = SumKey.ofScale s b := rfl
  have e2 : (ofScale s b).second = SumKey.ofScale s b := rfl
  rw [sumClosure, e1, e2, ofScale_operand, ofScale_operand, ofScale_result b s hR]
  ring

/-- [proved-derived; formal-checked] The menu's solution reads a difference's minuend as `s x` and its subtrahend as
`s y`. -/
theorem ofScale_minuend_subtrahend (s : R) (x y : ℕ) :
    (ofScale s b).minuend b x = s * x ∧ (ofScale s b).subtrahend b y = s * y := by
  constructor
  · unfold DiffKey.minuend
    split_ifs
    · simp only [ofScale]; ring
    · conv_rhs => rw [← Nat.div_add_mod x b]
      simp only [ofScale]; push_cast; ring
  · unfold DiffKey.subtrahend
    split_ifs
    · simp only [ofScale]; ring
    · conv_rhs => rw [← Nat.div_add_mod y b]
      simp only [ofScale]; push_cast; ring

/-- [proved-derived; formal-checked] The menu's solution on a difference line read in the hands `h`. -/
theorem ofScale_diffClosure (s : R) (h : Hands R) (x y c : ℕ) :
    diffClosure (ofScale s b).toDiffKey b h x y c =
      s * x + h.sub * (s * y) +
        if c < b then -(h.fin * s * c) else -(h.res * s * b) * ((c / b : ℕ) : R) - h.fin * s * ((c % b : ℕ) : R) := by
  obtain ⟨hm, hs⟩ := ofScale_minuend_subtrahend b s x y
  rw [diffClosure, hm, hs, diffResult]
  split_ifs
  · rfl
  · simp only [ofScale]; ring

/-- [proved-derived; formal-checked] Statement 3: with `−` reflecting and `=` restarting, the menu's solution closes
every difference line `x − y = c` to `s (x − y − c)`, over any ring and base. -/
theorem ofScale_restart_closure (s : R) (x y c : ℕ) :
    diffClosure (ofScale s b).toDiffKey b Hands.minusRestart x y c = s * ((x : R) - y - c) := by
  rw [ofScale_diffClosure]
  simp only [Hands.minusRestart]
  split_ifs
  · ring
  · conv_rhs => rw [← Nat.div_add_mod c b]
    push_cast; ring

/-- [proved-derived; formal-checked] Statement 4: with `−` reflecting alone and `c₀` in the starting hand, where
`2b = 0` the menu's solution closes every difference line to `s (x − y − c)`. -/
theorem ofScale_minus_closure (s : R) (h2 : ((2 * b : ℕ) : R) = 0) (x y c : ℕ) :
    diffClosure (ofScale s b).toDiffKey b Hands.minus x y c = s * ((x : R) - y - c) := by
  have h2' : 2 * (b : R) = 0 := by push_cast at h2; exact h2
  rw [ofScale_diffClosure]
  simp only [Hands.minus]
  split_ifs
  · ring
  · conv_rhs => rw [← Nat.div_add_mod c b]
    push_cast
    linear_combination (s * ((c / b : ℕ) : R)) * h2'

/-- [proved-derived; formal-checked] Statement 4: with no reflector the menu's solution closes a difference line to
`s (x + y − c)`. -/
theorem ofScale_plain_closure (s : R) (x y c : ℕ) :
    diffClosure (ofScale s b).toDiffKey b Hands.plain x y c = s * ((x : R) + y - c) := by
  rw [ofScale_diffClosure]
  simp only [Hands.plain]
  split_ifs
  · ring
  · conv_rhs => rw [← Nat.div_add_mod c b]
    push_cast; ring

/-- [proved-derived; formal-checked] Statement 4: with `−` reflecting and `c₀` in the hand in force, the menu's solution
closes a difference line to `s (x − y + c)`. -/
theorem ofScale_inForce_closure (s : R) (x y c : ℕ) :
    diffClosure (ofScale s b).toDiffKey b Hands.minusInForce x y c = s * ((x : R) - y + c) := by
  rw [ofScale_diffClosure]
  simp only [Hands.minusInForce]
  split_ifs
  · ring
  · conv_rhs => rw [← Nat.div_add_mod c b]
    push_cast; ring

/-- [proved-derived; formal-checked] `b(b + 1)` is even, so it vanishes wherever `2` does. -/
theorem two_mul_succ_cast (h2 : ((2 : ℕ) : R) = 0) : ((b * (b + 1) : ℕ) : R) = 0 := by
  obtain ⟨m, hm⟩ := (Nat.even_mul_succ_self b).two_dvd
  rw [hm, Nat.cast_mul, h2, zero_mul]

/-- [proved-derived; formal-checked] Statement 3: with `−` reflecting and `=` restarting, a key with `s` a unit closes
every true sum and difference exactly where `b(b + 1) = 0`. -/
theorem restart_exists_iff (hb : 2 ≤ b) :
    (∃ κ : MenuKey R, IsUnit κ.s ∧ κ.Closes b Hands.minusRestart) ↔ ((b * (b + 1) : ℕ) : R) = 0 := by
  constructor
  · rintro ⟨κ, hs, hS, -⟩
    have := (κ.sum_moves b hb hS).2.2.2.2.2.2.2
    rw [mul_assoc, hs.mul_right_eq_zero] at this
    push_cast
    exact this
  · intro hR
    refine ⟨ofScale 1 b, isUnit_one, fun x y _ _ => ?_, fun x y hxy _ => ?_⟩
    · rw [ofScale_sumClosure b 1 hR]; push_cast; ring
    · rw [ofScale_restart_closure, Nat.cast_sub hxy]; ring

/-- [proved-derived; formal-checked] Statement 3: modulo `q`, exactly when `q ∣ b(b + 1)`. -/
theorem restart_zmod_exists_iff (q : ℕ) (hb : 2 ≤ b) :
    (∃ κ : MenuKey (ZMod q), IsUnit κ.s ∧ κ.Closes b Hands.minusRestart) ↔ q ∣ b * (b + 1) := by
  rw [restart_exists_iff b hb, ZMod.natCast_eq_zero_iff]

/-- [proved-derived; formal-checked] Statement 3: modulo `b(b + 1)` the key with `s = 1` reads `c mod b(b + 1)` in both
families: it closes `x + y = c` exactly when `x + y ≡ c`, and `x − y = c` exactly when `x ≡ y + c`. -/
theorem restart_reads (x y c : ℕ) :
    ((ofScale (1 : ZMod (b * (b + 1))) b).sumClosure b x y c = 0 ↔ x + y ≡ c [MOD b * (b + 1)]) ∧
      (diffClosure (ofScale (1 : ZMod (b * (b + 1))) b).toDiffKey b Hands.minusRestart x y c = 0 ↔
        x ≡ y + c [MOD b * (b + 1)]) := by
  constructor
  · rw [ofScale_sumClosure b 1 (ZMod.natCast_self _), one_mul, sub_eq_zero, ← Nat.cast_add,
      ZMod.natCast_eq_natCast_iff]
  · rw [ofScale_restart_closure, one_mul, sub_sub, sub_eq_zero, ← Nat.cast_add, ZMod.natCast_eq_natCast_iff]

/-- [proved-derived; formal-checked] Statement 3 in base 10: modulo 110 one key closes `x + y = c` to `x + y − c` and
`x − y = c` to `x − y − c`. -/
theorem torsion110_menu (x y c : ℕ) :
    (ofScale (1 : ZMod 110) 10).sumClosure 10 x y c = (x : ZMod 110) + y - c ∧
      diffClosure (ofScale (1 : ZMod 110) 10).toDiffKey 10 Hands.minusRestart x y c = (x : ZMod 110) - y - c := by
  rw [ofScale_sumClosure 10 1 (by decide), ofScale_restart_closure]
  exact ⟨one_mul _, one_mul _⟩

/-- [proved-derived; formal-checked] Statement 4: with no reflector, a key closing the menu has `2 s = 0`: the shared
pair `(y, =)` takes an addend's units with `+s` and a subtrahend's with `−s` (lines `1 − 0`, `b − b`,
`(b + 1) − (b + 1)` beside the sums). -/
theorem plain_necessity (hb : 2 ≤ b) (hκ : κ.Closes b Hands.plain) : 2 * κ.s = 0 := by
  obtain ⟨hS, hD⟩ := hκ
  obtain ⟨a, -, -, -, e, -, g, -⟩ := κ.sum_moves b hb hS
  have h' : ∀ x y c, y ≤ x → x < b ^ 2 → c = x - y → diffClosure κ.toDiffKey b Hands.plain x y c = 0 :=
    fun x y c hxy hx hc => hc ▸ hD x y hxy hx
  obtain ⟨k, rfl⟩ : ∃ k, b = k + 2 := ⟨b - 2, by omega⟩
  have P1 := h' 1 0 1 (by omega) (by nlinarith) (by omega)
  rw [diffClosure, DiffKey.minuend_one _ (k + 2) (by omega : 1 < k + 2),
    DiffKey.subtrahend_one _ (k + 2) (by omega : 0 < k + 2), diffResult_one _ (k + 2) _ (by omega : 1 < k + 2)]
    at P1
  have P2 := h' ((k + 2) * 1 + 0) ((k + 2) * 1 + 0) 0 le_rfl (by nlinarith) (by omega)
  rw [diffClosure, DiffKey.minuend_two _ (k + 2) (by omega) le_rfl, DiffKey.subtrahend_two _ (k + 2) (by omega) le_rfl,
    diffResult_one _ (k + 2) _ (by omega : 0 < k + 2)] at P2
  have P3 := h' ((k + 2) * 1 + 1) ((k + 2) * 1 + 1) 0 le_rfl (by nlinarith) (by omega)
  rw [diffClosure, DiffKey.minuend_two _ (k + 2) (by omega) le_rfl, DiffKey.subtrahend_two _ (k + 2) (by omega) le_rfl,
    diffResult_one _ (k + 2) _ (by omega : 0 < k + 2)] at P3
  simp only [Hands.plain] at P1 P2 P3
  push_cast at P1 P2 P3
  linear_combination P3 - P2 - (e - a) - P1 - g

/-- [proved-derived; formal-checked] Statement 4: with no reflector, a key with `s` a unit closes the menu exactly where
`2 = 0`. -/
theorem plain_exists_iff (hb : 2 ≤ b) :
    (∃ κ : MenuKey R, IsUnit κ.s ∧ κ.Closes b Hands.plain) ↔ ((2 : ℕ) : R) = 0 := by
  constructor
  · rintro ⟨κ, hs, hκ⟩
    have := κ.plain_necessity b hb hκ
    rw [mul_comm, hs.mul_right_eq_zero] at this
    exact_mod_cast this
  · intro h2
    have h2' : (2 : R) = 0 := by exact_mod_cast h2
    refine ⟨ofScale 1 b, isUnit_one, fun x y _ _ => ?_, fun x y hxy _ => ?_⟩
    · rw [ofScale_sumClosure b 1 (two_mul_succ_cast b h2)]; push_cast; ring
    · rw [ofScale_plain_closure, Nat.cast_sub hxy]
      linear_combination (y : R) * h2'

/-- [proved-derived; formal-checked] Statement 4: modulo `q`, exactly when `q ∣ 2`. -/
theorem plain_zmod_exists_iff (q : ℕ) (hb : 2 ≤ b) :
    (∃ κ : MenuKey (ZMod q), IsUnit κ.s ∧ κ.Closes b Hands.plain) ↔ q ∣ 2 := by
  rw [plain_exists_iff b hb, ZMod.natCast_eq_zero_iff]

/-- [proved-derived; formal-checked] Statement 4: with `−` reflecting alone, `c₀` in the starting hand, a key closing
the menu has `2 s b = 0` beside `s b (b + 1) = 0`: `(=, c₁)` is reversed in a difference and not in a sum (line
`b − 0`). -/
theorem minus_necessity (hb : 2 ≤ b) (hκ : κ.Closes b Hands.minus) :
    2 * κ.s * (b : R) = 0 ∧ κ.s * (b : R) * ((b : R) + 1) = 0 := by
  obtain ⟨hS, hD⟩ := hκ
  obtain ⟨-, -, c', d, -, -, -, hb1⟩ := κ.sum_moves b hb hS
  refine ⟨?_, hb1⟩
  have M1 := hD ((b : ℕ) * 1 + 0) 0 (by omega) (by nlinarith)
  rw [Nat.sub_zero, diffClosure, DiffKey.minuend_two _ b (by omega) le_rfl,
    DiffKey.subtrahend_one _ b (by omega : 0 < b), diffResult_two _ b _ (by omega) le_rfl] at M1
  simp only [Hands.minus] at M1
  push_cast at M1
  linear_combination M1 - d + c'

/-- [proved-derived; formal-checked] Statement 4: with `−` reflecting alone, a key with `s` a unit closes the menu
exactly where `b(b + 1) = 0` and `2b = 0`. -/
theorem minus_exists_iff (hb : 2 ≤ b) :
    (∃ κ : MenuKey R, IsUnit κ.s ∧ κ.Closes b Hands.minus) ↔
      ((b * (b + 1) : ℕ) : R) = 0 ∧ ((2 * b : ℕ) : R) = 0 := by
  constructor
  · rintro ⟨κ, hs, hκ⟩
    obtain ⟨h2, h1⟩ := κ.minus_necessity b hb hκ
    rw [mul_comm 2, mul_assoc, hs.mul_right_eq_zero] at h2
    rw [mul_assoc, hs.mul_right_eq_zero] at h1
    push_cast
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨ofScale 1 b, isUnit_one, fun x y _ _ => ?_, fun x y hxy _ => ?_⟩
    · rw [ofScale_sumClosure b 1 h1]; push_cast; ring
    · rw [ofScale_minus_closure b 1 h2, Nat.cast_sub hxy]; ring

/-- [proved-derived; formal-checked] Statement 4: modulo `q`, exactly when `q ∣ b · gcd(2, b + 1)` (in base 10,
`q ∣ 10`: the units). -/
theorem minus_zmod_exists_iff (q : ℕ) (hb : 2 ≤ b) :
    (∃ κ : MenuKey (ZMod q), IsUnit κ.s ∧ κ.Closes b Hands.minus) ↔ q ∣ b * Nat.gcd 2 (b + 1) := by
  rw [minus_exists_iff b hb, ZMod.natCast_eq_zero_iff, ZMod.natCast_eq_zero_iff, ← Nat.dvd_gcd_iff,
    mul_comm 2 b, Nat.gcd_mul_left, Nat.gcd_comm]

/-- [proved-derived; formal-checked] Statement 4: with `−` reflecting and `c₀` in the hand in force, a key closing the
menu has `2 s = 0`: the shared `ψ` is read `+` in sums and `−` in differences (lines `b − 0`, `(b + 1) − 0`, `b − b`,
`1 − 1` beside the sums). -/
theorem inForce_necessity (hb : 2 ≤ b) (hκ : κ.Closes b Hands.minusInForce) : 2 * κ.s = 0 := by
  obtain ⟨hS, hD⟩ := hκ
  obtain ⟨-, -, -, -, -, -, g, -⟩ := κ.sum_moves b hb hS
  have h' : ∀ x y c, y ≤ x → x < b ^ 2 → c = x - y →
      diffClosure κ.toDiffKey b Hands.minusInForce x y c = 0 :=
    fun x y c hxy hx hc => hc ▸ hD x y hxy hx
  obtain ⟨k, rfl⟩ : ∃ k, b = k + 2 := ⟨b - 2, by omega⟩
  have F2 := h' ((k + 2) * 1 + 1) 0 ((k + 2) * 1 + 1) (by omega) (by nlinarith) (by omega)
  rw [diffClosure, DiffKey.minuend_two _ (k + 2) (by omega) le_rfl,
    DiffKey.subtrahend_one _ (k + 2) (by omega : 0 < k + 2), diffResult_two _ (k + 2) _ (by omega) le_rfl] at F2
  have F3 := h' ((k + 2) * 1 + 0) 0 ((k + 2) * 1 + 0) (by omega) (by nlinarith) (by omega)
  rw [diffClosure, DiffKey.minuend_two _ (k + 2) (by omega) le_rfl,
    DiffKey.subtrahend_one _ (k + 2) (by omega : 0 < k + 2), diffResult_two _ (k + 2) _ (by omega) le_rfl] at F3
  have F4 := h' ((k + 2) * 1 + 0) ((k + 2) * 1 + 0) 0 le_rfl (by nlinarith) (by omega)
  rw [diffClosure, DiffKey.minuend_two _ (k + 2) (by omega) le_rfl, DiffKey.subtrahend_two _ (k + 2) (by omega) le_rfl,
    diffResult_one _ (k + 2) _ (by omega : 0 < k + 2)] at F4
  have F5 := h' 1 1 0 le_rfl (by nlinarith) (by omega)
  rw [diffClosure, DiffKey.minuend_one _ (k + 2) (by omega : 1 < k + 2),
    DiffKey.subtrahend_one _ (k + 2) (by omega : 1 < k + 2), diffResult_one _ (k + 2) _ (by omega : 0 < k + 2)]
    at F5
  simp only [Hands.minusInForce] at F2 F3 F4 F5
  push_cast at F2 F3 F4 F5
  linear_combination -g + (F2 - F3) - (F5 - F4)

/-- [proved-derived; formal-checked] Statement 4: with `−` reflecting and `c₀` in the hand in force, a key with `s` a
unit closes the menu exactly where `2 = 0`. -/
theorem inForce_exists_iff (hb : 2 ≤ b) :
    (∃ κ : MenuKey R, IsUnit κ.s ∧ κ.Closes b Hands.minusInForce) ↔ ((2 : ℕ) : R) = 0 := by
  constructor
  · rintro ⟨κ, hs, hκ⟩
    have := κ.inForce_necessity b hb hκ
    rw [mul_comm, hs.mul_right_eq_zero] at this
    exact_mod_cast this
  · intro h2
    have h2' : (2 : R) = 0 := by exact_mod_cast h2
    refine ⟨ofScale 1 b, isUnit_one, fun x y _ _ => ?_, fun x y hxy _ => ?_⟩
    · rw [ofScale_sumClosure b 1 (two_mul_succ_cast b h2)]; push_cast; ring
    · rw [ofScale_inForce_closure, Nat.cast_sub hxy]
      linear_combination ((x : R) - y) * h2'

/-- [proved-derived; formal-checked] Statement 4: modulo `q`, exactly when `q ∣ 2`. -/
theorem inForce_zmod_exists_iff (q : ℕ) (hb : 2 ≤ b) :
    (∃ κ : MenuKey (ZMod q), IsUnit κ.s ∧ κ.Closes b Hands.minusInForce) ↔ q ∣ 2 := by
  rw [inForce_exists_iff b hb, ZMod.natCast_eq_zero_iff]

end MenuKey

end Menu

end Holonics.Landmarks.ClosureKeyMenus
