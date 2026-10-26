import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic

/-!
# The radix itinerary: on `q = bʷ − 1` the turn by `b` rotates the block, and its quotient is the digit

The record `research/records/2026-10-26_THE_OPERATION_IS_A_LINE_IN_THE_LIFT_AND_THE_RELEASE_READS_THE_RADIX_ITINERARY.md`
(§5) releases a residue held on the ring `q = bʷ − 1` as digits. On that ring the `w`-digit move is a
translation (`radix.grain-staircase`: `q ∣ bʷ − 1`), so a residue `S < q` is the whole `w`-digit
block of its value, zero-padded. The release reads that block by turning it: the point
`D_k = bᵏ S mod q` is the phase `frac(bᵏ S / q)` of the long division of `S` by `q`, one turn of
`D ↦ b D mod q` rotates the block one place, and the quotient `⌊b D_k / q⌋` the turn emits is the
block's digit `k`, read from the most significant end. This file proves it on `ℕ`, exactly.

[proved-standard; formal-checked] What is proved.

1. **One turn reads one digit** (`turn_reads_digit`): with `q + 1 = b B`, a residue
   `D = t B + r < q` (`t < b`, `r < B`) turns to `b D = t q + (r b + t)`, so `⌊b D / q⌋ = t` and
   `b D mod q = r b + t`, the block rotated left by one place.
2. **`k` turns rotate the block by `k` places** (`block_rotates`): with `q + 1 = K M`, a residue
   `S = A M + C < q` (`A < K`, `C < M`) has `K S mod q = C K + A`.
3. **The itinerary** (`point_succ`, `point_period`): `D_(k+1) = b D_k mod q`, and after `w` turns
   the point returns to `S`: the release closes as a cycle, not by a count.
4. **The digit** (`digit_of_point`): on `q + 1 = b^(k + 1 + m)`, for `S < q`,
   `⌊b D_k / q⌋ = ⌊S / bᵐ⌋ mod b`, the digit `k` places below the top of the block.
5. **The length is the first nonzero digit** (`digit_zero_above_length`,
   `digit_nonzero_at_length`): the digit at place `k` is zero when `S < bᵐ`, and nonzero when
   `bᵐ ≤ S < b^(m+1)`. So a value of `L` digits reads `w − L` zeros and then its leading digit:
   the release starts at the first nonzero digit of the itinerary and needs no separate size.
6. **The fibre** (`point_fibre`): `S` and `S + q` have the same itinerary, so the residue alone
   never separates a value from one a whole ring larger; a value at or past `q` needs the
   archimedean face (its length and leading digits), which this file does not supply.
7. **The joined ring's phase** (`joined_phase_9999`): on `9999 = 9 · 11 · 101`,
   `S/9999 = 7S/9 + 8S/11 + 50S/101 − 2S`, so modulo whole turns the phase on the joined ring is the
   seventh power of the phase on 9 times the eighth on 11 times the fiftieth on 101: the digit is
   read on the joined ring, whose phase the pair contact takes as a product of the rings' phases.

The computational object is the helical pair interaction: the residue is the phase of a ring, and
each turn is one winding of the helix whose carry is the emitted digit. Of the winding guide's six
general objects this touches the helix (the turn by `b`) and faces and placement (the digit read
as the turn's quotient); the pair, the cell holonomy, the tube and the tower thread stay attached.

Consumers: the atlas row `radix.itinerary-release` and the record's §5.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Mathematics.RadixItinerary

/-- [proved-standard; formal-checked] **One turn reads one digit.** On a ring with `q + 1 = b B`
(for `B = bⁿ`, `q = b^(n+1) − 1`), a residue `D = t B + r < q` with `t < b` and `r < B` turns to
`b D = t q + (r b + t)`: the quotient is the leading digit `t` and the remainder is the block rotated
left by one place. -/
theorem turn_reads_digit {b B q t r : ℕ} (hq : q + 1 = b * B) (ht : t < b) (hr : r < B)
    (hD : t * B + r < q) :
    b * (t * B + r) / q = t ∧ b * (t * B + r) % q = r * b + t := by
  have hlt : r * b + t < q := by
    rcases Nat.lt_or_ge (t + 1) b with h | h
    · have h1 : (r + 1) * b ≤ B * b := Nat.mul_le_mul_right b (by omega)
      nlinarith
    · have htb : b = t + 1 := by omega
      subst htb
      have hr2 : r + 2 ≤ B := by nlinarith
      have h1 : (r + 2) * (t + 1) ≤ B * (t + 1) := Nat.mul_le_mul_right (t + 1) hr2
      nlinarith
  have hqpos : 0 < q := lt_of_le_of_lt (Nat.zero_le _) hD
  have heq : r * b + t + q * t = b * (t * B + r) := by
    have h1 : b * (t * B + r) = t * (b * B) + r * b := by ring
    rw [h1, ← hq]
    ring
  exact (Nat.div_mod_unique hqpos).mpr ⟨heq, hlt⟩

/-- [proved-standard; formal-checked] **`k` turns rotate the block by `k` places.** With
`q + 1 = K M` (for `K = bᵏ`, `M = b^(w−k)`), a residue `S = A M + C < q` with `A < K` and `C < M`
has `K S mod q = C K + A`: the top `k` digits `A` move to the bottom. -/
theorem block_rotates {K M q A C : ℕ} (hq : q + 1 = K * M) (hA : A < K) (hC : C < M)
    (hS : A * M + C < q) :
    K * (A * M + C) % q = C * K + A := by
  have hlt : C * K + A < q := by
    rcases Nat.lt_or_ge (C + 1) M with h | h
    · have h1 : (C + 2) * K ≤ M * K := Nat.mul_le_mul_right K (by omega)
      nlinarith
    · have hM : M = C + 1 := by omega
      subst hM
      have hA2 : A + 2 ≤ K := by
        by_contra hcon
        have hK : K ≤ A + 1 := by omega
        have h1 : K * (C + 1) ≤ (A + 1) * (C + 1) := Nat.mul_le_mul_right (C + 1) hK
        nlinarith
      nlinarith
  have hqpos : 0 < q := lt_of_le_of_lt (Nat.zero_le _) hS
  have heq : C * K + A + q * A = K * (A * M + C) := by
    have h1 : K * (A * M + C) = A * (K * M) + C * K := by ring
    rw [h1, ← hq]
    ring
  exact ((Nat.div_mod_unique hqpos).mpr ⟨heq, hlt⟩).2

/-- [proved-standard; formal-checked] **The itinerary advances by one turn:**
`D_(k+1) = b D_k mod q` for `D_k = bᵏ S mod q`. -/
theorem point_succ (q b S k : ℕ) : b ^ (k + 1) * S % q = b * (b ^ k * S % q) % q := by
  rw [Nat.mul_mod b, Nat.mod_mod, ← Nat.mul_mod, pow_succ]
  congr 1
  ring

/-- [proved-standard; formal-checked] **The itinerary closes after `w` turns:** on `q + 1 = bʷ`,
`bʷ S mod q = S` for `S < q`. -/
theorem point_period {q b w S : ℕ} (hq : q + 1 = b ^ w) (hS : S < q) : b ^ w * S % q = S := by
  rw [← hq, show (q + 1) * S = S + q * S by ring, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hS]

/-- [proved-standard; formal-checked] **The digit is the turn's quotient.** On
`q + 1 = b^(k + 1 + m)`, for `S < q`, the quotient of the turn at the point `D_k = bᵏ S mod q` is
`⌊S / bᵐ⌋ mod b`, the digit `k` places below the top of the `(k + 1 + m)`-digit block. -/
theorem digit_of_point {b q k m S : ℕ} (hb : 0 < b) (hq : q + 1 = b ^ (k + 1 + m)) (hS : S < q) :
    b * (b ^ k * S % q) / q = S / b ^ m % b := by
  have hqpos : 0 < q := lt_of_le_of_lt (Nat.zero_le _) hS
  have hKpos : 0 < b ^ k := pow_pos hb k
  have hBpos : 0 < b ^ m := pow_pos hb m
  have hMpos : 0 < b ^ m * b := Nat.mul_pos hBpos hb
  -- the block split at `k` places from the top
  have hqKM : q + 1 = b ^ k * (b ^ m * b) := by
    rw [hq]
    ring
  set A := S / (b ^ m * b) with hAdef
  set C := S % (b ^ m * b) with hCdef
  have hSAC : A * (b ^ m * b) + C = S := Nat.div_add_mod' S (b ^ m * b)
  have hA : A < b ^ k := by
    rw [hAdef, Nat.div_lt_iff_lt_mul hMpos]
    have : S < b ^ k * (b ^ m * b) := by omega
    linarith [this]
  have hC : C < b ^ m * b := Nat.mod_lt S hMpos
  have hrot : b ^ k * S % q = C * b ^ k + A := by
    have h := block_rotates hqKM hA hC (by rw [hSAC]; exact hS)
    rwa [hSAC] at h
  -- the rotated block's leading digit
  set t := C / b ^ m with htdef
  set r := C % b ^ m with hrdef
  have hCtr : t * b ^ m + r = C := Nat.div_add_mod' C (b ^ m)
  have ht : t < b := by
    rw [htdef, Nat.div_lt_iff_lt_mul hBpos]
    linarith [hC]
  have hr : r < b ^ m := Nat.mod_lt C hBpos
  have hD : C * b ^ k + A = t * (b ^ m * b ^ k) + (r * b ^ k + A) := by
    rw [← hCtr]
    ring
  have hqB : q + 1 = b * (b ^ m * b ^ k) := by
    rw [hq]
    ring
  have hlow : r * b ^ k + A < b ^ m * b ^ k := by
    have h1 : (r + 1) * b ^ k ≤ b ^ m * b ^ k := Nat.mul_le_mul_right (b ^ k) (by omega)
    nlinarith
  have hDq : t * (b ^ m * b ^ k) + (r * b ^ k + A) < q := by
    rw [← hD, ← hrot]
    exact Nat.mod_lt _ hqpos
  have hturn := (turn_reads_digit hqB ht hlow hDq).1
  rw [hrot, hD, hturn, htdef, hCdef, Nat.mod_mul_right_div_self]

/-- [proved-standard; formal-checked] **Above the length the digit is zero:** if `S < bᵐ`, the digit
at the place `m` positions above the bottom is `0`. -/
theorem digit_zero_above_length {b m S : ℕ} (hS : S < b ^ m) : S / b ^ m % b = 0 := by
  rw [Nat.div_eq_of_lt hS, Nat.zero_mod]

/-- [proved-standard; formal-checked] **At the length the digit is nonzero:** if
`bᵐ ≤ S < b^(m+1)`, the digit at the place `m` positions above the bottom is the leading digit,
and it is not `0`. -/
theorem digit_nonzero_at_length {b m S : ℕ} (hb : 0 < b) (hlo : b ^ m ≤ S)
    (hhi : S < b ^ (m + 1)) : S / b ^ m % b ≠ 0 := by
  have hBpos : 0 < b ^ m := pow_pos hb m
  have hlt : S / b ^ m < b := by
    rw [Nat.div_lt_iff_lt_mul hBpos]
    calc S < b ^ (m + 1) := hhi
      _ = b * b ^ m := by ring
  have hpos : 0 < S / b ^ m := Nat.div_pos hlo hBpos
  rw [Nat.mod_eq_of_lt hlt]
  exact hpos.ne'

/-- [proved-standard; formal-checked] **The residue's fibre:** `S` and `S + q` have the same
itinerary point at every turn, so the ring alone never separates them. -/
theorem point_fibre (q b S k : ℕ) : b ^ k * (S + q) % q = b ^ k * S % q := by
  rw [mul_add, Nat.add_mul_mod_self_right]

/-- [proved-standard; formal-checked] **The joined ring's phase is a monomial of its rings'
phases:** on `9999 = 9 · 11 · 101`, `S/9999 = 7S/9 + 8S/11 + 50S/101 − 2S`, since
`7 · 1111 + 8 · 909 + 50 · 99 = 2 · 9999 + 1`. -/
theorem joined_phase_9999 (S : ℚ) :
    S / 9999 = 7 * S / 9 + 8 * S / 11 + 50 * S / 101 - 2 * S := by
  ring

end Holonics.Mathematics.RadixItinerary
