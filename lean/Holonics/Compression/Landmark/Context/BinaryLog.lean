import Holonics.Compression.Landmark.Context.Tree
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Compression.Landmark.Context.BinaryLog: the certified binary logarithm's squaring invariant

[definition; agent-inferred] The certified binary logarithm (#62, "the certified binary
logarithm's squaring invariant"; rebuild step 4, #73). `landmark::binary_log` reads `log₂ m` of a
positive integer by exact squaring: `y = m/2^w ∈ [1, 2)` (`w` the top bit) is held between two
fixed-point integers on `2^(−P)`, each step squares both bounds outward, and a fraction bit is
emitted only when both bounds agree on `y² ≥ 2` (then both halve, outward). Its consumers are the
grain exponent of a dyadic face (`grain_floor`, `dyadic_grain_exponent`) and the passage code's
enclosure (`ProductBound::log2`, `PassageCode`; the population's `log_ratio`). The computational
object is the helical pair interaction; this owner is a navigator's resident face: `log₂` is read
by squaring, the winding of the scale ratio `y` counted as carries (each emitted `1` is one carry of
`y^(2^k)` past `2`). Of the winding guide's six general objects it touches the **helix** (the
emitted bits are the carried windings of `y` under repeated squaring) and **faces and placement**
(the enclosure is a face at a declared grain); the pair, the cell holonomy, the tube and the tower
thread stay attached, unchanged.

The object, with the hidden real `z = y^(2^k)/2^f` after `k` emitted bits `f`:

```text
enclosure   1 ≤ z < 2 ,  lo ≤ 2^P z ≤ hi                                   (Encl P z lo hi)
square      ⌊lo²/2^P⌋ ≤ 2^P z² ≤ ⌈hi²/2^P⌉                                  (sqLo, sqHi)
bit 1       2^(P+1) ≤ ⌊lo²/2^P⌋:  z′ = z²/2 ,  lo′ = ⌊sqLo/2⌋ ,  hi′ = ⌊(sqHi + 1)/2⌋ = ⌈sqHi/2⌉
bit 0       ⌈hi²/2^P⌉ < 2^(P+1):  z′ = z² ,   lo′ = sqLo ,  hi′ = sqHi
result      w + f/2^k ≤ log₂ m < w + (f + 1)/2^k
carrier     hi ≤ 2^(P+1) at the founding and after every step, so hi² ≤ 2^(2P+2), sqHi ≤ 2^(P+2)
grain       ⌊L(w 2^k + f)/2^k⌋ = ⌊(L(w 2^k + f + 1) − 1)/2^k⌋  ⟹  ⌊L log₂ m⌋ is that value
```

[proved-derived; formal-checked] What is proved.
- `square_encl`: the outward squares enclose `2^P z²`.
- `bit_one`, `bit_zero`: each emitted bit keeps the enclosure at the new `z`; `step_one`,
  `step_zero` restate it for `z = y^(2^k)/2^f`, so the bits are the fraction of `log₂ y`.
- `found_exact` (`w ≤ P`, `lo = hi = m 2^(P−w)`) and `found_floor` (`P < w`,
  `lo = ⌊m/2^(w−P)⌋`, `hi = lo + 1`): the two foundings, read at `k = f = 0` by `start`.
- `log_encl`: the enclosure after `k` bits `f` gives `w + f/2^k ≤ log₂ m < w + (f + 1)/2^k`. The
  loop may stop at any step (the bit budget, `decided`, or the bounds straddling `2`) and the
  enclosure read so far is certified.
- `sqHi_le`, `found_exact_le`, `found_floor_le`, `hi_one_le`: the upper bound stays at most
  `2^(P+1)`, so every square is at most `2^(2P+2)` and `sqHi ≤ 2^(P+2)`: with `P = 125`
  (`FIXED = 128 − 3`) every operand is held in `u128`.
- `grain_floor_decided`, `grain_floor_of_encl`: when the two floors agree, `⌊L log₂ m⌋` is their
  value (`grain_floor`).

[conditional] **What the theorems cover in the Rust.** `square` computes `⌊x²/2^P⌋` from the
128-bit halves of `x²` and adds one unless the low `P` bits vanish, which is `sqLo` and `sqHi`;
`wide_mul`'s 256-bit product is checked by the tests, not stated here. `binary_log`'s loop is
`bit_one` (`low >= two`, `(low >> 1, (high + 1) >> 1)`) and `bit_zero` (`high < two`, `(low,
high)`), founded by `found_exact` (`whole <= fixed`) or `found_floor`. A power of two returns
`whole` exactly, `log₂ m = w`. `ProductBound::log2` reads `[w + f/2^k, w + (f + 1)/2^k]`, which
`log_encl` certifies (strictly inside the upper end). `grain_floor`'s operand widths (`L < 2^32`,
`w < 2^31`, at most 64 fraction bits, so `L (w 2^k + f + 1) < 2^127`) are the Rust's guard, not
stated here.

| Claim | Lean | Rust |
|---|---|---|
| the outward square and the two bits | `square_encl`, `bit_one`, `bit_zero`, `step_one`, `step_zero` | `landmark::context::square`, `binary_log` |
| the founding | `found_exact`, `found_floor`, `start` | `binary_log` |
| the certified enclosure | `log_encl` | `BinaryLog`, `ProductBound::log2` |
| the carrier | `sqHi_le`, `found_exact_le`, `found_floor_le`, `hi_one_le` | `FIXED`, `square` |
| the grain floor | `grain_floor_decided`, `grain_floor_of_encl` | `grain_floor`, `dyadic_grain_exponent` |
-/

namespace Holonics.Compression.Landmark.Context.BinaryLog

/-- [definition] **The enclosure** of the hidden `z ∈ [1, 2)` between two fixed-point integers on
`2^(−P)`. -/
structure Encl (P : ℕ) (z : ℝ) (lo hi : ℕ) : Prop where
  one_le : 1 ≤ z
  lt_two : z < 2
  lo_le : (lo : ℝ) ≤ 2 ^ P * z
  le_hi : 2 ^ P * z ≤ hi

/-- [definition] `⌊x²/2^P⌋`. -/
def sqLo (P x : ℕ) : ℕ := x * x / 2 ^ P

/-- [definition] `⌈x²/2^P⌉`: the floor, plus one unless the low `P` bits vanish (`square`). -/
def sqHi (P x : ℕ) : ℕ := x * x / 2 ^ P + if x * x % 2 ^ P = 0 then 0 else 1

theorem sqLo_mul_le (P x : ℕ) : sqLo P x * 2 ^ P ≤ x * x := Nat.div_mul_le_self _ _

theorem le_sqHi_mul (P x : ℕ) : x * x ≤ sqHi P x * 2 ^ P := by
  have h := Nat.div_add_mod (x * x) (2 ^ P)
  have hm := Nat.mod_lt (x * x) (pow_pos (two_pos : (0 : ℕ) < 2) P)
  unfold sqHi
  split_ifs with h0
  · rw [h0] at h; nlinarith
  · nlinarith

/-- [proved-derived] **`sqHi_le`: the outward square is at most any bound of the square.** -/
theorem sqHi_le {P x c : ℕ} (h : x * x ≤ c * 2 ^ P) : sqHi P x ≤ c := by
  have hpos := pow_pos (two_pos : 0 < 2) P
  have hd := Nat.div_add_mod (x * x) (2 ^ P)
  unfold sqHi
  split_ifs with h0
  · simpa using Nat.div_le_of_le_mul (by linarith [mul_comm c (2 ^ P)] : x * x ≤ 2 ^ P * c)
  · have hlt : x * x / 2 ^ P < c := by
      by_contra hc
      replace hc := not_lt.1 hc
      have : c * 2 ^ P ≤ x * x / 2 ^ P * 2 ^ P := Nat.mul_le_mul_right _ hc
      have hpos' : 0 < x * x % 2 ^ P := Nat.pos_of_ne_zero h0
      nlinarith
    omega

/-- [proved-derived] **`square_encl`: the outward squares enclose `2^P z²`.** -/
theorem square_encl {P lo hi : ℕ} {z : ℝ} (h : Encl P z lo hi) :
    (sqLo P lo : ℝ) ≤ 2 ^ P * z ^ 2 ∧ 2 ^ P * z ^ 2 ≤ sqHi P hi := by
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hz : 0 ≤ 2 ^ P * z := by nlinarith [h.one_le]
  have h1 : ((sqLo P lo * 2 ^ P : ℕ) : ℝ) ≤ ((lo * lo : ℕ) : ℝ) := by
    exact_mod_cast sqLo_mul_le P lo
  have h2 : ((hi * hi : ℕ) : ℝ) ≤ ((sqHi P hi * 2 ^ P : ℕ) : ℝ) := by
    exact_mod_cast le_sqHi_mul P hi
  push_cast at h1 h2
  have hlo := h.lo_le
  have hhi := h.le_hi
  have hlo0 : (0 : ℝ) ≤ lo := Nat.cast_nonneg _
  constructor
  · have : (lo : ℝ) * lo ≤ (2 ^ P * z) * (2 ^ P * z) := mul_le_mul hlo hlo hlo0 hz
    nlinarith
  · have : (2 ^ P * z) * (2 ^ P * z) ≤ (hi : ℝ) * hi := mul_le_mul hhi hhi hz (hz.trans hhi)
    nlinarith

/-- `⌊n/2⌋ ≤ n/2` and `n/2 ≤ ⌊(n + 1)/2⌋` in `ℝ`. -/
theorem half_floor_le (n : ℕ) : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := Nat.cast_div_le

theorem half_le_ceil (n : ℕ) : (n : ℝ) / 2 ≤ (((n + 1) / 2 : ℕ) : ℝ) := by
  have h := Nat.div_add_mod (n + 1) 2
  have hm := Nat.mod_lt (n + 1) (two_pos : 0 < 2)
  have : n ≤ 2 * ((n + 1) / 2) := by omega
  have : (n : ℝ) ≤ 2 * (((n + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast this
  linarith

/-- [proved-derived] **`bit_one`: a `1` keeps the enclosure at `z²/2`.** When the lower square
reaches `2^(P+1)`, `z² ≥ 2`, and `z²/2` is enclosed by the lower square halved down and the upper
halved up. -/
theorem bit_one {P lo hi : ℕ} {z : ℝ} (h : Encl P z lo hi) (hb : 2 ^ (P + 1) ≤ sqLo P lo) :
    Encl P (z ^ 2 / 2) (sqLo P lo / 2) ((sqHi P hi + 1) / 2) := by
  obtain ⟨s1, s2⟩ := square_encl h
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hb' : (2 : ℝ) ^ (P + 1) ≤ sqLo P lo := by exact_mod_cast hb
  rw [pow_succ] at hb'
  have hz2 : 2 ≤ z ^ 2 := by nlinarith
  have hz1 := h.one_le
  have hz2' := h.lt_two
  refine ⟨by linarith, by nlinarith, ?_, ?_⟩
  · calc ((sqLo P lo / 2 : ℕ) : ℝ) ≤ (sqLo P lo : ℝ) / 2 := half_floor_le _
      _ ≤ 2 ^ P * (z ^ 2 / 2) := by linarith
  · calc 2 ^ P * (z ^ 2 / 2) ≤ (sqHi P hi : ℝ) / 2 := by linarith
      _ ≤ _ := half_le_ceil _

/-- [proved-derived] **`bit_zero`: a `0` keeps the enclosure at `z²`.** When the upper square is
below `2^(P+1)`, `z² < 2`, and `z²` is enclosed by the two squares. -/
theorem bit_zero {P lo hi : ℕ} {z : ℝ} (h : Encl P z lo hi) (hb : sqHi P hi < 2 ^ (P + 1)) :
    Encl P (z ^ 2) (sqLo P lo) (sqHi P hi) := by
  obtain ⟨s1, s2⟩ := square_encl h
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hb' : (sqHi P hi : ℝ) < 2 ^ (P + 1) := by exact_mod_cast hb
  rw [pow_succ] at hb'
  have hz1 := h.one_le
  exact ⟨by nlinarith, by nlinarith, s1, s2⟩

/-! ### The emitted bits are the fraction of `log₂ y` -/

theorem z_one (y : ℝ) (k f : ℕ) :
    (y ^ 2 ^ k / 2 ^ f) ^ 2 / 2 = y ^ 2 ^ (k + 1) / 2 ^ (2 * f + 1) := by
  rw [show (2 : ℝ) ^ (2 * f + 1) = (2 ^ f) ^ 2 * 2 by ring,
    show y ^ 2 ^ (k + 1) = (y ^ 2 ^ k) ^ 2 by rw [pow_succ, pow_mul], div_pow]
  ring

theorem z_zero (y : ℝ) (k f : ℕ) :
    (y ^ 2 ^ k / 2 ^ f) ^ 2 = y ^ 2 ^ (k + 1) / 2 ^ (2 * f) := by
  rw [show (2 : ℝ) ^ (2 * f) = (2 ^ f) ^ 2 by ring,
    show y ^ 2 ^ (k + 1) = (y ^ 2 ^ k) ^ 2 by rw [pow_succ, pow_mul], div_pow]

/-- [proved-derived] **`step_one`**: at `z = y^(2^k)/2^f`, a `1` appends to the fraction. -/
theorem step_one {P lo hi k f : ℕ} {y : ℝ} (h : Encl P (y ^ 2 ^ k / 2 ^ f) lo hi)
    (hb : 2 ^ (P + 1) ≤ sqLo P lo) :
    Encl P (y ^ 2 ^ (k + 1) / 2 ^ (2 * f + 1)) (sqLo P lo / 2) ((sqHi P hi + 1) / 2) := by
  rw [← z_one]; exact bit_one h hb

/-- [proved-derived] **`step_zero`**: at `z = y^(2^k)/2^f`, a `0` appends to the fraction. -/
theorem step_zero {P lo hi k f : ℕ} {y : ℝ} (h : Encl P (y ^ 2 ^ k / 2 ^ f) lo hi)
    (hb : sqHi P hi < 2 ^ (P + 1)) :
    Encl P (y ^ 2 ^ (k + 1) / 2 ^ (2 * f)) (sqLo P lo) (sqHi P hi) := by
  rw [← z_zero]; exact bit_zero h hb

/-! ### The founding -/

theorem y_bounds {m w : ℕ} (h1 : 2 ^ w ≤ m) (h2 : m < 2 ^ (w + 1)) :
    1 ≤ (m : ℝ) / 2 ^ w ∧ (m : ℝ) / 2 ^ w < 2 := by
  have hw : (0 : ℝ) < 2 ^ w := by positivity
  have h1' : (2 : ℝ) ^ w ≤ m := by exact_mod_cast h1
  have h2' : (m : ℝ) < 2 ^ (w + 1) := by exact_mod_cast h2
  rw [pow_succ] at h2'
  constructor
  · rw [le_div_iff₀ hw]; linarith
  · rw [div_lt_iff₀ hw]; linarith

/-- [proved-derived] **`found_exact`**: at `w ≤ P` the founding `m 2^(P−w)` is exact. -/
theorem found_exact {P m w : ℕ} (h1 : 2 ^ w ≤ m) (h2 : m < 2 ^ (w + 1)) (hw : w ≤ P) :
    Encl P ((m : ℝ) / 2 ^ w) (m * 2 ^ (P - w)) (m * 2 ^ (P - w)) := by
  obtain ⟨b1, b2⟩ := y_bounds h1 h2
  have e : ((m * 2 ^ (P - w) : ℕ) : ℝ) = 2 ^ P * ((m : ℝ) / 2 ^ w) := by
    push_cast
    rw [show P = (P - w) + w by omega, pow_add]
    rw [show P - w + w - w = P - w by omega]
    field_simp
  exact ⟨b1, b2, e.le, e.ge⟩

/-- [proved-derived] **`found_floor`**: at `P < w` the founding is `⌊m/2^(w−P)⌋` and one above. -/
theorem found_floor {P m w : ℕ} (h1 : 2 ^ w ≤ m) (h2 : m < 2 ^ (w + 1)) (hw : P < w) :
    Encl P ((m : ℝ) / 2 ^ w) (m / 2 ^ (w - P)) (m / 2 ^ (w - P) + 1) := by
  obtain ⟨b1, b2⟩ := y_bounds h1 h2
  have hd : 0 < 2 ^ (w - P) := pow_pos (two_pos : (0 : ℕ) < 2) _
  have e : 2 ^ P * ((m : ℝ) / 2 ^ w) = (m : ℝ) / 2 ^ (w - P) := by
    rw [show w = (w - P) + P by omega, pow_add, show w - P + P - P = w - P by omega]
    field_simp
  refine ⟨b1, b2, ?_, ?_⟩
  · rw [e]
    have := Nat.cast_div_le (α := ℝ) (m := m) (n := 2 ^ (w - P))
    push_cast at this
    exact this
  · rw [e]
    have h := Nat.div_add_mod m (2 ^ (w - P))
    have hm := Nat.mod_lt m hd
    have hd' : (0 : ℝ) < 2 ^ (w - P) := by positivity
    rw [div_le_iff₀ hd']
    have : m ≤ (m / 2 ^ (w - P) + 1) * 2 ^ (w - P) := by nlinarith
    exact_mod_cast this

/-- [proved-derived] **`start`**: a founding is the enclosure before any bit (`k = f = 0`). -/
theorem start {P lo hi : ℕ} {y : ℝ} (h : Encl P y lo hi) : Encl P (y ^ 2 ^ 0 / 2 ^ 0) lo hi := by
  simpa using h

/-! ### The certified enclosure -/

/-- [proved-derived] **`log_encl`: the certified binary logarithm.** After `k` emitted bits `f`,
the enclosure of `y^(2^k)/2^f` with `y = m/2^w` gives
`w + f/2^k ≤ log₂ m < w + (f + 1)/2^k`. -/
theorem log_encl {P lo hi k f m w : ℕ} (hm : 0 < m)
    (h : Encl P (((m : ℝ) / 2 ^ w) ^ 2 ^ k / 2 ^ f) lo hi) :
    (w : ℝ) + f / 2 ^ k ≤ Real.logb 2 m ∧ Real.logb 2 m < w + (f + 1) / 2 ^ k := by
  have hy : (0 : ℝ) < (m : ℝ) / 2 ^ w := by positivity
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  have hz := h.one_le
  have hz2 := h.lt_two
  have hzpos : (0 : ℝ) < ((m : ℝ) / 2 ^ w) ^ 2 ^ k / 2 ^ f := by linarith
  have hlog : Real.logb 2 (((m : ℝ) / 2 ^ w) ^ 2 ^ k / 2 ^ f) =
      2 ^ k * (Real.logb 2 m - w) - f := by
    rw [Real.logb_div (by positivity) (by positivity), Real.logb_pow, Real.logb_pow,
      Real.logb_div (by positivity) (by positivity), Real.logb_pow, Real.logb_self_eq_one one_lt_two]
    push_cast
    ring
  have l0 : 0 ≤ Real.logb 2 (((m : ℝ) / 2 ^ w) ^ 2 ^ k / 2 ^ f) :=
    Real.logb_nonneg one_lt_two hz
  have l1 : Real.logb 2 (((m : ℝ) / 2 ^ w) ^ 2 ^ k / 2 ^ f) < 1 := by
    have := Real.logb_lt_logb one_lt_two hzpos hz2
    rwa [Real.logb_self_eq_one one_lt_two] at this
  rw [hlog] at l0 l1
  constructor
  · have : (f : ℝ) / 2 ^ k ≤ Real.logb 2 m - w := by rw [div_le_iff₀ hk]; linarith
    linarith
  · have : Real.logb 2 m - w < ((f : ℝ) + 1) / 2 ^ k := by rw [lt_div_iff₀ hk]; linarith
    linarith

/-! ### The carrier -/

/-- [proved-derived] **`found_exact_le`**: the exact founding is below `2^(P+1)`. -/
theorem found_exact_le {P m w : ℕ} (h2 : m < 2 ^ (w + 1)) (hw : w ≤ P) :
    m * 2 ^ (P - w) ≤ 2 ^ (P + 1) := by
  have : 2 ^ (P + 1) = 2 ^ (w + 1) * 2 ^ (P - w) := by rw [← pow_add]; congr 1; omega
  rw [this]
  exact Nat.mul_le_mul_right _ h2.le

/-- [proved-derived] **`found_floor_le`**: the floor founding plus one is at most `2^(P+1)`. -/
theorem found_floor_le {P m w : ℕ} (h2 : m < 2 ^ (w + 1)) (hw : P < w) :
    m / 2 ^ (w - P) + 1 ≤ 2 ^ (P + 1) := by
  have hd : 0 < 2 ^ (w - P) := pow_pos (two_pos : (0 : ℕ) < 2) _
  have e : 2 ^ (w + 1) = 2 ^ (P + 1) * 2 ^ (w - P) := by rw [← pow_add]; congr 1; omega
  have : m / 2 ^ (w - P) < 2 ^ (P + 1) := by
    rw [Nat.div_lt_iff_lt_mul hd, ← e]; exact h2
  omega

/-- [proved-derived] **`hi_one_le`**: after a `1` the upper bound stays at most `2^(P+1)`; after a
`0` it is below `2^(P+1)` by the branch itself. Every square is then at most `2^(2P+2)`. -/
theorem hi_one_le {P hi : ℕ} (h : hi ≤ 2 ^ (P + 1)) : (sqHi P hi + 1) / 2 ≤ 2 ^ (P + 1) := by
  have hs : sqHi P hi ≤ 2 ^ (P + 2) := by
    apply sqHi_le
    have : hi * hi ≤ 2 ^ (P + 1) * 2 ^ (P + 1) := Nat.mul_le_mul h h
    calc hi * hi ≤ 2 ^ (P + 1) * 2 ^ (P + 1) := this
      _ = 2 ^ (P + 2) * 2 ^ P := by rw [← pow_add, ← pow_add]; congr 1; omega
  have : 2 ^ (P + 2) = 2 * 2 ^ (P + 1) := by rw [pow_succ]; ring
  omega

/-! ### The grain floor -/

/-- [proved-derived] **`grain_floor_decided`**: for `base/2^b ≤ L < (base + 1)/2^b` and `g > 0`,
when `⌊g base/2^b⌋ = ⌊(g(base + 1) − 1)/2^b⌋`, that value is `⌊g L⌋` (`grain_floor`). -/
theorem grain_floor_decided {g base b : ℕ} {L : ℝ} (hg : 0 < g)
    (hL : (base : ℝ) / 2 ^ b ≤ L ∧ L < ((base : ℝ) + 1) / 2 ^ b)
    (heq : g * base / 2 ^ b = (g * (base + 1) - 1) / 2 ^ b) :
    ⌊(g : ℝ) * L⌋ = ((g * base / 2 ^ b : ℕ) : ℤ) := by
  have hb : (0 : ℝ) < 2 ^ b := by positivity
  have hbn : 0 < 2 ^ b := pow_pos (two_pos : (0 : ℕ) < 2) b
  set q := g * base / 2 ^ b with hq
  rw [Int.floor_eq_iff]
  push_cast
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  constructor
  · have h1 : ((q : ℕ) : ℝ) ≤ ((g * base : ℕ) : ℝ) / 2 ^ b := by
      rw [hq]
      have := Nat.cast_div_le (α := ℝ) (m := g * base) (n := 2 ^ b)
      push_cast at this ⊢
      exact this
    push_cast at h1
    have h2 : (g : ℝ) * base / 2 ^ b ≤ g * L := by
      rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hL.1 hg'.le
    linarith
  · -- `g(base + 1) ≤ (q + 1) 2^b`
    have hpos : 1 ≤ g * (base + 1) := Nat.mul_pos hg (Nat.succ_pos _)
    have hle : g * (base + 1) ≤ (q + 1) * 2 ^ b := by
      have h := Nat.div_add_mod (g * (base + 1) - 1) (2 ^ b)
      have hm := Nat.mod_lt (g * (base + 1) - 1) hbn
      rw [heq, ← Nat.sub_add_cancel hpos]
      generalize g * (base + 1) - 1 = n at h hm ⊢
      rw [Nat.add_sub_cancel]
      linarith
    have hle' : (g : ℝ) * (base + 1) ≤ ((q : ℝ) + 1) * 2 ^ b := by exact_mod_cast hle
    have h2 : (g : ℝ) * L < g * ((base + 1) / 2 ^ b) := mul_lt_mul_of_pos_left hL.2 hg'
    have h3 : (g : ℝ) * ((base + 1) / 2 ^ b) ≤ q + 1 := by
      rw [← mul_div_assoc, div_le_iff₀ hb]; exact hle'
    linarith

/-- [proved-derived] **`grain_floor_of_encl`: the grain floor from the certified enclosure.** After
`k` bits `f` of `log₂ m` (`log_encl`), with `base = w 2^k + f`, when the two floors agree their
value is `⌊g log₂ m⌋`. -/
theorem grain_floor_of_encl {P lo hi k f m w g : ℕ} (hm : 0 < m) (hg : 0 < g)
    (h : Encl P (((m : ℝ) / 2 ^ w) ^ 2 ^ k / 2 ^ f) lo hi)
    (heq : g * (w * 2 ^ k + f) / 2 ^ k = (g * (w * 2 ^ k + f + 1) - 1) / 2 ^ k) :
    ⌊(g : ℝ) * Real.logb 2 m⌋ = ((g * (w * 2 ^ k + f) / 2 ^ k : ℕ) : ℤ) := by
  obtain ⟨l1, l2⟩ := log_encl hm h
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  apply grain_floor_decided hg _ heq
  push_cast
  constructor
  · rw [div_le_iff₀ hk]
    have : (f : ℝ) ≤ (Real.logb 2 m - w) * 2 ^ k := by
      have := (div_le_iff₀ hk).1 (by linarith : (f : ℝ) / 2 ^ k ≤ Real.logb 2 m - w); linarith
    nlinarith
  · rw [lt_div_iff₀ hk]
    have : (Real.logb 2 m - w) * 2 ^ k < (f : ℝ) + 1 :=
      (lt_div_iff₀ hk).1 (by linarith)
    nlinarith

/-! ### Audit -/

#print axioms sqHi_le
#print axioms square_encl
#print axioms bit_one
#print axioms bit_zero
#print axioms step_one
#print axioms step_zero
#print axioms found_exact
#print axioms found_floor
#print axioms start
#print axioms log_encl
#print axioms found_exact_le
#print axioms found_floor_le
#print axioms hi_one_le
#print axioms grain_floor_decided
#print axioms grain_floor_of_encl

end Holonics.Compression.Landmark.Context.BinaryLog
