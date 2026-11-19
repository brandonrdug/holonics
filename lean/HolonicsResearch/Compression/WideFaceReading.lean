import Holonics.Compression.Landmark.Context.BinaryLog
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum.NatLog

/-!
# The wide-face reading: a face wider than `G` bits is read on its `G`-bit mantissa, widened by `3 · 2^(−G)`

[proved-standard; formal-checked] for the dyadic and logarithmic bounds and the rounding factors;
[proved-derived; formal-checked] for the readings, the code length's enclosure, the product's spread and the witness;
[definition] for the shift, the mantissas, the floor read, the two kept sides and the code length's ends.

Sources.
- The box of #410: "The wide-face reading: a face wider than `G` bits is read on its `G`-bit mantissa, its
  enclosure widened by `3 · 2^(−G)` (no current Rust owner found)."
- The record `research/records/2026-09-26_THE_LANDMARK_TREE_COMPRESSES_THE_STANDING_CUT_BELOW_PPM_TWO.md`, §3 (the
  wide-face reading of `landmark::code_length`, "a 98-bit mantissa with a certified widening", its Lean owed in #62,
  since folded into #410) and §4, "The reading" (the faces were read on a certified mantissa, then by the certified
  integer binary logarithm).
- The Rust, retired with the October library by C8c of #603 (`b09cc1192`). Its first form (`4934cd163`,
  `hnn/landmark.rs`, September 26): `reading_bits` `G = O + 2 = 98`; `mantissa(a, b, G)` the face's `G`-bit
  mantissa `m` and shift `s`, `q⁻ = m 2^(−s) ≤ q < q⁻(1 + 1/m)`; `code_length` reads `−log₂ q⁻` and returns
  `[ℓ⁻ − 3 · 2^(−G), ℓ⁺]`, since `log₂(1 + 1/m) ≤ log₂ e/m < 3 · 2^(−G)`. Its last form (`b09cc1192^`,
  `compression/landmark/context.rs`): `code_length` and `ratio_code_length` read `log₂ d − log₂ n` by `binary_log` at
  `O + 1` fraction bits, and `ProductBound` keeps a product to `KEPT = 127` significant bits after each factor,
  rounded down for the lower side and up for the upper.
- The owners reused: `Compression/Landmark/Context/Tree.rebase_log_residual` (a rebase's residual `ln(x/m) < 1/m`)
  and `Compression/Landmark/Context/BinaryLog.log_encl` (the squaring's certified enclosure).
- The atlas rows `radix.leading-fibre` (the leading face is multiplicative only up to the carry fibre of the unread
  places: the mantissa's face), `radix.leading-face-gas` (the length is the winding and the mantissa its phase) and
  `receiver.merge-code-length-pair` (integer product bounds kept at 127 bits and rounded outward, not in Lean there).

In the precision law's words: reading a face at width `G` releases its places below the top `G` by partition at a
declared width, `N = m · 2^s + r` with `0 ≤ r < 2^s`, and the remainder is accounted, never dropped: its whole effect
on `log₂ N` is under `3 · 2^(−G)`, the widening. The two kept sides of a product are sections (a floor and a ceiling)
standing between the factors of an ordered chain; each is taken outward, so each remainder is accounted by the side
it moves, and the two sides enclose the product with a spread fixed by the count of factors.

What is proved.
1. **The mantissa reading** (`shift`, `mantissa`). For `N ≥ 2^G`, `G ≥ 1`, `s = ⌊log₂ N⌋ + 1 − G` and
   `m = ⌊N/2^s⌋` have `2^(G−1) ≤ m < 2^G` (`mantissa_bounds`) and `m · 2^s ≤ N < (m + 1) · 2^s`
   (`mantissa_mul_le`, `lt_mantissa_succ_mul`); a face of at most `G` bits is read on itself, `s = 0` and `m = N`
   (`shift_eq_zero`, `mantissa_eq_self`). For every `N ≥ 1`: `s + log₂ m ≤ log₂ N < s + log₂(m + 1)`
   (`logb_mantissa_encl`), and the residual `log₂ N − s − log₂ m ∈ [0, 1/(m ln 2))` is the carrier's rebase
   residual read at `x = N/2^s` (`residual_lt`, through `Tree.rebase_log_residual`).
2. **The widening.** `log₂(m + 1) − log₂ m ≤ 1/(m ln 2)` (`logb_succ_sub_le`), `≤ 2^(1−G)/ln 2` for
   `m ≥ 2^(G−1)` (`inv_mul_log_le`), `< 3 · 2^(−G)` from Mathlib's `ln 2 > 0.6931471803 > 2/3`
   (`two_zpow_div_log_lt`, `logb_succ_sub_lt`). So `lo ≤ log₂ m ≤ hi` gives
   `s + lo ≤ log₂ N ≤ s + hi + 3 · 2^(−G)` (`widen`; strict above, `widen_lt`), for every `N ≥ 1`.
3. **A face read on its own mantissa** (the record's form; `faceShift`, `faceMantissa`). For a rational `q > 0`,
   `s = G − 1 − ⌊log₂ q⌋` (`Int.log`) and `m = ⌊q 2^s⌋` have `2^(G−1) ≤ m < 2^G` and `m ≤ q 2^s < m + 1`
   (`faceMantissa_bounds`), and an enclosure `[lo, hi]` of `−log₂ q⁻ = s − log₂ m` gives
   `lo − 3 · 2^(−G) ≤ −log₂ q ≤ hi` (`face_widen`): one widening, at the lower end, as `code_length` returned it.
   An integer face `N ≥ 2^(G−1)` reads the same mantissa with shift `−s` (`face_natCast`). The widening lies below
   the grid two octaves up, `3 · 2^(−G) < 2^(2−G)` (`widening_lt_grid`): with `G = O + 2`, below `2^(−O)`.
4. **A face's code length from its two parts.** For `q = n/d`, `n, d ≥ 1`, `−log₂ q = log₂ d − log₂ n`
   (`neg_logb_div`); a difference of enclosures encloses the difference at the summed width (`sub_encl`). With each
   part read on its mantissa at width `G` and the mantissa's `log₂` read by a floor read at `B` fraction bits, any
   `k : ℤ` with `k ≤ 2^B log₂ m < k + 1` (`FloorRead`, `FloorRead.encl`), the code length lies in
   `[codeLo, codeHi]` (`codeLength_encl`), whose width is `2^(1−B) + 6 · 2^(−G)` (`codeHi_sub_codeLo`). The
   certified binary logarithm's enclosure after `j` bits `f` is such a floor read, `k = w 2^j + f`
   (`floorRead_of_encl`, from `BinaryLog.log_encl`).
5. **The product bound** (`keepDown`, `keepUp`, `lowerFrom`, `upperFrom`, `productLower`, `productUpper`). Kept at
   `K` bits, `⌊x/2^s⌋ · 2^s ≤ x ≤ ⌈x/2^s⌉ · 2^s` with `s` the shift at width `K` (`keepDown_le`, `le_keepUp`); the
   floor's kept part is the mantissa and, for `x ≥ 2^K`, has `K` bits, the ceiling's at most `2^K` (`keepDown_eq`,
   `kept_bounds`); each side moves by a factor at most `1 + 2^(1−K)` (`le_keepDown`, `keepUp_le`). Over a list of `k`
   factors, rounded after each, `productLower ≤ ∏ ≤ productUpper` (`product_encl`; `lowerFrom_le`, `le_upperFrom`),
   `productUpper ≤ (1 + 2^(1−K))^(2k) · productLower` (`productUpper_le`, `upperFrom_le`), and for positive factors
   the lower side is positive and the upper over the lower is at most `(1 + 2^(1−K))^(2k)` (`lowerFrom_pos`,
   `productUpper_div_le`). The bounds need no positivity of the factors.
6. **A witness**: `N = 2^100 + 2^99 + 1` at `G = 98` has `⌊log₂ N⌋ = 100`, `s = 3`, `m = 2^97 + 2^96 = 3 · 2^96`,
   `2^97 ≤ m < 2^98` and `8m ≤ N < 8(m + 1)` (`witness_log`, `witness_shift`, `witness_mantissa`,
   `witness_bounds`); its floor read at `B = 3` is `780`, from `2^12 ≤ 3^8 < 2^13` (`witness_floorRead`), so
   `100.5 ≤ log₂ N ≤ 100.625 + 3 · 2^(−98)` (`witness_encl`); read as a face, its shift is `−3` and its mantissa
   the same (`witness_face`).

What the theorems cover in the Rust. `face_widen` is the first form's `code_length` on its shift and mantissa, with
the shift taken from `Int.log` where the Rust took it from the bit lengths, one lower when that floor had `G + 1`
bits; any shift with the bracket `m ≤ q 2^s < m + 1` and `m ≥ 2^(G−1)` gives the reading. `codeLength_encl` is the
last form's `ratio_code_length` with each part read wide first; in that form the wide part is read inside
`binary_log`'s founding (`BinaryLog.found_floor`, `hi = lo + 1` at `P = 125`), so its widening is carried by the
squaring's enclosure and no separate `3 · 2^(−G)` term stands there. `productLower` and `productUpper` model
`ProductBound` at its value `m · 2^e`: the product kept at `K` bits after each factor, the floor for the lower side
and the ceiling for the upper (the Rust raises the mantissa by one only when a dropped bit is set, and renormalizes
at `2^K`, which keeps the value), the factors read in list order from the empty product `1`.

What is not claimed.
- The certified binary logarithm itself: its squaring invariant is `BinaryLog`'s, and here a floor read is a
  hypothesis on any `k`, joined to `BinaryLog.log_encl` by `floorRead_of_encl`.
- The KT and CTW bounds (`Context/PriorMass`, `Context/Tree`; the record's `kraft_and_dominance` and the β chart's
  per-node bound).
- The Rust's choice of the ratio's shift from bit lengths, the rounding of an enclosure out to the grid `2^(−O)` by
  `interval_sum`, the machine words of `ProductBound` (its `u128` halves and `times_bound`), and the spread's log
  form `2k log₂(1 + 2^(1−K))`, which follows by monotonicity and is not stated.
- Which width a consumer reads at: `G = 98` and `K = 127` are the Rust's declarations, and only
  `widening_lt_grid` relates `G` to a grid.

The computational object is the helical pair interaction, read on a face's scale: a face's binary length is its
winding (the octaves counted by the shift and the top bit) and its mantissa its phase within the octave (atlas
`radix.leading-face-gas`); the reading at width `G` releases the phase below `G` bits and the widening accounts what
was released, and a product's two kept sides carry the octave as an exponent while the phase is kept to `K` bits.
Of the winding guide's six general objects it touches the **helix** (the octave winding `s` and the phase `log₂ m`
under a change of scale) and **faces and placement** (a face, its enclosure at a declared width and grain, and the
two sides of a product's enclosure); the pair, the cell holonomy, the tube and the tower thread stay attached
through `Context/Tree` and `Context/BinaryLog`.

Consumers: none in Rust (the owner retired with `b09cc1192`); the box of #410 and the atlas rows above.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Compression.WideFaceReading

open Holonics.Compression.Landmark.Context

/-! ## 0. Dyadic powers in the integer exponent -/

/-- [proved-standard; formal-checked] `2^(−G) = 1/2^G`. -/
theorem two_zpow_neg (G : ℕ) : (2 : ℝ) ^ (-(G : ℤ)) = 1 / 2 ^ G := by
  rw [zpow_neg, zpow_natCast, one_div]

/-- [proved-standard; formal-checked] `2^(1−G) = 1/2^(G−1)` for `G ≥ 1`. -/
theorem two_zpow_one_sub {G : ℕ} (hG : 1 ≤ G) : (2 : ℝ) ^ (1 - (G : ℤ)) = 1 / 2 ^ (G - 1) := by
  have h : (1 - (G : ℤ)) = -((G - 1 : ℕ) : ℤ) := by omega
  rw [h, zpow_neg, zpow_natCast, one_div]

/-- [proved-standard; formal-checked] `2^(1−G) = 2 · 2^(−G)`. -/
theorem two_zpow_one_sub_eq (G : ℕ) : (2 : ℝ) ^ (1 - (G : ℤ)) = 2 * 2 ^ (-(G : ℤ)) := by
  rw [show (1 - (G : ℤ)) = 1 + -(G : ℤ) by ring, zpow_add₀ (by norm_num), zpow_one]

/-! ## 1. The mantissa reading -/

/-- [definition] **The shift** of a face `N` read at width `G`: the bits below its top `G`,
`s = (⌊log₂ N⌋ + 1) − G`, zero when `N` has at most `G` bits. -/
def shift (G N : ℕ) : ℕ := Nat.log 2 N + 1 - G

/-- [definition] **The mantissa** of `N` at width `G`: its top `G` bits, `m = ⌊N/2^s⌋`. -/
def mantissa (G N : ℕ) : ℕ := N / 2 ^ shift G N

/-- [proved-standard; formal-checked] The mantissa's scale is at most the face: `m · 2^s ≤ N`. -/
theorem mantissa_mul_le (G N : ℕ) : mantissa G N * 2 ^ shift G N ≤ N :=
  Nat.div_mul_le_self _ _

/-- [proved-standard; formal-checked] The face is below the next scale: `N < (m + 1) · 2^s`. -/
theorem lt_mantissa_succ_mul (G N : ℕ) : N < (mantissa G N + 1) * 2 ^ shift G N := by
  have h := Nat.lt_div_mul_add (a := N) (pow_pos (two_pos : 0 < 2) (shift G N))
  unfold mantissa
  linarith

/-- [proved-standard; formal-checked] A face of at most `G` bits is read on itself: `s = 0`. -/
theorem shift_eq_zero {G N : ℕ} (hG : 1 ≤ G) (hN : N < 2 ^ G) : shift G N = 0 := by
  have : Nat.log 2 N < G := Nat.log_lt_of_lt_pow' (by omega) hN
  unfold shift
  omega

/-- [proved-standard; formal-checked] A face of at most `G` bits is its own mantissa: `m = N`. -/
theorem mantissa_eq_self {G N : ℕ} (hG : 1 ≤ G) (hN : N < 2 ^ G) : mantissa G N = N := by
  simp [mantissa, shift_eq_zero hG hN]

/-- [proved-standard; formal-checked] The shift leaves the top bit in place: `2^s ≤ N` for `N ≥ 1`. -/
theorem two_pow_shift_le {G N : ℕ} (hG : 1 ≤ G) (hN : 0 < N) : 2 ^ shift G N ≤ N := by
  have hL : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hs : shift G N ≤ Nat.log 2 N := by unfold shift; omega
  exact (Nat.pow_le_pow_right (by norm_num) hs).trans hL

/-- [proved-standard; formal-checked] A positive face has a positive mantissa. -/
theorem mantissa_pos {G N : ℕ} (hG : 1 ≤ G) (hN : 0 < N) : 0 < mantissa G N :=
  Nat.div_pos (two_pow_shift_le hG hN) (by positivity)

/-- [proved-standard; formal-checked] **The mantissa has `G` bits**: `2^G ≤ N` gives `2^(G−1) ≤ m < 2^G`. -/
theorem mantissa_bounds {G N : ℕ} (hG : 1 ≤ G) (hN : 2 ^ G ≤ N) :
    2 ^ (G - 1) ≤ mantissa G N ∧ mantissa G N < 2 ^ G := by
  have hN0 : N ≠ 0 := by have := Nat.one_le_two_pow (n := G); omega
  have hL : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 hN0
  have hL' : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have hGL : G ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) hN
  have hs : shift G N = Nat.log 2 N + 1 - G := rfl
  constructor
  · rw [mantissa, Nat.le_div_iff_mul_le (by positivity), ← pow_add]
    calc 2 ^ (G - 1 + shift G N) = 2 ^ Nat.log 2 N := by congr 1; omega
      _ ≤ N := hL
  · rw [mantissa, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    calc N < 2 ^ (Nat.log 2 N + 1) := hL'
      _ = 2 ^ (G + shift G N) := by congr 1; omega

/-- [proved-standard; formal-checked] `log₂(x · 2^s) = log₂ x + s`. -/
theorem logb_mul_two_pow {x : ℝ} (hx : 0 < x) (s : ℕ) :
    Real.logb 2 (x * 2 ^ s) = Real.logb 2 x + s := by
  rw [Real.logb_mul hx.ne' (by positivity), Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]

/-- [proved-standard; formal-checked] **The mantissa reading**: `s + log₂ m ≤ log₂ N < s + log₂(m + 1)`. -/
theorem logb_mantissa_encl {G N : ℕ} (hG : 1 ≤ G) (hN : 0 < N) :
    (shift G N : ℝ) + Real.logb 2 (mantissa G N) ≤ Real.logb 2 N ∧
      Real.logb 2 N < shift G N + Real.logb 2 ((mantissa G N : ℝ) + 1) := by
  have hm : (0 : ℝ) < mantissa G N := by exact_mod_cast mantissa_pos hG hN
  have h1 : ((mantissa G N : ℝ)) * 2 ^ shift G N ≤ N := by exact_mod_cast mantissa_mul_le G N
  have h2 : (N : ℝ) < ((mantissa G N : ℝ) + 1) * 2 ^ shift G N := by
    exact_mod_cast lt_mantissa_succ_mul G N
  constructor
  · have := Real.logb_le_logb_of_le one_lt_two (by positivity) h1
    rw [logb_mul_two_pow hm] at this
    linarith
  · have := Real.logb_lt_logb one_lt_two (by exact_mod_cast hN) h2
    rw [logb_mul_two_pow (by positivity)] at this
    linarith

/-- [proved-derived; formal-checked] **The residual is a rebase's**: `0 ≤ log₂ N − s − log₂ m < 1/(m ln 2)`. -/
theorem residual_lt {G N : ℕ} (hG : 1 ≤ G) (hN : 0 < N) :
    0 ≤ Real.logb 2 N - (shift G N + Real.logb 2 (mantissa G N)) ∧
      Real.logb 2 N - (shift G N + Real.logb 2 (mantissa G N)) <
        1 / (mantissa G N * Real.log 2) := by
  have hm1 : (1 : ℝ) ≤ mantissa G N := by exact_mod_cast mantissa_pos hG hN
  have hp : (0 : ℝ) < 2 ^ shift G N := by positivity
  have h1 : ((mantissa G N : ℝ)) * 2 ^ shift G N ≤ N := by exact_mod_cast mantissa_mul_le G N
  have h2 : (N : ℝ) < ((mantissa G N : ℝ) + 1) * 2 ^ shift G N := by
    exact_mod_cast lt_mantissa_succ_mul G N
  have hx1 : (mantissa G N : ℝ) ≤ N / 2 ^ shift G N := by rw [le_div_iff₀ hp]; exact h1
  have hx2 : (N : ℝ) / 2 ^ shift G N < mantissa G N + 1 := by rw [div_lt_iff₀ hp]; exact h2
  obtain ⟨r0, r1⟩ := Tree.rebase_log_residual.1 hm1 hx1 hx2
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hm : (0 : ℝ) < mantissa G N := by linarith
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have e : Real.logb 2 N - (shift G N + Real.logb 2 (mantissa G N)) =
      Real.log ((N : ℝ) / 2 ^ shift G N / mantissa G N) / Real.log 2 := by
    rw [Real.log_div (by positivity) hm.ne', Real.log_div hN'.ne' hp.ne', Real.log_pow]
    unfold Real.logb
    field_simp
    ring
  rw [e]
  refine ⟨div_nonneg r0 hl2.le, ?_⟩
  rw [div_lt_iff₀ hl2]
  calc Real.log ((N : ℝ) / 2 ^ shift G N / mantissa G N) < 1 / mantissa G N := r1
    _ = 1 / (mantissa G N * Real.log 2) * Real.log 2 := by field_simp

/-! ## 2. The widening -/

/-- [proved-standard; formal-checked] `log₂(m + 1) − log₂ m ≤ 1/(m ln 2)` for `m > 0`. -/
theorem logb_succ_sub_le {m : ℝ} (hm : 0 < m) :
    Real.logb 2 (m + 1) - Real.logb 2 m ≤ 1 / (m * Real.log 2) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [← Real.logb_div (by positivity) hm.ne', Real.logb, div_le_iff₀ hl2]
  calc Real.log ((m + 1) / m) ≤ (m + 1) / m - 1 := Real.log_le_sub_one_of_pos (by positivity)
    _ = 1 / (m * Real.log 2) * Real.log 2 := by field_simp; ring

/-- [proved-standard; formal-checked] `1/(m ln 2) ≤ 2^(1−G)/ln 2` for `m ≥ 2^(G−1)`. -/
theorem inv_mul_log_le {G : ℕ} {m : ℝ} (hG : 1 ≤ G) (hm : 2 ^ (G - 1) ≤ m) :
    1 / (m * Real.log 2) ≤ 2 ^ (1 - (G : ℤ)) / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hp : (0 : ℝ) < 2 ^ (G - 1) := by positivity
  rw [two_zpow_one_sub hG, div_div]
  exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_right hm hl2.le)

/-- [proved-standard; formal-checked] `2^(1−G)/ln 2 < 3 · 2^(−G)`, from `ln 2 > 2/3`. -/
theorem two_zpow_div_log_lt (G : ℕ) : (2 : ℝ) ^ (1 - (G : ℤ)) / Real.log 2 < 3 * 2 ^ (-(G : ℤ)) := by
  have hl : (2 : ℝ) / 3 < Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
  have hl2 : 0 < Real.log 2 := by linarith
  have hp : (0 : ℝ) < 2 ^ (-(G : ℤ)) := by positivity
  rw [two_zpow_one_sub_eq, div_lt_iff₀ hl2]
  nlinarith

/-- [proved-standard; formal-checked] **The widening's bound**: `m ≥ 2^(G−1)` gives `log₂(m+1) − log₂ m < 3·2^(−G)`. -/
theorem logb_succ_sub_lt {G : ℕ} {m : ℝ} (hG : 1 ≤ G) (hm : 2 ^ (G - 1) ≤ m) :
    Real.logb 2 (m + 1) - Real.logb 2 m < 3 * 2 ^ (-(G : ℤ)) := by
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hm
  exact (logb_succ_sub_le hm0).trans_lt ((inv_mul_log_le hG hm).trans_lt (two_zpow_div_log_lt G))

/-- [proved-derived; formal-checked] Strict widening: `lo ≤ log₂ m ≤ hi` gives `s + lo ≤ log₂ N < s + hi + 3·2^(−G)`. -/
theorem widen_lt {G N : ℕ} {lo hi : ℝ} (hG : 1 ≤ G) (hN : 0 < N)
    (hlo : lo ≤ Real.logb 2 (mantissa G N)) (hhi : Real.logb 2 (mantissa G N) ≤ hi) :
    (shift G N : ℝ) + lo ≤ Real.logb 2 N ∧ Real.logb 2 N < shift G N + hi + 3 * 2 ^ (-(G : ℤ)) := by
  obtain ⟨e1, e2⟩ := logb_mantissa_encl hG hN
  have hp : (0 : ℝ) < 2 ^ (-(G : ℤ)) := by positivity
  refine ⟨by linarith, ?_⟩
  rcases lt_or_ge N (2 ^ G) with hn | hn
  · have hs : shift G N = 0 := shift_eq_zero hG hn
    have hm : mantissa G N = N := mantissa_eq_self hG hn
    rw [hm] at hhi
    rw [hs]
    push_cast
    linarith
  · have hb := (mantissa_bounds hG hn).1
    have hb' : (2 : ℝ) ^ (G - 1) ≤ mantissa G N := by exact_mod_cast hb
    have := logb_succ_sub_lt hG hb'
    linarith

/-- [proved-derived; formal-checked] **The widening**: `lo ≤ log₂ m ≤ hi` ⇒ `s + lo ≤ log₂ N ≤ s + hi + 3·2^(−G)`. -/
theorem widen {G N : ℕ} {lo hi : ℝ} (hG : 1 ≤ G) (hN : 0 < N)
    (hlo : lo ≤ Real.logb 2 (mantissa G N)) (hhi : Real.logb 2 (mantissa G N) ≤ hi) :
    (shift G N : ℝ) + lo ≤ Real.logb 2 N ∧ Real.logb 2 N ≤ shift G N + hi + 3 * 2 ^ (-(G : ℤ)) :=
  ⟨(widen_lt hG hN hlo hhi).1, (widen_lt hG hN hlo hhi).2.le⟩

/-! ## 3. A face read on its own mantissa -/

/-- [proved-standard; formal-checked] `log₂ 2^s = s` for `s : ℤ`. -/
theorem logb_two_zpow (s : ℤ) : Real.logb 2 ((2 : ℝ) ^ s) = s := by
  rw [Real.logb, Real.log_zpow, mul_div_assoc, div_self (Real.log_pos one_lt_two).ne', mul_one]

/-- [proved-standard; formal-checked] The widening lies below the grid two octaves up: `3 · 2^(−G) < 2^(2−G)`. -/
theorem widening_lt_grid (G : ℕ) : 3 * (2 : ℝ) ^ (-(G : ℤ)) < 2 ^ (2 - (G : ℤ)) := by
  have hp : (0 : ℝ) < 2 ^ (-(G : ℤ)) := by positivity
  rw [show (2 - (G : ℤ)) = 2 + -(G : ℤ) by ring, zpow_add₀ (by norm_num)]
  norm_num

/-- [definition] **The face's shift** at width `G`: `s = G − 1 − ⌊log₂ q⌋` (`Int.log`), so that
`q 2^s ∈ [2^(G−1), 2^G)`; negative when `q` is above `2^(G−1)`. -/
def faceShift (G : ℕ) (q : ℚ) : ℤ := G - 1 - Int.log 2 q

/-- [definition] **The face's mantissa** at width `G`: `m = ⌊q 2^s⌋`, its top `G` bits. -/
def faceMantissa (G : ℕ) (q : ℚ) : ℕ := ⌊q * 2 ^ faceShift G q⌋₊

/-- [proved-standard; formal-checked] A face's mantissa: `2^(G−1) ≤ m < 2^G` and `m ≤ q 2^s < m + 1`. -/
theorem faceMantissa_bounds {G : ℕ} {q : ℚ} (hG : 1 ≤ G) (hq : 0 < q) :
    (2 ^ (G - 1) ≤ faceMantissa G q ∧ faceMantissa G q < 2 ^ G) ∧
      ((faceMantissa G q : ℚ) ≤ q * 2 ^ faceShift G q ∧
        q * 2 ^ faceShift G q < faceMantissa G q + 1) := by
  have h1 : (2 : ℚ) ^ Int.log 2 q ≤ q := by exact_mod_cast Int.zpow_log_le_self one_lt_two hq
  have h2 : q < (2 : ℚ) ^ (Int.log 2 q + 1) := by exact_mod_cast Int.lt_zpow_succ_log_self one_lt_two q
  have hp : (0 : ℚ) < 2 ^ faceShift G q := by positivity
  have hG1 : ((G - 1 : ℕ) : ℤ) = Int.log 2 q + faceShift G q := by unfold faceShift; omega
  have hG2 : (G : ℤ) = Int.log 2 q + 1 + faceShift G q := by unfold faceShift; omega
  have lo : (2 : ℚ) ^ (G - 1) ≤ q * 2 ^ faceShift G q := by
    rw [← zpow_natCast, hG1, zpow_add₀ (by norm_num)]
    exact mul_le_mul_of_nonneg_right h1 hp.le
  have hi : q * 2 ^ faceShift G q < (2 : ℚ) ^ G := by
    rw [← zpow_natCast, hG2, zpow_add₀ (by norm_num)]
    exact mul_lt_mul_of_pos_right h2 hp
  have hx : (0 : ℚ) ≤ q * 2 ^ faceShift G q := by positivity
  refine ⟨⟨Nat.le_floor (by exact_mod_cast lo), (Nat.floor_lt hx).2 (by exact_mod_cast hi)⟩,
    Nat.floor_le hx, Nat.lt_floor_add_one _⟩

/-- [proved-derived; formal-checked] **Wide-face reading**: `s − log₂ m ∈ [lo, hi]` ⇒ `−log₂ q ∈ [lo−3·2^(−G), hi]`. -/
theorem face_widen {G : ℕ} {q : ℚ} {lo hi : ℝ} (hG : 1 ≤ G) (hq : 0 < q)
    (hlo : lo ≤ (faceShift G q : ℝ) - Real.logb 2 (faceMantissa G q))
    (hhi : (faceShift G q : ℝ) - Real.logb 2 (faceMantissa G q) ≤ hi) :
    lo - 3 * 2 ^ (-(G : ℤ)) ≤ -Real.logb 2 (q : ℝ) ∧ -Real.logb 2 (q : ℝ) ≤ hi := by
  obtain ⟨⟨b1, -⟩, c1, c2⟩ := faceMantissa_bounds hG hq
  have c1' : ((faceMantissa G q : ℕ) : ℝ) ≤ (q : ℝ) * 2 ^ faceShift G q := by
    have := (Rat.cast_le (K := ℝ)).mpr c1
    push_cast at this
    exact this
  have c2' : (q : ℝ) * 2 ^ faceShift G q < (faceMantissa G q : ℝ) + 1 := by
    have := (Rat.cast_lt (K := ℝ)).mpr c2
    push_cast at this
    exact this
  have b1' : (2 : ℝ) ^ (G - 1) ≤ faceMantissa G q := by exact_mod_cast b1
  have hm : (0 : ℝ) < faceMantissa G q := lt_of_lt_of_le (by positivity) b1'
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have e : Real.logb 2 (q : ℝ) = Real.logb 2 ((q : ℝ) * 2 ^ faceShift G q) - faceShift G q := by
    rw [Real.logb_mul hq'.ne' (by positivity), logb_two_zpow]
    ring
  have l1 := Real.logb_le_logb_of_le one_lt_two hm c1'
  have l2 := Real.logb_lt_logb one_lt_two (by positivity) c2'
  have l3 := logb_succ_sub_lt hG b1'
  rw [e]
  constructor <;> linarith

/-- [proved-derived; formal-checked] An integer face `N ≥ 2^(G−1)` reads as before: shift `−s`, mantissa `m`. -/
theorem face_natCast {G N : ℕ} (hG : 1 ≤ G) (hN : 2 ^ (G - 1) ≤ N) :
    faceShift G N = -(shift G N : ℤ) ∧ faceMantissa G N = mantissa G N := by
  have hlog : Int.log 2 (N : ℚ) = Nat.log 2 N := Int.log_natCast 2 N
  have hGL : G - 1 ≤ Nat.log 2 N := Nat.le_log_of_pow_le one_lt_two hN
  have hs : faceShift G N = -(shift G N : ℤ) := by
    unfold faceShift shift
    rw [hlog]
    omega
  refine ⟨hs, ?_⟩
  unfold faceMantissa mantissa
  rw [hs, zpow_neg, zpow_natCast, ← div_eq_mul_inv]
  exact_mod_cast Nat.floor_div_eq_div (K := ℚ) N (2 ^ shift G N)

/-! ## 4. A face's code length from its two parts -/

/-- [definition] **The floor read** of `log₂ m` at `B` fraction bits: `k ≤ 2^B log₂ m < k + 1`. -/
def FloorRead (B m : ℕ) (k : ℤ) : Prop :=
  (k : ℝ) ≤ 2 ^ B * Real.logb 2 m ∧ 2 ^ B * Real.logb 2 m < k + 1

/-- [proved-standard; formal-checked] A floor read encloses: `k/2^B ≤ log₂ m < (k + 1)/2^B`. -/
theorem FloorRead.encl {B m : ℕ} {k : ℤ} (h : FloorRead B m k) :
    (k : ℝ) / 2 ^ B ≤ Real.logb 2 m ∧ Real.logb 2 m < (k + 1) / 2 ^ B := by
  have hp : (0 : ℝ) < 2 ^ B := by positivity
  refine ⟨?_, ?_⟩
  · rw [div_le_iff₀ hp]; linarith [h.1]
  · rw [lt_div_iff₀ hp]; linarith [h.2]

/-- [proved-derived; formal-checked] `BinaryLog.log_encl` at `j` bits `f`, top bit `w`, is a floor read `w 2^j + f`. -/
theorem floorRead_of_encl {P lo hi j f m w : ℕ} (hm : 0 < m)
    (h : BinaryLog.Encl P (((m : ℝ) / 2 ^ w) ^ 2 ^ j / 2 ^ f) lo hi) :
    FloorRead j m ((w : ℤ) * 2 ^ j + f) := by
  obtain ⟨h1, h2⟩ := BinaryLog.log_encl hm h
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  have e1 : (w : ℝ) + f / 2 ^ j = ((w : ℝ) * 2 ^ j + f) / 2 ^ j := by field_simp
  have e2 : (w : ℝ) + (f + 1) / 2 ^ j = ((w : ℝ) * 2 ^ j + f + 1) / 2 ^ j := by field_simp; ring
  rw [e1, div_le_iff₀ hp] at h1
  rw [e2, lt_div_iff₀ hp] at h2
  unfold FloorRead
  push_cast
  constructor <;> linarith

/-- [proved-standard; formal-checked] A difference of enclosures encloses the difference, at the summed width. -/
theorem sub_encl {a b la ua lb ub : ℝ} (ha : la ≤ a ∧ a ≤ ua) (hb : lb ≤ b ∧ b ≤ ub) :
    (lb - ua ≤ b - a ∧ b - a ≤ ub - la) ∧ (ub - la) - (lb - ua) = (ua - la) + (ub - lb) :=
  ⟨⟨by linarith [ha.2, hb.1], by linarith [ha.1, hb.2]⟩, by ring⟩

/-- [proved-standard; formal-checked] `−log₂(n/d) = log₂ d − log₂ n` for `n, d ≥ 1`. -/
theorem neg_logb_div {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    -Real.logb 2 ((n : ℝ) / d) = Real.logb 2 d - Real.logb 2 n := by
  rw [Real.logb_div (by positivity) (by positivity)]
  ring

/-- [definition] **The enclosure of a face's code length**, lower end: the denominator's lower end
less the numerator's widened upper end, each read on its mantissa at width `G` and its floor read
`k` at `B` fraction bits. -/
noncomputable def codeLo (G B n d : ℕ) (kn kd : ℤ) : ℝ :=
  (shift G d + kd / 2 ^ B) - (shift G n + (kn + 1) / 2 ^ B + 3 * 2 ^ (-(G : ℤ)))

/-- [definition] **The enclosure of a face's code length**, upper end: the denominator's widened
upper end less the numerator's lower end. -/
noncomputable def codeHi (G B n d : ℕ) (kn kd : ℤ) : ℝ :=
  (shift G d + (kd + 1) / 2 ^ B + 3 * 2 ^ (-(G : ℤ))) - (shift G n + kn / 2 ^ B)

/-- [proved-derived; formal-checked] **A face's code length, enclosed**: `codeLo ≤ −log₂(n/d) ≤ codeHi`. -/
theorem codeLength_encl {G B n d : ℕ} {kn kd : ℤ} (hG : 1 ≤ G) (hn : 0 < n) (hd : 0 < d)
    (hkn : FloorRead B (mantissa G n) kn) (hkd : FloorRead B (mantissa G d) kd) :
    codeLo G B n d kn kd ≤ -Real.logb 2 ((n : ℝ) / d) ∧
      -Real.logb 2 ((n : ℝ) / d) ≤ codeHi G B n d kn kd := by
  obtain ⟨n1, n2⟩ := hkn.encl
  obtain ⟨d1, d2⟩ := hkd.encl
  have wn := widen hG hn n1 n2.le
  have wd := widen hG hd d1 d2.le
  rw [neg_logb_div hn hd]
  exact (sub_encl wn wd).1

/-- [proved-derived; formal-checked] **The code length's width**: `codeHi − codeLo = 2^(1−B) + 6 · 2^(−G)`. -/
theorem codeHi_sub_codeLo (G B n d : ℕ) (kn kd : ℤ) :
    codeHi G B n d kn kd - codeLo G B n d kn kd = 2 ^ (1 - (B : ℤ)) + 6 * 2 ^ (-(G : ℤ)) := by
  rw [two_zpow_one_sub_eq, two_zpow_neg B]
  unfold codeHi codeLo
  ring

/-! ## 5. The product bound -/

/-- [definition] **Kept at `K` bits, rounded down**: `⌊x/2^s⌋ · 2^s`, `s` the shift at width `K`;
its kept part is the mantissa `mantissa K x`. -/
def keepDown (K x : ℕ) : ℕ := x / 2 ^ shift K x * 2 ^ shift K x

/-- [definition] **Kept at `K` bits, rounded up**: `⌈x/2^s⌉ · 2^s`, the ceiling read as
`⌊(x + 2^s − 1)/2^s⌋`. -/
def keepUp (K x : ℕ) : ℕ := (x + 2 ^ shift K x - 1) / 2 ^ shift K x * 2 ^ shift K x

/-- [proved-standard; formal-checked] Rounding down keeps the mantissa: `keepDown K x = m · 2^s`. -/
theorem keepDown_eq (K x : ℕ) : keepDown K x = mantissa K x * 2 ^ shift K x := rfl

/-- [proved-standard; formal-checked] Rounding down stays at or below: `keepDown K x ≤ x`. -/
theorem keepDown_le (K x : ℕ) : keepDown K x ≤ x := Nat.div_mul_le_self _ _

/-- [proved-standard; formal-checked] Rounding up stays above by less than a unit: `x ≤ keepUp K x < x + 2^s`. -/
theorem le_keepUp (K x : ℕ) : x ≤ keepUp K x ∧ keepUp K x < x + 2 ^ shift K x := by
  have hp : 0 < 2 ^ shift K x := by positivity
  have h1 := Nat.lt_div_mul_add (a := x + 2 ^ shift K x - 1) hp
  have h2 := Nat.div_mul_le_self (x + 2 ^ shift K x - 1) (2 ^ shift K x)
  unfold keepUp
  constructor <;> omega

/-- [proved-standard; formal-checked] **The kept part has `K` bits**: floor in `[2^(K−1), 2^K)`, ceiling up to `2^K`. -/
theorem kept_bounds {K x : ℕ} (hK : 1 ≤ K) (hx : 2 ^ K ≤ x) :
    (2 ^ (K - 1) ≤ x / 2 ^ shift K x ∧ x / 2 ^ shift K x < 2 ^ K) ∧
      (2 ^ (K - 1) ≤ (x + 2 ^ shift K x - 1) / 2 ^ shift K x ∧
        (x + 2 ^ shift K x - 1) / 2 ^ shift K x ≤ 2 ^ K) := by
  obtain ⟨b1, b2⟩ := mantissa_bounds hK hx
  have hp : 0 < 2 ^ shift K x := by positivity
  refine ⟨⟨b1, b2⟩, ?_, ?_⟩
  · exact b1.trans (Nat.div_le_div_right (by omega))
  · have hc := lt_mantissa_succ_mul K x
    have hle : x ≤ 2 ^ shift K x * 2 ^ K := by
      have : mantissa K x + 1 ≤ 2 ^ K := b2
      nlinarith
    rw [Nat.div_le_iff_le_mul_add_pred hp]
    omega

/-- [proved-standard; formal-checked] `x < (m + 1) A` and `P ≤ m` give `x P ≤ m A (P + 1)`. -/
theorem floor_step_nat {x m A P : ℕ} (hlt : x < (m + 1) * A) (hq : P ≤ m) :
    x * P ≤ m * A * (P + 1) := by
  have e1 := Nat.mul_le_mul_right P (Nat.succ_le_of_lt hlt)
  have e2 := Nat.mul_le_mul_left A hq
  rw [Nat.succ_eq_add_one] at e1
  nlinarith [e1, e2]

/-- [proved-standard; formal-checked] Rounding down, in integers: `x 2^(K−1) ≤ keepDown K x · (2^(K−1) + 1)`. -/
theorem le_keepDown_nat {K x : ℕ} (hK : 1 ≤ K) :
    x * 2 ^ (K - 1) ≤ keepDown K x * (2 ^ (K - 1) + 1) := by
  rcases Nat.eq_zero_or_pos (shift K x) with hs | hs
  · rw [keepDown, hs]; simp; nlinarith [Nat.one_le_two_pow (n := K - 1)]
  · have hx : 2 ^ K ≤ x := by
      have hl : K ≤ Nat.log 2 x := by unfold shift at hs; omega
      exact (Nat.pow_le_pow_right (by norm_num) hl).trans
        (Nat.pow_log_le_self 2 (by intro h; rw [h] at hl; simp at hl; omega))
    have hq := (mantissa_bounds hK hx).1
    have hlt := lt_mantissa_succ_mul K x
    rw [keepDown_eq]
    exact floor_step_nat hlt hq

/-- [proved-standard; formal-checked] Rounding up, in integers: `keepUp K x · 2^(K−1) ≤ x · (2^(K−1) + 1)`. -/
theorem keepUp_le_nat {K x : ℕ} (hK : 1 ≤ K) :
    keepUp K x * 2 ^ (K - 1) ≤ x * (2 ^ (K - 1) + 1) := by
  obtain ⟨_, hu⟩ := le_keepUp K x
  rcases Nat.eq_zero_or_pos (shift K x) with hs | hs
  · rw [hs] at hu
    have : keepUp K x ≤ x := by simpa using Nat.lt_succ_iff.mp hu
    have := Nat.mul_le_mul_right (2 ^ (K - 1)) this
    nlinarith
  · have hx : 2 ^ K ≤ x := by
      have hl : K ≤ Nat.log 2 x := by unfold shift at hs; omega
      exact (Nat.pow_le_pow_right (by norm_num) hl).trans
        (Nat.pow_log_le_self 2 (by intro h; rw [h] at hl; simp at hl; omega))
    have hq := (mantissa_bounds hK hx).1
    have h1 := mantissa_mul_le K x
    have hP : 2 ^ shift K x * 2 ^ (K - 1) ≤ x := by
      calc 2 ^ shift K x * 2 ^ (K - 1) ≤ 2 ^ shift K x * mantissa K x := Nat.mul_le_mul_left _ hq
        _ ≤ x := by rw [mul_comm]; exact h1
    nlinarith

/-- [proved-standard; formal-checked] `1 + 2^(1−K) = (2^(K−1) + 1)/2^(K−1)` for `K ≥ 1`. -/
theorem one_add_two_zpow {K : ℕ} (hK : 1 ≤ K) :
    (1 + 2 ^ (1 - (K : ℤ)) : ℝ) = (2 ^ (K - 1) + 1) / 2 ^ (K - 1) := by
  rw [two_zpow_one_sub hK]
  field_simp

/-- [proved-standard; formal-checked] **Rounding down's factor**: `x ≤ (1 + 2^(1−K)) · keepDown K x`. -/
theorem le_keepDown {K x : ℕ} (hK : 1 ≤ K) :
    (x : ℝ) ≤ (1 + 2 ^ (1 - (K : ℤ))) * keepDown K x := by
  have h : ((x * 2 ^ (K - 1) : ℕ) : ℝ) ≤ ((keepDown K x * (2 ^ (K - 1) + 1) : ℕ) : ℝ) := by
    exact_mod_cast le_keepDown_nat hK
  push_cast at h
  have hp : (0 : ℝ) < 2 ^ (K - 1) := by positivity
  rw [one_add_two_zpow hK, div_mul_eq_mul_div, le_div_iff₀ hp]
  linarith

/-- [proved-standard; formal-checked] **Rounding up's factor**: `keepUp K x ≤ (1 + 2^(1−K)) · x`. -/
theorem keepUp_le {K x : ℕ} (hK : 1 ≤ K) :
    (keepUp K x : ℝ) ≤ (1 + 2 ^ (1 - (K : ℤ))) * x := by
  have h : ((keepUp K x * 2 ^ (K - 1) : ℕ) : ℝ) ≤ ((x * (2 ^ (K - 1) + 1) : ℕ) : ℝ) := by
    exact_mod_cast keepUp_le_nat hK
  push_cast at h
  have hp : (0 : ℝ) < 2 ^ (K - 1) := by positivity
  rw [one_add_two_zpow hK, div_mul_eq_mul_div, le_div_iff₀ hp]
  linarith

/-- [definition] **The lower side of a product's enclosure** from `lo`: after each factor, the
product kept at `K` bits rounded down (`ProductBound::times` with `up = false`). -/
def lowerFrom (K lo : ℕ) (l : List ℕ) : ℕ := l.foldl (fun acc a => keepDown K (acc * a)) lo

/-- [definition] **The upper side of a product's enclosure** from `hi`: after each factor, the
product kept at `K` bits rounded up (`ProductBound::times` with `up = true`). -/
def upperFrom (K hi : ℕ) (l : List ℕ) : ℕ := l.foldl (fun acc a => keepUp K (acc * a)) hi

/-- [definition] The lower side of the product of `l`, from the empty product `1`. -/
def productLower (K : ℕ) (l : List ℕ) : ℕ := lowerFrom K 1 l

/-- [definition] The upper side of the product of `l`, from the empty product `1`. -/
def productUpper (K : ℕ) (l : List ℕ) : ℕ := upperFrom K 1 l

/-- [proved-standard; formal-checked] The lower side stays below: `lo ≤ P ⇒ lowerFrom ≤ P · ∏ l`. -/
theorem lowerFrom_le (K : ℕ) :
    ∀ (l : List ℕ) (lo P : ℕ), lo ≤ P → lowerFrom K lo l ≤ P * l.prod
  | [], lo, P, h => by simpa [lowerFrom] using h
  | a :: l, lo, P, h => by
    have h' : keepDown K (lo * a) ≤ P * a := (keepDown_le K _).trans (Nat.mul_le_mul_right a h)
    have := lowerFrom_le K l _ _ h'
    simp only [lowerFrom, List.foldl_cons] at this ⊢
    rw [List.prod_cons, ← mul_assoc]
    exact this

/-- [proved-standard; formal-checked] The upper side stays above: `P ≤ hi ⇒ P · ∏ l ≤ upperFrom`. -/
theorem le_upperFrom (K : ℕ) :
    ∀ (l : List ℕ) (hi P : ℕ), P ≤ hi → P * l.prod ≤ upperFrom K hi l
  | [], hi, P, h => by simpa [upperFrom] using h
  | a :: l, hi, P, h => by
    have h' : P * a ≤ keepUp K (hi * a) := (Nat.mul_le_mul_right a h).trans (le_keepUp K _).1
    have := le_upperFrom K l _ _ h'
    simp only [upperFrom, List.foldl_cons] at this ⊢
    rw [List.prod_cons, ← mul_assoc]
    exact this

/-- [proved-standard; formal-checked] **The product enclosure**: `productLower K l ≤ ∏ l ≤ productUpper K l`. -/
theorem product_encl (K : ℕ) (l : List ℕ) : productLower K l ≤ l.prod ∧ l.prod ≤ productUpper K l := by
  constructor
  · simpa [productLower] using lowerFrom_le K l 1 1 le_rfl
  · simpa [productUpper] using le_upperFrom K l 1 1 le_rfl

/-- [proved-standard; formal-checked] Each factor parts the sides by at most `(1 + 2^(1−K))²`, from `hi ≤ c · lo`. -/
theorem upperFrom_le (K : ℕ) (hK : 1 ≤ K) :
    ∀ (l : List ℕ) (lo hi : ℕ) (c : ℝ), 0 ≤ c → (hi : ℝ) ≤ c * lo →
      (upperFrom K hi l : ℝ) ≤ c * (1 + 2 ^ (1 - (K : ℤ))) ^ (2 * l.length) * lowerFrom K lo l
  | [], lo, hi, c, _, h => by simpa [upperFrom, lowerFrom] using h
  | a :: l, lo, hi, c, hc, h => by
    set ρ : ℝ := 1 + 2 ^ (1 - (K : ℤ)) with hρ
    have hρ0 : 0 ≤ ρ := by positivity
    have hstep : (keepUp K (hi * a) : ℝ) ≤ c * ρ ^ 2 * keepDown K (lo * a) := by
      have u := keepUp_le (x := hi * a) hK
      have d := le_keepDown (x := lo * a) hK
      push_cast at u d
      have ha : (0 : ℝ) ≤ a := by positivity
      calc (keepUp K (hi * a) : ℝ) ≤ ρ * (hi * a) := u
        _ ≤ ρ * (c * lo * a) := by gcongr
        _ = ρ * c * (lo * a) := by ring
        _ ≤ ρ * c * (ρ * keepDown K (lo * a)) := by gcongr
        _ = c * ρ ^ 2 * keepDown K (lo * a) := by ring
    have := upperFrom_le K hK l _ _ _ (by positivity) hstep
    simp only [upperFrom, lowerFrom, List.foldl_cons, List.length_cons] at this ⊢
    calc _ ≤ c * ρ ^ 2 * ρ ^ (2 * l.length) * _ := this
      _ = c * ρ ^ (2 * (l.length + 1)) * _ := by ring

/-- [proved-derived; formal-checked] **The spread**: `productUpper K l ≤ (1 + 2^(1−K))^(2k) · productLower K l`. -/
theorem productUpper_le (K : ℕ) (hK : 1 ≤ K) (l : List ℕ) :
    (productUpper K l : ℝ) ≤ (1 + 2 ^ (1 - (K : ℤ))) ^ (2 * l.length) * productLower K l := by
  simpa [productUpper, productLower] using upperFrom_le K hK l 1 1 1 zero_le_one (by simp)

/-- [proved-standard; formal-checked] Positive factors keep the lower side positive. -/
theorem lowerFrom_pos (K : ℕ) (hK : 1 ≤ K) :
    ∀ (l : List ℕ) (lo : ℕ), 0 < lo → (∀ a ∈ l, 0 < a) → 0 < lowerFrom K lo l
  | [], lo, h, _ => by simpa [lowerFrom] using h
  | a :: l, lo, h, hl => by
    have ha : 0 < a := hl a (by simp)
    have hk : 0 < keepDown K (lo * a) := by
      rw [keepDown_eq]
      exact Nat.mul_pos (mantissa_pos hK (Nat.mul_pos h ha)) (by positivity)
    have := lowerFrom_pos K hK l _ hk (fun b hb => hl b (by simp [hb]))
    simpa [lowerFrom] using this

/-- [proved-derived; formal-checked] **Upper over lower**: positive factors give at most `(1 + 2^(1−K))^(2k)`. -/
theorem productUpper_div_le (K : ℕ) (hK : 1 ≤ K) (l : List ℕ) (hl : ∀ a ∈ l, 0 < a) :
    (productUpper K l : ℝ) / productLower K l ≤ (1 + 2 ^ (1 - (K : ℤ))) ^ (2 * l.length) := by
  have hpos : (0 : ℝ) < productLower K l := by exact_mod_cast lowerFrom_pos K hK l 1 one_pos hl
  rw [div_le_iff₀ hpos]
  exact productUpper_le K hK l

/-! ## 6. A witness: `N = 2^100 + 2^99 + 1` at `G = 98` -/

/-- [definition] The witness face, `2^100 + 2^99 + 1`: a 101-bit integer. -/
def witnessN : ℕ := 2 ^ 100 + 2 ^ 99 + 1

/-- [proved-standard; formal-checked] The witness's top bit is bit 100: `⌊log₂ N⌋ = 100`. -/
theorem witness_log : Nat.log 2 witnessN = 100 := by
  unfold witnessN; norm_num

/-- [proved-standard; formal-checked] The witness's shift at `G = 98` is `s = 3`. -/
theorem witness_shift : shift 98 witnessN = 3 := by
  rw [shift, witness_log]

/-- [proved-standard; formal-checked] The witness's mantissa at `G = 98` is `m = 2^97 + 2^96 = 3 · 2^96`. -/
theorem witness_mantissa : mantissa 98 witnessN = 2 ^ 97 + 2 ^ 96 := by
  rw [mantissa, witness_shift, witnessN]; norm_num

/-- [proved-standard; formal-checked] The witness's mantissa: `2^97 ≤ m < 2^98` and `8m ≤ N < 8(m + 1)`. -/
theorem witness_bounds :
    (2 ^ 97 ≤ mantissa 98 witnessN ∧ mantissa 98 witnessN < 2 ^ 98) ∧
      (mantissa 98 witnessN * 2 ^ 3 ≤ witnessN ∧ witnessN < (mantissa 98 witnessN + 1) * 2 ^ 3) := by
  rw [witness_mantissa, witnessN]; norm_num

/-- [proved-standard; formal-checked] Floor read `780` at `B = 3`: `2^12 ≤ 3^8 < 2^13` gives `780 ≤ 8 log₂ m < 781`. -/
theorem witness_floorRead : FloorRead 3 (mantissa 98 witnessN) 780 := by
  rw [witness_mantissa]
  have hm : ((2 ^ 97 + 2 ^ 96 : ℕ) : ℝ) = 3 * 2 ^ 96 := by push_cast; ring
  have e : (2 : ℝ) ^ 3 * Real.logb 2 ((2 ^ 97 + 2 ^ 96 : ℕ) : ℝ) = Real.logb 2 6561 + 768 := by
    rw [hm, logb_mul_two_pow (by norm_num), show (6561 : ℝ) = 3 ^ 8 by norm_num, Real.logb_pow]
    push_cast
    ring
  have p2 : ∀ j : ℕ, Real.logb 2 ((2 : ℝ) ^ j) = j := fun j => by
    rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]
  have l1 : Real.logb 2 ((2 : ℝ) ^ 12) ≤ Real.logb 2 6561 :=
    Real.logb_le_logb_of_le one_lt_two (by positivity) (by norm_num)
  have l2 : Real.logb 2 6561 < Real.logb 2 ((2 : ℝ) ^ 13) :=
    Real.logb_lt_logb one_lt_two (by norm_num) (by norm_num)
  rw [p2] at l1 l2
  unfold FloorRead
  rw [e]
  push_cast at l1 l2 ⊢
  constructor <;> linarith

/-- [proved-derived; formal-checked] **The witness's enclosure**: `100.5 ≤ log₂ N ≤ 100.625 + 3 · 2^(−98)`. -/
theorem witness_encl :
    (201 / 2 : ℝ) ≤ Real.logb 2 witnessN ∧ Real.logb 2 witnessN ≤ 805 / 8 + 3 * 2 ^ (-(98 : ℤ)) := by
  obtain ⟨h1, h2⟩ := witness_floorRead.encl
  have w := widen (G := 98) (N := witnessN) (by norm_num) (by unfold witnessN; norm_num) h1 h2.le
  rw [witness_shift] at w
  push_cast at w
  constructor <;> linarith [w.1, w.2]

/-- [proved-derived; formal-checked] Read as a face, the witness has shift `−3` and mantissa `2^97 + 2^96`. -/
theorem witness_face : faceShift 98 witnessN = -3 ∧ faceMantissa 98 witnessN = 2 ^ 97 + 2 ^ 96 := by
  obtain ⟨h1, h2⟩ := face_natCast (G := 98) (N := witnessN) (by norm_num) (by unfold witnessN; norm_num)
  rw [h1, h2, witness_shift, witness_mantissa]
  norm_num

end Holonics.Compression.WideFaceReading
