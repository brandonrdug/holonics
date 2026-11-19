import Mathlib.Algebra.ContinuedFractions.Computation.Translations
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Int.Log
import Mathlib.Data.Rat.Floor

/-!
# Constants as navigators: the logarithm's atanh series, Taylor enclosures and the shared word

The box of #410 "`series.log-atanh`, `series.log-atanh-exp`, `series.common-continued-fraction`,
`analytic.certified-capture`, `analytic.euler-maclaurin-eta` (constants as navigators, parked in
#409)" owes the Lean statements of five atlas rows (`docs/atlas/arithmetic.tsv`); this file takes
the first three. Their only owner was the retired `crates/holonics/src/geometry/exact_analysis`
(`elementary.rs`: `atanh_log_unit_interval`, `log_rational_interval`, `exp_nonnegative_point`,
`sin_cos_small`, `cis_interval`; `constants.rs`: `interval_common_continued_fraction`;
[history](https://github.com/brandonrdug/holonics/tree/13f8c734/crates/holonics/src/geometry/exact_analysis),
removed at `d329cb541`), whose open paragraph reads "Rational enclosures for receiver-relative
complex analysis". The record
`research/records/2026-09-11_PI_AND_E_CONSTRAINT_IDENTITIES_HAVE_ORIENTED_GENERATOR_FACES.md` reads
π and `e` as constraint identities whose finite partial sums carry their remainder, and the
precision law of `CLAUDE.md` states the reading: π and `e` are navigators, a number is read at a
declared width (a face of its navigator), and a term is released only by partition at a declared
tolerance, with its remainder accounted. Here the declared term count is the partition, the
released tail is the remainder, and the enclosure is the face.

[proved-standard; formal-checked] What is proved.

1. **The logarithm by its atanh series** (`series.log-atanh`). For `x > 0` the coordinate
   `z = (x − 1)/(x + 1)` has `|z| < 1` (`abs_atanhCoord_lt_one`), `log(1 + z) − log(1 − z) = log x`
   (`log_one_add_sub_log_one_sub`), and `log x = 2 Σ_(k≥0) z^(2k+1)/(2k+1)` (`hasSum_log_atanh`,
   from Mathlib's `Real.hasSum_log_sub_log_of_abs_lt_one`). Each tail term sits under a geometric
   term of ratio `z²` (`abs_atanhTerm_add_le`), so the tail after `N` terms is at most
   `2 |z|^(2N+1)/((2N+1)(1 − z²))` (`abs_sub_logPartial_le`, `abs_log_sub_logPartial_le`). For
   `x ≥ 1` the partial sum is a lower end and the partial sum plus that remainder an upper end
   (`atanhCoord_nonneg`, `log_mem_enclosure`).
2. **A declared term count gives a declared width.** On `1 ≤ x ≤ 2`, `z ≤ 1/3`
   (`atanhCoord_le_third`) and the remainder is at most `9/(4 (2N+1) 3^(2N+1))`, which is
   `(9/4) · 3^(−(2N+1))/(2N+1)` (`logRemainder_le_unit`, `log_unit_enclosure`). At `x = 2`,
   `z = 1/3` (`atanhCoord_two`), and four terms give
   `53056/76545 ≤ log 2 ≤ 53056/76545 + 1/78732` (`log_two_enclosure`). Other ratios factor out a
   power of two: `log(2^k y) = k log 2 + log y` (`log_two_zpow_mul`), and every `x > 0` is `2^k y`
   with `1 ≤ y < 2` at `k = Int.log 2 x` (`unit_reduction`), so `N` terms at `1/3` and at `y`
   read `log x` within `(|k| + 1) · 9/(4 (2N+1) 3^(2N+1))` (`abs_log_sub_reduced_le`, the one
   statement here of the house's own composition, [proved-derived; formal-checked]).
3. **Taylor enclosures of `exp`, `cos`, `sin` and `cis`** (`series.log-atanh-exp`). At `|x| ≤ 1`
   and `n ≥ 1` declared terms, `exp x` lies in `[P − r, P + r]` with `P = Σ_(m<n) x^m/m!` and the
   named remainder `r = |x|^n (n+1)/(n! n)` (`expPartial`, `expRemainder`, `exp_mem_enclosure`,
   from Mathlib's `Real.exp_bound`). The first `2N` terms of `exp(i x)` split into the cosine's
   and the sine's alternating partial sums (`cis_partial`), so by Mathlib's `Complex.exp_bound`
   `cis x = exp(i x)` is within `r` at `n = 2N` of `cosPartial x N + i sinPartial x N`
   (`norm_cis_sub_partial_le`); its real and imaginary parts give the cosine's and the sine's
   enclosures (`cos_mem_enclosure`, `sin_mem_enclosure`), and the two together a box containing
   `cis x` (`cis_mem_box`). The reductions that bring a ratio to `|x| ≤ 1` are stated as identities:
   `exp x = exp(x/2^k)^(2^k)` (`exp_eq_pow_halving`), `sin x = 2 sin(x/2) cos(x/2)` and
   `cos x = cos(x/2)² − sin(x/2)²` (`sin_cos_doubling`).
4. **The word an enclosure shares** (`series.common-continued-fraction`,
   [proved-derived; formal-checked]). `commonWord n lo hi` runs the owner's loop on two rationals at
   declared depth `n`: while `⌊lo⌋ = ⌊hi⌋ = a` it emits `a`, stops if an end lands on `a`, and
   otherwise continues on `(1/(hi − a), 1/(lo − a))`; it stops at the first disagreement. The digit
   `cfDigit x i` is the integer part of Mathlib's `IntFractPair.stream x i` (`cfDigit_zero`,
   `cfDigit_succ`, `cfDigit_succ_of_fract_eq_zero`). For every `x` of a linearly ordered field
   with a floor and `lo ≤ x ≤ hi`, each digit of the word is `x`'s digit at the same place
   (`floor_eq_of_mem`, `commonWord_digit`): the head is `(GenContFract.of x).h` and the later digits
   are its partial denominators (`commonWord_head`, `commonWord_partDen`). The word is also as long
   as the enclosure allows: when it stops before its depth, the two ends' digits at the next place
   differ, or both ends' streams end there (`commonWord_maximal`). The law needs no sign on the
   enclosure; the owner's positivity assertion is not used.
5. **Witnesses**, computed by `decide +kernel` on the rational loop. `[355/113 − 10⁻⁶, 355/113 +
   10⁻⁶]` shares `[3; 7]` (`commonWord_around_355_113`), and so does `[3.14159, 3.1416]`
   (`commonWord_five_places`): each holds the convergent `355/113`, whose word is `[3; 7, 16]`
   (`commonWord_point_355_113`, a point enclosure reading the whole word), and the ends of the first
   part at the third digit, `15` below it and `16` above it (`ends_part_around_355_113`). Mathlib's
   twenty-place enclosure of π
   (`piLower`, `piUpper`, `pi_mem_enclosure`) shares nineteen digits (`commonWord_pi`), so π's
   continued fraction begins `[3; 7, 15, 1, 292, 1, 1, 1, 2, 1, 3, 1, 14, 2, 1, 1, 2, 2, 2]`
   (`pi_cfDigit`), and `GenContFract.of π` has head `3` and partial denominators `7, 15, 1, 292`
   (`of_pi_head`).

What is not claimed. `analytic.certified-capture` (relaxed release of a complex source box into a
capture square, with mean-value inclusion) and `analytic.euler-maclaurin-eta` (ζ and η with their
Euler–Maclaurin remainders and jets) stay owed in #410. The owner's rounding of each enclosure out
to a bit grain, and the propagation of enclosures through squaring, doubling and the sum
`k log 2 + log y` as interval arithmetic, are not formalized; the identities they rest on are.
The sine's and cosine's remainders here are the exponential's at `2N` terms, not the sharper
alternating bounds `|x|^(2N)/(2N)!` and `|x|^(2N+1)/(2N+1)!` the owner's small-argument loop used.
The atlas row's reading, that the word is the Farey address the enclosure cannot leave
(`uses:lock.farey-neighbour`), is not proved as a statement on Farey intervals and their mediants;
`commonWord_digit` and `commonWord_maximal` state it on the digits.

The computational object is the helical pair interaction, read on a constant. A navigator (the
atanh series at `z`, the exponential's series at `i x`) carries the pair (current term, partial sum)
one term per tick, and the declared term count releases the tail with its remainder named. The
continued-fraction word is the Farey address of the enclosure: each digit is one letter of the
unimodular word whose products carry the convergents (`Geometry/Farey`, `lock.continued-fraction-word`;
the convergents are Farey neighbours in `Holonics/Aeon/Clock/Lock`), and each inversion
`(lo, hi) ↦ (1/(hi − a), 1/(lo − a))` exchanges the two ends. It is the radix window certificate
of `Compression/Landmark/ConstraintIdentity` (`⌊bᵏ⁺ˡ L⌋ = ⌊bᵏ⁺ˡ U⌋`) read in the
continued-fraction chart. Of the winding guide's six general objects this touches the helix
(`cis x` is a point of the circle read through its Taylor box, and the logarithm's reduction by
powers of two is a carry of whole doublings), the pair (the Farey address of an enclosure and the
exchange of its ends) and faces and placement (an enclosure is a face read at a declared width);
the cell holonomy, the tube and the tower thread stay attached.

Consumers: the atlas rows `series.log-atanh`, `series.log-atanh-exp` and
`series.common-continued-fraction`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Mathematics.ConstantNavigators

open Finset Real

/-! ## 1. The logarithm by its atanh series -/

section Log

/-- [definition] The atanh coordinate of a ratio: `z = (x − 1)/(x + 1)`. -/
noncomputable def atanhCoord (x : ℝ) : ℝ := (x - 1) / (x + 1)

/-- [definition] The `k`-th term of the atanh series: `2 z^(2k+1)/(2k+1)`. -/
noncomputable def atanhTerm (z : ℝ) (k : ℕ) : ℝ := 2 * (1 / (2 * k + 1)) * z ^ (2 * k + 1)

/-- [definition] The logarithm's partial navigator: the first `N` terms of the atanh series. -/
noncomputable def logPartial (z : ℝ) (N : ℕ) : ℝ := ∑ k ∈ range N, atanhTerm z k

/-- [definition] The declared remainder after `N` terms: `2 |z|^(2N+1)/((2N+1)(1 − z²))`. -/
noncomputable def logRemainder (z : ℝ) (N : ℕ) : ℝ :=
  2 * |z| ^ (2 * N + 1) / ((2 * N + 1) * (1 - z ^ 2))

/-- [proved-standard; formal-checked] A positive ratio has its atanh coordinate inside the unit disc. -/
theorem abs_atanhCoord_lt_one {x : ℝ} (hx : 0 < x) : |atanhCoord x| < 1 := by
  unfold atanhCoord
  rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < x + 1), div_lt_one (by linarith), abs_lt]
  constructor <;> linarith

/-- [proved-standard; formal-checked] `log (1 + z) − log (1 − z) = log x` at `z = (x − 1)/(x + 1)`. -/
theorem log_one_add_sub_log_one_sub {x : ℝ} (hx : 0 < x) :
    log (1 + atanhCoord x) - log (1 - atanhCoord x) = log x := by
  have hx1 : x + 1 ≠ 0 := by positivity
  have h1 : 1 + atanhCoord x = 2 * x / (x + 1) := by
    unfold atanhCoord
    field_simp
    ring
  have h2 : 1 - atanhCoord x = 2 / (x + 1) := by
    unfold atanhCoord
    field_simp
    ring
  rw [h1, h2, ← log_div (by positivity) (by positivity)]
  congr 1
  field_simp

/-- [proved-standard; formal-checked] The atanh series sums to the logarithm of every positive ratio. -/
theorem hasSum_log_atanh {x : ℝ} (hx : 0 < x) : HasSum (atanhTerm (atanhCoord x)) (log x) := by
  rw [← log_one_add_sub_log_one_sub hx]
  exact hasSum_log_sub_log_of_abs_lt_one (abs_atanhCoord_lt_one hx)

/-- [proved-standard; formal-checked] Each tail term is under a geometric term of ratio `z²`. -/
theorem abs_atanhTerm_add_le (z : ℝ) (N k : ℕ) :
    |atanhTerm z (k + N)| ≤ 2 / (2 * N + 1) * |z| ^ (2 * N + 1) * (z ^ 2) ^ k := by
  have hpow : |z| ^ (2 * (k + N) + 1) = |z| ^ (2 * N + 1) * (z ^ 2) ^ k := by
    rw [← sq_abs z, ← pow_mul, ← pow_add]
    congr 1
    ring
  have hden : (2 : ℝ) / (2 * ((k + N : ℕ) : ℝ) + 1) ≤ 2 / (2 * N + 1) := by
    gcongr
    exact_mod_cast Nat.le_add_left N k
  unfold atanhTerm
  rw [abs_mul, abs_mul, abs_pow, hpow, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * ((k + N : ℕ) : ℝ) + 1))]
  calc 2 * (1 / (2 * ((k + N : ℕ) : ℝ) + 1)) * (|z| ^ (2 * N + 1) * (z ^ 2) ^ k)
      = 2 / (2 * ((k + N : ℕ) : ℝ) + 1) * (|z| ^ (2 * N + 1) * (z ^ 2) ^ k) := by ring
    _ ≤ 2 / (2 * N + 1) * (|z| ^ (2 * N + 1) * (z ^ 2) ^ k) := by gcongr
    _ = 2 / (2 * N + 1) * |z| ^ (2 * N + 1) * (z ^ 2) ^ k := by ring

/-- [proved-standard; formal-checked] The tail after `N` terms is within the declared remainder. -/
theorem abs_sub_logPartial_le {z : ℝ} (hz : |z| < 1) (N : ℕ) :
    |(log (1 + z) - log (1 - z)) - logPartial z N| ≤ logRemainder z N := by
  have hf := hasSum_log_sub_log_of_abs_lt_one hz
  have htail : HasSum (fun k => atanhTerm z (k + N)) ((log (1 + z) - log (1 - z)) - logPartial z N) :=
    (hasSum_nat_add_iff' N).mpr hf
  have hz2 : z ^ 2 < 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg z]
  have hg : HasSum (fun k : ℕ => 2 / (2 * N + 1) * |z| ^ (2 * N + 1) * (z ^ 2) ^ k)
      (2 / (2 * N + 1) * |z| ^ (2 * N + 1) * (1 - z ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (sq_nonneg z) hz2).mul_left _
  have hR : logRemainder z N = 2 / (2 * N + 1) * |z| ^ (2 * N + 1) * (1 - z ^ 2)⁻¹ := by
    unfold logRemainder
    rw [div_eq_mul_inv, mul_inv]
    ring
  have hup := hasSum_le (fun k => (le_abs_self _).trans (abs_atanhTerm_add_le z N k)) htail hg
  have hlo := hasSum_le (fun k => neg_le_of_abs_le (abs_atanhTerm_add_le z N k)) hg.neg htail
  rw [hR, abs_le]
  exact ⟨hlo, hup⟩

/-- [proved-standard; formal-checked] `log x` is within the declared remainder of its partial navigator. -/
theorem abs_log_sub_logPartial_le {x : ℝ} (hx : 0 < x) (N : ℕ) :
    |log x - logPartial (atanhCoord x) N| ≤ logRemainder (atanhCoord x) N := by
  have h := abs_sub_logPartial_le (abs_atanhCoord_lt_one hx) N
  rwa [log_one_add_sub_log_one_sub hx] at h

/-- [proved-standard; formal-checked] At `x ≥ 1` the atanh coordinate is nonnegative. -/
theorem atanhCoord_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ atanhCoord x :=
  div_nonneg (by linarith) (by linarith)

/-- [proved-standard; formal-checked] At `x ≥ 1`: partial sum `≤ log x ≤` partial sum plus the declared remainder. -/
theorem log_mem_enclosure {x : ℝ} (hx : 1 ≤ x) (N : ℕ) :
    logPartial (atanhCoord x) N ≤ log x ∧
      log x ≤ logPartial (atanhCoord x) N + logRemainder (atanhCoord x) N := by
  have hx0 : 0 < x := by linarith
  have hz := atanhCoord_nonneg hx
  refine ⟨sum_le_hasSum (range N) (fun k _ => ?_) (hasSum_log_atanh hx0), ?_⟩
  · unfold atanhTerm
    exact mul_nonneg (by positivity) (pow_nonneg hz _)
  · have h := abs_log_sub_logPartial_le hx0 N
    linarith [le_abs_self (log x - logPartial (atanhCoord x) N)]

/-- [proved-standard; formal-checked] On `1 ≤ x ≤ 2` the atanh coordinate is at most `1/3`. -/
theorem atanhCoord_le_third {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) : atanhCoord x ≤ 1 / 3 := by
  unfold atanhCoord
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- [proved-standard; formal-checked] On `1 ≤ x ≤ 2` the remainder is at most `9/(4 (2N+1) 3^(2N+1))`. -/
theorem logRemainder_le_unit {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) (N : ℕ) :
    logRemainder (atanhCoord x) N ≤ 9 / (4 * ((2 * N + 1) * 3 ^ (2 * N + 1))) := by
  have hz0 := atanhCoord_nonneg h1
  have hz3 := atanhCoord_le_third h1 h2
  have hsq : (8 : ℝ) / 9 ≤ 1 - atanhCoord x ^ 2 := by nlinarith
  unfold logRemainder
  rw [abs_of_nonneg hz0]
  calc 2 * atanhCoord x ^ (2 * N + 1) / ((2 * N + 1) * (1 - atanhCoord x ^ 2))
      ≤ 2 * (1 / 3) ^ (2 * N + 1) / ((2 * N + 1) * (8 / 9)) := by gcongr
    _ = 9 / (4 * ((2 * N + 1) * 3 ^ (2 * N + 1))) := by
      rw [one_div_pow]
      field_simp
      ring

/-- [proved-standard; formal-checked] **Unit enclosure**: on `[1, 2]`, `N` terms read `log x` within that width. -/
theorem log_unit_enclosure {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) (N : ℕ) :
    logPartial (atanhCoord x) N ≤ log x ∧
      log x ≤ logPartial (atanhCoord x) N + 9 / (4 * ((2 * N + 1) * 3 ^ (2 * N + 1))) := by
  obtain ⟨hl, hu⟩ := log_mem_enclosure h1 N
  exact ⟨hl, hu.trans (by linarith [logRemainder_le_unit h1 h2 N])⟩

/-- [proved-standard; formal-checked] The atanh coordinate of `2` is `1/3`. -/
theorem atanhCoord_two : atanhCoord 2 = 1 / 3 := by
  norm_num [atanhCoord]

/-- [proved-standard; formal-checked] **`log 2` at four terms**: `53056/76545 ≤ log 2 ≤ 53056/76545 + 1/78732`. -/
theorem log_two_enclosure :
    (53056 / 76545 : ℝ) ≤ log 2 ∧ log 2 ≤ 53056 / 76545 + 1 / 78732 := by
  have h := log_unit_enclosure (x := 2) (by norm_num) le_rfl 4
  have hP : logPartial (atanhCoord 2) 4 = 53056 / 76545 := by
    rw [atanhCoord_two]
    norm_num [logPartial, atanhTerm, sum_range_succ]
  rw [hP] at h
  refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
  norm_num

/-- [proved-standard; formal-checked] Factoring out a power of two: `log (2^k y) = k log 2 + log y`. -/
theorem log_two_zpow_mul (k : ℤ) {y : ℝ} (hy : 0 < y) :
    log (2 ^ k * y) = k * log 2 + log y := by
  rw [log_mul (by positivity) hy.ne', log_zpow]

/-- [proved-standard; formal-checked] Every `x > 0` is `2^k y` with `1 ≤ y < 2` at `k = Int.log 2 x`. -/
theorem unit_reduction {x : ℝ} (hx : 0 < x) :
    1 ≤ x / 2 ^ Int.log 2 x ∧ x / 2 ^ Int.log 2 x < 2 ∧
      x = 2 ^ Int.log 2 x * (x / 2 ^ Int.log 2 x) := by
  have h1 := Int.zpow_log_le_self (b := 2) (by norm_num) hx
  have h2 := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) x
  have hp : (0 : ℝ) < 2 ^ Int.log 2 x := by positivity
  push_cast at h1 h2
  rw [zpow_add_one₀ two_ne_zero] at h2
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ hp]
    linarith
  · rw [div_lt_iff₀ hp]
    linarith
  · field_simp

/-- [proved-derived; formal-checked] **Every `x > 0`**: `N` terms read `log x` within `(|k| + 1)` unit widths. -/
theorem abs_log_sub_reduced_le {x : ℝ} (hx : 0 < x) (N : ℕ) :
    |log x - (Int.log 2 x * logPartial (1 / 3) N +
        logPartial (atanhCoord (x / 2 ^ Int.log 2 x)) N)| ≤
      (|(Int.log 2 x : ℝ)| + 1) * (9 / (4 * ((2 * N + 1) * 3 ^ (2 * N + 1)))) := by
  obtain ⟨hy1, hy2, hxy⟩ := unit_reduction hx
  have hy0 : 0 < x / 2 ^ Int.log 2 x := by linarith
  have h2 := log_unit_enclosure (x := 2) (by norm_num) le_rfl N
  rw [atanhCoord_two] at h2
  have hy := log_unit_enclosure hy1 hy2.le N
  have hlog : log x = Int.log 2 x * log 2 + log (x / 2 ^ Int.log 2 x) := by
    conv_lhs => rw [hxy]
    exact log_two_zpow_mul _ hy0
  have hsplit : log x - (Int.log 2 x * logPartial (1 / 3) N +
        logPartial (atanhCoord (x / 2 ^ Int.log 2 x)) N) =
      Int.log 2 x * (log 2 - logPartial (1 / 3) N) +
        (log (x / 2 ^ Int.log 2 x) - logPartial (atanhCoord (x / 2 ^ Int.log 2 x)) N) := by
    rw [hlog]
    ring
  have hw : 0 ≤ (9 : ℝ) / (4 * ((2 * N + 1) * 3 ^ (2 * N + 1))) := by positivity
  have ha : |log 2 - logPartial (1 / 3) N| ≤ 9 / (4 * ((2 * N + 1) * 3 ^ (2 * N + 1))) := by
    rw [abs_le]
    constructor <;> linarith [h2.1, h2.2]
  have hb : |log (x / 2 ^ Int.log 2 x) - logPartial (atanhCoord (x / 2 ^ Int.log 2 x)) N| ≤
      9 / (4 * ((2 * N + 1) * 3 ^ (2 * N + 1))) := by
    rw [abs_le]
    constructor <;> linarith [hy.1, hy.2]
  rw [hsplit]
  calc |(Int.log 2 x : ℝ) * (log 2 - logPartial (1 / 3) N) +
        (log (x / 2 ^ Int.log 2 x) - logPartial (atanhCoord (x / 2 ^ Int.log 2 x)) N)|
      ≤ |(Int.log 2 x : ℝ)| * |log 2 - logPartial (1 / 3) N| +
        |log (x / 2 ^ Int.log 2 x) - logPartial (atanhCoord (x / 2 ^ Int.log 2 x)) N| := by
        rw [← abs_mul]
        exact abs_add_le _ _
    _ ≤ |(Int.log 2 x : ℝ)| * (9 / (4 * ((2 * N + 1) * 3 ^ (2 * N + 1)))) +
        9 / (4 * ((2 * N + 1) * 3 ^ (2 * N + 1))) := by
        gcongr
    _ = (|(Int.log 2 x : ℝ)| + 1) * (9 / (4 * ((2 * N + 1) * 3 ^ (2 * N + 1)))) := by ring

end Log

/-! ## 2. Taylor enclosures of `exp`, `cos`, `sin` and `cis` -/

section Taylor

/-- [definition] The exponential's partial navigator: `Σ_(m<n) x^m/m!`. -/
noncomputable def expPartial (x : ℝ) (n : ℕ) : ℝ := ∑ m ∈ range n, x ^ m / m.factorial

/-- [definition] Its declared remainder at `n` terms: `|x|^n (n+1)/(n! n)`. -/
noncomputable def expRemainder (x : ℝ) (n : ℕ) : ℝ := |x| ^ n * ((n + 1) / (n.factorial * n))

/-- [proved-standard; formal-checked] **`exp`** at `|x| ≤ 1` and `n ≥ 1` terms lies in `[P − r, P + r]`. -/
theorem exp_mem_enclosure {x : ℝ} (hx : |x| ≤ 1) {n : ℕ} (hn : 0 < n) :
    expPartial x n - expRemainder x n ≤ exp x ∧ exp x ≤ expPartial x n + expRemainder x n := by
  have h := Real.exp_bound hx hn
  have hR : expRemainder x n = |x| ^ n * ((n.succ : ℝ) / (n.factorial * n)) := by
    simp [expRemainder]
  rw [← hR] at h
  obtain ⟨h1, h2⟩ := abs_sub_le_iff.mp h
  exact ⟨by unfold expPartial; linarith, by unfold expPartial; linarith⟩

/-- [proved-standard; formal-checked] Halving and squaring: `exp x = exp (x/2^k)^(2^k)`. -/
theorem exp_eq_pow_halving (x : ℝ) (k : ℕ) : exp x = exp (x / 2 ^ k) ^ 2 ^ k := by
  rw [← exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- [definition] The cosine's partial navigator: `Σ_(k<N) (−1)^k x^(2k)/(2k)!`. -/
noncomputable def cosPartial (x : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ range N, (-1) ^ k * x ^ (2 * k) / (2 * k).factorial

/-- [definition] The sine's partial navigator: `Σ_(k<N) (−1)^k x^(2k+1)/(2k+1)!`. -/
noncomputable def sinPartial (x : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ range N, (-1) ^ k * x ^ (2 * k + 1) / (2 * k + 1).factorial

/-- [proved-standard; formal-checked] The first `2N` terms of `exp (i x)` are `cosPartial x N + i sinPartial x N`. -/
theorem cis_partial (x : ℝ) (N : ℕ) :
    ∑ m ∈ range (2 * N), ((x : ℂ) * Complex.I) ^ m / m.factorial =
      (cosPartial x N : ℂ) + (sinPartial x N : ℂ) * Complex.I := by
  induction N with
  | zero => simp [cosPartial, sinPartial]
  | succ N ih =>
    have hc : cosPartial x (N + 1) =
        cosPartial x N + (-1) ^ N * x ^ (2 * N) / (2 * N).factorial := sum_range_succ _ _
    have hs : sinPartial x (N + 1) =
        sinPartial x N + (-1) ^ N * x ^ (2 * N + 1) / (2 * N + 1).factorial := sum_range_succ _ _
    have hI : Complex.I ^ (2 * N) = (-1) ^ N := by rw [pow_mul, Complex.I_sq]
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih, hc, hs]
    push_cast
    rw [mul_pow, mul_pow, pow_succ Complex.I (2 * N), hI]
    ring

/-- [proved-standard; formal-checked] `cis x` is within `expRemainder x (2N)` of `cosPartial x N + i sinPartial x N`. -/
theorem norm_cis_sub_partial_le {x : ℝ} (hx : |x| ≤ 1) {N : ℕ} (hN : 0 < N) :
    ‖Complex.exp (x * Complex.I) - ((cosPartial x N : ℂ) + (sinPartial x N : ℂ) * Complex.I)‖ ≤
      expRemainder x (2 * N) := by
  have hn : ‖(x : ℂ) * Complex.I‖ = |x| := by simp
  have h := Complex.exp_bound (x := (x : ℂ) * Complex.I) (by rw [hn]; exact hx)
    (n := 2 * N) (by omega)
  rw [cis_partial, hn] at h
  refine h.trans (le_of_eq ?_)
  unfold expRemainder
  push_cast
  ring

/-- [proved-standard; formal-checked] **The cosine's enclosure** at `|x| ≤ 1` and `N ≥ 1`. -/
theorem cos_mem_enclosure {x : ℝ} (hx : |x| ≤ 1) {N : ℕ} (hN : 0 < N) :
    cosPartial x N - expRemainder x (2 * N) ≤ cos x ∧
      cos x ≤ cosPartial x N + expRemainder x (2 * N) := by
  have h := norm_cis_sub_partial_le hx hN
  have hre := Complex.abs_re_le_norm
    (Complex.exp (x * Complex.I) - ((cosPartial x N : ℂ) + (sinPartial x N : ℂ) * Complex.I))
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, mul_zero, zero_mul,
    sub_zero] at hre
  obtain ⟨h1, h2⟩ := abs_sub_le_iff.mp (hre.trans h)
  exact ⟨by linarith, by linarith⟩

/-- [proved-standard; formal-checked] **The sine's enclosure** at `|x| ≤ 1` and `N ≥ 1`. -/
theorem sin_mem_enclosure {x : ℝ} (hx : |x| ≤ 1) {N : ℕ} (hN : 0 < N) :
    sinPartial x N - expRemainder x (2 * N) ≤ sin x ∧
      sin x ≤ sinPartial x N + expRemainder x (2 * N) := by
  have h := norm_cis_sub_partial_le hx hN
  have him := Complex.abs_im_le_norm
    (Complex.exp (x * Complex.I) - ((cosPartial x N : ℂ) + (sinPartial x N : ℂ) * Complex.I))
  simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, Complex.exp_ofReal_mul_I_im, mul_zero, mul_one, zero_add,
    add_zero] at him
  obtain ⟨h1, h2⟩ := abs_sub_le_iff.mp (him.trans h)
  exact ⟨by linarith, by linarith⟩

/-- [proved-standard; formal-checked] **The box of `cis x`**: its parts lie in the cosine and sine enclosures. -/
theorem cis_mem_box {x : ℝ} (hx : |x| ≤ 1) {N : ℕ} (hN : 0 < N) :
    (Complex.exp (x * Complex.I)).re ∈
        Set.Icc (cosPartial x N - expRemainder x (2 * N)) (cosPartial x N + expRemainder x (2 * N)) ∧
      (Complex.exp (x * Complex.I)).im ∈
        Set.Icc (sinPartial x N - expRemainder x (2 * N)) (sinPartial x N + expRemainder x (2 * N)) := by
  rw [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  exact ⟨cos_mem_enclosure hx hN, sin_mem_enclosure hx hN⟩

/-- [proved-standard; formal-checked] Doubling: `sin x = 2 sin(x/2) cos(x/2)` and `cos x = cos(x/2)² − sin(x/2)²`. -/
theorem sin_cos_doubling (x : ℝ) :
    sin x = 2 * sin (x / 2) * cos (x / 2) ∧ cos x = cos (x / 2) ^ 2 - sin (x / 2) ^ 2 := by
  have hx : x = 2 * (x / 2) := by ring
  constructor
  · conv_lhs => rw [hx]
    exact sin_two_mul _
  · conv_lhs => rw [hx]
    exact cos_two_mul' _

end Taylor

/-! ## 3. The continued-fraction word an enclosure shares -/

section CommonWord

open GenContFract

/-- [definition] **The common word of an enclosure** `[lo, hi]` at declared depth `n`: while the
floors agree, emit the floor; stop when an endpoint lands on it, otherwise subtract it and invert,
`(lo, hi) ↦ (1/(hi − a), 1/(lo − a))`; stop at the first disagreement. -/
def commonWord : ℕ → ℚ → ℚ → List ℤ
  | 0, _, _ => []
  | n + 1, lo, hi =>
    if ⌊lo⌋ = ⌊hi⌋ then
      if Int.fract lo = 0 ∨ Int.fract hi = 0 then [⌊lo⌋]
      else ⌊lo⌋ :: commonWord n (Int.fract hi)⁻¹ (Int.fract lo)⁻¹
    else []

/-- [definition] The continued-fraction digit of `x` at place `i`, from Mathlib's `IntFractPair.stream`. -/
def cfDigit {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] (x : K) (i : ℕ) :
    Option ℤ :=
  (IntFractPair.stream x i).map IntFractPair.b

variable {K : Type*} [Field K] [LinearOrder K] [FloorRing K]

/-- [proved-standard; formal-checked] The first digit is the floor. -/
theorem cfDigit_zero (x : K) : cfDigit x 0 = some ⌊x⌋ := rfl

/-- [proved-standard; formal-checked] Past a nonzero fractional part the digits are those of its inverse. -/
theorem cfDigit_succ {x : K} (h : Int.fract x ≠ 0) (i : ℕ) :
    cfDigit x (i + 1) = cfDigit (Int.fract x)⁻¹ i := by
  unfold cfDigit
  rw [IntFractPair.stream_succ h]

variable [IsStrictOrderedRing K]

/-- [proved-standard; formal-checked] An integer reads one digit. -/
theorem cfDigit_succ_of_fract_eq_zero {x : K} (h : Int.fract x = 0) (i : ℕ) :
    cfDigit x (i + 1) = none := by
  rw [← Int.self_sub_floor, sub_eq_zero] at h
  unfold cfDigit
  rw [h, IntFractPair.stream_succ_of_int]
  rfl

/-- [proved-standard; formal-checked] Every value of an enclosure whose ends share a floor has that floor. -/
theorem floor_eq_of_mem {lo hi : ℚ} {x : K} (hfl : ⌊lo⌋ = ⌊hi⌋) (hlo : (lo : K) ≤ x)
    (hhi : x ≤ (hi : K)) : ⌊x⌋ = ⌊lo⌋ := by
  have h1 : ⌊lo⌋ ≤ ⌊x⌋ := by
    rw [← Rat.floor_cast (α := K) lo]
    exact Int.floor_mono hlo
  have h2 : ⌊x⌋ ≤ ⌊hi⌋ := by
    rw [← Rat.floor_cast (α := K) hi]
    exact Int.floor_mono hhi
  omega

/-- [proved-derived; formal-checked] **Every value of the enclosure reads the word**, digit by digit. -/
theorem commonWord_digit (n : ℕ) :
    ∀ (lo hi : ℚ) (x : K), (lo : K) ≤ x → x ≤ (hi : K) →
      ∀ (i : ℕ) (a : ℤ), (commonWord n lo hi)[i]? = some a → cfDigit x i = some a := by
  induction n with
  | zero =>
    intro lo hi x _ _ i a h
    simp [commonWord] at h
  | succ n ih =>
    intro lo hi x hlo hhi i a h
    simp only [commonWord] at h
    split_ifs at h with hfl hz
    · have hx := floor_eq_of_mem hfl hlo hhi
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        rw [cfDigit_zero, hx, h]
      | succ j => simp at h
    · have hx := floor_eq_of_mem hfl hlo hhi
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        rw [cfDigit_zero, hx, h]
      | succ j =>
        simp only [List.getElem?_cons_succ] at h
        push Not at hz
        have hlo0 : Int.fract (lo : K) ≠ 0 := by
          rw [← Rat.cast_fract]
          exact_mod_cast hz.1
        have hflo : 0 < Int.fract (lo : K) := lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hlo0)
        have hfl_x : Int.fract (lo : K) ≤ Int.fract x := by
          rw [← Int.self_sub_floor, ← Int.self_sub_floor, hx, Rat.floor_cast]
          linarith
        have hfx_hi : Int.fract x ≤ Int.fract (hi : K) := by
          rw [← Int.self_sub_floor, ← Int.self_sub_floor, hx, Rat.floor_cast, hfl]
          linarith
        have hfx : 0 < Int.fract x := lt_of_lt_of_le hflo hfl_x
        rw [cfDigit_succ hfx.ne']
        refine ih _ _ _ ?_ ?_ j a h
        · rw [Rat.cast_inv, Rat.cast_fract]
          exact inv_anti₀ hfx hfx_hi
        · rw [Rat.cast_inv, Rat.cast_fract]
          exact inv_anti₀ hflo hfl_x
    · simp at h

/-- [proved-derived; formal-checked] The word's head is the head of `GenContFract.of x`. -/
theorem commonWord_head {n : ℕ} {lo hi : ℚ} {x : K} (hlo : (lo : K) ≤ x) (hhi : x ≤ (hi : K))
    {a : ℤ} (h : (commonWord n lo hi)[0]? = some a) : (GenContFract.of x).h = a := by
  have hd := commonWord_digit n lo hi x hlo hhi 0 a h
  rw [cfDigit_zero, Option.some.injEq] at hd
  rw [GenContFract.of_h_eq_floor, hd]

/-- [proved-derived; formal-checked] The word's later digits are the partial denominators of `GenContFract.of x`. -/
theorem commonWord_partDen {n : ℕ} {lo hi : ℚ} {x : K} (hlo : (lo : K) ≤ x) (hhi : x ≤ (hi : K))
    {i : ℕ} {a : ℤ} (h : (commonWord n lo hi)[i + 1]? = some a) :
    (GenContFract.of x).s.get? i = some ⟨1, (a : K)⟩ := by
  have hd := commonWord_digit n lo hi x hlo hhi (i + 1) a h
  unfold cfDigit at hd
  obtain ⟨p, hp, hpb⟩ := Option.map_eq_some_iff.mp hd
  rw [GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream hp, hpb]

/-- [proved-derived; formal-checked] **Maximality**: below its depth the word stops where its ends part or both end. -/
theorem commonWord_maximal (n : ℕ) :
    ∀ (lo hi : ℚ), lo ≤ hi → (commonWord n lo hi).length < n →
      cfDigit lo (commonWord n lo hi).length ≠ cfDigit hi (commonWord n lo hi).length ∨
        (cfDigit lo (commonWord n lo hi).length = none ∧
          cfDigit hi (commonWord n lo hi).length = none) := by
  induction n with
  | zero => intro lo hi _ h; simp at h
  | succ n ih =>
    intro lo hi hle hlen
    simp only [commonWord] at hlen ⊢
    split_ifs at hlen ⊢ with hfl hz
    · simp only [List.length_singleton]
      rcases hz with hz | hz
      · rw [cfDigit_succ_of_fract_eq_zero hz]
        by_cases hh : Int.fract hi = 0
        · rw [cfDigit_succ_of_fract_eq_zero hh]
          exact Or.inr ⟨rfl, rfl⟩
        · rw [cfDigit_succ hh]
          left
          simp [cfDigit, IntFractPair.stream]
      · rw [cfDigit_succ_of_fract_eq_zero hz]
        by_cases hl : Int.fract lo = 0
        · rw [cfDigit_succ_of_fract_eq_zero hl]
          exact Or.inr ⟨rfl, rfl⟩
        · rw [cfDigit_succ hl]
          left
          simp [cfDigit, IntFractPair.stream]
    · push Not at hz
      simp only [List.length_cons] at hlen ⊢
      have hflo : 0 < Int.fract lo := lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hz.1)
      have hle' : Int.fract lo ≤ Int.fract hi := by
        rw [← Int.self_sub_floor, ← Int.self_sub_floor, hfl]
        linarith
      rw [cfDigit_succ hz.1, cfDigit_succ hz.2]
      rcases ih _ _ (inv_anti₀ hflo hle') (by omega) with h | h
      · exact Or.inl (Ne.symm h)
      · exact Or.inr ⟨h.2, h.1⟩
    · simp only [List.length_nil, cfDigit_zero]
      left
      simpa using hfl

end CommonWord

/-! ## 4. Witnesses -/

section Witnesses

open GenContFract

/-- [proved-derived; formal-checked] `[355/113 − 10⁻⁶, 355/113 + 10⁻⁶]` shares the word `[3; 7]`. -/
theorem commonWord_around_355_113 :
    commonWord 10 (355 / 113 - 1 / 10 ^ 6) (355 / 113 + 1 / 10 ^ 6) = [3, 7] := by
  decide +kernel

/-- [proved-derived; formal-checked] Its ends part at the third digit: `15` below `355/113` and `16` above it. -/
theorem ends_part_around_355_113 :
    cfDigit (355 / 113 - 1 / 10 ^ 6 : ℚ) 2 = some 15 ∧
      cfDigit (355 / 113 + 1 / 10 ^ 6 : ℚ) 2 = some 16 := by
  decide +kernel

/-- [proved-derived; formal-checked] A point enclosure reads the whole word: `355/113 = [3; 7, 16]`. -/
theorem commonWord_point_355_113 : commonWord 10 (355 / 113) (355 / 113) = [3, 7, 16] := by
  decide +kernel

/-- [proved-derived; formal-checked] The enclosure `[3.14159, 3.1416]` shares the word `[3; 7]`. -/
theorem commonWord_five_places :
    commonWord 10 (314159 / 100000) (31416 / 10000) = [3, 7] := by
  decide +kernel

/-- [definition] The lower end of Mathlib's twenty-place enclosure of π. -/
def piLower : ℚ := 314159265358979323846 / 10 ^ 20

/-- [definition] The upper end of Mathlib's twenty-place enclosure of π. -/
def piUpper : ℚ := 314159265358979323847 / 10 ^ 20

/-- [proved-derived; formal-checked] The twenty-place enclosure of π shares nineteen digits. -/
theorem commonWord_pi :
    commonWord 24 piLower piUpper = [3, 7, 15, 1, 292, 1, 1, 1, 2, 1, 3, 1, 14, 2, 1, 1, 2, 2, 2] := by
  decide +kernel

/-- [proved-standard; formal-checked] π lies in its twenty-place enclosure (`Real.pi_gt_d20`, `Real.pi_lt_d20`). -/
theorem pi_mem_enclosure : (piLower : ℝ) ≤ π ∧ π ≤ (piUpper : ℝ) := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  unfold piLower piUpper
  constructor
  · push_cast
    norm_num at h1 ⊢
    linarith
  · push_cast
    norm_num at h2 ⊢
    linarith

/-- [proved-derived; formal-checked] π's word begins `[3; 7, 15, 1, 292, 1, 1, 1, 2, 1, 3, 1, 14, 2, 1, 1, 2, 2, 2]` -/
theorem pi_cfDigit (i : ℕ) (a : ℤ)
    (h : [3, 7, 15, 1, 292, 1, 1, 1, 2, 1, 3, 1, 14, 2, 1, 1, 2, 2, 2][i]? = some a) :
    cfDigit π i = some a := by
  rw [← commonWord_pi] at h
  exact commonWord_digit 24 piLower piUpper π pi_mem_enclosure.1 pi_mem_enclosure.2 i a h

/-- [proved-derived; formal-checked] `GenContFract.of π` has head `3` and partial denominators `7, 15, 1, 292`. -/
theorem of_pi_head :
    (GenContFract.of π).h = 3 ∧ (GenContFract.of π).s.get? 0 = some ⟨1, 7⟩ ∧
      (GenContFract.of π).s.get? 1 = some ⟨1, 15⟩ ∧ (GenContFract.of π).s.get? 2 = some ⟨1, 1⟩ ∧
      (GenContFract.of π).s.get? 3 = some ⟨1, 292⟩ := by
  have hlo := pi_mem_enclosure.1
  have hhi := pi_mem_enclosure.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast commonWord_head (a := 3) hlo hhi (by rw [commonWord_pi]; rfl)
  · exact_mod_cast commonWord_partDen (i := 0) (a := 7) hlo hhi (by rw [commonWord_pi]; rfl)
  · exact_mod_cast commonWord_partDen (i := 1) (a := 15) hlo hhi (by rw [commonWord_pi]; rfl)
  · exact_mod_cast commonWord_partDen (i := 2) (a := 1) hlo hhi (by rw [commonWord_pi]; rfl)
  · exact_mod_cast commonWord_partDen (i := 3) (a := 292) hlo hhi (by rw [commonWord_pi]; rfl)

end Witnesses

end Holonics.Mathematics.ConstantNavigators
