import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# A number is a word at a level: the level laws, the leading face's cancellation, a factor's action on a cycle,
# and Fermat on a ring

Source: #410's box "Association is evaluation, and a number is a word at a level of the base's tower (#404)", from the
record `2026-10-23_ASSOCIATION_IS_EVALUATION_A_NUMBER_IS_A_WORD_OF_TURNING_DIGITS_AT_A_LEVEL_OF_THE_BASES_TOWER`,
§§1, 2, 4, 6 and 7. Its first clause, a kept face descends exactly when every fibre is one point and a jointly
injective family evaluates `T`, is `Compression/OneFaceLaw` (`conserved_iff_fibre`, `closure_reads_T`); this file
proves the rest.

The level of `n ≠ 0` in a base `b ≥ 2` is the largest `d` with `bᵈ ∣ n`, and its face the word `r = n / bᵈ`, which
`b` does not divide (Mathlib's `padicValNat b n` and `Nat.divMaxPow n b`, defined for every base; the unique chart is
`Foundation/PrimeValuationRadixAtlas.theExactChartIsUnique`).

[proved-standard; formal-checked] What is proved.

1. **The level laws** (§1). `n = bᵏ r` with `b ∤ r` reads level `k` (`level_eq_of_chart`). A product adds the levels
   and climbs by its words' own product, `d(xy) = d(x) + d(y) + d(r_x r_y)` (`level_mul`); at a prime base the words'
   product never climbs (`level_mul_prime`). A sum keeps the lower level where the levels differ (`level_add_of_lt`),
   and so does a difference (`level_sub_of_lt`, `level_sub_of_gt`); at equal levels it can only climb (`le_level_add`,
   `le_level_sub`). The record's witnesses: `12,400` is `124` at level two, `2 · 5 = 10` climbs one level and
   `1,250 + 750 = 2,000` climbs two (`level_12400`, `level_two_mul_five`, `level_1250_add_750`).
2. **A difference cancels its leading face** (§2). Two numbers whose digits from place `m` up agree differ by less
   than `bᵐ` (`sub_lt_of_div_eq`), read on the digit lists too (`sub_lt_of_leading_digits`; for words of length `n`
   sharing `j` leading digits, `m = n − j`), with the record's `5102 − 5097 = 5` and `5199 − 5001 = 198`
   (`cancel_5102_5097`, `cancel_5199_5001`).
3. **A factor on a cycle** (§1). Multiplication by `m` on `ℤ/q` lands on `q / gcd(q, m)` values
   (`card_range_mul`; on `ℤ/10`, `2` reaches five, `5` two and `3` all ten, `card_range_mul_ten`); a factor coprime
   to `q` turns the cycle, a permutation (`mul_bijective_of_coprime`). A factor `≡ −1` is the half-turn
   (`mul_eq_neg_of_eq_neg_one`), so `9x ≡ −x (mod 10)` (`nine_mul_mod_ten`). The base's two cycles carry Fermat,
   `x² = x` on `ℤ/2` and `x⁵ = x` on `ℤ/5`, joined by the Chinese remainder theorem into `n⁵ ≡ n (mod 10)`
   (`pow_five_modEq_ten`).
4. **The trailing digit law factors over the base's primes** (§1). The count of digit pairs with product `d`
   (`pairCount`, the fibre of the product, `pairCount_eq_card`) is the product of its counts on the factors of any
   multiplicative splitting `R ≃* S × T`, the Chinese remainder theorem's among them (`pairCount_prod`); on a finite
   field of `q` elements it is `2q − 1` for `0` and `q − 1` for each unit (`pairCount_zero_field`,
   `pairCount_unit_field`). Base ten reads `(27, 4, 12, 4, 12, 9, 12, 4, 12, 4)` (`pairCount_ten`), the product of
   `(3, 1)` on `ℤ/2` and `(9, 4, 4, 4, 4)` on `ℤ/5` (`pairCount_two_five`) through `ℤ/10 ≅ ℤ/2 × ℤ/5`
   (`pairCount_ten_factors`).
5. **Fermat on a ring** (§4). For every integer square matrix and prime `p`, `tr(A^p) ≡ tr(A) (mod p)`
   (`trace_pow_prime_modEq`), through the Frobenius of `ZMod p` on the characteristic polynomial; on one site,
   `a^p ≡ a` (`int_pow_prime_modEq`).
6. **An unread carry** (§4). Of two digits, `b` of the `b²` pairs pass a carry on, their sum being `b − 1`
   (`card_propagate`), so a carry that entered `m` places below is still unread on `bᵐ` of the `b^(2m)` words of digit
   pairs (`card_unread_carry`): probability `b^(−m)` (`unread_carry_prob`).
7. **The clock cast** (§6). With `logRate g = g′/g`, the derivative of `ln g` along the clock where `g ≠ 0`
   (`logRate_hasDerivAt`), the code's equation of state `w = −d ln L/d ln V` (`eos`) read on another clock `V′` is
   `w · d ln V/d ln V′` wherever both clocks move (`clock_cast`). A constant cast, on the clock or on the length,
   leaves it (`logRate_const_mul`, `clock_cast_const`); a region at its byte floor `w = −1` reads `w < −1` on a unit
   clock that grows slower than the bytes, and that phantom is the cast (`clock_cast_phantom`).

Limits. The carry chain's long-run law over many summands (the Eulerian stationary law `A(n, j)/n!` and the spectrum
`1, b⁻¹, …, b^(−(n−1))` of Holte's chain) is not proved here; statement 6 is its two-summand clause. The `n`-summand
and general-base splitting of the trailing law into every prime power is read from the two-factor
`pairCount_prod` by induction, not stated. The leading face is read on numbers and their digit lists; the helix's
phase `θ = frac(log_b n)` and Benford's law (`radix.leading-face-gas`) are not here. The discrete-log phases of
`(ℤ/10)^× = ⟨3⟩` are not stated, and base twelve's split `ℤ/4 × ℤ/3` is not instantiated (`pairCount_prod` takes it
through `ZMod.chineseRemainder`). `tr(A^p) ≡ tr(A)` is proved for every integer matrix; the necklace count `P_n ∈ ℤ`
of `Compression/Landmark/NecklaceIntegrality` stays its own, for nonnegative entries.

The computational object is the helical pair interaction: a digit turns on the base's cycle, a carry steps the
staircase (the helix's winding), a product is a pair contact of two words with their levels added, and a factor
crossing a cycle's prime collapses it. Of the winding guide's six general objects this touches the helix (digits and
carries), faces and placement (the level, the face and the leading digits) and the tower thread (the cycles `ℤ/2` and
`ℤ/5` below `ℤ/10`); the pair, the cell holonomy and the tube stay attached.

Consumers: the atlas rows `radix.level-laws`, `radix.difference-leading-cancellation`, `radix.multiplier-face-action`,
`radix.product-digit-law-factors`, `arith.fermat-ring-partition`, `radix.carry-chain-eulerian` and `code.clock-cast`,
and the #410 box "Association is evaluation".

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Mathematics.LevelLaws

/-! ## 1. The level laws -/

section Level

variable {b : ℕ}

/-- [proved-standard; formal-checked] A chart reads its level: `n = bᵏ r` with `r ≠ 0` and `b ∤ r` is at level `k`. -/
theorem level_eq_of_chart (hb : 2 ≤ b) {k r : ℕ} (hr : r ≠ 0) (hbr : ¬ b ∣ r) :
    padicValNat b (b ^ k * r) = k := by
  have hb1 : b ≠ 1 := by omega
  have hn : b ^ k * r ≠ 0 := mul_ne_zero (pow_ne_zero _ (by omega)) hr
  apply le_antisymm
  · by_contra h
    have h' : k + 1 ≤ padicValNat b (b ^ k * r) := by omega
    have hdvd : b ^ (k + 1) ∣ b ^ k * r := (Nat.pow_dvd_iff_le_padicValNat hb1 hn).mpr h'
    rw [pow_succ] at hdvd
    exact hbr (Nat.dvd_of_mul_dvd_mul_left (pow_pos (by omega) k) hdvd)
  · exact (Nat.pow_dvd_iff_le_padicValNat hb1 hn).mp (dvd_mul_right _ _)

/-- [proved-standard; formal-checked] Every nonzero number is its face at its level, and the base does not divide
the face. -/
theorem chart (hb : 2 ≤ b) {n : ℕ} (hn : n ≠ 0) :
    n = b ^ padicValNat b n * Nat.divMaxPow n b ∧ ¬ b ∣ Nat.divMaxPow n b ∧ Nat.divMaxPow n b ≠ 0 := by
  refine ⟨(Nat.pow_padicValNat_mul_divMaxPow b n).symm, Nat.not_dvd_divMaxPow (by omega) hn, ?_⟩
  intro h
  have := Nat.pow_padicValNat_mul_divMaxPow b n
  rw [h, mul_zero] at this
  exact hn this.symm

/-- [proved-standard; formal-checked] **A product adds the levels and climbs by its words' product**:
`d(xy) = d(x) + d(y) + d(r_x r_y)`. -/
theorem level_mul (hb : 2 ≤ b) {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) :
    padicValNat b (x * y) = padicValNat b x + padicValNat b y +
      padicValNat b (Nat.divMaxPow x b * Nat.divMaxPow y b) := by
  obtain ⟨-, -, rx0⟩ := chart hb hx
  obtain ⟨-, -, ry0⟩ := chart hb hy
  have hr : Nat.divMaxPow x b * Nat.divMaxPow y b ≠ 0 := mul_ne_zero rx0 ry0
  obtain ⟨-, hbr, r0⟩ := chart hb hr
  have hxy : x * y = b ^ (padicValNat b x + padicValNat b y +
      padicValNat b (Nat.divMaxPow x b * Nat.divMaxPow y b)) *
      Nat.divMaxPow (Nat.divMaxPow x b * Nat.divMaxPow y b) b := by
    calc x * y = (b ^ padicValNat b x * Nat.divMaxPow x b) *
          (b ^ padicValNat b y * Nat.divMaxPow y b) := by
          rw [Nat.pow_padicValNat_mul_divMaxPow, Nat.pow_padicValNat_mul_divMaxPow]
      _ = b ^ padicValNat b x * b ^ padicValNat b y *
          (Nat.divMaxPow x b * Nat.divMaxPow y b) := by ring
      _ = b ^ padicValNat b x * b ^ padicValNat b y *
          (b ^ padicValNat b (Nat.divMaxPow x b * Nat.divMaxPow y b) *
            Nat.divMaxPow (Nat.divMaxPow x b * Nat.divMaxPow y b) b) := by
          rw [Nat.pow_padicValNat_mul_divMaxPow]
      _ = _ := by rw [pow_add, pow_add]; ring
  rw [hxy, level_eq_of_chart hb r0 hbr]

/-- [proved-standard; formal-checked] At a prime base the words' own product never climbs: `d(r_x r_y) = 0`. -/
theorem level_mul_prime {p : ℕ} (hp : p.Prime) {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) :
    padicValNat p (Nat.divMaxPow x p * Nat.divMaxPow y p) = 0 := by
  have h2 := hp.two_le
  obtain ⟨-, hbx, -⟩ := chart h2 hx
  obtain ⟨-, hby, -⟩ := chart h2 hy
  have : ¬ p ∣ Nat.divMaxPow x p * Nat.divMaxPow y p := fun h =>
    (hp.dvd_mul.mp h).elim hbx hby
  have h1 : padicValNat p (p ^ 0 * (Nat.divMaxPow x p * Nat.divMaxPow y p)) = 0 :=
    level_eq_of_chart h2 (fun h0 => this (h0 ▸ dvd_zero p)) this
  simpa using h1

/-- [proved-standard; formal-checked] **A sum keeps the lower level** where the levels differ. -/
theorem level_add_of_lt (hb : 2 ≤ b) {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hlt : padicValNat b x < padicValNat b y) : padicValNat b (x + y) = padicValNat b x := by
  obtain ⟨ex, hbx, rx0⟩ := chart hb hx
  obtain ⟨ey, -, -⟩ := chart hb hy
  set dx := padicValNat b x
  set dy := padicValNat b y
  set rx := Nat.divMaxPow x b
  set ry := Nat.divMaxPow y b
  obtain ⟨e, he⟩ : ∃ e, dy = dx + (e + 1) := ⟨dy - dx - 1, by omega⟩
  have hsum : x + y = b ^ dx * (rx + b ^ (e + 1) * ry) := by
    rw [ex, ey, he, pow_add]; ring
  have hndvd : ¬ b ∣ rx + b ^ (e + 1) * ry := by
    intro h
    have : b ∣ b ^ (e + 1) * ry := dvd_mul_of_dvd_left (dvd_pow_self b (by omega)) ry
    exact hbx ((Nat.dvd_add_left this).mp h)
  have hne : rx + b ^ (e + 1) * ry ≠ 0 := by omega
  rw [hsum, level_eq_of_chart hb hne hndvd]

/-- [proved-standard; formal-checked] A difference keeps the lower level too, the larger operand at the lower
level. -/
theorem level_sub_of_lt (hb : 2 ≤ b) {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) (hyx : y < x)
    (hlt : padicValNat b x < padicValNat b y) : padicValNat b (x - y) = padicValNat b x := by
  obtain ⟨ex, hbx, rx0⟩ := chart hb hx
  obtain ⟨ey, -, -⟩ := chart hb hy
  set dx := padicValNat b x
  set dy := padicValNat b y
  set rx := Nat.divMaxPow x b
  set ry := Nat.divMaxPow y b
  obtain ⟨e, he⟩ : ∃ e, dy = dx + (e + 1) := ⟨dy - dx - 1, by omega⟩
  have hy' : y = b ^ dx * (b ^ (e + 1) * ry) := by rw [ey, he, pow_add]; ring
  have hle : b ^ (e + 1) * ry < rx := by
    have : b ^ dx * (b ^ (e + 1) * ry) < b ^ dx * rx := by rw [← hy', ← ex]; exact hyx
    exact lt_of_mul_lt_mul_left this (Nat.zero_le _)
  have hdiff : x - y = b ^ dx * (rx - b ^ (e + 1) * ry) := by
    rw [Nat.mul_sub, ← ex, ← hy']
  have hndvd : ¬ b ∣ rx - b ^ (e + 1) * ry := by
    intro h
    have h2 : b ∣ b ^ (e + 1) * ry := dvd_mul_of_dvd_left (dvd_pow_self b (by omega)) ry
    have : b ∣ (rx - b ^ (e + 1) * ry) + b ^ (e + 1) * ry := dvd_add h h2
    rw [Nat.sub_add_cancel hle.le] at this
    exact hbx this
  have hne : rx - b ^ (e + 1) * ry ≠ 0 := by omega
  rw [hdiff, level_eq_of_chart hb hne hndvd]

/-- [proved-standard; formal-checked] And with the larger operand at the higher level, the difference reads the
smaller operand's level. -/
theorem level_sub_of_gt (hb : 2 ≤ b) {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) (hyx : y < x)
    (hgt : padicValNat b y < padicValNat b x) : padicValNat b (x - y) = padicValNat b y := by
  obtain ⟨ex, -, -⟩ := chart hb hx
  obtain ⟨ey, hby, ry0⟩ := chart hb hy
  set dx := padicValNat b x
  set dy := padicValNat b y
  set rx := Nat.divMaxPow x b
  set ry := Nat.divMaxPow y b
  obtain ⟨e, he⟩ : ∃ e, dx = dy + (e + 1) := ⟨dx - dy - 1, by omega⟩
  have hx' : x = b ^ dy * (b ^ (e + 1) * rx) := by rw [ex, he, pow_add]; ring
  have hle : ry < b ^ (e + 1) * rx := by
    have : b ^ dy * ry < b ^ dy * (b ^ (e + 1) * rx) := by rw [← hx', ← ey]; exact hyx
    exact lt_of_mul_lt_mul_left this (Nat.zero_le _)
  have hdiff : x - y = b ^ dy * (b ^ (e + 1) * rx - ry) := by
    rw [Nat.mul_sub, ← ey, ← hx']
  have hndvd : ¬ b ∣ b ^ (e + 1) * rx - ry := by
    intro h
    have h2 : b ∣ b ^ (e + 1) * rx := dvd_mul_of_dvd_left (dvd_pow_self b (by omega)) rx
    have h3 : b ∣ b ^ (e + 1) * rx - (b ^ (e + 1) * rx - ry) := Nat.dvd_sub h2 h
    rw [Nat.sub_sub_self hle.le] at h3
    exact hby h3
  have hne : b ^ (e + 1) * rx - ry ≠ 0 := by omega
  rw [hdiff, level_eq_of_chart hb hne hndvd]

/-- [proved-standard; formal-checked] At equal levels a sum can only climb. -/
theorem le_level_add (hb : 2 ≤ b) {x y : ℕ} (hx : x ≠ 0)
    (heq : padicValNat b x = padicValNat b y) : padicValNat b x ≤ padicValNat b (x + y) := by
  have hb1 : b ≠ 1 := by omega
  apply (Nat.pow_dvd_iff_le_padicValNat hb1 (by omega)).mp
  have h1 : b ^ padicValNat b x ∣ y := by rw [heq]; exact pow_padicValNat_dvd
  exact dvd_add pow_padicValNat_dvd h1

/-- [proved-standard; formal-checked] And so can a difference. -/
theorem le_level_sub (hb : 2 ≤ b) {x y : ℕ} (hyx : y < x)
    (heq : padicValNat b x = padicValNat b y) : padicValNat b x ≤ padicValNat b (x - y) := by
  have hb1 : b ≠ 1 := by omega
  apply (Nat.pow_dvd_iff_le_padicValNat hb1 (by omega)).mp
  have h1 : b ^ padicValNat b x ∣ y := by rw [heq]; exact pow_padicValNat_dvd
  exact Nat.dvd_sub pow_padicValNat_dvd h1

/-- [proved-standard; formal-checked] `12,400` is the word `124` at level two. -/
theorem level_12400 : padicValNat 10 12400 = 2 ∧ Nat.divMaxPow 12400 10 = 124 := by
  have h : padicValNat 10 (10 ^ 2 * 124) = 2 := level_eq_of_chart (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  refine ⟨h, ?_⟩
  have := Nat.pow_padicValNat_mul_divMaxPow 10 12400
  rw [h] at this
  omega

/-- [proved-standard; formal-checked] `2 · 5 = 10` climbs one level: the words' own product climbs. -/
theorem level_two_mul_five : padicValNat 10 2 = 0 ∧ padicValNat 10 5 = 0 ∧ padicValNat 10 (2 * 5) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show (2 : ℕ) = 10 ^ 0 * 2 by norm_num]
    exact level_eq_of_chart (by norm_num) (by norm_num) (by norm_num)
  · rw [show (5 : ℕ) = 10 ^ 0 * 5 by norm_num]
    exact level_eq_of_chart (by norm_num) (by norm_num) (by norm_num)
  · rw [show 2 * 5 = 10 ^ 1 * 1 by norm_num]
    exact level_eq_of_chart (by norm_num) (by norm_num) (by norm_num)

/-- [proved-standard; formal-checked] `1,250 + 750 = 2,000` climbs two levels from equal levels one. -/
theorem level_1250_add_750 :
    padicValNat 10 1250 = 1 ∧ padicValNat 10 750 = 1 ∧ padicValNat 10 (1250 + 750) = 3 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show (1250 : ℕ) = 10 ^ 1 * 125 by norm_num]
    exact level_eq_of_chart (by norm_num) (by norm_num) (by norm_num)
  · rw [show (750 : ℕ) = 10 ^ 1 * 75 by norm_num]
    exact level_eq_of_chart (by norm_num) (by norm_num) (by norm_num)
  · rw [show 1250 + 750 = 10 ^ 3 * 2 by norm_num]
    exact level_eq_of_chart (by norm_num) (by norm_num) (by norm_num)

end Level

/-! ## 2. The leading face of a difference cancels -/

section Leading

/-- [proved-standard; formal-checked] **A difference cancels its leading face**: two numbers that agree above place
`m` differ by less than `bᵐ`, so the difference is read from the places below alone. -/
theorem sub_lt_of_div_eq {b m x y : ℕ} (hb : 0 < b) (h : x / b ^ m = y / b ^ m) (hyx : y ≤ x) :
    x - y < b ^ m := by
  have hB : 0 < b ^ m := pow_pos hb m
  have e1 := Nat.div_add_mod x (b ^ m)
  have e2 := Nat.div_add_mod y (b ^ m)
  have r1 := Nat.mod_lt x hB
  rw [h] at e1
  generalize b ^ m * (y / b ^ m) = t at e1 e2
  generalize x % b ^ m = u at e1 r1
  generalize y % b ^ m = v at e2
  generalize b ^ m = B at r1 ⊢
  omega

/-- [proved-standard; formal-checked] The same read on the digit lists: words whose digits from place `m` up agree
(the shared leading digits, the list being least digit first) differ by less than `bᵐ`; for two words of length `n`
sharing `j` leading digits, `m = n − j`. -/
theorem sub_lt_of_leading_digits {b m x y : ℕ} (hb : 2 ≤ b)
    (h : (b.digits x).drop m = (b.digits y).drop m) (hyx : y ≤ x) : x - y < b ^ m := by
  apply sub_lt_of_div_eq (by omega) _ hyx
  rw [Nat.self_div_pow_eq_ofDigits_drop m x hb, Nat.self_div_pow_eq_ofDigits_drop m y hb, h]

/-- [proved-standard; formal-checked] `5102 − 5097 = 5`: one shared leading digit, and the difference's leading digit
is read from the places below it. -/
theorem cancel_5102_5097 : 5102 / 10 ^ 3 = 5097 / 10 ^ 3 ∧ 5102 - 5097 = 5 := by norm_num

/-- [proved-standard; formal-checked] `5199 − 5001 = 198`: the same leading digit, and a different leading digit of the
difference, so the fibre over the shared face holds every leading digit. -/
theorem cancel_5199_5001 : 5199 / 10 ^ 3 = 5001 / 10 ^ 3 ∧ 5199 - 5001 = 198 := by norm_num

end Leading

/-! ## 3. A factor on a cycle -/

section Factor

/-- [proved-standard; formal-checked] **Multiplication by `m` on `ℤ/q` reaches `q / gcd(q, m)` values**: its range
is the cyclic subgroup `m` generates, of order `q / gcd(q, m)`. -/
theorem card_range_mul (q m : ℕ) [NeZero q] :
    Nat.card (Set.range fun x : ZMod q => (m : ZMod q) * x) = q / q.gcd m := by
  have hset : (Set.range fun x : ZMod q => (m : ZMod q) * x) =
      ((AddSubgroup.zmultiples (m : ZMod q) : AddSubgroup (ZMod q)) : Set (ZMod q)) := by
    ext y
    simp only [Set.mem_range, SetLike.mem_coe, AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨(x.val : ℤ), ?_⟩
      rw [zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_zmod_val, mul_comm]
    · rintro ⟨k, rfl⟩
      exact ⟨(k : ZMod q), by rw [zsmul_eq_mul, mul_comm]⟩
  rw [hset]
  exact (Nat.card_zmultiples _).trans (ZMod.addOrderOf_coe m (NeZero.ne q))

/-- [proved-standard; formal-checked] On base ten's cycle: `2` reaches five values, `5` two and `3` all ten. -/
theorem card_range_mul_ten :
    (Finset.univ.image fun x : ZMod 10 => 2 * x).card = 5 ∧
    (Finset.univ.image fun x : ZMod 10 => 5 * x).card = 2 ∧
    (Finset.univ.image fun x : ZMod 10 => 3 * x).card = 10 := by
  decide

/-- [proved-standard; formal-checked] A factor coprime to the cycle turns it: multiplication is a permutation. -/
theorem mul_bijective_of_coprime {q m : ℕ} (hm : m.Coprime q) :
    Function.Bijective fun x : ZMod q => (m : ZMod q) * x := by
  convert (Units.mulLeft (ZMod.unitOfCoprime m hm)).bijective using 1
  funext x
  exact (congrArg (· * x) (ZMod.coe_unitOfCoprime m hm)).symm

/-- [proved-standard; formal-checked] A factor `≡ −1` on the cycle is the half-turn. -/
theorem mul_eq_neg_of_eq_neg_one {R : Type*} [Ring R] {m : R} (h : m = -1) (x : R) : m * x = -x := by
  rw [h, neg_one_mul]

/-- [proved-standard; formal-checked] `9x ≡ −x (mod 10)`, through the half-turn `9 = −1` on `ℤ/10`. -/
theorem nine_mul_mod_ten (x : ℤ) : 9 * x ≡ -x [ZMOD 10] := by
  have h := (ZMod.intCast_eq_intCast_iff (9 * x) (-x) 10).mp (by
    push_cast
    exact mul_eq_neg_of_eq_neg_one (by decide) _)
  exact h

/-- [proved-standard; formal-checked] **Fermat at `2` and `5` joined by the Chinese remainder theorem**:
`n⁵ ≡ n (mod 10)`. On `ℤ/2` every `x` has `x² = x`, on `ℤ/5` Fermat gives `x⁵ = x`, and the two cycles under `ℤ/10`
join. -/
theorem pow_five_modEq_ten (n : ℤ) : n ^ 5 ≡ n [ZMOD 10] := by
  have h2 : n ^ 5 ≡ n [ZMOD 2] := by
    have hz : ∀ x : ZMod 2, x ^ 5 = x := by decide
    exact (ZMod.intCast_eq_intCast_iff (n ^ 5) n 2).mp (by push_cast; exact hz _)
  have h5 : n ^ 5 ≡ n [ZMOD 5] := by
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact (ZMod.intCast_eq_intCast_iff (n ^ 5) n 5).mp (by push_cast; exact ZMod.pow_card _)
  have h := (Int.modEq_and_modEq_iff_modEq_mul (a := n ^ 5) (b := n) (m := 2) (n := 5)
    (by norm_num)).mp ⟨h2, h5⟩
  simpa using h

end Factor

/-! ## 4. The trailing digit law factors -/

section Trailing

/-- [definition] The count of digit pairs on a cycle `R` whose product is `d`. -/
def pairCount (R : Type*) [Mul R] [Fintype R] [DecidableEq R] (d : R) : ℕ :=
  (Finset.univ.filter fun p : R × R => p.1 * p.2 = d).card

/-- [proved-standard; formal-checked] The count is the size of the fibre of the product over `d`. -/
theorem pairCount_eq_card (R : Type*) [Mul R] [Fintype R] [DecidableEq R] (d : R) :
    pairCount R d = Fintype.card {p : R × R // p.1 * p.2 = d} :=
  (Fintype.card_subtype _).symm

/-- [proved-standard; formal-checked] **The trailing digit law factors over a splitting**: for a multiplicative
splitting `R ≃* S × T` (the Chinese remainder theorem's, for one), the count over `d` is the product of the counts on
the two factors. -/
theorem pairCount_prod {R S T : Type*} [Mul R] [Mul S] [Mul T] [Fintype R] [Fintype S] [Fintype T]
    [DecidableEq R] [DecidableEq S] [DecidableEq T] (e : R ≃* S × T) (d : R) :
    pairCount R d = pairCount S (e d).1 * pairCount T (e d).2 := by
  rw [pairCount_eq_card, pairCount_eq_card, pairCount_eq_card, ← Fintype.card_prod]
  refine Fintype.card_congr ?_
  refine (Equiv.subtypeEquiv
    (q := fun c : (S × S) × (T × T) => c.1.1 * c.1.2 = (e d).1 ∧ c.2.1 * c.2.2 = (e d).2)
    ((e.toEquiv.prodCongr e.toEquiv).trans (Equiv.prodProdProdComm S T S T)) ?_).trans
    (Equiv.subtypeProdEquivProd (p := fun a : S × S => a.1 * a.2 = (e d).1)
      (q := fun a : T × T => a.1 * a.2 = (e d).2))
  rintro ⟨a, c⟩
  change a * c = d ↔ (e a).1 * (e c).1 = (e d).1 ∧ (e a).2 * (e c).2 = (e d).2
  rw [← e.injective.eq_iff, map_mul, Prod.ext_iff]
  rfl

/-- [proved-standard; formal-checked] On a finite field of `q` elements, `0` has `2q − 1` pairs: one factor or the
other collapses. -/
theorem pairCount_zero_field (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    pairCount F 0 = 2 * Fintype.card F - 1 := by
  have hA : (Finset.univ.filter fun p : F × F => p.1 = 0) = {0} ×ˢ Finset.univ := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, Finset.mem_singleton, and_true]
  have hB : (Finset.univ.filter fun p : F × F => p.2 = 0) = Finset.univ ×ˢ {0} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, Finset.mem_singleton]
  have hAB : (Finset.univ.filter fun p : F × F => p.1 = 0) ∩
      (Finset.univ.filter fun p : F × F => p.2 = 0) = {(0, 0)} := by
    ext ⟨a, c⟩; simp
  have hU : (Finset.univ.filter fun p : F × F => p.1 * p.2 = 0) =
      (Finset.univ.filter fun p : F × F => p.1 = 0) ∪ (Finset.univ.filter fun p : F × F => p.2 = 0) := by
    ext p; simp [mul_eq_zero]
  have := Finset.card_union_add_card_inter (Finset.univ.filter fun p : F × F => p.1 = 0)
    (Finset.univ.filter fun p : F × F => p.2 = 0)
  rw [← hU, hAB, hA, hB, Finset.card_product, Finset.card_product] at this
  simp only [Finset.card_singleton, Finset.card_univ, one_mul, mul_one] at this
  unfold pairCount
  omega

/-- [proved-standard; formal-checked] On a finite field of `q` elements, each unit `d` has `q − 1` pairs: the first
factor is any unit and fixes the second. -/
theorem pairCount_unit_field (F : Type*) [Field F] [Fintype F] [DecidableEq F] {d : F} (hd : d ≠ 0) :
    pairCount F d = Fintype.card F - 1 := by
  rw [pairCount_eq_card, ← Fintype.card_units]
  refine Fintype.card_congr
    { toFun := fun p => Units.mk0 p.1.1 (fun h => hd (by rw [← p.2, h, zero_mul]))
      invFun := fun u => ⟨((u : F), (u : F)⁻¹ * d), by simp⟩
      left_inv := ?_
      right_inv := fun u => by ext; rfl }
  rintro ⟨⟨a, c⟩, h⟩
  have ha : a ≠ 0 := fun h0 => hd (by rw [← h, h0, zero_mul])
  apply Subtype.ext
  simp only [Units.val_mk0, Prod.mk.injEq, true_and]
  rw [← h, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]

/-- [proved-standard; formal-checked] Base ten's trailing digit law: of the hundred digit pairs,
`27, 4, 12, 4, 12, 9, 12, 4, 12, 4` end in `0, 1, …, 9`. -/
theorem pairCount_ten :
    pairCount (ZMod 10) 0 = 27 ∧ pairCount (ZMod 10) 1 = 4 ∧ pairCount (ZMod 10) 2 = 12 ∧
    pairCount (ZMod 10) 3 = 4 ∧ pairCount (ZMod 10) 4 = 12 ∧ pairCount (ZMod 10) 5 = 9 ∧
    pairCount (ZMod 10) 6 = 12 ∧ pairCount (ZMod 10) 7 = 4 ∧ pairCount (ZMod 10) 8 = 12 ∧
    pairCount (ZMod 10) 9 = 4 := by
  decide

/-- [proved-standard; formal-checked] Its factors: `(3, 1)` on `ℤ/2` and `(9, 4, 4, 4, 4)` on `ℤ/5`, the field counts
`2q − 1` and `q − 1`. -/
theorem pairCount_two_five :
    pairCount (ZMod 2) 0 = 3 ∧ pairCount (ZMod 2) 1 = 1 ∧ pairCount (ZMod 5) 0 = 9 ∧
    pairCount (ZMod 5) 1 = 4 ∧ pairCount (ZMod 5) 2 = 4 ∧ pairCount (ZMod 5) 3 = 4 ∧
    pairCount (ZMod 5) 4 = 4 := by
  decide

/-- [proved-standard; formal-checked] **Base ten's law is the product of its two cycles' laws**, through the
Chinese remainder splitting `ℤ/10 ≅ ℤ/2 × ℤ/5`. -/
theorem pairCount_ten_factors (d : ZMod 10) :
    pairCount (ZMod 10) d = pairCount (ZMod 2) (d.cast) * pairCount (ZMod 5) (d.cast) :=
  pairCount_prod (ZMod.chineseRemainder (m := 2) (n := 5) (by norm_num)).toMulEquiv d

end Trailing

/-! ## 5. Fermat on a ring -/

section Fermat

/-- [proved-standard; formal-checked] **Fermat on a ring of `p` sites**: for every integer square matrix and prime
`p`, `tr(A^p) ≡ tr(A) (mod p)`, through the Frobenius on `ZMod p`. -/
theorem trace_pow_prime_modEq {n : Type*} [Fintype n] [DecidableEq n] (p : ℕ) [Fact p.Prime]
    (A : Matrix n n ℤ) : (A ^ p).trace ≡ A.trace [ZMOD p] := by
  rw [← ZMod.intCast_eq_intCast_iff]
  have hmap : ∀ B : Matrix n n ℤ,
      ((B.trace : ℤ) : ZMod p) = ((Int.castRingHom (ZMod p)).mapMatrix B).trace := fun B =>
    AddMonoidHom.map_trace (Int.castRingHom (ZMod p)) B
  rw [hmap, hmap, map_pow, ZMod.trace_pow_card, ZMod.pow_card]

/-- [proved-standard; formal-checked] On one site: `a^p ≡ a (mod p)`. -/
theorem int_pow_prime_modEq (p : ℕ) [Fact p.Prime] (a : ℤ) : a ^ p ≡ a [ZMOD p] := by
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  exact ZMod.pow_card _

end Fermat

/-! ## 6. An unread carry -/

section Carry

/-- [proved-standard; formal-checked] Of two digits in base `b`, exactly `b` of the `b²` pairs pass a carry on
(their sum is `b − 1`, the propagating pairs). -/
theorem card_propagate (b : ℕ) :
    (Finset.univ.filter fun p : Fin b × Fin b => (p.1 : ℕ) + p.2 = b - 1).card = b := by
  have hset : (Finset.univ.filter fun p : Fin b × Fin b => (p.1 : ℕ) + p.2 = b - 1) =
      Finset.univ.image fun i : Fin b => (i, i.rev) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
    have hx := x.isLt
    have hy := y.isLt
    constructor
    · intro h
      refine ⟨x, rfl, ?_⟩
      ext
      simp only [Fin.val_rev]
      omega
    · rintro ⟨i, rfl, rfl⟩
      simp only [Fin.val_rev]
      omega
  rw [hset, Finset.card_image_of_injective _ (fun i j h => (Prod.mk.inj h).1), Finset.card_univ,
    Fintype.card_fin]

/-- [proved-standard; formal-checked] **A carry stays unread** through `m` places on `bᵐ` of the `b^(2m)` words of
digit pairs: every place must propagate. -/
theorem card_unread_carry (b m : ℕ) :
    (Fintype.piFinset fun _ : Fin m =>
      Finset.univ.filter fun p : Fin b × Fin b => (p.1 : ℕ) + p.2 = b - 1).card = b ^ m ∧
    Fintype.card (Fin m → Fin b × Fin b) = b ^ (2 * m) := by
  constructor
  · rw [Fintype.card_piFinset_const, card_propagate]
  · rw [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, pow_mul, sq]

/-- [proved-standard; formal-checked] So the probability that a carry is still unread after `m` lower places is
`b^(−m)`. -/
theorem unread_carry_prob {b : ℕ} (hb : b ≠ 0) (m : ℕ) :
    ((b ^ m : ℕ) : ℚ) / ((b ^ (2 * m) : ℕ) : ℚ) = ((b : ℚ) ^ m)⁻¹ := by
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  push_cast
  rw [pow_mul', sq, div_mul_eq_div_div, div_self (pow_ne_zero m hb'), one_div]

end Carry

/-! ## 7. The clock cast -/

section Clock

/-- [definition] The log-rate of a quantity along a clock, `d ln g/ds = g′/g`. -/
noncomputable def logRate (g : ℝ → ℝ) (s : ℝ) : ℝ := deriv g s / g s

/-- [proved-standard; formal-checked] The log-rate is the derivative of the logarithm. -/
theorem logRate_hasDerivAt {g : ℝ → ℝ} {s : ℝ} (hg : DifferentiableAt ℝ g s) (h0 : g s ≠ 0) :
    HasDerivAt (fun t => Real.log (g t)) (logRate g s) s :=
  hg.hasDerivAt.log h0

/-- [definition] The code's equation of state on the clock `V`: `w = −d ln L/d ln V`. -/
noncomputable def eos (L V : ℝ → ℝ) (s : ℝ) : ℝ := -(logRate L s / logRate V s)

/-- [proved-derived; formal-checked] **The clock cast**: read on another clock `V′`, the equation of state is
`w′ = w · d ln V/d ln V′`. -/
theorem clock_cast (L V V' : ℝ → ℝ) (s : ℝ) (hV : logRate V s ≠ 0) (hV' : logRate V' s ≠ 0) :
    eos L V' s = eos L V s * (logRate V s / logRate V' s) := by
  unfold eos
  field_simp

/-- [proved-standard; formal-checked] A constant factor leaves a log-rate. -/
theorem logRate_const_mul {g : ℝ → ℝ} {s c : ℝ} (hc : c ≠ 0) (hg : DifferentiableAt ℝ g s) :
    logRate (fun t => c * g t) s = logRate g s := by
  unfold logRate
  rw [deriv_const_mul c hg, mul_div_mul_left _ _ hc]

/-- [proved-derived; formal-checked] **A constant cast leaves `w`**, on the clock (cell to byte, a region's steady
share) and on the length (bits to nats). -/
theorem clock_cast_const {L V : ℝ → ℝ} {s c : ℝ} (hc : c ≠ 0) (hL : DifferentiableAt ℝ L s)
    (hV : DifferentiableAt ℝ V s) :
    eos L (fun t => c * V t) s = eos L V s ∧ eos (fun t => c * L t) V s = eos L V s := by
  unfold eos
  rw [logRate_const_mul hc hV, logRate_const_mul hc hL]
  exact ⟨rfl, rfl⟩

/-- [proved-derived; formal-checked] **A lengthening unit reads phantom**: a region at its byte floor (`w = −1` on
the byte clock `N`) reads `w < −1` on the unit clock `k` while `N` grows faster than `k`; the phantom is the cast. -/
theorem clock_cast_phantom {L N k : ℝ → ℝ} {s : ℝ} (hk : 0 < logRate k s) (hNk : logRate k s < logRate N s)
    (hfloor : eos L N s = -1) : eos L k s < -1 := by
  have hN : logRate N s ≠ 0 := by linarith
  rw [clock_cast L N k s hN hk.ne', hfloor, neg_one_mul, neg_lt_neg_iff]
  exact (one_lt_div hk).mpr hNk

end Clock

end Holonics.Mathematics.LevelLaws
