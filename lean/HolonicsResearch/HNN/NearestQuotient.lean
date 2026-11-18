import Mathlib

/-!
# A nearest quotient keeps its bits under a common factor

[proved-derived] The source is the engine record of November 12
(`research/records/2026-11-12_A_SITES_ARITHMETIC_IS_COUNTED_AGAINST_THE_CARDS_LANES_THE_STORE_TRAINER_RUNS_AT_ONE_FORTIETH_OF_THEM_A_PAIRS_SKIN_IS_FORMED_ONCE_A_CLOCK_AND_COST_FOLLOWS_SURPRISE.md`,
§9, "The multiplier"). A contact row forms its currents and shares as nearest quotients of a magnitude `a = |x|` by a
mass `m`, both carried at a common multiplier `K` (`2^62` in `contact_body` and `SeriesRow`). The record infers that
the multiplier is the carrier's and never the row's: the quotient is the same integer at multiplier 1.

What is proved, in the floor division of the naturals, `a` standing for the magnitude `|x|`.

1. **The half form is the nearest quotient**: `⌊(a + ⌊m/2⌋)/m⌋ = ⌊(2a + m)/(2m)⌋` for every `m`, the odd ones included
   (`half_form`). The two could differ only where `2a + m` is a multiple of `2m` with `m` odd, and an odd number is
   never one (`odd_sum_not_multiple`).
2. **A common factor leaves the quotient**: for every `K > 0`, `⌊(aK + ⌊mK/2⌋)/(mK)⌋ = ⌊(2a + m)/(2m)⌋`
   (`common_factor`). The record states it for an even `K` (`even_factor`); the half form at `aK` and `mK` gives it for
   an odd `K` as well, so the hypothesis of evenness is not needed.
3. **Multiplier 1 gives the integers of every multiplier** (`multiplier_one`), of every power of two
   (`two_pow_multiplier`) and of `2^62` (`multiplier_two_pow_62`).
4. **The quotient is a nearest one**: `q = ⌊(2a + m)/(2m)⌋` has `2qm ≤ 2a + m < 2qm + 2m`, so `a` stands within half
   of `m` of `q·m`, a tie going up (`nearest`), and it is the only such integer (`nearest_unique`).
5. The same on the integers with `|x|` (`common_factor_int`, `half_form_int`).
6. **The engine's signed nearest division** `q(x, m)` (`divNearest`, the form of `holonics_engine::ratio::div_nearest`,
   a half going away from zero) is the sign beside the magnitude's quotient (`divNearest_eq_sign_mul`), is left by a
   common factor, `q(Kx, Km) = q(x, m)` for every `K ≥ 1` (`divNearest_common_factor`), and stands within half a
   divisor of the ratio (`divNearest_nearest`).

Limits. The statements are of one quotient. The record's "grouped row's equality", beside which #410 sets this lemma, is
a different statement and is not here. The integers are unbounded; the engine's 128-bit carrier and its range are not
modelled.

The computational object is the helical pair interaction: the quotient is a pair contact's current, or its share,
formed from the contact row's sums. Of the winding guide's six general objects this touches the pair (the contact row)
and faces and placement (the grain a quotient is released at); the helix, cell holonomy, tube and tower thread stay
attached.

Consumers: #410's box "A nearest quotient keeps its bits under an even common factor"; atlas
`radix.nearest-quotient-of-the-ratio`; the engine's contact row (the contact body and the series row), whose 62-bit
multiplier this shows to be a realization's.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.NearestQuotient

/-- The nearest quotient of a magnitude `a` by a mass `m`, a tie going up: `⌊(2a + m)/(2m)⌋`. -/
def nearestQuotient (a m : ℕ) : ℕ := (2 * a + m) / (2 * m)

/-- [proved-standard] An odd number is no multiple of an even one: with `m` odd, `2a + m` is never a multiple of
`2m`. -/
theorem odd_sum_not_multiple (a : ℕ) {m : ℕ} (hm : Odd m) : ¬ 2 * m ∣ 2 * a + m := by
  rintro ⟨c, hc⟩
  obtain ⟨j, rfl⟩ := hm
  have h : 2 * a + (2 * j + 1) = 2 * ((2 * j + 1) * c) := by rw [hc]; ring
  omega

/-- [proved-standard] **The quotient is a nearest one**, a tie going up: `q = ⌊(2a + m)/(2m)⌋` has
`2qm ≤ 2a + m < 2qm + 2m`, so `a − qm` lies in `[−m/2, m/2)`. -/
theorem nearest (a : ℕ) {m : ℕ} (hm : 0 < m) :
    2 * (nearestQuotient a m * m) ≤ 2 * a + m ∧ 2 * a + m < 2 * (nearestQuotient a m * m) + 2 * m := by
  unfold nearestQuotient
  have h1 := Nat.div_mul_le_self (2 * a + m) (2 * m)
  have h2 := Nat.lt_mul_div_succ (2 * a + m) (show 0 < 2 * m by omega)
  have e1 : (2 * a + m) / (2 * m) * (2 * m) = 2 * ((2 * a + m) / (2 * m) * m) := by ring
  have e2 : 2 * m * ((2 * a + m) / (2 * m) + 1) = 2 * ((2 * a + m) / (2 * m) * m) + 2 * m := by ring
  rw [e1] at h1
  rw [e2] at h2
  exact ⟨h1, h2⟩

/-- [proved-standard] **The nearest quotient is the only integer in that place**: `2qm ≤ 2a + m < 2qm + 2m` gives
`q = ⌊(2a + m)/(2m)⌋`. -/
theorem nearest_unique (a q : ℕ) {m : ℕ} (h1 : 2 * (q * m) ≤ 2 * a + m) (h2 : 2 * a + m < 2 * (q * m) + 2 * m) :
    q = nearestQuotient a m := by
  unfold nearestQuotient
  symm
  apply Nat.div_eq_of_lt_le
  · rw [show q * (2 * m) = 2 * (q * m) by ring]
    exact h1
  · rw [show (q + 1) * (2 * m) = 2 * (q * m) + 2 * m by ring]
    exact h2

/-- [proved-derived] **The half form is the nearest quotient**: `⌊(a + ⌊m/2⌋)/m⌋ = ⌊(2a + m)/(2m)⌋`, for every `m`. -/
theorem half_form (a m : ℕ) : (a + m / 2) / m = nearestQuotient a m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [nearestQuotient]
  obtain ⟨h1, h2⟩ := nearest a hm
  apply Nat.div_eq_of_lt_le
  · generalize nearestQuotient a m * m = t at *
    omega
  · rw [show (nearestQuotient a m + 1) * m = nearestQuotient a m * m + m by ring]
    generalize nearestQuotient a m * m = t at *
    omega

/-- [proved-derived] **A common factor leaves the quotient**: for every `K > 0`,
`⌊(aK + ⌊mK/2⌋)/(mK)⌋ = ⌊(2a + m)/(2m)⌋`. -/
theorem common_factor (a m : ℕ) {K : ℕ} (hK0 : 0 < K) :
    (a * K + m * K / 2) / (m * K) = nearestQuotient a m := by
  rw [half_form (a * K) (m * K)]
  unfold nearestQuotient
  rw [show 2 * (a * K) + m * K = K * (2 * a + m) by ring, show 2 * (m * K) = K * (2 * m) by ring]
  exact Nat.mul_div_mul_left _ _ hK0

/-- [proved-derived] **An even common factor leaves the quotient**, the record's statement: for an even `K > 0`,
`⌊(aK + ⌊mK/2⌋)/(mK)⌋ = ⌊(2a + m)/(2m)⌋`. Evenness is not used. -/
theorem even_factor (a m : ℕ) {K : ℕ} (_hK : Even K) (hK0 : 0 < K) :
    (a * K + m * K / 2) / (m * K) = nearestQuotient a m :=
  common_factor a m hK0

/-- [proved-derived] **Multiplier 1 gives the integers of every multiplier**: for `K > 0`,
`⌊(aK + ⌊mK/2⌋)/(mK)⌋ = ⌊(a + ⌊m/2⌋)/m⌋`. -/
theorem multiplier_one (a m : ℕ) {K : ℕ} (hK0 : 0 < K) :
    (a * K + m * K / 2) / (m * K) = (a + m / 2) / m := by
  rw [common_factor a m hK0, half_form]

/-- [proved-derived] The same at every power of two. -/
theorem two_pow_multiplier (a m e : ℕ) :
    (a * 2 ^ e + m * 2 ^ e / 2) / (m * 2 ^ e) = (a + m / 2) / m :=
  multiplier_one a m (by positivity)

/-- [proved-derived] **A contact's currents and shares at multiplier 1 are the integers they are at `2^62`.** -/
theorem multiplier_two_pow_62 (a m : ℕ) :
    (a * 2 ^ 62 + m * 2 ^ 62 / 2) / (m * 2 ^ 62) = (a + m / 2) / m :=
  two_pow_multiplier a m 62

/-- [proved-derived] The common factor on the integers, with the magnitude `|x|`. -/
theorem common_factor_int (x : ℤ) {m K : ℤ} (hm : 0 ≤ m) (hK0 : 0 < K) :
    (|x| * K + m * K / 2) / (m * K) = (2 * |x| + m) / (2 * m) := by
  lift m to ℕ using hm
  lift K to ℕ using hK0.le
  have hK0' : 0 < K := by exact_mod_cast hK0
  have h := common_factor x.natAbs m hK0'
  unfold nearestQuotient at h
  rw [← Int.natCast_natAbs x]
  exact_mod_cast h

/-- [proved-derived] The half form on the integers, with the magnitude `|x|`. -/
theorem half_form_int (x : ℤ) {m : ℤ} (hm : 0 ≤ m) : (|x| + m / 2) / m = (2 * |x| + m) / (2 * m) := by
  lift m to ℕ using hm
  have h := half_form x.natAbs m
  unfold nearestQuotient at h
  rw [← Int.natCast_natAbs x]
  exact_mod_cast h

/-! ## The engine's signed nearest division -/

/-- The engine's nearest division (`holonics_engine::ratio::div_nearest`): `x / k` to the nearest integer, a half going
away from zero. -/
def divNearest (x k : ℤ) : ℤ := if 0 ≤ x then (x + k / 2) / k else -((-x + k / 2) / k)

/-- [proved-derived] On a magnitude, a common factor of the two terms leaves the half form. -/
theorem nonneg_scale {y m K : ℤ} (hy : 0 ≤ y) (hm : 0 ≤ m) (hK : 0 < K) :
    (K * y + K * m / 2) / (K * m) = (y + m / 2) / m := by
  have h1 := common_factor_int y hm hK
  have h2 := half_form_int y hm
  rw [abs_of_nonneg hy] at h1 h2
  rw [mul_comm K y, mul_comm K m, h1, h2]

/-- [proved-derived] **The nearest division reads the ratio and not its terms**: a factor `K ≥ 1` shared by the
numerator and the divisor leaves it, `q(Kx, Km) = q(x, m)`. -/
theorem divNearest_common_factor (x : ℤ) {m K : ℤ} (hm : 0 ≤ m) (hK : 0 < K) :
    divNearest (K * x) (K * m) = divNearest x m := by
  unfold divNearest
  by_cases hx : 0 ≤ x
  · rw [if_pos hx, if_pos (mul_nonneg hK.le hx), nonneg_scale hx hm hK]
  · have hx' : x < 0 := not_le.mp hx
    have hKx : ¬ 0 ≤ K * x := not_le.mpr (mul_neg_of_pos_of_neg hK hx')
    rw [if_neg hx, if_neg hKx, ← mul_neg, nonneg_scale (neg_nonneg.mpr hx'.le) hm hK]

/-- [proved-derived] The nearest division is odd in its numerator. -/
theorem divNearest_neg (x : ℤ) {k : ℤ} (hk : 0 ≤ k) : divNearest (-x) k = -divNearest x k := by
  unfold divNearest
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [if_pos (by omega), if_neg (by omega), neg_neg]
  · rcases eq_or_lt_of_le hk with rfl | hpos
    · simp
    · have hlt : k / 2 < k := by omega
      have h0 : 0 ≤ k / 2 := by omega
      simp [Int.ediv_eq_zero_of_lt h0 hlt]
  · rw [if_neg (by omega), if_pos (by omega), neg_neg]

/-- [proved-derived] **The nearest division is the sign beside the magnitude's quotient**:
`q(x, m) = sign x · ⌊(|x| + ⌊m/2⌋)/m⌋`. -/
theorem divNearest_eq_sign_mul (x : ℤ) {m : ℤ} (hm : 0 ≤ m) : divNearest x m = x.sign * ((|x| + m / 2) / m) := by
  unfold divNearest
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [if_neg (by omega), Int.sign_eq_neg_one_of_neg hx, abs_of_neg hx]
    ring
  · rcases eq_or_lt_of_le hm with rfl | hpos
    · simp
    · have hlt : m / 2 < m := by omega
      have h0 : 0 ≤ m / 2 := by omega
      simp [Int.ediv_eq_zero_of_lt h0 hlt]
  · rw [if_pos hx.le, Int.sign_eq_one_of_pos hx, abs_of_pos hx, one_mul]

/-- [proved-standard] **The nearest division stands within half a divisor of the ratio**:
`−m ≤ 2(x − m·q(x, m)) ≤ m`. -/
theorem divNearest_nearest (x : ℤ) {m : ℤ} (hm : 0 < m) :
    -m ≤ 2 * (x - m * divNearest x m) ∧ 2 * (x - m * divNearest x m) ≤ m := by
  unfold divNearest
  by_cases hx : 0 ≤ x
  · rw [if_pos hx]
    have h1 := Int.mul_ediv_add_emod (x + m / 2) m
    have h2 := Int.emod_nonneg (x + m / 2) hm.ne'
    have h3 := Int.emod_lt_of_pos (x + m / 2) hm
    generalize (x + m / 2) / m = q at *
    generalize (x + m / 2) % m = r at *
    generalize hmq : m * q = t at *
    omega
  · rw [if_neg hx, mul_neg]
    have h1 := Int.mul_ediv_add_emod (-x + m / 2) m
    have h2 := Int.emod_nonneg (-x + m / 2) hm.ne'
    have h3 := Int.emod_lt_of_pos (-x + m / 2) hm
    generalize (-x + m / 2) / m = q at *
    generalize (-x + m / 2) % m = r at *
    generalize hmq : m * q = t at *
    omega

end Holonics.HNN.NearestQuotient
