import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic

/-!
# Einstein's strength: the free data an order, and `z₁` three times the free functions of three variables

The Einstein record of November 11
(`research/records/2026-11-11_EINSTEINS_FIELD_PROGRAM_ON_THE_COMPLEX_THE_UNIFIED_FIELD_IS_A_TWO_WAY_FLOW_A_GRAIN_GIVES_THE_MASS_AND_A_PROBABILITY_IS_ITS_FLAT_PART.md`,
§5.6 and §11; atlas `gr.strength-free-data`) reads Einstein's strength of a system of field equations (1955) as a count.
In four variables a function has `C(n + 3, 3)` coefficients of order `n`. A system of terms `(m_j, s_j)` (fields at
shift `0`, an equation of order `k` at shift `−k` with `m < 0`, a gauge function at `+1` with `m < 0`, an identity of
order `k` at `−k`) leaves `z(n) = Σ_j m_j C(n + 3 + s_j, 3)` coefficients free at order `n`, and its strength is
`z₁ = lim n z(n)/C(n + 3, 3)`.

[proved-standard; formal-checked] What is proved, over any field of characteristic zero where a count is read and over
`ℝ` where a limit is taken. Write `b_j = 2 + s_j` and `M_k = Σ_j m_j b_jᵏ` (`moment`).

1. **The count is a cubic in the order** (`freeCount_eq`): `6 z(n) = M₀ n³ + 3M₁ n² + (3M₂ − M₀) n + M₃ − M₁`, from
   `C(x, 3) = x(x − 1)(x − 2)/6` (`binom3`, equal to `Nat.choose` at every natural, `binom3_natCast`).
2. **What a system leaves free of four variables** (`tendsto_free_four`): `z(n)/C(n + 3, 3) → M₀`, so a system leaves no
   function of four variables free exactly when its terms balance, `Σ_j m_j = 0`.
3. **The free functions of three variables** (`tendsto_free_three`): when `M₀ = 0`, `z(n)/C(n + 2, 2) → M₁`, the
   count of functions of three variables the system leaves free.
4. **The strength** (`tendsto_strength`, `strength_eq_three_mul`): when `M₀ = 0`, `n z(n)/C(n + 3, 3) → 3M₁`, three
   times the free functions of three variables. (The record's reading, a value and a rate for each degree of freedom,
   stands beside the count.)
5. **The four systems the record reads** (`wave`, `maxwellStrengths`, `maxwellPotentials`, `gravitation`): each balances;
   their counts are `(n + 1)²`, `2(n + 1)(n + 3)`, `2n(n + 2)` and `2(n − 1)(n + 3)` at every order (so `z(10)` and
   `z(100)` are the record's 121 and 10,201; 286 and 20,806; 240 and 20,400; 234 and 20,394), and their strengths are
   6, 12, 12 and 12, the free functions of three variables 2, 4, 4 and 4. Maxwell reads 12 in both charts while their
   counts differ at every order: the chart moves the lower terms and never the strength.

The computational object is the helical pair interaction read as a count of free coefficients: a field's jet of order
`n` is its description to that depth, and a system's free data is the length of what it leaves to be written. Of the
winding guide's six general objects this touches faces and placement (the count read order by order); the helix, the
pair, the cell holonomy, the tube and the tower thread stay attached.

What stands beside it: Einstein's own table (Appendix II of *The Meaning of Relativity*), which the record does not
quote; the convention that assigns each term its shift, which is the count standard's (ruler 1), not derived here; the
invariance theorem of description length; and `Mathematics/PolynomialDeRham`, the three-variable chain whose alternating
count is the same kind of balance (`gr.strength-alternating-count`).

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Physics.Spacetime.StrengthFreeData

open Filter Topology

variable {K : Type*} [Field K]

/-! ## 1. The count -/

/-- `C(x, 3)` as the polynomial `x(x − 1)(x − 2)/6`, read at any argument. -/
def binom3 (x : K) : K := x * (x - 1) * (x - 2) / 6

/-- At every natural the polynomial is the binomial coefficient. -/
theorem binom3_natCast [CharZero K] (k : ℕ) : binom3 (k : K) = (k.choose 3 : K) := by
  have h := descPochhammer_eval_eq_descFactorial K k 3
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h
  simp only [descPochhammer_succ_right, descPochhammer_zero, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_natCast, one_mul, Nat.cast_zero, sub_zero] at h
  push_cast at h
  have h6 : ((Nat.factorial 3 : ℕ) : K) = 6 := by norm_num [Nat.factorial]
  rw [h6] at h
  rw [binom3, h, mul_div_cancel_left₀ _ (by norm_num : (6 : K) ≠ 0)]

/-- The free data a system of terms `(m_j, s_j)` leaves at order `n`: `z(n) = Σ_j m_j C(n + 3 + s_j, 3)`. -/
def freeCount (T : List (ℤ × ℤ)) (n : ℕ) : K :=
  (T.map fun t => (t.1 : K) * binom3 ((n : K) + 3 + t.2)).sum

/-- The moments `M_k = Σ_j m_j (2 + s_j)ᵏ`. -/
def moment (T : List (ℤ × ℤ)) (k : ℕ) : K :=
  (T.map fun t => (t.1 : K) * ((2 : K) + t.2) ^ k).sum

/-- **The count is a cubic in the order**: `6 z(n) = M₀ n³ + 3M₁ n² + (3M₂ − M₀) n + M₃ − M₁`. -/
theorem freeCount_eq [CharZero K] (T : List (ℤ × ℤ)) (n : ℕ) :
    6 * freeCount (K := K) T n
      = moment T 0 * (n : K) ^ 3 + 3 * moment T 1 * (n : K) ^ 2 + (3 * moment T 2 - moment T 0) * n
        + (moment T 3 - moment T 1) := by
  induction T with
  | nil => simp [freeCount, moment]
  | cons t T ih =>
      have e : ∀ k, moment (K := K) (t :: T) k = (t.1 : K) * ((2 : K) + t.2) ^ k + moment T k := fun k => by
        simp [moment]
      have f : freeCount (K := K) (t :: T) n = (t.1 : K) * binom3 ((n : K) + 3 + t.2) + freeCount T n := by
        simp [freeCount]
      rw [e, e, e, e, f, mul_add, ih, binom3]
      ring

/-! ## 2. The limits -/

/-- `C(n + 3, 3)` in closed form. -/
theorem choose_three_eq (n : ℕ) : ((n + 3).choose 3 : ℝ) = ((n : ℝ) + 3) * (n + 2) * (n + 1) / 6 := by
  rw [← binom3_natCast, binom3]
  push_cast
  ring

/-- `C(n + 2, 2)` in closed form. -/
theorem choose_two_eq (n : ℕ) : ((n + 2).choose 2 : ℝ) = ((n : ℝ) + 2) * (n + 1) / 2 := by
  rw [Nat.cast_choose_two]
  push_cast
  ring

private theorem tendsto_inv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
  tendsto_one_div_atTop_nhds_zero_nat

/-- **A system leaves `M₀` functions of four variables free**: `z(n)/C(n + 3, 3) → Σ_j m_j`. -/
theorem tendsto_free_four (T : List (ℤ × ℤ)) :
    Tendsto (fun n : ℕ => freeCount (K := ℝ) T n / ((n + 3).choose 3 : ℝ)) atTop (𝓝 (moment T 0)) := by
  set M0 : ℝ := moment T 0
  set M1 : ℝ := moment T 1
  set M2 : ℝ := moment T 2
  set M3 : ℝ := moment T 3
  have hnum : Tendsto (fun n : ℕ => M0 + 3 * M1 * (1 / (n : ℝ)) + (3 * M2 - M0) * (1 / (n : ℝ)) ^ 2
      + (M3 - M1) * (1 / (n : ℝ)) ^ 3) atTop (𝓝 (M0 + 3 * M1 * 0 + (3 * M2 - M0) * 0 ^ 2 + (M3 - M1) * 0 ^ 3)) :=
    ((tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_inv)).add
      (tendsto_const_nhds.mul (tendsto_inv.pow 2))).add (tendsto_const_nhds.mul (tendsto_inv.pow 3))
  have hden : Tendsto (fun n : ℕ => (1 + 3 * (1 / (n : ℝ))) * (1 + 2 * (1 / (n : ℝ))) * (1 + 1 / (n : ℝ))) atTop
      (𝓝 ((1 + 3 * 0) * (1 + 2 * 0) * (1 + 0))) :=
    ((tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_inv)).mul
      (tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_inv))).mul (tendsto_const_nhds.add tendsto_inv)
  have h := hnum.div hden (by norm_num)
  simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_one,
    div_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hz : freeCount (K := ℝ) T n
      = (M0 * (n : ℝ) ^ 3 + 3 * M1 * (n : ℝ) ^ 2 + (3 * M2 - M0) * n + (M3 - M1)) / 6 := by
    rw [← freeCount_eq]; ring
  rw [Pi.div_apply, hz, choose_three_eq]
  field_simp

/-- **The free functions of three variables**: for a balanced system, `z(n)/C(n + 2, 2) → M₁`. -/
theorem tendsto_free_three (T : List (ℤ × ℤ)) (hT : moment (K := ℝ) T 0 = 0) :
    Tendsto (fun n : ℕ => freeCount (K := ℝ) T n / ((n + 2).choose 2 : ℝ)) atTop (𝓝 (moment T 1)) := by
  set M1 : ℝ := moment T 1
  set M2 : ℝ := moment T 2
  set M3 : ℝ := moment T 3
  have hnum : Tendsto (fun n : ℕ => M1 + M2 * (1 / (n : ℝ)) + (M3 - M1) / 3 * (1 / (n : ℝ)) ^ 2) atTop
      (𝓝 (M1 + M2 * 0 + (M3 - M1) / 3 * 0 ^ 2)) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_inv)).add (tendsto_const_nhds.mul (tendsto_inv.pow 2))
  have hden : Tendsto (fun n : ℕ => (1 + 2 * (1 / (n : ℝ))) * (1 + 1 / (n : ℝ))) atTop
      (𝓝 ((1 + 2 * 0) * (1 + 0))) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_inv)).mul (tendsto_const_nhds.add tendsto_inv)
  have h := hnum.div hden (by norm_num)
  simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_one,
    div_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hz : freeCount (K := ℝ) T n = (3 * M1 * (n : ℝ) ^ 2 + 3 * M2 * n + (M3 - M1)) / 6 := by
    have := freeCount_eq (K := ℝ) T n
    rw [hT] at this
    linear_combination this / 6
  rw [Pi.div_apply, hz, choose_two_eq]
  field_simp
  ring

/-- **The strength**: for a balanced system, `n z(n)/C(n + 3, 3) → 3M₁`. -/
theorem tendsto_strength (T : List (ℤ × ℤ)) (hT : moment (K := ℝ) T 0 = 0) :
    Tendsto (fun n : ℕ => (n : ℝ) * freeCount (K := ℝ) T n / ((n + 3).choose 3 : ℝ)) atTop
      (𝓝 (3 * moment T 1)) := by
  set M1 : ℝ := moment T 1
  set M2 : ℝ := moment T 2
  set M3 : ℝ := moment T 3
  have hnum : Tendsto (fun n : ℕ => 3 * M1 + 3 * M2 * (1 / (n : ℝ)) + (M3 - M1) * (1 / (n : ℝ)) ^ 2) atTop
      (𝓝 (3 * M1 + 3 * M2 * 0 + (M3 - M1) * 0 ^ 2)) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_inv)).add (tendsto_const_nhds.mul (tendsto_inv.pow 2))
  have hden : Tendsto (fun n : ℕ => (1 + 3 * (1 / (n : ℝ))) * (1 + 2 * (1 / (n : ℝ))) * (1 + 1 / (n : ℝ))) atTop
      (𝓝 ((1 + 3 * 0) * (1 + 2 * 0) * (1 + 0))) :=
    ((tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_inv)).mul
      (tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_inv))).mul (tendsto_const_nhds.add tendsto_inv)
  have h := hnum.div hden (by norm_num)
  simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_one,
    div_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hz : freeCount (K := ℝ) T n = (3 * M1 * (n : ℝ) ^ 2 + 3 * M2 * n + (M3 - M1)) / 6 := by
    have := freeCount_eq (K := ℝ) T n
    rw [hT] at this
    linear_combination this / 6
  rw [Pi.div_apply, hz, choose_three_eq]
  field_simp

/-- **The strength is three times the free functions of three variables**: the two limits of a balanced system. -/
theorem strength_eq_three_mul (T : List (ℤ × ℤ)) (hT : moment (K := ℝ) T 0 = 0) :
    Tendsto (fun n : ℕ => (n : ℝ) * freeCount (K := ℝ) T n / ((n + 3).choose 3 : ℝ)) atTop
        (𝓝 (3 * moment T 1)) ∧
      Tendsto (fun n : ℕ => freeCount (K := ℝ) T n / ((n + 2).choose 2 : ℝ)) atTop (𝓝 (moment T 1)) :=
  ⟨tendsto_strength T hT, tendsto_free_three T hT⟩

/-! ## 3. The four systems the record reads -/

/-- The scalar wave equation: one field, one equation of order two. -/
def wave : List (ℤ × ℤ) := [(1, 0), (-1, -2)]

/-- Maxwell through the field strengths: six fields, eight equations of order one, two identities of order two. -/
def maxwellStrengths : List (ℤ × ℤ) := [(6, 0), (-8, -1), (2, -2)]

/-- Maxwell through the potentials: four fields, one gauge function, four equations of order two, one identity of order
three. -/
def maxwellPotentials : List (ℤ × ℤ) := [(4, 0), (-1, 1), (-4, -2), (1, -3)]

/-- Empty-space gravitation: ten fields, four gauge functions, ten equations of order two, four identities of order
three. -/
def gravitation : List (ℤ × ℤ) := [(10, 0), (-4, 1), (-10, -2), (4, -3)]

theorem wave_count (n : ℕ) : freeCount (K := ℚ) wave n = ((n : ℚ) + 1) ^ 2 := by
  simp only [freeCount, wave, binom3, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

theorem maxwellStrengths_count (n : ℕ) : freeCount (K := ℚ) maxwellStrengths n = 2 * ((n : ℚ) + 1) * (n + 3) := by
  simp only [freeCount, maxwellStrengths, binom3, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

theorem maxwellPotentials_count (n : ℕ) : freeCount (K := ℚ) maxwellPotentials n = 2 * (n : ℚ) * (n + 2) := by
  simp only [freeCount, maxwellPotentials, binom3, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

theorem gravitation_count (n : ℕ) : freeCount (K := ℚ) gravitation n = 2 * ((n : ℚ) - 1) * (n + 3) := by
  simp only [freeCount, gravitation, binom3, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

/-- The record's table, `z(10)` and `z(100)`. -/
theorem record_counts :
    freeCount (K := ℚ) wave 10 = 121 ∧ freeCount (K := ℚ) wave 100 = 10201 ∧
    freeCount (K := ℚ) maxwellStrengths 10 = 286 ∧ freeCount (K := ℚ) maxwellStrengths 100 = 20806 ∧
    freeCount (K := ℚ) maxwellPotentials 10 = 240 ∧ freeCount (K := ℚ) maxwellPotentials 100 = 20400 ∧
    freeCount (K := ℚ) gravitation 10 = 234 ∧ freeCount (K := ℚ) gravitation 100 = 20394 := by
  simp only [wave_count, maxwellStrengths_count, maxwellPotentials_count, gravitation_count]
  norm_num

/-- Each of the four systems balances, so none leaves a function of four variables free. -/
theorem balanced :
    moment (K := ℝ) wave 0 = 0 ∧ moment (K := ℝ) maxwellStrengths 0 = 0 ∧
    moment (K := ℝ) maxwellPotentials 0 = 0 ∧ moment (K := ℝ) gravitation 0 = 0 := by
  simp only [moment, wave, maxwellStrengths, maxwellPotentials, gravitation, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num

/-- Their free functions of three variables: 2, 4, 4 and 4. -/
theorem free_functions :
    moment (K := ℝ) wave 1 = 2 ∧ moment (K := ℝ) maxwellStrengths 1 = 4 ∧
    moment (K := ℝ) maxwellPotentials 1 = 4 ∧ moment (K := ℝ) gravitation 1 = 4 := by
  simp only [moment, wave, maxwellStrengths, maxwellPotentials, gravitation, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num

/-- **The strengths the record reads**: 6 for the wave equation, 12 for Maxwell in either chart and for empty-space
gravitation. -/
theorem strengths :
    Tendsto (fun n : ℕ => (n : ℝ) * freeCount (K := ℝ) wave n / ((n + 3).choose 3 : ℝ)) atTop (𝓝 6) ∧
    Tendsto (fun n : ℕ => (n : ℝ) * freeCount (K := ℝ) maxwellStrengths n / ((n + 3).choose 3 : ℝ)) atTop
      (𝓝 12) ∧
    Tendsto (fun n : ℕ => (n : ℝ) * freeCount (K := ℝ) maxwellPotentials n / ((n + 3).choose 3 : ℝ)) atTop
      (𝓝 12) ∧
    Tendsto (fun n : ℕ => (n : ℝ) * freeCount (K := ℝ) gravitation n / ((n + 3).choose 3 : ℝ)) atTop
      (𝓝 12) := by
  obtain ⟨h0, h1, h2, h3⟩ := balanced
  obtain ⟨f0, f1, f2, f3⟩ := free_functions
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := tendsto_strength wave h0
    rwa [f0, show (3 : ℝ) * 2 = 6 by norm_num] at h
  · have h := tendsto_strength maxwellStrengths h1
    rwa [f1, show (3 : ℝ) * 4 = 12 by norm_num] at h
  · have h := tendsto_strength maxwellPotentials h2
    rwa [f2, show (3 : ℝ) * 4 = 12 by norm_num] at h
  · have h := tendsto_strength gravitation h3
    rwa [f3, show (3 : ℝ) * 4 = 12 by norm_num] at h

end Holonics.Physics.Spacetime.StrengthFreeData
