import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# CanonicalHeight: Tate's telescoping construction

The Néron–Tate height is not an arithmetic object at its core — it is an **analytic
limit forced by a quasi-quadratic bound**.  If a height is quadratic under doubling up
to a constant, `|h(Dx) − 4h(x)| ≤ C`, then the successive terms of `h(Dⁿx)/4ⁿ` differ
geometrically with ratio `1/4`, so the sequence is Cauchy and the canonical limit
exists.  Nothing about elliptic curves enters; the arithmetic input is only the
two-sided bound, and `GeneralHeight` is where that bound lives.

This is the structural half of the one missing organ's arithmetic instance: the pairing
whose positivity is the content is built from exactly this limit.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

namespace Soma.Holonics.Millennium.CanonicalHeight

open Filter Topology

/-- **TATE'S TELESCOPING CONSTRUCTION.**  A height that is quasi-quadratic under a
doubling map — `|h(Dx) − 4h(x)| ≤ C` — has a canonical limit `ĥ(x) = lim h(Dⁿx)/4ⁿ`,
because the successive differences are geometric with ratio `1/4`.  This is the whole
content of the Néron–Tate construction; the arithmetic input is only the two-sided
bound. -/
theorem theCanonicalHeightExists {X : Type*} (h : X → ℝ) (D : X → X) (C : ℝ)
    (hC : ∀ y, |h (D y) - 4 * h y| ≤ C) (x : X) :
    ∃ L : ℝ, Tendsto (fun n : ℕ => h (D^[n] x) / 4 ^ n) atTop (𝓝 L) := by
  have hCnn : 0 ≤ C := le_trans (abs_nonneg _) (hC x)
  have hstep : ∀ n : ℕ,
      dist (h (D^[n] x) / 4 ^ n) (h (D^[n+1] x) / 4 ^ (n+1)) ≤ (C / 4) * (1/4 : ℝ) ^ n := by
    intro n
    have hiter : D^[n+1] x = D (D^[n] x) := by
      rw [Function.iterate_succ_apply']
    have h4 : (0:ℝ) < 4 ^ n := by positivity
    rw [Real.dist_eq, hiter]
    have hkey : h (D^[n] x) / 4 ^ n - h (D (D^[n] x)) / 4 ^ (n+1)
        = -(h (D (D^[n] x)) - 4 * h (D^[n] x)) / 4 ^ (n+1) := by
      field_simp
      ring
    rw [hkey, abs_div, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 4 ^ (n+1))]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 ^ (n+1))]
    calc |h (D (D^[n] x)) - 4 * h (D^[n] x)| ≤ C := hC _
      _ = (C / 4) * (1/4 : ℝ) ^ n * 4 ^ (n+1) := by
          have hpow : (1/4 : ℝ) ^ n * 4 ^ n = 1 := by
            rw [← mul_pow]; norm_num
          rw [pow_succ]
          linear_combination (-C) * hpow
  have hcau : CauchySeq (fun n : ℕ => h (D^[n] x) / 4 ^ n) :=
    cauchySeq_of_le_geometric (1/4 : ℝ) (C/4) (by norm_num) hstep
  exact cauchySeq_tendsto_of_complete hcau

/-- **THE LIMIT IS EXACTLY QUADRATIC.**  The quasi-quadratic bound is only approximate;
the limit it forces is exact: `ĥ(Dx) = 4·ĥ(x)`, with no error term at all.  That is the
whole reason for the construction — the canonical height is the unique quadratic
function the naive height approximates. -/
theorem theLimitIsExactlyQuadratic {X : Type*} (h : X → ℝ) (D : X → X) (x : X)
    (L L' : ℝ)
    (hL : Tendsto (fun n : ℕ => h (D^[n] x) / 4 ^ n) atTop (𝓝 L))
    (hL' : Tendsto (fun n : ℕ => h (D^[n] (D x)) / 4 ^ n) atTop (𝓝 L')) :
    L' = 4 * L := by
  have hshift : Tendsto (fun n : ℕ => h (D^[n+1] x) / 4 ^ (n+1)) atTop (𝓝 L) :=
    hL.comp (tendsto_add_atTop_nat 1)
  have hfun : ∀ n : ℕ, h (D^[n] (D x)) / 4 ^ n = 4 * (h (D^[n+1] x) / 4 ^ (n+1)) := by
    intro n
    rw [← Function.iterate_succ_apply D n x, pow_succ]
    field_simp
  have h4 : Tendsto (fun n : ℕ => h (D^[n] (D x)) / 4 ^ n) atTop (𝓝 (4 * L)) := by
    simpa [hfun] using hshift.const_mul (4 : ℝ)
  exact tendsto_nhds_unique hL' h4

/-! ## The upper half of the quasi-quadratic bound -/

/-- A monomial of total degree four is bounded by the fourth power of the max. -/
private lemma mono_le (c m n : ℤ) (i j : ℕ) (hij : i + j = 4) :
    |c * m ^ i * n ^ j| ≤ |c| * (max |m| |n|) ^ 4 := by
  have hm : |m| ≤ max |m| |n| := le_max_left _ _
  have hn : |n| ≤ max |m| |n| := le_max_right _ _
  have hM : (0:ℤ) ≤ max |m| |n| := le_trans (abs_nonneg m) hm
  have h1 : |c * m ^ i * n ^ j| = |c| * |m| ^ i * |n| ^ j := by
    rw [abs_mul, abs_mul, abs_pow, abs_pow]
  rw [h1]
  have h2 : |m| ^ i ≤ (max |m| |n|) ^ i := pow_le_pow_left₀ (abs_nonneg m) hm i
  have h3 : |n| ^ j ≤ (max |m| |n|) ^ j := pow_le_pow_left₀ (abs_nonneg n) hn j
  calc |c| * |m| ^ i * |n| ^ j
      ≤ |c| * (max |m| |n|) ^ i * (max |m| |n|) ^ j := by
        gcongr <;> first | exact abs_nonneg _ | exact hm | exact hn | positivity
    _ = |c| * (max |m| |n|) ^ 4 := by rw [mul_assoc, ← pow_add, hij]

/-- **A BINARY QUARTIC IS BOUNDED BY THE FOURTH POWER OF ITS ARGUMENTS.**  This is the
upper half of the quasi-quadratic bound: a degree-four duplication formula can raise the
height by at most a constant factor times the fourth power, which in the additive chart
is `h(2P) ≤ 4·h(P) + C`. -/
theorem theQuarticFormIsBoundedByTheFourthPower (a0 a1 a2 a3 a4 m n : ℤ) :
    |a0 * m ^ 4 * n ^ 0 + a1 * m ^ 3 * n ^ 1 + a2 * m ^ 2 * n ^ 2
        + a3 * m ^ 1 * n ^ 3 + a4 * m ^ 0 * n ^ 4|
      ≤ (|a0| + |a1| + |a2| + |a3| + |a4|) * (max |m| |n|) ^ 4 := by
  have b0 := mono_le a0 m n 4 0 rfl
  have b1 := mono_le a1 m n 3 1 rfl
  have b2 := mono_le a2 m n 2 2 rfl
  have b3 := mono_le a3 m n 1 3 rfl
  have b4 := mono_le a4 m n 0 4 rfl
  rw [abs_le] at b0 b1 b2 b3 b4 ⊢
  constructor <;> linarith [b0.1, b0.2, b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2]

/-- The doubled abscissa on `y² = x(x−a)(x−b)` is `(x²−ab)²/(4x(x−a)(x−b))`.  Written on
`x = m/n` both parts are binary quartics: numerator `(m²−abn²)²`, denominator
`4mn(m−an)(m−bn)`. -/
theorem theDoubledNumeratorIsBoundedAbove (a b m n : ℤ) :
    |(m ^ 2 - a * b * n ^ 2) ^ 2|
      ≤ (|(1:ℤ)| + |(0:ℤ)| + |(-2) * (a * b)| + |(0:ℤ)| + |(a * b) ^ 2|)
          * (max |m| |n|) ^ 4 := by
  have h := theQuarticFormIsBoundedByTheFourthPower 1 0 ((-2) * (a * b)) 0 ((a * b) ^ 2) m n
  have heq : (1:ℤ) * m ^ 4 * n ^ 0 + 0 * m ^ 3 * n ^ 1 + ((-2) * (a * b)) * m ^ 2 * n ^ 2
      + 0 * m ^ 1 * n ^ 3 + ((a * b) ^ 2) * m ^ 0 * n ^ 4
      = (m ^ 2 - a * b * n ^ 2) ^ 2 := by ring
  rwa [heq] at h

theorem theDoubledDenominatorIsBoundedAbove (a b m n : ℤ) :
    |4 * m * n * (m - a * n) * (m - b * n)|
      ≤ (|(0:ℤ)| + |(4:ℤ)| + |(-4) * (a + b)| + |4 * (a * b)| + |(0:ℤ)|)
          * (max |m| |n|) ^ 4 := by
  have h := theQuarticFormIsBoundedByTheFourthPower 0 4 ((-4) * (a + b)) (4 * (a * b)) 0 m n
  have heq : (0:ℤ) * m ^ 4 * n ^ 0 + 4 * m ^ 3 * n ^ 1 + ((-4) * (a + b)) * m ^ 2 * n ^ 2
      + (4 * (a * b)) * m ^ 1 * n ^ 3 + 0 * m ^ 0 * n ^ 4
      = 4 * m * n * (m - a * n) * (m - b * n) := by ring
  rwa [heq] at h

/-- **THE DUPLICATION IS BOUNDED ABOVE.**  Both parts of the doubled abscissa are
bounded by one constant times the fourth power of the argument's height, so in the
additive chart `h(2P) ≤ 4·h(P) + C`.  With the tree's growth bound below, the height is
quasi-quadratic and Tate's construction applies. -/
theorem theDuplicationIsBoundedAbove (a b m n : ℤ) :
    ∃ K : ℤ, 0 ≤ K ∧
      |(m ^ 2 - a * b * n ^ 2) ^ 2| ≤ K * (max |m| |n|) ^ 4 ∧
      |4 * m * n * (m - a * n) * (m - b * n)| ≤ K * (max |m| |n|) ^ 4 := by
  refine ⟨(1 + 2 * |a * b| + |a * b| ^ 2) + (4 + 4 * |a + b| + 4 * |a * b|), by positivity,
    ?_, ?_⟩
  · refine le_trans (theDoubledNumeratorIsBoundedAbove a b m n) ?_
    have hM : (0:ℤ) ≤ (max |m| |n|) ^ 4 := by positivity
    have h1 : |(-2) * (a * b)| = 2 * |a * b| := by rw [abs_mul]; norm_num
    have h2 : |(a * b) ^ 2| = |a * b| ^ 2 := by rw [abs_pow]
    refine mul_le_mul_of_nonneg_right ?_ hM
    rw [h1, h2]
    have hab := abs_nonneg (a + b)
    have hab2 := abs_nonneg (a * b)
    simp only [abs_zero, abs_one]
    linarith
  · refine le_trans (theDoubledDenominatorIsBoundedAbove a b m n) ?_
    have hM : (0:ℤ) ≤ (max |m| |n|) ^ 4 := by positivity
    have h1 : |(-4) * (a + b)| = 4 * |a + b| := by rw [abs_mul]; norm_num
    have h2 : |4 * (a * b)| = 4 * |a * b| := by rw [abs_mul]; norm_num
    refine mul_le_mul_of_nonneg_right ?_ hM
    rw [h1, h2]
    have hab := abs_nonneg (a * b)
    have hsq := sq_nonneg |a * b|
    simp only [abs_zero]
    norm_num
    positivity

end Soma.Holonics.Millennium.CanonicalHeight
