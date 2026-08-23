import ElementaryHolonics.Millennium.GeneralCertificate

/-!
# GeneralHeight: the duplication grows the height on every full-2-torsion curve

The last input the descent needs.  Writing `x = p/q` in lowest terms and
`M = max(|p|, q) = hgt x`, the doubled abscissa is `A/B` with

```text
A = (p² − ab·q²)²,      B = 2²·q·p·(p − a·q)·(p − b·q),
```

and the two certificates of `GeneralCertificate` bound `M⁷` against
`max(|A|,|B|)` times a cubic form.  Since the cancellation divides
`2²·(ab)²·(a−b)²`, the reduced numerator and denominator still carry `M⁴`:

```text
hgt(x)⁴  ≤  2⁶ · D¹² · hgt(x(2P)),        D = |a| + |b| + 1.
```

Constants are kept factored — `2⁶` is the accumulated denominator and coefficient
count, `D¹²` the coefficient size to the twelfth — so the flow of the bound stays
readable.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.GeneralHeight

open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.GeneralCertificate

/-! ## 1. The size parameter and the coefficient bounds -/

/-- The coefficient size of the curve. -/
def sizeOf (a b : ℤ) : ℕ := a.natAbs + b.natAbs + 1

lemma one_le_sizeOf (a b : ℤ) : 1 ≤ sizeOf a b := by
  unfold sizeOf; omega

lemma sub_le_sizeOf (a b : ℤ) : (a - b).natAbs ≤ sizeOf a b := by
  unfold sizeOf
  have := Int.natAbs_sub_le a b
  omega

lemma add_le_sizeOf (a b : ℤ) : (a + b).natAbs ≤ sizeOf a b := by
  unfold sizeOf
  have := Int.natAbs_add_le a b
  omega

lemma mul_le_sizeOf_sq (a b : ℤ) : (a * b).natAbs ≤ sizeOf a b ^ 2 := by
  rw [Int.natAbs_mul]
  unfold sizeOf
  nlinarith [Nat.zero_le a.natAbs, Nat.zero_le b.natAbs]

/-! ## 2. The cubic-form bound -/

/-- A three-term bound: each monomial of a homogeneous cubic in `(p,q)` with
coefficient size at most `c` is at most `c·M³`. -/
lemma natAbs_bound_cubic {p q : ℤ} {M : ℕ} (hp : p.natAbs ≤ M) (hq : q.natAbs ≤ M)
    (c : ℤ) (i j : ℕ) (hij : i + j = 3) :
    (c * p ^ i * q ^ j).natAbs ≤ c.natAbs * M ^ 3 := by
  rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow]
  have h1 : p.natAbs ^ i ≤ M ^ i := Nat.pow_le_pow_left hp i
  have h2 : q.natAbs ^ j ≤ M ^ j := Nat.pow_le_pow_left hq j
  calc c.natAbs * p.natAbs ^ i * q.natAbs ^ j
      ≤ c.natAbs * M ^ i * M ^ j := by
        exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
    _ = c.natAbs * M ^ 3 := by rw [mul_assoc, ← pow_add, hij]


/-! ## 3. The four cofactors are bounded by `2⁶·D⁶·M³` -/

variable {a b p q : ℤ} {M : ℕ}

/-- The `q`-side cofactor of the numerator. -/
def Fq (a b p q : ℤ) : ℤ :=
  2 ^ 2 * ((a - b) ^ 2 * q ^ 3 + 2 * (a + b) * p * q ^ 2 - 3 * p ^ 2 * q)

/-- The `q`-side cofactor of the denominator. -/
def Gq (a b p q : ℤ) : ℤ :=
  3 * p ^ 3 + (a + b) * p ^ 2 * q - 5 * (a * b) * p * q ^ 2
    - 2 * (a * b) * (a + b) * q ^ 3

/-- The `p`-side cofactor of the numerator. -/
def Fp (a b p q : ℤ) : ℤ :=
  2 ^ 2 * ((a - b) ^ 2 * p ^ 3 + 2 * (a * b) * (a + b) * p ^ 2 * q
    - 3 * (a * b) ^ 2 * p * q ^ 2)

/-- The `p`-side cofactor of the denominator. -/
def Gp (a b p q : ℤ) : ℤ :=
  -2 * (a * b) * (a + b) * p ^ 3 - 5 * (a * b) ^ 2 * p ^ 2 * q
    + (a + b) * (a * b) ^ 2 * p * q ^ 2 + 3 * (a * b) ^ 3 * q ^ 3

private lemma four_term_bound {c₁ c₂ c₃ c₄ : ℤ} (hp : p.natAbs ≤ M) (hq : q.natAbs ≤ M)
    {i₁ j₁ i₂ j₂ i₃ j₃ i₄ j₄ : ℕ}
    (h₁ : i₁ + j₁ = 3) (h₂ : i₂ + j₂ = 3) (h₃ : i₃ + j₃ = 3) (h₄ : i₄ + j₄ = 3) :
    (c₁ * p ^ i₁ * q ^ j₁ + c₂ * p ^ i₂ * q ^ j₂ + c₃ * p ^ i₃ * q ^ j₃
      + c₄ * p ^ i₄ * q ^ j₄).natAbs
      ≤ (c₁.natAbs + c₂.natAbs + c₃.natAbs + c₄.natAbs) * M ^ 3 := by
  have b₁ := natAbs_bound_cubic hp hq c₁ i₁ j₁ h₁
  have b₂ := natAbs_bound_cubic hp hq c₂ i₂ j₂ h₂
  have b₃ := natAbs_bound_cubic hp hq c₃ i₃ j₃ h₃
  have b₄ := natAbs_bound_cubic hp hq c₄ i₄ j₄ h₄
  have hadd := Int.natAbs_add_le (c₁ * p ^ i₁ * q ^ j₁ + c₂ * p ^ i₂ * q ^ j₂
    + c₃ * p ^ i₃ * q ^ j₃) (c₄ * p ^ i₄ * q ^ j₄)
  have hadd2 := Int.natAbs_add_le (c₁ * p ^ i₁ * q ^ j₁ + c₂ * p ^ i₂ * q ^ j₂)
    (c₃ * p ^ i₃ * q ^ j₃)
  have hadd3 := Int.natAbs_add_le (c₁ * p ^ i₁ * q ^ j₁) (c₂ * p ^ i₂ * q ^ j₂)
  calc (c₁ * p ^ i₁ * q ^ j₁ + c₂ * p ^ i₂ * q ^ j₂ + c₃ * p ^ i₃ * q ^ j₃
      + c₄ * p ^ i₄ * q ^ j₄).natAbs
      ≤ c₁.natAbs * M ^ 3 + c₂.natAbs * M ^ 3 + c₃.natAbs * M ^ 3
        + c₄.natAbs * M ^ 3 := by omega
    _ = (c₁.natAbs + c₂.natAbs + c₃.natAbs + c₄.natAbs) * M ^ 3 := by ring


private lemma sizeOf_pow_mono (a b : ℤ) {i j : ℕ} (h : i ≤ j) :
    sizeOf a b ^ i ≤ sizeOf a b ^ j :=
  Nat.pow_le_pow_right (one_le_sizeOf a b) h

lemma Fq_bound (hp : p.natAbs ≤ M) (hq : q.natAbs ≤ M) :
    (Fq a b p q).natAbs ≤ 2 ^ 6 * sizeOf a b ^ 6 * M ^ 3 := by
  set D : ℕ := sizeOf a b with hD
  have hD1 : 1 ≤ D := one_le_sizeOf a b
  have hrw : Fq a b p q = (2 ^ 2 * (a - b) ^ 2) * p ^ 0 * q ^ 3
      + (2 ^ 3 * (a + b)) * p ^ 1 * q ^ 2 + (-(2 ^ 2 * 3)) * p ^ 2 * q ^ 1
      + 0 * p ^ 3 * q ^ 0 := by
    unfold Fq; ring
  rw [hrw]
  refine le_trans (four_term_bound hp hq rfl rfl rfl rfl) ?_
  have c1 : (2 ^ 2 * (a - b) ^ 2 : ℤ).natAbs = 2 ^ 2 * (a - b).natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_pow]
    norm_num
  have c2 : (2 ^ 3 * (a + b) : ℤ).natAbs = 2 ^ 3 * (a + b).natAbs := by
    rw [Int.natAbs_mul]
    norm_num
  have c3 : (-(2 ^ 2 * 3) : ℤ).natAbs = 2 ^ 2 * 3 := by decide
  rw [c1, c2, c3]
  have hsub : (a - b).natAbs ≤ D := sub_le_sizeOf a b
  have hadd : (a + b).natAbs ≤ D := add_le_sizeOf a b
  have hbound : 2 ^ 2 * (a - b).natAbs ^ 2 + 2 ^ 3 * (a + b).natAbs + 2 ^ 2 * 3
      + (0 : ℤ).natAbs ≤ 2 ^ 6 * D ^ 6 := by
    have h1 : (a - b).natAbs ^ 2 ≤ D ^ 2 := Nat.pow_le_pow_left hsub 2
    have h2 : D ^ 2 ≤ D ^ 6 := sizeOf_pow_mono a b (by omega)
    have h3 : D ≤ D ^ 6 := by
      calc D = D ^ 1 := (pow_one D).symm
        _ ≤ D ^ 6 := sizeOf_pow_mono a b (by omega)
    have h4 : 1 ≤ D ^ 6 := Nat.one_le_pow _ _ (by omega)
    simp only [Int.natAbs_zero]
    omega
  exact Nat.mul_le_mul_right _ hbound

lemma Gq_bound (hp : p.natAbs ≤ M) (hq : q.natAbs ≤ M) :
    (Gq a b p q).natAbs ≤ 2 ^ 6 * sizeOf a b ^ 6 * M ^ 3 := by
  set D : ℕ := sizeOf a b with hD
  have hD1 : 1 ≤ D := one_le_sizeOf a b
  have hrw : Gq a b p q = (3 : ℤ) * p ^ 3 * q ^ 0 + (a + b) * p ^ 2 * q ^ 1
      + (-(5 * (a * b))) * p ^ 1 * q ^ 2 + (-(2 * (a * b) * (a + b))) * p ^ 0 * q ^ 3 := by
    unfold Gq; ring
  rw [hrw]
  refine le_trans (four_term_bound hp hq rfl rfl rfl rfl) ?_
  have c1 : (3 : ℤ).natAbs = 3 := by decide
  have c3 : (-(5 * (a * b)) : ℤ).natAbs = 5 * (a * b).natAbs := by
    rw [Int.natAbs_neg, Int.natAbs_mul]
    norm_num
  have c4 : (-(2 * (a * b) * (a + b)) : ℤ).natAbs
      = 2 * (a * b).natAbs * (a + b).natAbs := by
    rw [Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_mul]
    norm_num
  rw [c1, c3, c4]
  have hadd : (a + b).natAbs ≤ D := add_le_sizeOf a b
  have hmul : (a * b).natAbs ≤ D ^ 2 := mul_le_sizeOf_sq a b
  have hbound : 3 + (a + b).natAbs + 5 * (a * b).natAbs
      + 2 * (a * b).natAbs * (a + b).natAbs ≤ 2 ^ 6 * D ^ 6 := by
    have h1 : 2 * (a * b).natAbs * (a + b).natAbs ≤ 2 * D ^ 2 * D := by
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hmul) hadd
    have h2 : 2 * D ^ 2 * D = 2 * D ^ 3 := by ring
    have h3 : D ^ 3 ≤ D ^ 6 := sizeOf_pow_mono a b (by omega)
    have h4 : D ^ 2 ≤ D ^ 6 := sizeOf_pow_mono a b (by omega)
    have h5 : D ≤ D ^ 6 := by
      calc D = D ^ 1 := (pow_one D).symm
        _ ≤ D ^ 6 := sizeOf_pow_mono a b (by omega)
    have h6 : 1 ≤ D ^ 6 := Nat.one_le_pow _ _ (by omega)
    omega
  exact Nat.mul_le_mul_right _ hbound


lemma Fp_bound (hp : p.natAbs ≤ M) (hq : q.natAbs ≤ M) :
    (Fp a b p q).natAbs ≤ 2 ^ 6 * sizeOf a b ^ 6 * M ^ 3 := by
  set D : ℕ := sizeOf a b with hD
  have hD1 : 1 ≤ D := one_le_sizeOf a b
  have hrw : Fp a b p q = (2 ^ 2 * (a - b) ^ 2) * p ^ 3 * q ^ 0
      + (2 ^ 3 * (a * b) * (a + b)) * p ^ 2 * q ^ 1
      + (-(2 ^ 2 * 3 * (a * b) ^ 2)) * p ^ 1 * q ^ 2 + 0 * p ^ 0 * q ^ 3 := by
    unfold Fp; ring
  rw [hrw]
  refine le_trans (four_term_bound hp hq rfl rfl rfl rfl) ?_
  have c1 : (2 ^ 2 * (a - b) ^ 2 : ℤ).natAbs = 2 ^ 2 * (a - b).natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_pow]; norm_num
  have c2 : (2 ^ 3 * (a * b) * (a + b) : ℤ).natAbs
      = 2 ^ 3 * (a * b).natAbs * (a + b).natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_mul]; norm_num
  have c3 : (-(2 ^ 2 * 3 * (a * b) ^ 2) : ℤ).natAbs = 2 ^ 2 * 3 * (a * b).natAbs ^ 2 := by
    rw [Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_pow]; norm_num
  rw [c1, c2, c3]
  have hsub : (a - b).natAbs ≤ D := sub_le_sizeOf a b
  have hadd : (a + b).natAbs ≤ D := add_le_sizeOf a b
  have hmul : (a * b).natAbs ≤ D ^ 2 := mul_le_sizeOf_sq a b
  have hbound : 2 ^ 2 * (a - b).natAbs ^ 2 + 2 ^ 3 * (a * b).natAbs * (a + b).natAbs
      + 2 ^ 2 * 3 * (a * b).natAbs ^ 2 + (0 : ℤ).natAbs ≤ 2 ^ 6 * D ^ 6 := by
    have h1 : (a - b).natAbs ^ 2 ≤ D ^ 2 := Nat.pow_le_pow_left hsub 2
    have h2 : (a * b).natAbs * (a + b).natAbs ≤ D ^ 3 := by
      calc (a * b).natAbs * (a + b).natAbs ≤ D ^ 2 * D := Nat.mul_le_mul hmul hadd
        _ = D ^ 3 := by ring
    have h3 : (a * b).natAbs ^ 2 ≤ D ^ 4 := by
      calc (a * b).natAbs ^ 2 ≤ (D ^ 2) ^ 2 := Nat.pow_le_pow_left hmul 2
        _ = D ^ 4 := by ring
    have h4 : D ^ 2 ≤ D ^ 6 := sizeOf_pow_mono a b (by omega)
    have h5 : D ^ 3 ≤ D ^ 6 := sizeOf_pow_mono a b (by omega)
    have h6 : D ^ 4 ≤ D ^ 6 := sizeOf_pow_mono a b (by omega)
    have hX : (a - b).natAbs ^ 2 ≤ D ^ 6 := le_trans h1 h4
    have hYZ : (a * b).natAbs * (a + b).natAbs ≤ D ^ 6 := le_trans h2 h5
    have hY2 : (a * b).natAbs ^ 2 ≤ D ^ 6 := le_trans h3 h6
    have t1 : 2 ^ 2 * (a - b).natAbs ^ 2 ≤ 2 ^ 2 * D ^ 6 := Nat.mul_le_mul_left _ hX
    have t2 : 2 ^ 3 * (a * b).natAbs * (a + b).natAbs ≤ 2 ^ 3 * D ^ 6 := by
      rw [mul_assoc]
      exact Nat.mul_le_mul_left _ hYZ
    have t3 : 2 ^ 2 * 3 * (a * b).natAbs ^ 2 ≤ 2 ^ 2 * 3 * D ^ 6 :=
      Nat.mul_le_mul_left _ hY2
    simp only [Int.natAbs_zero]
    omega
  exact Nat.mul_le_mul_right _ hbound

lemma Gp_bound (hp : p.natAbs ≤ M) (hq : q.natAbs ≤ M) :
    (Gp a b p q).natAbs ≤ 2 ^ 6 * sizeOf a b ^ 6 * M ^ 3 := by
  set D : ℕ := sizeOf a b with hD
  have hD1 : 1 ≤ D := one_le_sizeOf a b
  have hrw : Gp a b p q = (-(2 * (a * b) * (a + b))) * p ^ 3 * q ^ 0
      + (-(5 * (a * b) ^ 2)) * p ^ 2 * q ^ 1
      + ((a + b) * (a * b) ^ 2) * p ^ 1 * q ^ 2 + (3 * (a * b) ^ 3) * p ^ 0 * q ^ 3 := by
    unfold Gp; ring
  rw [hrw]
  refine le_trans (four_term_bound hp hq rfl rfl rfl rfl) ?_
  have c1 : (-(2 * (a * b) * (a + b)) : ℤ).natAbs
      = 2 * (a * b).natAbs * (a + b).natAbs := by
    rw [Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_mul]; norm_num
  have c2 : (-(5 * (a * b) ^ 2) : ℤ).natAbs = 5 * (a * b).natAbs ^ 2 := by
    rw [Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_pow]; norm_num
  have c3 : ((a + b) * (a * b) ^ 2 : ℤ).natAbs = (a + b).natAbs * (a * b).natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_pow]
  have c4 : ((3 : ℤ) * (a * b) ^ 3).natAbs = 3 * (a * b).natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow]; norm_num
  rw [c1, c2, c3, c4]
  have hadd : (a + b).natAbs ≤ D := add_le_sizeOf a b
  have hmul : (a * b).natAbs ≤ D ^ 2 := mul_le_sizeOf_sq a b
  have hbound : 2 * (a * b).natAbs * (a + b).natAbs + 5 * (a * b).natAbs ^ 2
      + (a + b).natAbs * (a * b).natAbs ^ 2 + 3 * (a * b).natAbs ^ 3 ≤ 2 ^ 6 * D ^ 6 := by
    have h1 : (a * b).natAbs * (a + b).natAbs ≤ D ^ 3 := by
      calc (a * b).natAbs * (a + b).natAbs ≤ D ^ 2 * D := Nat.mul_le_mul hmul hadd
        _ = D ^ 3 := by ring
    have h2 : (a * b).natAbs ^ 2 ≤ D ^ 4 := by
      calc (a * b).natAbs ^ 2 ≤ (D ^ 2) ^ 2 := Nat.pow_le_pow_left hmul 2
        _ = D ^ 4 := by ring
    have h3 : (a + b).natAbs * (a * b).natAbs ^ 2 ≤ D ^ 5 := by
      calc (a + b).natAbs * (a * b).natAbs ^ 2 ≤ D * D ^ 4 := Nat.mul_le_mul hadd h2
        _ = D ^ 5 := by ring
    have h4 : (a * b).natAbs ^ 3 ≤ D ^ 6 := by
      calc (a * b).natAbs ^ 3 ≤ (D ^ 2) ^ 3 := Nat.pow_le_pow_left hmul 3
        _ = D ^ 6 := by ring
    have m3 : D ^ 3 ≤ D ^ 6 := sizeOf_pow_mono a b (by omega)
    have m4 : D ^ 4 ≤ D ^ 6 := sizeOf_pow_mono a b (by omega)
    have m5 : D ^ 5 ≤ D ^ 6 := sizeOf_pow_mono a b (by omega)
    have u1 : 2 * (a * b).natAbs * (a + b).natAbs ≤ 2 * D ^ 6 := by
      rw [mul_assoc]
      exact Nat.mul_le_mul_left _ (le_trans h1 m3)
    have u2 : 5 * (a * b).natAbs ^ 2 ≤ 5 * D ^ 6 :=
      Nat.mul_le_mul_left _ (le_trans h2 m4)
    have u3 : (a + b).natAbs * (a * b).natAbs ^ 2 ≤ D ^ 6 := le_trans h3 m5
    have u4 : 3 * (a * b).natAbs ^ 3 ≤ 3 * D ^ 6 := Nat.mul_le_mul_left _ h4
    omega
  exact Nat.mul_le_mul_right _ hbound


/-! ## 4. The two-sided bound on the quartic pair -/

/-- The numerator of the doubled abscissa. -/
def numA (a b p q : ℤ) : ℤ := (p ^ 2 - a * b * q ^ 2) ^ 2

/-- The denominator of the doubled abscissa. -/
def denB (a b p q : ℤ) : ℤ := 2 ^ 2 * q * p * (p - a * q) * (p - b * q)

lemma certificate_q (a b p q : ℤ) :
    Fq a b p q * numA a b p q + Gq a b p q * denB a b p q
      = 2 ^ 2 * (a * b) ^ 2 * (a - b) ^ 2 * q ^ 7 := by
  unfold Fq Gq numA denB
  ring

lemma certificate_p (a b p q : ℤ) :
    Fp a b p q * numA a b p q + Gp a b p q * denB a b p q
      = 2 ^ 2 * (a - b) ^ 2 * p ^ 7 := by
  unfold Fp Gp numA denB
  ring

/-- **THE QUARTIC PAIR DOMINATES THE SEVENTH POWER**: `2²(a−b)²·M⁷` is at most
`2⁷·D⁶·M³` times the larger of the two, so the reduced pair carries `M⁴`. -/
theorem theQuarticPairDominates (a b p q : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) {M : ℕ}
    (hp : p.natAbs ≤ M) (hq : q.natAbs ≤ M) (hM : M = max p.natAbs q.natAbs) :
    (2 ^ 2 * (a - b) ^ 2 : ℤ).natAbs * M ^ 7
      ≤ 2 ^ 7 * sizeOf a b ^ 6 * M ^ 3
        * max (numA a b p q).natAbs (denB a b p q).natAbs := by
  set D : ℕ := sizeOf a b with hD
  set N : ℕ := max (numA a b p q).natAbs (denB a b p q).natAbs with hN
  set K : ℕ := (2 ^ 2 * (a - b) ^ 2 : ℤ).natAbs with hK
  have master : ∀ (F G : ℤ) (R : ℤ), F * numA a b p q + G * denB a b p q = R →
      F.natAbs ≤ 2 ^ 6 * D ^ 6 * M ^ 3 → G.natAbs ≤ 2 ^ 6 * D ^ 6 * M ^ 3 →
      R.natAbs ≤ 2 ^ 7 * D ^ 6 * M ^ 3 * N := by
    intro F G R hR hF hG
    have h1 : R.natAbs ≤ (F * numA a b p q).natAbs + (G * denB a b p q).natAbs := by
      rw [← hR]
      exact Int.natAbs_add_le _ _
    have h2 : (F * numA a b p q).natAbs ≤ (2 ^ 6 * D ^ 6 * M ^ 3) * N := by
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul hF (le_max_left _ _)
    have h3 : (G * denB a b p q).natAbs ≤ (2 ^ 6 * D ^ 6 * M ^ 3) * N := by
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul hG (le_max_right _ _)
    have h4 : 2 ^ 7 * D ^ 6 * M ^ 3 * N
        = (2 ^ 6 * D ^ 6 * M ^ 3) * N + (2 ^ 6 * D ^ 6 * M ^ 3) * N := by ring
    omega
  have hqside := master _ _ _ (certificate_q a b p q) (Fq_bound hp hq) (Gq_bound hp hq)
  have hpside := master _ _ _ (certificate_p a b p q) (Fp_bound hp hq) (Gp_bound hp hq)
  have hpval : (2 ^ 2 * (a - b) ^ 2 * p ^ 7 : ℤ).natAbs = K * p.natAbs ^ 7 := by
    rw [hK, Int.natAbs_mul, Int.natAbs_pow]
  have hfac : (2 ^ 2 * (a * b) ^ 2 * (a - b) ^ 2 * q ^ 7 : ℤ).natAbs
      = (a * b).natAbs ^ 2 * K * q.natAbs ^ 7 := by
    rw [show (2 ^ 2 * (a * b) ^ 2 * (a - b) ^ 2 * q ^ 7 : ℤ)
        = ((a * b) ^ 2 * (2 ^ 2 * (a - b) ^ 2)) * q ^ 7 from by ring]
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow, hK]
  have hab1 : 1 ≤ (a * b).natAbs ^ 2 :=
    Nat.one_le_pow _ _ (Nat.pos_of_ne_zero fun hc =>
      (mul_ne_zero ha hb) (Int.natAbs_eq_zero.mp hc))
  rw [hpval] at hpside
  rw [hfac] at hqside
  rcases max_cases p.natAbs q.natAbs with ⟨hmax, -⟩ | ⟨hmax, -⟩
  · have hM7 : M ^ 7 = p.natAbs ^ 7 := by rw [hM, hmax]
    rw [hM7]
    exact hpside
  · have hM7 : M ^ 7 = q.natAbs ^ 7 := by rw [hM, hmax]
    rw [hM7]
    calc K * q.natAbs ^ 7 ≤ (a * b).natAbs ^ 2 * K * q.natAbs ^ 7 := by
          refine Nat.mul_le_mul_right _ ?_
          exact Nat.le_mul_of_pos_left _ (by omega)
      _ ≤ 2 ^ 7 * D ^ 6 * M ^ 3 * N := hqside


/-! ## 5. The duplication height law -/

open Soma.Holonics.Millennium.FiveHeight

/-- The reduced pair carries the full pair, divided by the cancellation. -/
lemma reduced_pair_height {A B : ℤ} (hA : A ≠ 0) (hB : B ≠ 0) :
    max A.natAbs B.natAbs
      = Int.gcd A B * max (A / (Int.gcd A B : ℤ)).natAbs (B / (Int.gcd A B : ℤ)).natAbs := by
  set d : ℕ := Int.gcd A B with hd
  have hd0 : 0 < d := Int.gcd_pos_of_ne_zero_left B hA
  have hdA : (d : ℤ) ∣ A := Int.gcd_dvd_left A B
  have hdB : (d : ℤ) ∣ B := Int.gcd_dvd_right A B
  have hA' : A = (d : ℤ) * (A / (d : ℤ)) := (Int.ediv_mul_cancel hdA).symm.trans (mul_comm _ _)
  have hB' : B = (d : ℤ) * (B / (d : ℤ)) := (Int.ediv_mul_cancel hdB).symm.trans (mul_comm _ _)
  have hAn : A.natAbs = d * (A / (d : ℤ)).natAbs := by
    conv_lhs => rw [hA']
    rw [Int.natAbs_mul, Int.natAbs_natCast]
  have hBn : B.natAbs = d * (B / (d : ℤ)).natAbs := by
    conv_lhs => rw [hB']
    rw [Int.natAbs_mul, Int.natAbs_natCast]
  rw [hAn, hBn, ← Nat.mul_max_mul_left]

set_option maxHeartbeats 1000000 in
/-- **THE DUPLICATION GROWS THE HEIGHT ON EVERY FULL-TWO-TORSION CURVE**: with
`D = |a| + |b| + 1`, the doubled abscissa satisfies

```text
hgt(x)⁴  ≤  2⁷ · D¹⁰ · hgt(x(2P)).
```

Quartic growth with a constant polynomial in the coefficients, on every elliptic curve
over `ℚ` with full rational two-torsion.  The congruent slice's `16n⁶` is this law read
at `b = −a`. -/
theorem theDuplicationGrowsTheHeightOnEveryFullTwoTorsionCurve
    (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0) (u : ℚ)
    (hA : numA a b u.num (u.den : ℤ) ≠ 0) (hB : denB a b u.num (u.den : ℤ) ≠ 0) :
    hgt u ^ 4 ≤ 2 ^ 7 * sizeOf a b ^ 10
      * max (numA a b u.num (u.den : ℤ) / (Int.gcd (numA a b u.num (u.den : ℤ))
          (denB a b u.num (u.den : ℤ)) : ℤ)).natAbs
        (denB a b u.num (u.den : ℤ) / (Int.gcd (numA a b u.num (u.den : ℤ))
          (denB a b u.num (u.den : ℤ)) : ℤ)).natAbs := by
  set p : ℤ := u.num with hpdef
  set q : ℤ := (u.den : ℤ) with hqdef
  set D : ℕ := sizeOf a b with hD
  set d : ℕ := Int.gcd (numA a b p q) (denB a b p q) with hddef
  set H : ℕ := max (numA a b p q / (d : ℤ)).natAbs (denB a b p q / (d : ℤ)).natAbs with hH
  set M : ℕ := hgt u with hM
  set K : ℕ := (2 ^ 2 * (a - b) ^ 2 : ℤ).natAbs with hK
  have hqn : q.natAbs = u.den := by rw [hqdef, Int.natAbs_natCast]
  have hMeq : M = max p.natAbs q.natAbs := by rw [hM, hgt, hpdef, hqn]
  have hp : p.natAbs ≤ M := by rw [hMeq]; exact le_max_left _ _
  have hq : q.natAbs ≤ M := by rw [hMeq]; exact le_max_right _ _
  have hM0 : 0 < M := by rw [hM]; exact hgt_pos u
  have hpair := theQuarticPairDominates a b p q ha hb hp hq hMeq
  -- the cancellation divides the certificate constant
  have hcop : IsCoprime p q := by
    rw [hpdef, hqdef]
    exact Int.isCoprime_iff_gcd_eq_one.mpr (by simpa using u.reduced)
  have hdvd : (d : ℤ) ∣ 2 ^ 2 * (a * b) ^ 2 * (a - b) ^ 2 := by
    refine theCancellationIsExactlyBounded a b p q hcop _ ?_ ?_
    · rw [hddef]; exact Int.gcd_dvd_left _ _
    · rw [hddef]
      have := Int.gcd_dvd_right (numA a b p q) (denB a b p q)
      unfold denB at this
      exact this
  have hKpos : 0 < K := by
    rw [hK, Int.natAbs_pos]
    positivity
  have habs : ((a * b).natAbs : ℤ) ^ 2 = (a * b) ^ 2 := by
    rw [← Int.abs_eq_natAbs, sq_abs]
  have hKint : ((K : ℕ) : ℤ) = 2 ^ 2 * (a - b) ^ 2 := by
    rw [hK, Int.natAbs_of_nonneg (by positivity)]
  have hdle : d ≤ (a * b).natAbs ^ 2 * K := by
    have hpos : (0 : ℤ) < 2 ^ 2 * (a * b) ^ 2 * (a - b) ^ 2 := by
      have : (a * b) ≠ 0 := mul_ne_zero ha hb
      positivity
    have h1 : (d : ℤ) ≤ 2 ^ 2 * (a * b) ^ 2 * (a - b) ^ 2 := Int.le_of_dvd hpos hdvd
    have h2 : (((a * b).natAbs ^ 2 * K : ℕ) : ℤ) = 2 ^ 2 * (a * b) ^ 2 * (a - b) ^ 2 := by
      push_cast
      rw [sq_abs, hKint]
      ring
    omega
  -- the pair splits into the cancellation and the reduced pair
  have hsplit : max (numA a b p q).natAbs (denB a b p q).natAbs = d * H := by
    rw [hH, hddef]
    exact reduced_pair_height hA hB
  rw [hsplit] at hpair
  -- divide the seventh power down to the fourth
  have hchain : K * M ^ 7 ≤ 2 ^ 7 * D ^ 6 * M ^ 3 * ((a * b).natAbs ^ 2 * K * H) := by
    calc K * M ^ 7 ≤ 2 ^ 7 * D ^ 6 * M ^ 3 * (d * H) := hpair
      _ ≤ 2 ^ 7 * D ^ 6 * M ^ 3 * ((a * b).natAbs ^ 2 * K * H) := by
          refine Nat.mul_le_mul_left _ ?_
          exact Nat.mul_le_mul_right _ hdle
  have hcancel : M ^ 7 ≤ 2 ^ 7 * D ^ 6 * M ^ 3 * ((a * b).natAbs ^ 2 * H) := by
    have hre : 2 ^ 7 * D ^ 6 * M ^ 3 * ((a * b).natAbs ^ 2 * K * H)
        = K * (2 ^ 7 * D ^ 6 * M ^ 3 * ((a * b).natAbs ^ 2 * H)) := by ring
    rw [hre] at hchain
    exact Nat.le_of_mul_le_mul_left hchain hKpos
  have hM3 : M ^ 7 = M ^ 3 * M ^ 4 := by ring
  have hfourth : M ^ 4 ≤ 2 ^ 7 * D ^ 6 * ((a * b).natAbs ^ 2 * H) := by
    have hre : 2 ^ 7 * D ^ 6 * M ^ 3 * ((a * b).natAbs ^ 2 * H)
        = M ^ 3 * (2 ^ 7 * D ^ 6 * ((a * b).natAbs ^ 2 * H)) := by ring
    rw [hM3, hre] at hcancel
    exact Nat.le_of_mul_le_mul_left hcancel (pow_pos hM0 3)
  -- the coefficient square is bounded by `D⁴`
  have hcoef : (a * b).natAbs ^ 2 ≤ D ^ 4 := by
    have h1 : (a * b).natAbs ≤ D ^ 2 := mul_le_sizeOf_sq a b
    calc (a * b).natAbs ^ 2 ≤ (D ^ 2) ^ 2 := Nat.pow_le_pow_left h1 2
      _ = D ^ 4 := by ring
  calc M ^ 4 ≤ 2 ^ 7 * D ^ 6 * ((a * b).natAbs ^ 2 * H) := hfourth
    _ ≤ 2 ^ 7 * D ^ 6 * (D ^ 4 * H) := by
        refine Nat.mul_le_mul_left _ ?_
        exact Nat.mul_le_mul_right _ hcoef
    _ = 2 ^ 7 * D ^ 10 * H := by ring


/-! ## 6. The chord bound

The chord through a point and a fixed point meets the curve again at an abscissa
satisfying a quadratic whose coefficients are **degree two** in the moving abscissa:

```text
(x − x_R)²·Z² − 2[x·x_R·(x + x_R − 2(a+b)) + ab·(x + x_R)]·Z + (x·x_R − ab)² = 0.
```

At `b = −a` this is the congruent slice's `(x+x_R)(x·x_R − n²)` and `(x·x_R + n²)²`
on the nose.  Degree two is what makes the growth quadratic against the duplication's
quartic, and that gap is the descent. -/

/-- The middle coefficient of the chord quadratic. -/
def chordW (a b x xR : ℚ) : ℚ := x * xR * (x + xR - 2 * (a + b)) + a * b * (x + xR)

/-- The constant coefficient of the chord quadratic. -/
def chordK (a b x xR : ℚ) : ℚ := (x * xR - a * b) ^ 2

lemma chordW_eq (a b x xR : ℚ) :
    chordW a b x xR
      = x * (x - a) * (x - b) + xR * (xR - a) * (xR - b)
        + ((a + b) - x - xR) * (x - xR) ^ 2 := by
  unfold chordW; ring

lemma chordK_eq (a b x xR : ℚ) :
    chordK a b x xR * (x - xR) ^ 2
      = chordW a b x xR ^ 2
        - 2 ^ 2 * (x * (x - a) * (x - b)) * (xR * (xR - a) * (xR - b)) := by
  unfold chordK chordW; ring

/-- **THE CHORD ROOT SATISFIES THE QUADRATIC**, on every full-2-torsion curve.  The
whole content is that `P − W = 2·y·y_R` once both points are on the curve, so the
expression collapses to `(2·y·y_R)² − 2²·f(x)·f(x_R) = 0`. -/
theorem theChordRootSatisfiesTheQuadratic {a b x y xR yR : ℚ}
    (hcx : y ^ 2 = x * (x - a) * (x - b))
    (hcr : yR ^ 2 = xR * (xR - a) * (xR - b)) (hne : x ≠ xR) :
    (x - xR) ^ 2 * (((y + yR) / (x - xR)) ^ 2 + (a + b) - x - xR) ^ 2
      - 2 * chordW a b x xR * (((y + yR) / (x - xR)) ^ 2 + (a + b) - x - xR)
      + chordK a b x xR = 0 := by
  have hD : x - xR ≠ 0 := sub_ne_zero.mpr hne
  set z : ℚ := ((y + yR) / (x - xR)) ^ 2 + (a + b) - x - xR with hz
  have hzD : z * (x - xR) ^ 2
      = (y + yR) ^ 2 + ((a + b) - x - xR) * (x - xR) ^ 2 := by
    have h1 : ((y + yR) / (x - xR)) ^ 2 * (x - xR) ^ 2 = (y + yR) ^ 2 := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 hD)]
    calc z * (x - xR) ^ 2
        = ((y + yR) / (x - xR)) ^ 2 * (x - xR) ^ 2
          + ((a + b) - x - xR) * (x - xR) ^ 2 := by rw [hz]; ring
      _ = (y + yR) ^ 2 + ((a + b) - x - xR) * (x - xR) ^ 2 := by rw [h1]
  have hmain : (((x - xR) ^ 2 * z ^ 2 - 2 * chordW a b x xR * z + chordK a b x xR)
      * (x - xR) ^ 2) = 0 := by
    have hexp : ((x - xR) ^ 2 * z ^ 2 - 2 * chordW a b x xR * z + chordK a b x xR)
        * (x - xR) ^ 2
        = (z * (x - xR) ^ 2) ^ 2 - 2 * chordW a b x xR * (z * (x - xR) ^ 2)
          + chordK a b x xR * (x - xR) ^ 2 := by ring
    rw [hexp, hzD]
    unfold chordW chordK
    linear_combination
      ((y ^ 2 - x * (x - a) * (x - b))
        - 2 * (yR ^ 2 - xR * (xR - a) * (xR - b))
        + 2 ^ 2 * y * yR + 2 ^ 2 * yR ^ 2) * hcx
      + ((yR ^ 2 - xR * (xR - a) * (xR - b)) + 2 ^ 2 * y * yR + 2 ^ 2 * y ^ 2) * hcr
  rcases mul_eq_zero.mp hmain with h | h
  · exact h
  · exact absurd h (pow_ne_zero 2 hD)

end Soma.Holonics.Millennium.GeneralHeight
