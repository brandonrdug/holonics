import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# FiveHeight: the naive height and the duplication growth law

**The measuring instrument of the descent at five.**  The naive height of a rational
is the larger of its reduced numerator and denominator; the duplication map of
`y² = x³ − 25x`,

```text
x ↦ (x² + 25)² / (4x(x² − 25)),
```

grows the height by a fourth power up to the certified cancellation bound:

* **`theDuplicationGrowsTheHeight`** — `hgt(u)⁴ ≤ 250000·hgt(x(2Q))`.  The
  numerator `A = (p² + 25q²)²` dominates `max(|p|, q)⁴`; the cancellation
  `gcd(A, B)` is coprime to `q` (because `A ≡ p⁴ mod q`) and divides `250000·q⁷`
  through the Bézout certificate
  `(400q² − 12p²)·qA + (125pq² + 3p³)·B = 250000·q⁷`,
  so it divides `250000` outright.

This is the contraction that powers the finite-generation descent: a half-point's
height is at most the fourth root of a bounded multiple of the point's height.
Every `theorem` is discharged and none depends on `sorryAx`.
-/

namespace Soma.Holonics.Millennium.FiveHeight

/-- The naive height of a rational: the larger of the reduced numerator and
denominator. -/
def hgt (x : ℚ) : ℕ := max x.num.natAbs x.den

lemma hgt_pos (x : ℚ) : 0 < hgt x := lt_of_lt_of_le x.den_pos (le_max_right _ _)

lemma num_natAbs_le_hgt (x : ℚ) : x.num.natAbs ≤ hgt x := le_max_left _ _

lemma den_le_hgt (x : ℚ) : x.den ≤ hgt x := le_max_right _ _

/-- **The duplication growth law**: the height of the doubled abscissa dominates the
fourth power of the height, up to the certified constant. -/
theorem theDuplicationGrowsTheHeight (u : ℚ) (hu : u ≠ 0) (hu2 : u ^ 2 ≠ 25) :
    hgt u ^ 4 ≤ 250000 * hgt ((u ^ 2 + 25) ^ 2 / (4 * u * (u ^ 2 - 25))) := by
  set p : ℤ := u.num with hp_def
  set q : ℤ := (u.den : ℤ) with hq_def
  have hq0 : 0 < q := by
    rw [hq_def]
    exact_mod_cast u.den_pos
  have hp0 : p ≠ 0 := Rat.num_ne_zero.mpr hu
  have hcop : Nat.Coprime p.natAbs q.natAbs := by
    rw [hq_def]
    simpa using u.reduced
  -- the integer forms of the duplication
  set A : ℤ := (p ^ 2 + 25 * q ^ 2) ^ 2 with hA_def
  set B : ℤ := 4 * p * q * (p ^ 2 - 25 * q ^ 2) with hB_def
  have hu_eq : u = (p : ℚ) / (q : ℚ) := by
    rw [hp_def, hq_def]
    exact_mod_cast (Rat.num_div_den u).symm
  have hq0' : (q : ℚ) ≠ 0 := by
    exact_mod_cast hq0.ne'
  have hp0' : (p : ℚ) ≠ 0 := by exact_mod_cast hp0
  have hpq25 : p ^ 2 - 25 * q ^ 2 ≠ 0 := by
    intro hc
    apply hu2
    rw [hu_eq, div_pow]
    have hpq : (p : ℚ) ^ 2 = 25 * (q : ℚ) ^ 2 := by
      have h1 : (p ^ 2 : ℤ) = 25 * q ^ 2 := by linarith
      exact_mod_cast h1
    rw [hpq]
    field_simp
  have hB0 : B ≠ 0 := by
    rw [hB_def]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hp0) hq0.ne') hpq25
  have hA0 : A ≠ 0 := by
    rw [hA_def]
    apply pow_ne_zero
    intro hc
    have h1 : (0 : ℤ) < p ^ 2 + 25 * q ^ 2 := by positivity
    omega
  -- the doubled abscissa as the integer fraction
  have hu25 : u ^ 2 - 25 ≠ 0 := fun hc => hu2 (by linarith [hc])
  have hd1 : 4 * u * (u ^ 2 - 25) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hu) hu25
  have hd2 : (B : ℚ) ≠ 0 := by exact_mod_cast hB0
  have key : ((u ^ 2 + 25) ^ 2) * (B : ℚ) = (A : ℚ) * (4 * u * (u ^ 2 - 25)) := by
    rw [hu_eq, hA_def, hB_def]
    push_cast
    field_simp
  have hx2 : (u ^ 2 + 25) ^ 2 / (4 * u * (u ^ 2 - 25)) = (A : ℚ) / (B : ℚ) := by
    rw [div_eq_div_iff hd1 hd2]
    exact key
  set x₂ : ℚ := (u ^ 2 + 25) ^ 2 / (4 * u * (u ^ 2 - 25)) with hx2_def
  -- the cancellation
  set d : ℕ := Int.gcd A B with hd_def
  have hd0 : 0 < d := Int.gcd_pos_of_ne_zero_left B hA0
  have hdA : (d : ℤ) ∣ A := Int.gcd_dvd_left A B
  have hdB : (d : ℤ) ∣ B := Int.gcd_dvd_right A B
  -- the certificate: `gcd(A, B)` divides `250000·q⁷`
  have hcert : (400 * q ^ 2 - 12 * p ^ 2) * q * A + (125 * p * q ^ 2 + 3 * p ^ 3) * B
      = 250000 * q ^ 7 := by
    rw [hA_def, hB_def]
    ring
  have hdvd_q7 : (d : ℤ) ∣ 250000 * q ^ 7 := by
    rw [← hcert]
    exact dvd_add (Dvd.dvd.mul_left hdA _) (Dvd.dvd.mul_left hdB _)
  -- the cancellation is coprime to `q`
  have hAq : IsCoprime A q := by
    have hpq : IsCoprime p q := Int.isCoprime_iff_gcd_eq_one.mpr hcop
    have hp4q : IsCoprime (p ^ 4) q := hpq.pow_left
    have hshape : A = p ^ 4 + q * (50 * p ^ 2 * q + 625 * q ^ 3) := by
      rw [hA_def]
      ring
    rw [hshape]
    exact (IsCoprime.add_mul_left_left hp4q _)
  have hdq : IsCoprime (d : ℤ) q := hAq.of_isCoprime_of_dvd_left hdA
  have hdvd : (d : ℤ) ∣ 250000 := by
    have h7 : IsCoprime (d : ℤ) (q ^ 7) := hdq.pow_right
    exact h7.dvd_of_dvd_mul_right hdvd_q7
  have hd_le : d ≤ 250000 := by
    have := Int.le_of_dvd (by norm_num) hdvd
    exact_mod_cast this
  -- the reduced numerator carries `A/d`
  set A₁ : ℤ := A / (d : ℤ) with hA1_def
  set B₁ : ℤ := B / (d : ℤ) with hB1_def
  have hd0' : (d : ℤ) ≠ 0 := by exact_mod_cast hd0.ne'
  have hA_split : A = (d : ℤ) * A₁ := (Int.ediv_mul_cancel hdA).symm.trans (mul_comm _ _)
  have hB_split : B = (d : ℤ) * B₁ := (Int.ediv_mul_cancel hdB).symm.trans (mul_comm _ _)
  have hB10 : B₁ ≠ 0 := by
    intro hc
    apply hB0
    rw [hB_split, hc, mul_zero]
  have hcop1 : Nat.Coprime A₁.natAbs B₁.natAbs := by
    rw [hA1_def, hB1_def, hd_def]
    exact Int.gcd_div_gcd_div_gcd (Int.gcd_pos_of_ne_zero_left B hA0)
  have hx2' : x₂ = (A₁ : ℚ) / (B₁ : ℚ) := by
    rw [hx2, hA_split, hB_split]
    push_cast
    rw [mul_div_mul_left _ _ (show ((d : ℕ) : ℚ) ≠ 0 from by exact_mod_cast hd0.ne')]
  have hnum : x₂.num.natAbs = A₁.natAbs := by
    rcases lt_trichotomy B₁ 0 with hB1s | hB1s | hB1s
    · have hx2'' : x₂ = ((-A₁ : ℤ) : ℚ) / ((-B₁ : ℤ) : ℚ) := by
        rw [hx2']
        push_cast
        rw [div_neg, neg_div, neg_neg]
      have hcop' : Nat.Coprime (-A₁).natAbs (-B₁).natAbs := by
        rwa [Int.natAbs_neg, Int.natAbs_neg]
      have := Rat.num_div_eq_of_coprime (by omega : (0 : ℤ) < -B₁) hcop'
      rw [← hx2''] at this
      rw [this, Int.natAbs_neg]
    · exact absurd hB1s hB10
    · have := Rat.num_div_eq_of_coprime hB1s hcop1
      rw [← hx2'] at this
      rw [this]
  -- the numerator dominates the fourth power of the height
  have hA_ge : hgt u ^ 4 ≤ A.natAbs := by
    have hA_nonneg : 0 ≤ A := by rw [hA_def]; positivity
    have hA_natAbs : (A.natAbs : ℤ) = A := Int.natAbs_of_nonneg hA_nonneg
    have hcase : (hgt u : ℤ) ^ 4 ≤ A := by
      rw [hA_def]
      have hple : (p.natAbs : ℤ) ^ 4 ≤ (p ^ 2 + 25 * q ^ 2) ^ 2 := by
        have h1 : (p.natAbs : ℤ) ^ 2 = p ^ 2 := by
          rw [← sq_abs p, Int.abs_eq_natAbs]
        nlinarith [sq_nonneg q, sq_nonneg p, sq_nonneg (p ^ 2 + 25 * q ^ 2)]
      have hqle : q ^ 4 ≤ (p ^ 2 + 25 * q ^ 2) ^ 2 := by
        nlinarith [sq_nonneg p, sq_nonneg q, sq_nonneg (p ^ 2 + 25 * q ^ 2),
          sq_nonneg (p ^ 2 + 24 * q ^ 2)]
      rcases max_cases p.natAbs u.den with ⟨hmax, _⟩ | ⟨hmax, _⟩
      · rw [hgt, hp_def] at *
        rw [hmax]
        exact hple
      · rw [hgt, hp_def] at *
        rw [hmax]
        rw [hq_def] at hqle
        exact_mod_cast hqle
    calc hgt u ^ 4 = ((hgt u : ℤ) ^ 4).toNat := by
          rw [show ((hgt u : ℤ) ^ 4) = ((hgt u ^ 4 : ℕ) : ℤ) from by push_cast; ring]
          exact (Int.toNat_natCast _).symm
      _ ≤ A.toNat := by
          apply Int.toNat_le_toNat hcase
      _ = A.natAbs := by omega
  -- assemble
  have hA1_val : A₁.natAbs * d = A.natAbs := by
    have : A.natAbs = ((d : ℤ) * A₁).natAbs := by rw [← hA_split]
    rw [this, Int.natAbs_mul, Int.natAbs_natCast]
    ring
  calc hgt u ^ 4 ≤ A.natAbs := hA_ge
    _ = A₁.natAbs * d := hA1_val.symm
    _ ≤ A₁.natAbs * 250000 := Nat.mul_le_mul_left _ hd_le
    _ = 250000 * x₂.num.natAbs := by rw [hnum]; ring
    _ ≤ 250000 * hgt x₂ := Nat.mul_le_mul_left _ (num_natAbs_le_hgt x₂)

end Soma.Holonics.Millennium.FiveHeight
