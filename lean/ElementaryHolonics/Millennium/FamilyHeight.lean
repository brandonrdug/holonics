import ElementaryHolonics.Millennium.FiveTranslation
import Mathlib.Tactic

/-!
# FamilyHeight: the contraction laws at every modulus

**The family descent's measuring laws.**  The two growth laws that powered the
Mordell–Weil descent at five were never about five: on every congruent-number curve
`y² = x³ − n²x`,

* **`theDuplicationGrowsTheHeightAtEveryModulus`** — duplication grows the height
  quartically up to the certified cancellation `16n⁶`, through the family Bézout
  certificate

  ```text
  (16n²q² − 12p²)·qA + (5n²pq² + 3p³)·B = 16n⁶·q⁷,
  ```

  so the cancellation divides `16n⁶` — only the bad primes, at every modulus;
* **`theChordRootIsBoundedAtEveryModulus`** — translation by a fixed representative
  `x_R = α/β` grows the height only quadratically, `hgt z ≤ 2L²·hgt(x)²` with
  `L = |α| + n²β`, through the family chord certificate.

Quartic against quadratic with certified constants polynomial in the modulus: the
descent contraction is a family law, and the threshold it closes at is computable
per twist.  Every `theorem` is discharged and none depends on `sorryAx`.
-/

namespace Soma.Holonics.Millennium.FamilyHeight

open Soma.Holonics.Millennium.FiveHeight

set_option maxHeartbeats 1000000 in
/-- **THE DUPLICATION GROWS THE HEIGHT AT EVERY MODULUS**: on `y² = x³ − n²x` the
doubled abscissa dominates the fourth power of the height up to `16n⁶` — the family
Bézout certificate bounds the cancellation by the bad primes alone. -/
theorem theDuplicationGrowsTheHeightAtEveryModulus (n : ℕ) (hn : 0 < n) (u : ℚ)
    (hu : u ≠ 0) (hu2 : u ^ 2 ≠ (n : ℚ) ^ 2) :
    hgt u ^ 4 ≤ 16 * n ^ 6 *
      hgt ((u ^ 2 + (n : ℚ) ^ 2) ^ 2 / (4 * u * (u ^ 2 - (n : ℚ) ^ 2))) := by
  set m : ℤ := (n : ℤ) with hm_def
  have hm1 : (1 : ℤ) ≤ m := by rw [hm_def]; omega
  set p : ℤ := u.num with hp_def
  set q : ℤ := (u.den : ℤ) with hq_def
  have hq0 : 0 < q := by
    rw [hq_def]
    exact_mod_cast u.den_pos
  have hp0 : p ≠ 0 := Rat.num_ne_zero.mpr hu
  have hcop : Nat.Coprime p.natAbs q.natAbs := by
    rw [hq_def]
    simpa using u.reduced
  set A : ℤ := (p ^ 2 + m ^ 2 * q ^ 2) ^ 2 with hA_def
  set B : ℤ := 4 * p * q * (p ^ 2 - m ^ 2 * q ^ 2) with hB_def
  have hu_eq : u = (p : ℚ) / (q : ℚ) := by
    rw [hp_def, hq_def]
    exact_mod_cast (Rat.num_div_den u).symm
  have hq0' : (q : ℚ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hp0' : (p : ℚ) ≠ 0 := by exact_mod_cast hp0
  have hmq : ((m : ℚ)) = (n : ℚ) := by rw [hm_def]; push_cast; rfl
  have hpq : p ^ 2 - m ^ 2 * q ^ 2 ≠ 0 := by
    intro hc
    apply hu2
    rw [hu_eq, div_pow, ← hmq]
    have hpq2 : (p : ℚ) ^ 2 = (m : ℚ) ^ 2 * (q : ℚ) ^ 2 := by
      have h1 : (p ^ 2 : ℤ) = m ^ 2 * q ^ 2 := by linarith
      exact_mod_cast h1
    rw [hpq2]
    field_simp
  have hB0 : B ≠ 0 := by
    rw [hB_def]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hp0) hq0.ne') hpq
  have hA0 : A ≠ 0 := by
    rw [hA_def]
    apply pow_ne_zero
    intro hc
    have h1 : (0 : ℤ) < p ^ 2 + m ^ 2 * q ^ 2 := by positivity
    omega
  -- the doubled abscissa as the integer fraction
  have hu25 : u ^ 2 - (n : ℚ) ^ 2 ≠ 0 := fun hc => hu2 (by linarith [hc])
  have hd1 : 4 * u * (u ^ 2 - (n : ℚ) ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hu) hu25
  have hd2 : (B : ℚ) ≠ 0 := by exact_mod_cast hB0
  have key : ((u ^ 2 + (n : ℚ) ^ 2) ^ 2) * (B : ℚ)
      = (A : ℚ) * (4 * u * (u ^ 2 - (n : ℚ) ^ 2)) := by
    rw [hu_eq, hA_def, hB_def, ← hmq]
    push_cast
    field_simp
  have hx2 : (u ^ 2 + (n : ℚ) ^ 2) ^ 2 / (4 * u * (u ^ 2 - (n : ℚ) ^ 2))
      = (A : ℚ) / (B : ℚ) := by
    rw [div_eq_div_iff hd1 hd2]
    exact key
  set x₂ : ℚ := (u ^ 2 + (n : ℚ) ^ 2) ^ 2 / (4 * u * (u ^ 2 - (n : ℚ) ^ 2)) with hx2_def
  -- the cancellation
  set d : ℕ := Int.gcd A B with hd_def
  have hd0 : 0 < d := Int.gcd_pos_of_ne_zero_left B hA0
  have hdA : (d : ℤ) ∣ A := Int.gcd_dvd_left A B
  have hdB : (d : ℤ) ∣ B := Int.gcd_dvd_right A B
  -- the family certificate: the cancellation divides `16n⁶·q⁷`
  have hcert : (16 * m ^ 2 * q ^ 2 - 12 * p ^ 2) * q * A
      + (5 * m ^ 2 * p * q ^ 2 + 3 * p ^ 3) * B = 16 * m ^ 6 * q ^ 7 := by
    rw [hA_def, hB_def]
    ring
  have hdvd_q7 : (d : ℤ) ∣ 16 * m ^ 6 * q ^ 7 := by
    rw [← hcert]
    exact dvd_add (Dvd.dvd.mul_left hdA _) (Dvd.dvd.mul_left hdB _)
  -- the cancellation is coprime to `q`
  have hAq : IsCoprime A q := by
    have hpq' : IsCoprime p q := Int.isCoprime_iff_gcd_eq_one.mpr hcop
    have hp4q : IsCoprime (p ^ 4) q := hpq'.pow_left
    have hshape : A = p ^ 4 + q * (2 * m ^ 2 * p ^ 2 * q + m ^ 4 * q ^ 3) := by
      rw [hA_def]
      ring
    rw [hshape]
    exact IsCoprime.add_mul_left_left hp4q _
  have hdq : IsCoprime (d : ℤ) q := hAq.of_isCoprime_of_dvd_left hdA
  have hdvd : (d : ℤ) ∣ 16 * m ^ 6 := by
    have h7 : IsCoprime (d : ℤ) (q ^ 7) := hdq.pow_right
    exact h7.dvd_of_dvd_mul_right hdvd_q7
  have hd_le : d ≤ 16 * n ^ 6 := by
    have h1 : (d : ℤ) ≤ 16 * m ^ 6 := Int.le_of_dvd (by positivity) hdvd
    have h2 : ((16 * n ^ 6 : ℕ) : ℤ) = 16 * m ^ 6 := by
      rw [hm_def]
      push_cast
      ring
    omega
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
    have hcase : (hgt u : ℤ) ^ 4 ≤ A := by
      rw [hA_def]
      have hw : (0 : ℤ) ≤ m ^ 2 * q ^ 2 := by positivity
      have hple : (p.natAbs : ℤ) ^ 4 ≤ (p ^ 2 + m ^ 2 * q ^ 2) ^ 2 := by
        have h1 : (p.natAbs : ℤ) ^ 2 = p ^ 2 := by
          rw [← sq_abs p, Int.abs_eq_natAbs]
        nlinarith [sq_nonneg p, hw]
      have hqle : q ^ 4 ≤ (p ^ 2 + m ^ 2 * q ^ 2) ^ 2 := by
        have hm4 : (1 : ℤ) ≤ m ^ 4 := by nlinarith [hm1]
        have h1 : q ^ 4 ≤ m ^ 4 * q ^ 4 :=
          le_mul_of_one_le_left (by positivity) hm4
        nlinarith [sq_nonneg p, hw, h1]
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
    have h1 : A.natAbs = ((d : ℤ) * A₁).natAbs := by rw [← hA_split]
    rw [h1, Int.natAbs_mul, Int.natAbs_natCast]
    ring
  calc hgt u ^ 4 ≤ A.natAbs := hA_ge
    _ = A₁.natAbs * d := hA1_val.symm
    _ ≤ A₁.natAbs * (16 * n ^ 6) := Nat.mul_le_mul_left _ hd_le
    _ = 16 * n ^ 6 * x₂.num.natAbs := by rw [hnum]; ring
    _ ≤ 16 * n ^ 6 * hgt x₂ := Nat.mul_le_mul_left _ (num_natAbs_le_hgt x₂)

set_option maxHeartbeats 1000000 in
/-- **THE CHORD ROOT IS BOUNDED AT EVERY MODULUS**: on `y² = x³ − n²x`, translating
by the representative `x_R = α/β` moves the abscissa to a rational of height at most
`2L²·hgt(x)²` with `L = |α| + n²β` — quadratic growth, at every modulus, through the
family chord certificate. -/
theorem theChordRootIsBoundedAtEveryModulus (n : ℕ) (hn : 0 < n)
    (x y x_R y_R : ℚ) (α β : ℤ)
    (hβ : 0 < β) (hxR : x_R = (α : ℚ) / (β : ℚ))
    (hcx : y ^ 2 = x ^ 3 - (n : ℚ) ^ 2 * x)
    (hcr : y_R ^ 2 = x_R ^ 3 - (n : ℚ) ^ 2 * x_R)
    (hne : x ≠ x_R) :
    hgt (((y + y_R) / (x - x_R)) ^ 2 - x - x_R)
      ≤ 2 * (α.natAbs + n ^ 2 * β.natAbs) ^ 2 * hgt x ^ 2 := by
  set m : ℤ := (n : ℤ) with hm_def
  have hmq : ((m : ℚ)) = (n : ℚ) := by rw [hm_def]; push_cast; rfl
  set z : ℚ := ((y + y_R) / (x - x_R)) ^ 2 - x - x_R with hz_def
  set a : ℤ := x.num with ha_def
  set b : ℤ := (x.den : ℤ) with hb_def
  have hb0 : 0 < b := by rw [hb_def]; exact_mod_cast x.den_pos
  have hx_eq : x = (a : ℚ) / (b : ℚ) := by
    rw [ha_def, hb_def]
    exact_mod_cast (Rat.num_div_den x).symm
  have hb0' : (b : ℚ) ≠ 0 := by exact_mod_cast hb0.ne'
  have hβ0' : (β : ℚ) ≠ 0 := by exact_mod_cast hβ.ne'
  have hDne : x - x_R ≠ 0 := sub_ne_zero.mpr hne
  -- the ℚ-level quadratic through the family certificate
  have hqQ : (x - x_R) ^ 2 * z ^ 2
      - (2 * (x + x_R) * (x * x_R - (n : ℚ) ^ 2)) * z
      + (x * x_R + (n : ℚ) ^ 2) ^ 2 = 0 := by
    have hNz : z * (x - x_R) ^ 2 = (y + y_R) ^ 2 - (x + x_R) * (x - x_R) ^ 2 := by
      have h1 : ((y + y_R) / (x - x_R)) ^ 2 = (y + y_R) ^ 2 / (x - x_R) ^ 2 :=
        div_pow _ _ 2
      rw [hz_def, h1, sub_mul, sub_mul,
        div_mul_cancel₀ _ (pow_ne_zero 2 hDne)]
      ring
    have hcert : ((y + y_R) ^ 2 - (x + x_R) * (x - x_R) ^ 2) ^ 2
        - (2 * (x + x_R) * (x * x_R - (n : ℚ) ^ 2)) *
            ((y + y_R) ^ 2 - (x + x_R) * (x - x_R) ^ 2)
        + (x * x_R + (n : ℚ) ^ 2) ^ 2 * (x - x_R) ^ 2 = 0 := by
      linear_combination
        (6 * y_R ^ 2 + 2 * (n : ℚ) ^ 2 * x_R - 2 * x_R ^ 3 + 4 * y * y_R + y ^ 2
          + (n : ℚ) ^ 2 * x - x ^ 3) * hcx
        + (y_R ^ 2 + (n : ℚ) ^ 2 * x_R - x_R ^ 3 + 4 * y * y_R
          - 4 * (n : ℚ) ^ 2 * x + 4 * x ^ 3) * hcr
    have h0 : ((x - x_R) ^ 2 * z ^ 2
        - (2 * (x + x_R) * (x * x_R - (n : ℚ) ^ 2)) * z
        + (x * x_R + (n : ℚ) ^ 2) ^ 2) * (x - x_R) ^ 2 = 0 := by
      have hexpand : ((x - x_R) ^ 2 * z ^ 2
          - (2 * (x + x_R) * (x * x_R - (n : ℚ) ^ 2)) * z
          + (x * x_R + (n : ℚ) ^ 2) ^ 2) * (x - x_R) ^ 2
          = (z * (x - x_R) ^ 2) ^ 2
            - (2 * (x + x_R) * (x * x_R - (n : ℚ) ^ 2)) * (z * (x - x_R) ^ 2)
            + (x * x_R + (n : ℚ) ^ 2) ^ 2 * (x - x_R) ^ 2 := by
        ring
      rw [hexpand, hNz]
      exact hcert
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact h1
    · exact absurd h1 (pow_ne_zero 2 hDne)
  -- the integer-cleared quadratic
  set M : ℤ := (a * β - α * b) ^ 2 with hM_def
  set S₁ : ℤ := 2 * (a * β + α * b) * (a * α - m ^ 2 * b * β) with hS₁_def
  set S₂ : ℤ := (a * α + m ^ 2 * b * β) ^ 2 with hS₂_def
  have hM0 : M ≠ 0 := by
    rw [hM_def]
    apply pow_ne_zero
    intro hc
    apply hne
    rw [hx_eq, hxR, div_eq_div_iff hb0' hβ0']
    have h1 : a * β = α * b := by linarith
    exact_mod_cast h1
  have hqZ : (M : ℚ) * z ^ 2 - (S₁ : ℚ) * z + (S₂ : ℚ) = 0 := by
    have hscale : (M : ℚ) * z ^ 2 - (S₁ : ℚ) * z + (S₂ : ℚ)
        = ((x - x_R) ^ 2 * z ^ 2
            - (2 * (x + x_R) * (x * x_R - (n : ℚ) ^ 2)) * z
            + (x * x_R + (n : ℚ) ^ 2) ^ 2) * ((b : ℚ) * (β : ℚ)) ^ 2 := by
      rw [hM_def, hS₁_def, hS₂_def, hx_eq, hxR, ← hmq]
      push_cast
      field_simp
    rw [hscale, hqQ, zero_mul]
  -- the root bound, then the arithmetic
  have hroot := FiveTranslation.root_bound hM0 hqZ
  set H : ℕ := hgt x with hH_def
  set L : ℕ := α.natAbs + n ^ 2 * β.natAbs with hL_def
  have hm_abs : m.natAbs = n := by rw [hm_def, Int.natAbs_natCast]
  have hm2_abs : (m ^ 2).natAbs = n ^ 2 := by rw [Int.natAbs_pow, hm_abs]
  have ha_le : a.natAbs ≤ H := by rw [ha_def, hH_def]; exact num_natAbs_le_hgt x
  have hb_le : b.natAbs ≤ H := by
    rw [hb_def, hH_def]
    simpa using den_le_hgt x
  have hsum1 : (a * β + α * b).natAbs ≤ L * H := by
    have h1 : (a * β + α * b).natAbs ≤ a.natAbs * β.natAbs + α.natAbs * b.natAbs := by
      calc (a * β + α * b).natAbs
          ≤ (a * β).natAbs + (α * b).natAbs := Int.natAbs_add_le _ _
        _ = a.natAbs * β.natAbs + α.natAbs * b.natAbs := by
            rw [Int.natAbs_mul, Int.natAbs_mul]
    have h2 : a.natAbs * β.natAbs + α.natAbs * b.natAbs ≤ L * H := by
      rw [hL_def]
      have e1 : a.natAbs * β.natAbs ≤ H * β.natAbs :=
        Nat.mul_le_mul ha_le (le_refl β.natAbs)
      have e2 : α.natAbs * b.natAbs ≤ α.natAbs * H :=
        Nat.mul_le_mul (le_refl α.natAbs) hb_le
      have e3 : H * β.natAbs ≤ n ^ 2 * β.natAbs * H := by
        calc H * β.natAbs = β.natAbs * H := Nat.mul_comm _ _
          _ ≤ n ^ 2 * β.natAbs * H :=
              Nat.mul_le_mul
                (Nat.le_mul_of_pos_left β.natAbs (by positivity)) (le_refl H)
      calc a.natAbs * β.natAbs + α.natAbs * b.natAbs
          ≤ H * β.natAbs + α.natAbs * H := Nat.add_le_add e1 e2
        _ ≤ n ^ 2 * β.natAbs * H + α.natAbs * H := Nat.add_le_add_right e3 _
        _ = (α.natAbs + n ^ 2 * β.natAbs) * H := by ring
    exact le_trans h1 h2
  have hdiff1 : (a * β - α * b).natAbs ≤ L * H := by
    have h1 : (a * β - α * b).natAbs ≤ a.natAbs * β.natAbs + α.natAbs * b.natAbs := by
      calc (a * β - α * b).natAbs
          ≤ (a * β).natAbs + (α * b).natAbs := Int.natAbs_sub_le _ _
        _ = a.natAbs * β.natAbs + α.natAbs * b.natAbs := by
            rw [Int.natAbs_mul, Int.natAbs_mul]
    have h2 : a.natAbs * β.natAbs + α.natAbs * b.natAbs ≤ L * H := by
      rw [hL_def]
      have e1 : a.natAbs * β.natAbs ≤ H * β.natAbs :=
        Nat.mul_le_mul ha_le (le_refl β.natAbs)
      have e2 : α.natAbs * b.natAbs ≤ α.natAbs * H :=
        Nat.mul_le_mul (le_refl α.natAbs) hb_le
      have e3 : H * β.natAbs ≤ n ^ 2 * β.natAbs * H := by
        calc H * β.natAbs = β.natAbs * H := Nat.mul_comm _ _
          _ ≤ n ^ 2 * β.natAbs * H :=
              Nat.mul_le_mul
                (Nat.le_mul_of_pos_left β.natAbs (by positivity)) (le_refl H)
      calc a.natAbs * β.natAbs + α.natAbs * b.natAbs
          ≤ H * β.natAbs + α.natAbs * H := Nat.add_le_add e1 e2
        _ ≤ n ^ 2 * β.natAbs * H + α.natAbs * H := Nat.add_le_add_right e3 _
        _ = (α.natAbs + n ^ 2 * β.natAbs) * H := by ring
    exact le_trans h1 h2
  have hmixgen : ∀ w : ℤ, w = a * α + m ^ 2 * b * β ∨ w = a * α - m ^ 2 * b * β →
      w.natAbs ≤ H * L := by
    intro w hw
    have h1 : w.natAbs ≤ a.natAbs * α.natAbs + n ^ 2 * b.natAbs * β.natAbs := by
      have hmm : (m ^ 2 * b * β).natAbs = n ^ 2 * b.natAbs * β.natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_mul, hm2_abs]
      rcases hw with rfl | rfl
      · calc (a * α + m ^ 2 * b * β).natAbs
            ≤ (a * α).natAbs + (m ^ 2 * b * β).natAbs := Int.natAbs_add_le _ _
          _ = a.natAbs * α.natAbs + n ^ 2 * b.natAbs * β.natAbs := by
              rw [Int.natAbs_mul, hmm]
      · calc (a * α - m ^ 2 * b * β).natAbs
            ≤ (a * α).natAbs + (m ^ 2 * b * β).natAbs := Int.natAbs_sub_le _ _
          _ = a.natAbs * α.natAbs + n ^ 2 * b.natAbs * β.natAbs := by
              rw [Int.natAbs_mul, hmm]
    have h2 : a.natAbs * α.natAbs + n ^ 2 * b.natAbs * β.natAbs ≤ H * L := by
      rw [hL_def]
      have e4 : a.natAbs * α.natAbs ≤ H * α.natAbs :=
        Nat.mul_le_mul ha_le (le_refl α.natAbs)
      have e5 : n ^ 2 * b.natAbs * β.natAbs ≤ n ^ 2 * H * β.natAbs :=
        Nat.mul_le_mul (Nat.mul_le_mul (le_refl (n ^ 2)) hb_le) (le_refl β.natAbs)
      calc a.natAbs * α.natAbs + n ^ 2 * b.natAbs * β.natAbs
          ≤ H * α.natAbs + n ^ 2 * H * β.natAbs := Nat.add_le_add e4 e5
        _ = H * (α.natAbs + n ^ 2 * β.natAbs) := by ring
    exact le_trans h1 h2
  have hM_le : M.natAbs ≤ L ^ 2 * H ^ 2 := by
    calc M.natAbs = (a * β - α * b).natAbs ^ 2 := by
          rw [hM_def, Int.natAbs_pow]
      _ ≤ (L * H) ^ 2 := Nat.pow_le_pow_left hdiff1 2
      _ = L ^ 2 * H ^ 2 := by ring
  have hS₂_le : S₂.natAbs ≤ L ^ 2 * H ^ 2 := by
    calc S₂.natAbs = (a * α + m ^ 2 * b * β).natAbs ^ 2 := by
          rw [hS₂_def, Int.natAbs_pow]
      _ ≤ (H * L) ^ 2 := Nat.pow_le_pow_left (hmixgen _ (Or.inl rfl)) 2
      _ = L ^ 2 * H ^ 2 := by ring
  have hS₁_le : S₁.natAbs ≤ 2 * (L ^ 2 * H ^ 2) := by
    calc S₁.natAbs
        = 2 * (a * β + α * b).natAbs * (a * α - m ^ 2 * b * β).natAbs := by
          rw [hS₁_def]
          simp [Int.natAbs_mul]
      _ ≤ 2 * (L * H) * (H * L) :=
          Nat.mul_le_mul (Nat.mul_le_mul (le_refl 2) hsum1) (hmixgen _ (Or.inr rfl))
      _ = 2 * (L ^ 2 * H ^ 2) := by ring
  have hmax : max (max S₁.natAbs S₂.natAbs) M.natAbs ≤ 2 * (L ^ 2 * H ^ 2) := by
    have h1 : L ^ 2 * H ^ 2 ≤ 2 * (L ^ 2 * H ^ 2) := by omega
    exact max_le (max_le hS₁_le (le_trans hS₂_le h1)) (le_trans hM_le h1)
  calc hgt z ≤ max (max S₁.natAbs S₂.natAbs) M.natAbs := hroot
    _ ≤ 2 * (L ^ 2 * H ^ 2) := hmax
    _ = 2 * L ^ 2 * H ^ 2 := by ring

end Soma.Holonics.Millennium.FamilyHeight
