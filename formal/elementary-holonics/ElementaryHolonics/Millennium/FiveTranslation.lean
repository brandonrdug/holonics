import ElementaryHolonics.Millennium.FiveHeight
import Mathlib.Tactic

/-!
# FiveTranslation: the chord root is height-bounded

**The second measuring law of the descent at five.**  Translating a point by a fixed
representative moves the abscissa to a root of a monic quadratic whose coefficients
are degree-two rational functions of the abscissa alone:

```text
z² − σz + π = 0,   σ = 2(x + x_R)(x·x_R − 25)/(x − x_R)²,   π = (x·x_R + 25)²/(x − x_R)²,
```

and a rational root of an integer quadratic has numerator dividing the constant term
and denominator dividing the leading term.  With the representative `x_R = α/β` this
returns

* **`theChordRootIsBounded`** — `hgt z ≤ 2L²·hgt(x)²` with `L = |α| + 25β`:
  quadratic growth, against the quartic growth of duplication — the gap the descent
  contraction lives in.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

namespace Soma.Holonics.Millennium.FiveTranslation

open Soma.Holonics.Millennium.FiveHeight

/-! ## 1. Height facts for integer fractions -/

lemma hgt_div_le (A B : ℤ) (hB : B ≠ 0) :
    hgt ((A : ℚ) / (B : ℚ)) ≤ max A.natAbs B.natAbs := by
  rw [show (A : ℚ) / (B : ℚ) = Rat.divInt A B from (Rat.divInt_eq_div A B).symm]
  rcases eq_or_ne A 0 with rfl | hA
  · rw [Rat.zero_divInt]
    have hB1 : 1 ≤ B.natAbs := Int.natAbs_pos.mpr hB
    have h0 : hgt 0 = 1 := by unfold hgt; simp
    rw [h0]
    omega
  · have hnum : (Rat.divInt A B).num ∣ A := Rat.num_dvd A hB
    have hden : ((Rat.divInt A B).den : ℤ) ∣ B := Rat.den_dvd A B
    have h1 : (Rat.divInt A B).num.natAbs ≤ A.natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr hA) (Int.natAbs_dvd_natAbs.mpr hnum)
    have h2 : (Rat.divInt A B).den ≤ B.natAbs := by
      have h3 := Int.natAbs_dvd_natAbs.mpr hden
      rw [Int.natAbs_natCast] at h3
      exact Nat.le_of_dvd (Int.natAbs_pos.mpr hB) h3
    unfold hgt
    omega

/-! ## 2. The rational root bound -/

/-- A rational root of an integer quadratic has numerator dividing the constant term
and denominator dividing the leading term. -/
lemma root_bound {M S₁ S₂ : ℤ} {z : ℚ} (hM : M ≠ 0)
    (hquad : (M : ℚ) * z ^ 2 - (S₁ : ℚ) * z + (S₂ : ℚ) = 0) :
    hgt z ≤ max (max S₁.natAbs S₂.natAbs) M.natAbs := by
  set n : ℤ := z.num with hn_def
  set d : ℤ := (z.den : ℤ) with hd_def
  have hd0 : 0 < d := by rw [hd_def]; exact_mod_cast z.den_pos
  have hcop : Nat.Coprime n.natAbs d.natAbs := by
    rw [hd_def]
    simpa using z.reduced
  have hz_eq : z = (n : ℚ) / (d : ℚ) := by
    rw [hn_def, hd_def]
    exact_mod_cast (Rat.num_div_den z).symm
  have hd0' : (d : ℚ) ≠ 0 := by exact_mod_cast hd0.ne'
  have hzd : z * (d : ℚ) = (n : ℚ) := by
    rw [hz_eq]
    field_simp
  -- the cleared integer relation
  have hint : M * n ^ 2 - S₁ * n * d + S₂ * d ^ 2 = 0 := by
    have h1 : ((M * n ^ 2 - S₁ * n * d + S₂ * d ^ 2 : ℤ) : ℚ)
        = ((M : ℚ) * z ^ 2 - (S₁ : ℚ) * z + (S₂ : ℚ)) * (d : ℚ) ^ 2 := by
      push_cast
      rw [← hzd]
      ring
    rw [hquad, zero_mul] at h1
    exact_mod_cast h1
  -- the denominator divides the leading term
  have hden_dvd : d ∣ M := by
    have h1 : d ∣ M * n ^ 2 := by
      have h2 : M * n ^ 2 = S₁ * n * d - S₂ * d ^ 2 := by linarith
      rw [h2]
      exact dvd_sub (Dvd.intro_left _ rfl) ⟨S₂ * d, by ring⟩
    have hcop2 : IsCoprime d (n ^ 2) :=
      (Int.isCoprime_iff_gcd_eq_one.mpr (Nat.Coprime.symm hcop)).pow_right
    exact hcop2.dvd_of_dvd_mul_right h1
  have hden_le : z.den ≤ M.natAbs := by
    have h1 := Int.natAbs_dvd_natAbs.mpr hden_dvd
    rw [hd_def, Int.natAbs_natCast] at h1
    exact Nat.le_of_dvd (Int.natAbs_pos.mpr hM) h1
  -- the numerator divides the constant term, with the degenerate cases split
  have hnum_le : n.natAbs ≤ max S₁.natAbs S₂.natAbs := by
    rcases eq_or_ne n 0 with hn0 | hn0
    · rw [hn0]
      simp
    have h1 : n ∣ S₂ * d ^ 2 := by
      have h2 : S₂ * d ^ 2 = S₁ * n * d - M * n ^ 2 := by linarith
      rw [h2]
      exact dvd_sub ⟨S₁ * d, by ring⟩ ⟨M * n, by ring⟩
    have hcop2 : IsCoprime n (d ^ 2) :=
      (Int.isCoprime_iff_gcd_eq_one.mpr hcop).pow_right
    have hnS₂ : n ∣ S₂ := hcop2.dvd_of_dvd_mul_left (by rwa [mul_comm] at h1)
    rcases eq_or_ne S₂ 0 with rfl | hS₂
    · -- the degenerate constant term: the root is `σ` itself
      have h3 : n * (M * n - S₁ * d) = 0 := by linear_combination hint
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 hn0
      · have h5 : M * n = S₁ * d := by linarith
        have h6 : n ∣ S₁ * d := ⟨M, by linear_combination - h5⟩
        have h7 : IsCoprime n d := Int.isCoprime_iff_gcd_eq_one.mpr hcop
        have h8 : n ∣ S₁ := h7.dvd_of_dvd_mul_right h6
        have hS₁ : S₁ ≠ 0 := by
          intro hc
          rw [hc, zero_mul] at h5
          exact mul_ne_zero hM hn0 h5
        exact le_max_of_le_left
          (Nat.le_of_dvd (Int.natAbs_pos.mpr hS₁) (Int.natAbs_dvd_natAbs.mpr h8))
    · exact le_max_of_le_right
        (Nat.le_of_dvd (Int.natAbs_pos.mpr hS₂) (Int.natAbs_dvd_natAbs.mpr hnS₂))
  unfold hgt
  omega

/-! ## 3. The chord quadratic and the translation bound -/

set_option maxHeartbeats 1000000 in
/-- **The chord root is height-bounded**: translating by the fixed representative
`x_R = α/β` (with ordinate `y_R`) moves the abscissa to a rational of height at most
`2L²·hgt(x)²`, `L = |α| + 25β`. -/
theorem theChordRootIsBounded (x y x_R y_R : ℚ) (α β : ℤ) (hβ : 0 < β)
    (hxR : x_R = (α : ℚ) / (β : ℚ))
    (hcx : y ^ 2 = x ^ 3 - 25 * x) (hcr : y_R ^ 2 = x_R ^ 3 - 25 * x_R)
    (hne : x ≠ x_R) :
    hgt (((y + y_R) / (x - x_R)) ^ 2 - x - x_R)
      ≤ 2 * (α.natAbs + 25 * β.natAbs) ^ 2 * hgt x ^ 2 := by
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
  -- the ℚ-level quadratic through the certificate
  have hqQ : (x - x_R) ^ 2 * z ^ 2 - (2 * (x + x_R) * (x * x_R - 25)) * z
      + (x * x_R + 25) ^ 2 = 0 := by
    have hNz : z * (x - x_R) ^ 2 = (y + y_R) ^ 2 - (x + x_R) * (x - x_R) ^ 2 := by
      have h1 : ((y + y_R) / (x - x_R)) ^ 2 = (y + y_R) ^ 2 / (x - x_R) ^ 2 :=
        div_pow _ _ 2
      rw [hz_def, h1, sub_mul, sub_mul,
        div_mul_cancel₀ _ (pow_ne_zero 2 hDne)]
      ring
    have hcert : ((y + y_R) ^ 2 - (x + x_R) * (x - x_R) ^ 2) ^ 2
        - (2 * (x + x_R) * (x * x_R - 25)) *
            ((y + y_R) ^ 2 - (x + x_R) * (x - x_R) ^ 2)
        + (x * x_R + 25) ^ 2 * (x - x_R) ^ 2 = 0 := by
      linear_combination
        (6 * y_R ^ 2 + 50 * x_R - 2 * x_R ^ 3 + 4 * y * y_R + y ^ 2 + 25 * x - x ^ 3) * hcx
        + (y_R ^ 2 + 25 * x_R - x_R ^ 3 + 4 * y * y_R - 100 * x + 4 * x ^ 3) * hcr
    have h0 : ((x - x_R) ^ 2 * z ^ 2 - (2 * (x + x_R) * (x * x_R - 25)) * z
        + (x * x_R + 25) ^ 2) * (x - x_R) ^ 2 = 0 := by
      have hexpand : ((x - x_R) ^ 2 * z ^ 2 - (2 * (x + x_R) * (x * x_R - 25)) * z
          + (x * x_R + 25) ^ 2) * (x - x_R) ^ 2
          = (z * (x - x_R) ^ 2) ^ 2 - (2 * (x + x_R) * (x * x_R - 25)) *
              (z * (x - x_R) ^ 2) + (x * x_R + 25) ^ 2 * (x - x_R) ^ 2 := by
        ring
      rw [hexpand, hNz]
      exact hcert
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact h1
    · exact absurd h1 (pow_ne_zero 2 hDne)
  -- the integer-cleared quadratic
  set M : ℤ := (a * β - α * b) ^ 2 with hM_def
  set S₁ : ℤ := 2 * (a * β + α * b) * (a * α - 25 * b * β) with hS₁_def
  set S₂ : ℤ := (a * α + 25 * b * β) ^ 2 with hS₂_def
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
        = ((x - x_R) ^ 2 * z ^ 2 - (2 * (x + x_R) * (x * x_R - 25)) * z
            + (x * x_R + 25) ^ 2) * ((b : ℚ) * (β : ℚ)) ^ 2 := by
      rw [hM_def, hS₁_def, hS₂_def, hx_eq, hxR]
      push_cast
      field_simp
    rw [hscale, hqQ, zero_mul]
  -- the root bound, then the arithmetic
  have hroot := root_bound hM0 hqZ
  set H : ℕ := hgt x with hH_def
  set L : ℕ := α.natAbs + 25 * β.natAbs with hL_def
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
      have e3 : H * β.natAbs ≤ 25 * β.natAbs * H := by
        calc H * β.natAbs = β.natAbs * H := Nat.mul_comm _ _
          _ ≤ 25 * β.natAbs * H :=
              Nat.mul_le_mul (by omega : β.natAbs ≤ 25 * β.natAbs) (le_refl H)
      calc a.natAbs * β.natAbs + α.natAbs * b.natAbs
          ≤ H * β.natAbs + α.natAbs * H := Nat.add_le_add e1 e2
        _ ≤ 25 * β.natAbs * H + α.natAbs * H := Nat.add_le_add_right e3 _
        _ = (α.natAbs + 25 * β.natAbs) * H := by ring
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
      have e3 : H * β.natAbs ≤ 25 * β.natAbs * H := by
        calc H * β.natAbs = β.natAbs * H := Nat.mul_comm _ _
          _ ≤ 25 * β.natAbs * H :=
              Nat.mul_le_mul (by omega : β.natAbs ≤ 25 * β.natAbs) (le_refl H)
      calc a.natAbs * β.natAbs + α.natAbs * b.natAbs
          ≤ H * β.natAbs + α.natAbs * H := Nat.add_le_add e1 e2
        _ ≤ 25 * β.natAbs * H + α.natAbs * H := Nat.add_le_add_right e3 _
        _ = (α.natAbs + 25 * β.natAbs) * H := by ring
    exact le_trans h1 h2
  have hmix : (a * α - 25 * b * β).natAbs ≤ H * L := by
    have h1 : (a * α - 25 * b * β).natAbs
        ≤ a.natAbs * α.natAbs + 25 * b.natAbs * β.natAbs := by
      calc (a * α - 25 * b * β).natAbs
          ≤ (a * α).natAbs + (25 * b * β).natAbs := Int.natAbs_sub_le _ _
        _ = a.natAbs * α.natAbs + 25 * b.natAbs * β.natAbs := by
            simp [Int.natAbs_mul]
    have h2 : a.natAbs * α.natAbs + 25 * b.natAbs * β.natAbs ≤ H * L := by
      rw [hL_def]
      have e4 : a.natAbs * α.natAbs ≤ H * α.natAbs :=
        Nat.mul_le_mul ha_le (le_refl α.natAbs)
      have e5 : 25 * b.natAbs * β.natAbs ≤ 25 * H * β.natAbs :=
        Nat.mul_le_mul (Nat.mul_le_mul (le_refl 25) hb_le) (le_refl β.natAbs)
      calc a.natAbs * α.natAbs + 25 * b.natAbs * β.natAbs
          ≤ H * α.natAbs + 25 * H * β.natAbs := Nat.add_le_add e4 e5
        _ = H * (α.natAbs + 25 * β.natAbs) := by ring
    exact le_trans h1 h2
  have hmixp : (a * α + 25 * b * β).natAbs ≤ H * L := by
    have h1 : (a * α + 25 * b * β).natAbs
        ≤ a.natAbs * α.natAbs + 25 * b.natAbs * β.natAbs := by
      calc (a * α + 25 * b * β).natAbs
          ≤ (a * α).natAbs + (25 * b * β).natAbs := Int.natAbs_add_le _ _
        _ = a.natAbs * α.natAbs + 25 * b.natAbs * β.natAbs := by
            simp [Int.natAbs_mul]
    have h2 : a.natAbs * α.natAbs + 25 * b.natAbs * β.natAbs ≤ H * L := by
      rw [hL_def]
      have e4 : a.natAbs * α.natAbs ≤ H * α.natAbs :=
        Nat.mul_le_mul ha_le (le_refl α.natAbs)
      have e5 : 25 * b.natAbs * β.natAbs ≤ 25 * H * β.natAbs :=
        Nat.mul_le_mul (Nat.mul_le_mul (le_refl 25) hb_le) (le_refl β.natAbs)
      calc a.natAbs * α.natAbs + 25 * b.natAbs * β.natAbs
          ≤ H * α.natAbs + 25 * H * β.natAbs := Nat.add_le_add e4 e5
        _ = H * (α.natAbs + 25 * β.natAbs) := by ring
    exact le_trans h1 h2
  have hM_le : M.natAbs ≤ L ^ 2 * H ^ 2 := by
    calc M.natAbs = (a * β - α * b).natAbs ^ 2 := by
          rw [hM_def, Int.natAbs_pow]
      _ ≤ (L * H) ^ 2 := Nat.pow_le_pow_left hdiff1 2
      _ = L ^ 2 * H ^ 2 := by ring
  have hS₂_le : S₂.natAbs ≤ L ^ 2 * H ^ 2 := by
    calc S₂.natAbs = (a * α + 25 * b * β).natAbs ^ 2 := by
          rw [hS₂_def, Int.natAbs_pow]
      _ ≤ (H * L) ^ 2 := Nat.pow_le_pow_left hmixp 2
      _ = L ^ 2 * H ^ 2 := by ring
  have hS₁_le : S₁.natAbs ≤ 2 * (L ^ 2 * H ^ 2) := by
    calc S₁.natAbs
        = 2 * (a * β + α * b).natAbs * (a * α - 25 * b * β).natAbs := by
          rw [hS₁_def]
          simp [Int.natAbs_mul]
      _ ≤ 2 * (L * H) * (H * L) :=
          Nat.mul_le_mul (Nat.mul_le_mul (le_refl 2) hsum1) hmix
      _ = 2 * (L ^ 2 * H ^ 2) := by ring
  have hmax : max (max S₁.natAbs S₂.natAbs) M.natAbs ≤ 2 * (L ^ 2 * H ^ 2) := by
    have h1 : L ^ 2 * H ^ 2 ≤ 2 * (L ^ 2 * H ^ 2) := by omega
    exact max_le (max_le hS₁_le (le_trans hS₂_le h1)) (le_trans hM_le h1)
  calc hgt z ≤ max (max S₁.natAbs S₂.natAbs) M.natAbs := hroot
    _ ≤ 2 * (L ^ 2 * H ^ 2) := hmax
    _ = 2 * L ^ 2 * H ^ 2 := by ring

end Soma.Holonics.Millennium.FiveTranslation
