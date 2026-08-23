import ElementaryHolonics.Millennium.FamilyPrimeRank
import Mathlib.Tactic

/-!
# FamilyGenocchi: the residue read and the character tables on the three-mod-eight branch

**The first stage of Genocchi's law, family-wise.**  On the branch `p ≡ 3 (mod 8)` the
quadratic character has `χ_p(−1) = −1` and `χ_p(2) = −1`, and reading the slot classes
of any non-torsion point through the residue field collapses the descent cells:

* **`chiRead`** — the quadratic character of a `p`-integral rational, read through
  `num · den` (the denominator's square is invisible to the character);
* **`chiRead_of_sqcls`** — a square class is visible to the read: `χ(z) = χ_p(d)`;
* **`chiRead_congr`** — the read is constant on residue classes;
* the parity, sign, and third-slot laws, and the character tables that pin the
  `p`-free rungs by their character value.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyGenocchi

open Soma.Holonics.Millennium

variable {p : ℕ} [Fact p.Prime]

/-! ## 1. The residue read -/

/-- The quadratic character of a `p`-integral rational, read through `num · den`. -/
def chiRead (p : ℕ) [Fact p.Prime] (z : ℚ) : ℤ :=
  quadraticChar (ZMod p) (((z.num * (z.den : ℤ) : ℤ) : ZMod p))

lemma int_dvd_natAbs {m : ℤ} : (p : ℤ) ∣ m ↔ p ∣ m.natAbs := by
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]

private lemma val_zero_parts {z : ℚ} (hz : z ≠ 0) (hv : padicValRat p z = 0) :
    ¬ (p : ℤ) ∣ z.num ∧ ¬ p ∣ z.den := by
  have hp : p.Prime := Fact.out
  have hnum0 : z.num ≠ 0 := Rat.num_ne_zero.mpr hz
  have hden0 : z.den ≠ 0 := z.den_nz
  have hcop := z.reduced
  have hnotboth : ¬ ((p : ℤ) ∣ z.num ∧ p ∣ z.den) := by
    rintro ⟨h1, h2⟩
    have h3 : p ∣ Nat.gcd z.num.natAbs z.den :=
      Nat.dvd_gcd (int_dvd_natAbs.mp h1) h2
    rw [Nat.Coprime.gcd_eq_one hcop] at h3
    have h4 := Nat.le_of_dvd one_pos h3
    have h5 := hp.two_le
    omega
  constructor
  · intro hdvd
    have hden : ¬ p ∣ z.den := fun h2 => hnotboth ⟨hdvd, h2⟩
    have h1 : padicValNat p z.den = 0 := padicValNat.eq_zero_of_not_dvd hden
    have h2 : padicValInt p z.num ≠ 0 := by
      intro h0
      rcases padicValInt.eq_zero_iff.mp h0 with h | h | h
      · exact absurd h hp.one_lt.ne'
      · exact hnum0 h
      · exact h hdvd
    unfold padicValRat at hv
    omega
  · intro hdvd
    have hnum : ¬ (p : ℤ) ∣ z.num := fun h1 => hnotboth ⟨h1, hdvd⟩
    have h1 : padicValInt p z.num = 0 :=
      padicValInt.eq_zero_iff.mpr (Or.inr (Or.inr hnum))
    have h2 : padicValNat p z.den ≠ 0 := by
      intro h0
      rcases padicValNat.eq_zero_iff.mp h0 with h | h | h
      · exact absurd h hp.one_lt.ne'
      · exact hden0 h
      · exact h hdvd
    unfold padicValRat at hv
    omega

private lemma prod_not_dvd {z : ℚ} (hz : z ≠ 0) (hv : padicValRat p z = 0) :
    ¬ (p : ℤ) ∣ z.num * (z.den : ℤ) := by
  have hp : p.Prime := Fact.out
  obtain ⟨h1, h2⟩ := val_zero_parts hz hv
  intro hdvd
  rw [int_dvd_natAbs, Int.natAbs_mul, Int.natAbs_natCast] at hdvd
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
  · exact h1 (int_dvd_natAbs.mpr h)
  · exact h2 h

lemma chiRead_ne_zero {z : ℚ} (hz : z ≠ 0) (hv : padicValRat p z = 0) :
    chiRead p z ≠ 0 := by
  unfold chiRead
  rw [Ne, quadraticChar_eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact prod_not_dvd hz hv

lemma chiRead_intCast (m : ℤ) :
    chiRead p ((m : ℤ) : ℚ) = quadraticChar (ZMod p) ((m : ZMod p)) := by
  unfold chiRead
  rw [Rat.num_intCast, Rat.den_intCast]
  push_cast
  rw [mul_one]

lemma int_val_zero {m : ℤ} (hm : ¬ (p : ℤ) ∣ m) :
    padicValRat p ((m : ℤ) : ℚ) = 0 := by
  rw [padicValRat.of_int, padicValInt.eq_zero_iff.mpr (Or.inr (Or.inr hm))]
  simp

lemma nat_den_val_zero {z : ℚ} (h : ¬ p ∣ z.den) :
    padicValRat p ((z.den : ℕ) : ℚ) = 0 := by
  have h' : ¬ (p : ℤ) ∣ ((z.den : ℕ) : ℤ) := by
    rw [Int.natCast_dvd_natCast]
    exact h
  have := int_val_zero (p := p) h'
  push_cast at this ⊢
  exact this

/-- **A square class is visible to the residue read.** -/
theorem chiRead_of_sqcls {z : ℚ} {d : ℤ} (hz : z ≠ 0) (hv : padicValRat p z = 0)
    (hd : ¬ (p : ℤ) ∣ d) (h : Descent.SqCls z ((d : ℤ) : ℚ)) :
    chiRead p z = quadraticChar (ZMod p) ((d : ZMod p)) := by
  have hp : p.Prime := Fact.out
  obtain ⟨c, hc, hcv⟩ := h
  have hd0 : d ≠ 0 := by
    intro h0
    exact hd (h0 ▸ dvd_zero _)
  have hdq : ((d : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hd0
  have hvd : padicValRat p ((d : ℤ) : ℚ) = 0 := int_val_zero hd
  have hvc : padicValRat p c = 0 := by
    have hsq : padicValRat p z
        = 2 * padicValRat p c + padicValRat p ((d : ℤ) : ℚ) := by
      rw [hcv, padicValRat.mul (pow_ne_zero 2 hc) hdq, padicValRat.pow hc]
      ring
    omega
  obtain ⟨hcn, hcd⟩ := val_zero_parts hc hvc
  obtain ⟨hzn, hzd⟩ := val_zero_parts hz hv
  -- the cross-multiplied identity
  have hznum : (z.num : ℚ) = z * z.den := (Rat.mul_den_eq_num z).symm
  have hcnum : (c.num : ℚ) = c * c.den := (Rat.mul_den_eq_num c).symm
  have hkey : (z.num : ℚ) * (c.den : ℚ) ^ 2 = (c.num : ℚ) ^ 2 * d * (z.den : ℚ) := by
    rw [hznum, hcnum, hcv]
    ring
  have hint : z.num * (c.den : ℤ) ^ 2 = c.num ^ 2 * d * (z.den : ℤ) := by
    exact_mod_cast hkey
  -- read it through the character
  have hzmod : ((z.num : ZMod p)) * (((c.den : ℤ)) : ZMod p) ^ 2
      = ((c.num : ZMod p)) ^ 2 * ((d : ZMod p)) * (((z.den : ℤ)) : ZMod p) := by
    have h1 := congrArg (fun t : ℤ => ((t : ZMod p))) hint
    push_cast at h1
    exact_mod_cast h1
  have hcd0 : (((c.den : ℤ)) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hdd
    exact hcd (Int.natCast_dvd_natCast.mp hdd)
  have hcn0 : ((c.num : ZMod p)) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hcn
  have hzd0 : (((z.den : ℤ)) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hdd
    exact hzd (Int.natCast_dvd_natCast.mp hdd)
  have hread := congrArg (quadraticChar (ZMod p)) hzmod
  rw [map_mul, map_mul, map_mul, quadraticChar_sq_one' hcd0,
    quadraticChar_sq_one' hcn0] at hread
  have hzden2 : quadraticChar (ZMod p) (((z.den : ℤ) : ZMod p)) ^ 2 = 1 :=
    quadraticChar_sq_one hzd0
  unfold chiRead
  rw [show (((z.num * (z.den : ℤ) : ℤ)) : ZMod p)
      = ((z.num : ZMod p)) * (((z.den : ℤ)) : ZMod p) from by push_cast; ring,
    map_mul]
  linear_combination (quadraticChar (ZMod p) (((z.den : ℤ) : ZMod p))) * hread
    + (quadraticChar (ZMod p) ((d : ZMod p))) * hzden2

/-- **The residue read is constant on residue classes.** -/
theorem chiRead_congr {z z' : ℚ} (hz : z ≠ 0) (hz' : z' ≠ 0)
    (hv : padicValRat p z = 0) (hv' : padicValRat p z' = 0)
    (hdiff : 0 < padicValRat p (z - z')) :
    chiRead p z = chiRead p z' := by
  have hp : p.Prime := Fact.out
  have hne : z ≠ z' := by
    intro h
    rw [h, sub_self] at hdiff
    simp [padicValRat] at hdiff
  have hzz' : z - z' ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨hzn, hzd⟩ := val_zero_parts hz hv
  obtain ⟨hzn', hzd'⟩ := val_zero_parts hz' hv'
  have hznum : (z.num : ℚ) = z * z.den := (Rat.mul_den_eq_num z).symm
  have hznum' : (z'.num : ℚ) = z' * z'.den := (Rat.mul_den_eq_num z').symm
  set N : ℤ := z.num * (z'.den : ℤ) - z'.num * (z.den : ℤ) with hN
  have hNq : ((N : ℤ) : ℚ) = (z - z') * ((z.den : ℚ) * (z'.den : ℚ)) := by
    rw [hN]
    push_cast
    rw [hznum, hznum']
    ring
  have hd1 : ((z.den : ℚ)) ≠ 0 := by exact_mod_cast z.den_nz
  have hd2 : ((z'.den : ℚ)) ≠ 0 := by exact_mod_cast z'.den_nz
  have hN0 : N ≠ 0 := by
    intro h0
    rw [h0] at hNq
    have h1 : (z - z') * ((z.den : ℚ) * (z'.den : ℚ)) = 0 := by exact_mod_cast hNq.symm
    rcases mul_eq_zero.mp h1 with h | h
    · exact hzz' h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact hd1 h'
      · exact hd2 h'
  have hvN : 0 < padicValRat p ((N : ℤ) : ℚ) := by
    rw [hNq, padicValRat.mul hzz' (mul_ne_zero hd1 hd2),
      padicValRat.mul hd1 hd2, nat_den_val_zero (p := p) hzd,
      nat_den_val_zero (p := p) hzd']
    omega
  have hdvdN : (p : ℤ) ∣ N := by
    by_contra hnd
    rw [int_val_zero hnd] at hvN
    omega
  have hzmod : ((z.num : ZMod p)) * (((z'.den : ℤ)) : ZMod p)
      = ((z'.num : ZMod p)) * (((z.den : ℤ)) : ZMod p) := by
    have h1 : ((N : ℤ) : ZMod p) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hdvdN
    rw [hN] at h1
    push_cast at h1
    push_cast
    linear_combination h1
  have hread := congrArg (quadraticChar (ZMod p)) hzmod
  rw [map_mul, map_mul] at hread
  have hzd0 : (((z.den : ℤ)) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hdd
    exact hzd (Int.natCast_dvd_natCast.mp hdd)
  have hzd0' : (((z'.den : ℤ)) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hdd
    exact hzd' (Int.natCast_dvd_natCast.mp hdd)
  have hs : quadraticChar (ZMod p) (((z.den : ℤ) : ZMod p)) ^ 2 = 1 :=
    quadraticChar_sq_one hzd0
  have hs' : quadraticChar (ZMod p) (((z'.den : ℤ) : ZMod p)) ^ 2 = 1 :=
    quadraticChar_sq_one hzd0'
  unfold chiRead
  rw [show (((z.num * (z.den : ℤ) : ℤ)) : ZMod p)
      = ((z.num : ZMod p)) * (((z.den : ℤ)) : ZMod p) from by push_cast; ring,
    show (((z'.num * (z'.den : ℤ) : ℤ)) : ZMod p)
      = ((z'.num : ZMod p)) * (((z'.den : ℤ)) : ZMod p) from by push_cast; ring,
    map_mul, map_mul]
  linear_combination
    (quadraticChar (ZMod p) (((z.den : ℤ) : ZMod p)) *
      quadraticChar (ZMod p) (((z'.den : ℤ) : ZMod p))) * hread
    - (quadraticChar (ZMod p) ((z.num : ZMod p)) *
      quadraticChar (ZMod p) (((z.den : ℤ) : ZMod p))) * hs'
    + (quadraticChar (ZMod p) ((z'.num : ZMod p)) *
      quadraticChar (ZMod p) (((z'.den : ℤ) : ZMod p))) * hs

/-! ## 2. Parity, sign, and the third slot -/

/-- The valuation of a square-class member has the parity of its class. -/
lemma sqcls_val_parity {z : ℚ} {d : ℤ} (hz : z ≠ 0) (hd : d ≠ 0)
    (h : Descent.SqCls z ((d : ℤ) : ℚ)) :
    ∃ e : ℤ, padicValRat p z = 2 * e + padicValRat p ((d : ℤ) : ℚ) := by
  obtain ⟨c, hc, hcv⟩ := h
  have hdq : ((d : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hd
  refine ⟨padicValRat p c, ?_⟩
  rw [hcv, padicValRat.mul (pow_ne_zero 2 hc) hdq, padicValRat.pow hc]
  ring

/-- A positive square-class member has a positive class. -/
lemma sqcls_sign {z : ℚ} {d : ℤ} (h : Descent.SqCls z ((d : ℤ) : ℚ)) (hzpos : 0 < z) :
    0 < d := by
  obtain ⟨c, hc, hcv⟩ := h
  have hc2 : 0 < c ^ 2 := by positivity
  by_contra hdneg
  push_neg at hdneg
  have hdq : ((d : ℤ) : ℚ) ≤ 0 := by exact_mod_cast hdneg
  have hle : z ≤ 0 := by
    rw [hcv]
    exact mul_nonpos_of_nonneg_of_nonpos hc2.le hdq
  linarith

/-- The third slot carries the product class. -/
lemma sqcls_third {x y n : ℚ} (hcurve : y ^ 2 = x ^ 3 - n ^ 2 * x)
    (hy : y ≠ 0) (hx : x ≠ 0) (hxm : x - n ≠ 0) {d₁ d₂ : ℤ}
    (h₁ : Descent.SqCls x ((d₁ : ℤ) : ℚ)) (h₂ : Descent.SqCls (x - n) ((d₂ : ℤ) : ℚ)) :
    Descent.SqCls (x + n) (((d₁ * d₂ : ℤ)) : ℚ) := by
  obtain ⟨c₁, hc₁, hv₁⟩ := h₁
  obtain ⟨c₂, hc₂, hv₂⟩ := h₂
  have hd₁ : ((d₁ : ℤ) : ℚ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hv₁
    exact hx hv₁
  have hd₂ : ((d₂ : ℤ) : ℚ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hv₂
    exact hxm hv₂
  have hfact : y ^ 2 = x * (x - n) * (x + n) := by linear_combination hcurve
  have hC0 : (c₁ * c₂ * ((d₁ : ℤ) : ℚ) * ((d₂ : ℤ) : ℚ)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hc₁ hc₂) hd₁) hd₂
  refine ⟨y / (c₁ * c₂ * ((d₁ : ℤ) : ℚ) * ((d₂ : ℤ) : ℚ)), div_ne_zero hy hC0, ?_⟩
  have hC : (x + n) * (c₁ * c₂ * ((d₁ : ℤ) : ℚ) * ((d₂ : ℤ) : ℚ)) ^ 2
      = y ^ 2 * (((d₁ : ℤ) : ℚ) * ((d₂ : ℤ) : ℚ)) := by
    calc (x + n) * (c₁ * c₂ * ((d₁ : ℤ) : ℚ) * ((d₂ : ℤ) : ℚ)) ^ 2
        = (c₁ ^ 2 * ((d₁ : ℤ) : ℚ)) * (c₂ ^ 2 * ((d₂ : ℤ) : ℚ)) * (x + n) *
            (((d₁ : ℤ) : ℚ) * ((d₂ : ℤ) : ℚ)) := by ring
      _ = x * (x - n) * (x + n) * (((d₁ : ℤ) : ℚ) * ((d₂ : ℤ) : ℚ)) := by
          rw [← hv₁, ← hv₂]
      _ = y ^ 2 * (((d₁ : ℤ) : ℚ) * ((d₂ : ℤ) : ℚ)) := by rw [← hfact]
  rw [div_pow]
  rw [div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hC0)]
  push_cast at hC ⊢
  linear_combination hC

/-! ## 3. The character table on the three-mod-eight branch -/

lemma chi_neg_one (hp8 : p % 8 = 3) :
    quadraticChar (ZMod p) ((-1 : ℤ) : ZMod p) = -1 := by
  have hp : p.Prime := Fact.out
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  rw [show ((-1 : ℤ) : ZMod p) = (-1 : ZMod p) from by push_cast; ring,
    quadraticChar_neg_one hchar, ZMod.card p, ZMod.χ₄_nat_three_mod_four (by omega)]

lemma chi_two' (hp8 : p % 8 = 3) :
    quadraticChar (ZMod p) ((2 : ℤ) : ZMod p) = -1 := by
  have hp : p.Prime := Fact.out
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  rw [show ((2 : ℤ) : ZMod p) = (2 : ZMod p) from by push_cast; ring,
    quadraticChar_two hchar, ZMod.card p, ZMod.χ₈_nat_eq_if_mod_eight,
    if_neg (by omega), if_neg (by omega)]

lemma chi_neg_two (hp8 : p % 8 = 3) :
    quadraticChar (ZMod p) ((-2 : ℤ) : ZMod p) = 1 := by
  have h := congrArg (quadraticChar (ZMod p))
    (show ((-2 : ℤ) : ZMod p) = ((-1 : ℤ) : ZMod p) * ((2 : ℤ) : ZMod p) from by
      push_cast; ring)
  rw [map_mul, chi_neg_one hp8, chi_two' hp8] at h
  rw [h]
  ring

lemma chi_one' :
    quadraticChar (ZMod p) ((1 : ℤ) : ZMod p) = 1 := by
  rw [show ((1 : ℤ) : ZMod p) = (1 : ZMod p) from by push_cast; ring]
  exact map_one _

/-- The `p`-free rungs with character one are `1` and `−2`. -/
lemma rung_char_one (hp8 : p % 8 = 3) {d : ℤ} (hd0 : d ≠ 0)
    (hdvd : d.natAbs ∣ 2 * p) (hfree : ¬ (p : ℤ) ∣ d)
    (hchi : quadraticChar (ZMod p) ((d : ZMod p)) = 1) :
    d = 1 ∨ d = -2 := by
  have hp : p.Prime := Fact.out
  have h4 := FamilyPrimeRank.dvd_two_mul_prime hp hdvd
  have habs := Int.natAbs_eq d
  have hpd : (p : ℤ) ∣ (p : ℤ) := dvd_refl ((p : ℤ))
  have h2pd : (p : ℤ) ∣ 2 * (p : ℤ) := ⟨2, by ring⟩
  have hnp : d ≠ (p : ℤ) ∧ d ≠ -(p : ℤ) ∧ d ≠ 2 * p ∧ d ≠ -(2 * (p : ℤ)) := by
    refine ⟨fun h0 => hfree (h0 ▸ hpd), fun h0 => hfree (h0 ▸ dvd_neg.mpr hpd),
      fun h0 => hfree (h0 ▸ h2pd), fun h0 => hfree (h0 ▸ dvd_neg.mpr h2pd)⟩
  have hd14 : d = 1 ∨ d = -1 ∨ d = 2 ∨ d = -2 := by
    rcases h4 with h | h | h | h <;> omega
  rcases hd14 with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · rw [chi_neg_one hp8] at hchi
    omega
  · rw [chi_two' hp8] at hchi
    omega
  · exact Or.inr rfl

/-- The `p`-free rungs with character minus one are `−1` and `2`. -/
lemma rung_char_neg_one (hp8 : p % 8 = 3) {d : ℤ} (hd0 : d ≠ 0)
    (hdvd : d.natAbs ∣ 2 * p) (hfree : ¬ (p : ℤ) ∣ d)
    (hchi : quadraticChar (ZMod p) ((d : ZMod p)) = -1) :
    d = -1 ∨ d = 2 := by
  have hp : p.Prime := Fact.out
  have h4 := FamilyPrimeRank.dvd_two_mul_prime hp hdvd
  have habs := Int.natAbs_eq d
  have hpd : (p : ℤ) ∣ (p : ℤ) := dvd_refl ((p : ℤ))
  have h2pd : (p : ℤ) ∣ 2 * (p : ℤ) := ⟨2, by ring⟩
  have hnp : d ≠ (p : ℤ) ∧ d ≠ -(p : ℤ) ∧ d ≠ 2 * p ∧ d ≠ -(2 * (p : ℤ)) := by
    refine ⟨fun h0 => hfree (h0 ▸ hpd), fun h0 => hfree (h0 ▸ dvd_neg.mpr hpd),
      fun h0 => hfree (h0 ▸ h2pd), fun h0 => hfree (h0 ▸ dvd_neg.mpr h2pd)⟩
  have hd14 : d = 1 ∨ d = -1 ∨ d = 2 ∨ d = -2 := by
    rcases h4 with h | h | h | h <;> omega
  rcases hd14 with rfl | rfl | rfl | rfl
  · rw [chi_one'] at hchi
    omega
  · exact Or.inl rfl
  · exact Or.inr rfl
  · rw [chi_neg_two hp8] at hchi
    omega


/-! ## 4. The mod-`p` collapse of the slot classes -/

lemma val_p (hp : p.Prime) : padicValRat p (((p : ℕ) : ℚ)) = 1 :=
  padicValRat.self hp.one_lt

lemma rung_split (hp3 : 2 < p) {d : ℤ} (hd0 : d ≠ 0) (hdvd : d.natAbs ∣ 2 * p) :
    ((¬ (p : ℤ) ∣ d) ∧ padicValRat p ((d : ℤ) : ℚ) = 0) ∨
    ((p : ℤ) ∣ d ∧ ∃ d' : ℤ, d = (p : ℤ) * d' ∧ ¬ (p : ℤ) ∣ d' ∧
      d'.natAbs ∣ 2 * p ∧ d' ≠ 0 ∧ padicValRat p ((d : ℤ) : ℚ) = 1) := by
  have hp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hp.two_le
  by_cases hpd : (p : ℤ) ∣ d
  · right
    obtain ⟨d', hd'⟩ := hpd
    have hd'0 : d' ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hd'
      exact hd0 hd'
    have h4 := FamilyPrimeRank.dvd_two_mul_prime hp hdvd
    have habs : d.natAbs = p * d'.natAbs := by
      rw [hd', Int.natAbs_mul, Int.natAbs_natCast]
    have hd'abs : d'.natAbs = 1 ∨ d'.natAbs = 2 := by
      have h1 : p * d'.natAbs ∣ 2 * p := habs ▸ hdvd
      have h3 : p * d'.natAbs ∣ p * 2 := by
        rw [show p * 2 = 2 * p from by ring]
        exact h1
      have h2 : d'.natAbs ∣ 2 := (mul_dvd_mul_iff_left hp.pos.ne').mp h3
      exact (Nat.dvd_prime Nat.prime_two).mp h2
    have hd'free : ¬ (p : ℤ) ∣ d' := by
      intro hc
      have h1 : p ∣ d'.natAbs := int_dvd_natAbs.mp hc
      have h2 := Nat.le_of_dvd (by omega) h1
      omega
    have hd'dvd : d'.natAbs ∣ 2 * p := by
      rcases hd'abs with h | h <;> rw [h]
      · exact one_dvd _
      · exact Dvd.intro p rfl
    have hval : padicValRat p ((d : ℤ) : ℚ) = 1 := by
      rw [hd']
      push_cast
      rw [padicValRat.mul (by exact_mod_cast hp.pos.ne') (by exact_mod_cast hd'0),
        val_p hp, int_val_zero hd'free]
      ring
    exact ⟨⟨d', hd'⟩, d', hd', hd'free, hd'dvd, hd'0, hval⟩
  · exact Or.inl ⟨hpd, int_val_zero hpd⟩

set_option maxHeartbeats 4000000 in
/-- **THE SLOT CLASSES COLLAPSE ON THE THREE-MOD-EIGHT BRANCH**: at every prime
`p ≡ 3 (mod 8)`, the slot-class pair of any point of `y² = x³ − p²x` with `y ≠ 0`
lies among **eight** named cells — the residue field reads the three slots and the
character table `χ_p(−1) = χ_p(2) = −1` refuses the other fifty-six. -/
theorem theSlotClassesCollapseOnTheThreeModEightBranch
    (hp8 : p % 8 = 3) {x y : ℚ}
    (hcurve : y ^ 2 = x ^ 3 - ((p : ℕ) : ℚ) ^ 2 * x) (hy : y ≠ 0)
    {d₁ d₂ : ℤ} (h₁0 : d₁ ≠ 0) (h₂0 : d₂ ≠ 0)
    (h₁v : d₁.natAbs ∣ 2 * p) (h₂v : d₂.natAbs ∣ 2 * p)
    (h₁ : Descent.SqCls x ((d₁ : ℤ) : ℚ))
    (h₂ : Descent.SqCls (x - ((p : ℕ) : ℚ)) ((d₂ : ℤ) : ℚ)) :
    (d₁ = 1 ∧ d₂ = 1) ∨ (d₁ = -2 ∧ d₂ = -2) ∨
    (d₁ = -1 ∧ d₂ = -(p : ℤ)) ∨ (d₁ = 2 ∧ d₂ = 2 * p) ∨
    (d₁ = (p : ℤ) ∧ d₂ = 2) ∨ (d₁ = -2 * p ∧ d₂ = -1) ∨
    (d₁ = 2 * (p : ℤ) ∧ d₂ = (p : ℤ)) ∨ (d₁ = -(p : ℤ) ∧ d₂ = -2 * p) := by
  have hp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hp.two_le
  have hpq0 : (((p : ℕ) : ℚ)) ≠ 0 := by exact_mod_cast hp.pos.ne'
  have hpqpos : (0 : ℚ) < ((p : ℕ) : ℚ) := by exact_mod_cast hp.pos
  obtain ⟨hx0, hxn, hxmn⟩ :=
    FaceHomomorphism.theNonzeroOrdinateAvoidsTheRoots hcurve hy
  have hxm0 : x - ((p : ℕ) : ℚ) ≠ 0 := sub_ne_zero.mpr hxn
  have hxp0 : x + ((p : ℕ) : ℚ) ≠ 0 := fun hc => hxmn (by linarith)
  have hy2 : 0 < y ^ 2 :=
    (sq_nonneg y).lt_of_ne fun h => hy (pow_eq_zero_iff two_ne_zero |>.mp h.symm)
  have hfact : y ^ 2 = x * (x - ((p : ℕ) : ℚ)) * (x + ((p : ℕ) : ℚ)) := by
    linear_combination hcurve
  have hxppos : 0 < x + ((p : ℕ) : ℚ) := by
    rcases lt_trichotomy (x + ((p : ℕ) : ℚ)) 0 with h | h | h
    · exfalso
      have hxneg : x < 0 := by linarith
      have hxmneg : x - ((p : ℕ) : ℚ) < 0 := by linarith
      nlinarith [mul_pos_of_neg_of_neg hxneg hxmneg]
    · exact absurd h hxp0
    · exact h
  have h₃ : Descent.SqCls (x + ((p : ℕ) : ℚ)) (((d₁ * d₂ : ℤ)) : ℚ) :=
    sqcls_third hcurve hy hx0 hxm0 h₁ h₂
  have h₁₂0 : d₁ * d₂ ≠ 0 := mul_ne_zero h₁0 h₂0
  have h₁₂pos : 0 < d₁ * d₂ := sqcls_sign h₃ hxppos
  -- the valuation ledger
  have hvp : padicValRat p (((p : ℕ) : ℚ)) = 1 := val_p hp
  have hvsum : 2 * padicValRat p y = padicValRat p x
      + padicValRat p (x - ((p : ℕ) : ℚ)) + padicValRat p (x + ((p : ℕ) : ℚ)) := by
    have h1 : padicValRat p (y ^ 2) = 2 * padicValRat p y := by
      rw [pow_two, padicValRat.mul hy hy]
      ring
    rw [← h1, hfact, padicValRat.mul (mul_ne_zero hx0 hxm0) hxp0,
      padicValRat.mul hx0 hxm0]
  set V : ℤ := padicValRat p x with hV
  by_cases hVle : V ≤ 0
  · -- the shifted-unit case: both classes are `p`-free with character one
    have hvxm : padicValRat p (x - ((p : ℕ) : ℚ)) = V := by
      have he : x - ((p : ℕ) : ℚ) = x + (-((p : ℕ) : ℚ)) := by ring
      rw [he]
      refine FamilySupport.val_add_left hx0 (by rw [← he]; exact hxm0) ?_
      rw [padicValRat.neg, hvp]
      omega
    have hvxp : padicValRat p (x + ((p : ℕ) : ℚ)) = V := by
      refine FamilySupport.val_add_left hx0 hxp0 ?_
      rw [hvp]
      omega
    have hVeven : Even V := by
      rw [hvxm, hvxp] at hvsum
      exact ⟨padicValRat p y - V, by omega⟩
    -- the classes are `p`-free
    have hfree₁ : ¬ (p : ℤ) ∣ d₁ := by
      rcases rung_split (by omega) h₁0 h₁v with ⟨hf, -⟩ | ⟨-, d', -, -, -, -, hv1⟩
      · exact hf
      · obtain ⟨e, he⟩ := sqcls_val_parity (p := p) hx0 h₁0 h₁
        rw [hv1] at he
        obtain ⟨w, hw⟩ := hVeven
        omega
    have hfree₂ : ¬ (p : ℤ) ∣ d₂ := by
      rcases rung_split (by omega) h₂0 h₂v with ⟨hf, -⟩ | ⟨-, d', -, -, -, -, hv1⟩
      · exact hf
      · obtain ⟨e, he⟩ := sqcls_val_parity (p := p) hxm0 h₂0 h₂
        rw [hvxm, hv1] at he
        obtain ⟨w, hw⟩ := hVeven
        omega
    have hfree₁₂ : ¬ (p : ℤ) ∣ d₁ * d₂ := by
      intro hc
      rw [int_dvd_natAbs, Int.natAbs_mul] at hc
      rcases (Nat.Prime.dvd_mul hp).mp hc with h | h
      · exact hfree₁ (int_dvd_natAbs.mpr h)
      · exact hfree₂ (int_dvd_natAbs.mpr h)
    -- the shift to valuation zero
    set k : ℕ := (-V).toNat with hk
    have hkV : (k : ℤ) = -V := Int.toNat_of_nonneg (by omega)
    obtain ⟨j, hj⟩ : Even k := by
      obtain ⟨w, hw⟩ := hVeven
      refine ⟨(-w).toNat, ?_⟩
      omega
    have hppow : ((p : ℚ)) ^ k ≠ 0 := pow_ne_zero _ hpq0
    have hvpow : padicValRat p (((p : ℕ) : ℚ) ^ k) = k := by
      rw [padicValRat.pow hpq0, hvp]
      ring
    set x₁ : ℚ := x * ((p : ℕ) : ℚ) ^ k with hx₁
    set x₂ : ℚ := (x - ((p : ℕ) : ℚ)) * ((p : ℕ) : ℚ) ^ k with hx₂
    set x₃ : ℚ := (x + ((p : ℕ) : ℚ)) * ((p : ℕ) : ℚ) ^ k with hx₃
    have hx₁0 : x₁ ≠ 0 := mul_ne_zero hx0 hppow
    have hx₂0 : x₂ ≠ 0 := mul_ne_zero hxm0 hppow
    have hx₃0 : x₃ ≠ 0 := mul_ne_zero hxp0 hppow
    have hvx₁ : padicValRat p x₁ = 0 := by
      rw [hx₁, padicValRat.mul hx0 hppow, hvpow]
      omega
    have hvx₂ : padicValRat p x₂ = 0 := by
      rw [hx₂, padicValRat.mul hxm0 hppow, hvpow, hvxm]
      omega
    have hvx₃ : padicValRat p x₃ = 0 := by
      rw [hx₃, padicValRat.mul hxp0 hppow, hvpow, hvxp]
      omega
    have hsq₁ : Descent.SqCls x₁ ((d₁ : ℤ) : ℚ) := by
      obtain ⟨c, hc, hcv⟩ := h₁
      refine ⟨c * ((p : ℕ) : ℚ) ^ j, mul_ne_zero hc (pow_ne_zero _ hpq0), ?_⟩
      rw [hx₁, hcv, hj]
      ring
    have hsq₂ : Descent.SqCls x₂ ((d₂ : ℤ) : ℚ) := by
      obtain ⟨c, hc, hcv⟩ := h₂
      refine ⟨c * ((p : ℕ) : ℚ) ^ j, mul_ne_zero hc (pow_ne_zero _ hpq0), ?_⟩
      rw [hx₂, hcv, hj]
      ring
    have hsq₃ : Descent.SqCls x₃ (((d₁ * d₂ : ℤ)) : ℚ) := by
      obtain ⟨c, hc, hcv⟩ := h₃
      refine ⟨c * ((p : ℕ) : ℚ) ^ j, mul_ne_zero hc (pow_ne_zero _ hpq0), ?_⟩
      rw [hx₃, hcv, hj]
      ring
    have hr₁ := chiRead_of_sqcls hx₁0 hvx₁ hfree₁ hsq₁
    have hr₂ := chiRead_of_sqcls hx₂0 hvx₂ hfree₂ hsq₂
    have hr₃ := chiRead_of_sqcls hx₃0 hvx₃ hfree₁₂ hsq₃
    have hc₁₂ : chiRead p x₁ = chiRead p x₂ := by
      refine chiRead_congr hx₁0 hx₂0 hvx₁ hvx₂ ?_
      have hd : x₁ - x₂ = ((p : ℕ) : ℚ) ^ (k + 1) := by
        rw [hx₁, hx₂]
        ring
      rw [hd, padicValRat.pow hpq0, hvp]
      omega
    have hc₁₃ : chiRead p x₁ = chiRead p x₃ := by
      refine chiRead_congr hx₁0 hx₃0 hvx₁ hvx₃ ?_
      have hd : x₁ - x₃ = -((p : ℕ) : ℚ) ^ (k + 1) := by
        rw [hx₁, hx₃]
        ring
      rw [hd, padicValRat.neg, padicValRat.pow hpq0, hvp]
      omega
    have hmul : quadraticChar (ZMod p) (((d₁ * d₂ : ℤ)) : ZMod p)
        = quadraticChar (ZMod p) ((d₁ : ZMod p)) *
          quadraticChar (ZMod p) ((d₂ : ZMod p)) := by
      rw [show (((d₁ * d₂ : ℤ)) : ZMod p) = ((d₁ : ZMod p)) * ((d₂ : ZMod p)) from by
        push_cast; ring, map_mul]
    have heq₁₂ : quadraticChar (ZMod p) ((d₁ : ZMod p))
        = quadraticChar (ZMod p) ((d₂ : ZMod p)) := by
      rw [← hr₁, ← hr₂, hc₁₂]
    have heqprod : quadraticChar (ZMod p) ((d₁ : ZMod p))
        = quadraticChar (ZMod p) ((d₁ : ZMod p)) *
          quadraticChar (ZMod p) ((d₂ : ZMod p)) := by
      rw [← hmul, ← hr₃, ← hc₁₃, hr₁]
    have hne₁ : quadraticChar (ZMod p) ((d₁ : ZMod p)) ≠ 0 := by
      rw [Ne, quadraticChar_eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hfree₁
    have hchi₂ : quadraticChar (ZMod p) ((d₂ : ZMod p)) = 1 :=
      mul_left_cancel₀ hne₁ (by rw [← heqprod, mul_one])
    have hchi₁ : quadraticChar (ZMod p) ((d₁ : ZMod p)) = 1 := by
      rw [heq₁₂, hchi₂]
    rcases rung_char_one hp8 h₁0 h₁v hfree₁ hchi₁ with rfl | rfl <;>
      rcases rung_char_one hp8 h₂0 h₂v hfree₂ hchi₂ with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exfalso
      omega
    · exfalso
      omega
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · -- the `p`-adic branch: at least one slot meets the prime
    push_neg at hVle
    have hVpos : 0 < V := hVle
    have hvxm1 : 1 ≤ padicValRat p (x - ((p : ℕ) : ℚ)) := by
      have he : x - ((p : ℕ) : ℚ) = x + (-((p : ℕ) : ℚ)) := by ring
      have hmin := padicValRat.min_le_padicValRat_add (p := p)
        (q := x) (r := -((p : ℕ) : ℚ)) (by rw [← he]; exact hxm0)
      rw [padicValRat.neg, hvp] at hmin
      rw [he]
      omega
    have hvxp1 : 1 ≤ padicValRat p (x + ((p : ℕ) : ℚ)) := by
      have hmin := padicValRat.min_le_padicValRat_add (p := p)
        (q := x) (r := ((p : ℕ) : ℚ)) hxp0
      rw [hvp] at hmin
      omega
    set v₂ : ℤ := padicValRat p (x - ((p : ℕ) : ℚ)) with hv₂
    set v₃ : ℤ := padicValRat p (x + ((p : ℕ) : ℚ)) with hv₃
    -- at most one of the three valuations exceeds one
    have hpair₁₂ : ¬ (2 ≤ V ∧ 2 ≤ v₂) := by
      rintro ⟨ha, hb⟩
      have he : ((p : ℕ) : ℚ) = x + (-(x - ((p : ℕ) : ℚ))) := by ring
      have hmin := padicValRat.min_le_padicValRat_add (p := p)
        (q := x) (r := -(x - ((p : ℕ) : ℚ))) (by rw [← he]; exact hpq0)
      rw [← he, padicValRat.neg, hvp] at hmin
      omega
    have hpair₁₃ : ¬ (2 ≤ V ∧ 2 ≤ v₃) := by
      rintro ⟨ha, hb⟩
      have he : ((p : ℕ) : ℚ) = (x + ((p : ℕ) : ℚ)) + (-x) := by ring
      have hmin := padicValRat.min_le_padicValRat_add (p := p)
        (q := x + ((p : ℕ) : ℚ)) (r := -x) (by rw [← he]; exact hpq0)
      rw [← he, padicValRat.neg, hvp] at hmin
      omega
    have hv2p : padicValRat p ((2 : ℚ) * ((p : ℕ) : ℚ)) = 1 := by
      have h2 : ¬ (p : ℤ) ∣ (2 : ℤ) := by
        intro hc
        have := Int.le_of_dvd (by norm_num) hc
        omega
      have hv2 : padicValRat p ((2 : ℚ)) = 0 := by
        have := int_val_zero (p := p) h2
        push_cast at this ⊢
        exact this
      rw [padicValRat.mul (by norm_num) hpq0, hv2, hvp]
      ring
    have hpair₂₃ : ¬ (2 ≤ v₂ ∧ 2 ≤ v₃) := by
      rintro ⟨ha, hb⟩
      have he : (2 : ℚ) * ((p : ℕ) : ℚ)
          = (x + ((p : ℕ) : ℚ)) + (-(x - ((p : ℕ) : ℚ))) := by ring
      have hne : (2 : ℚ) * ((p : ℕ) : ℚ) ≠ 0 := by
        have := hpqpos
        positivity
      have hmin := padicValRat.min_le_padicValRat_add (p := p)
        (q := x + ((p : ℕ) : ℚ)) (r := -(x - ((p : ℕ) : ℚ))) (by rw [← he]; exact hne)
      rw [← he, padicValRat.neg, hv2p] at hmin
      omega
    -- the parities of the classes track the valuations
    obtain ⟨e₁, he₁⟩ := sqcls_val_parity (p := p) hx0 h₁0 h₁
    obtain ⟨e₂, he₂⟩ := sqcls_val_parity (p := p) hxm0 h₂0 h₂
    -- helper facts about small integers
    have hnd1 : ¬ (p : ℤ) ∣ (1 : ℤ) := by
      intro hc
      have := Int.le_of_dvd (by norm_num) hc
      omega
    have hndm1 : ¬ (p : ℤ) ∣ (-1 : ℤ) := by
      intro hc
      have := Int.le_of_dvd (by norm_num) (dvd_neg.mp hc)
      omega
    have hnd2 : ¬ (p : ℤ) ∣ (2 : ℤ) := by
      intro hc
      have := Int.le_of_dvd (by norm_num) hc
      omega
    have hndm2 : ¬ (p : ℤ) ∣ (-2 : ℤ) := by
      intro hc
      have := Int.le_of_dvd (by norm_num) (dvd_neg.mp hc)
      omega
    -- decide which valuation is the even one
    rcases Int.even_or_odd V with hVe | hVo
    · -- `V` even, so `V ≥ 2` and `v₂ = v₃ = 1`
      have hV2 : 2 ≤ V := by
        obtain ⟨w, hw⟩ := hVe
        omega
      have hv₂1 : v₂ = 1 := by
        by_contra hc
        exact hpair₁₂ ⟨hV2, by omega⟩
      have hv₃1 : v₃ = 1 := by
        by_contra hc
        exact hpair₁₃ ⟨hV2, by omega⟩
      -- `d₁` is `p`-free, `d₂` meets the prime
      have hfree₁ : ¬ (p : ℤ) ∣ d₁ := by
        rcases rung_split (by omega) h₁0 h₁v with ⟨hf, -⟩ | ⟨-, d', -, -, -, -, hv1⟩
        · exact hf
        · rw [hv1] at he₁
          obtain ⟨w, hw⟩ := hVe
          omega
      obtain ⟨d₂', hd₂', hd₂'free, hd₂'v, hd₂'0, -⟩ :
          ∃ d' : ℤ, d₂ = (p : ℤ) * d' ∧ ¬ (p : ℤ) ∣ d' ∧ d'.natAbs ∣ 2 * p ∧
            d' ≠ 0 ∧ padicValRat p ((d₂ : ℤ) : ℚ) = 1 := by
        rcases rung_split (by omega) h₂0 h₂v with ⟨hf, hv0⟩ | ⟨-, hr⟩
        · exfalso
          rw [hv0] at he₂
          omega
        · exact hr
      -- the reads at level `1/p`
      set z₂ : ℚ := (x - ((p : ℕ) : ℚ)) / ((p : ℕ) : ℚ) with hz₂
      set z₃ : ℚ := (x + ((p : ℕ) : ℚ)) / ((p : ℕ) : ℚ) with hz₃
      have hz₂0 : z₂ ≠ 0 := div_ne_zero hxm0 hpq0
      have hz₃0 : z₃ ≠ 0 := div_ne_zero hxp0 hpq0
      have hvz₂ : padicValRat p z₂ = 0 := by
        rw [hz₂, padicValRat.div hxm0 hpq0, hvp]
        omega
      have hvz₃ : padicValRat p z₃ = 0 := by
        rw [hz₃, padicValRat.div hxp0 hpq0, hvp]
        omega
      have hsqz₂ : Descent.SqCls z₂ ((d₂' : ℤ) : ℚ) := by
        obtain ⟨c, hc, hcv⟩ := h₂
        refine ⟨c, hc, ?_⟩
        rw [hz₂, hcv, hd₂']
        push_cast
        field_simp
        try ring
      have hsqz₃ : Descent.SqCls z₃ (((d₁ * d₂' : ℤ)) : ℚ) := by
        obtain ⟨c, hc, hcv⟩ := h₃
        refine ⟨c, hc, ?_⟩
        rw [hz₃, hcv, hd₂']
        push_cast
        field_simp
        try ring
      have hfree₁₂' : ¬ (p : ℤ) ∣ d₁ * d₂' := by
        intro hc
        rw [int_dvd_natAbs, Int.natAbs_mul] at hc
        rcases (Nat.Prime.dvd_mul hp).mp hc with h | h
        · exact hfree₁ (int_dvd_natAbs.mpr h)
        · exact hd₂'free (int_dvd_natAbs.mpr h)
      have hrz₂ := chiRead_of_sqcls hz₂0 hvz₂ hd₂'free hsqz₂
      have hrz₃ := chiRead_of_sqcls hz₃0 hvz₃ hfree₁₂' hsqz₃
      have hcong₂ : chiRead p z₂ = chiRead p (((-1 : ℤ)) : ℚ) := by
        refine chiRead_congr hz₂0 (by norm_num) hvz₂ (int_val_zero hndm1) ?_
        have hd : z₂ - (((-1 : ℤ)) : ℚ) = x / ((p : ℕ) : ℚ) := by
          rw [hz₂]
          push_cast
          field_simp
          try ring
        rw [hd, padicValRat.div hx0 hpq0, hvp]
        omega
      have hcong₃ : chiRead p z₃ = chiRead p (((1 : ℤ)) : ℚ) := by
        refine chiRead_congr hz₃0 (by norm_num) hvz₃ (int_val_zero hnd1) ?_
        have hd : z₃ - (((1 : ℤ)) : ℚ) = x / ((p : ℕ) : ℚ) := by
          rw [hz₃]
          push_cast
          field_simp
          try ring
        rw [hd, padicValRat.div hx0 hpq0, hvp]
        omega
      have hchi₂' : quadraticChar (ZMod p) ((d₂' : ZMod p)) = -1 := by
        rw [← hrz₂, hcong₂, chiRead_intCast, chi_neg_one hp8]
      have hchi₁₂' : quadraticChar (ZMod p) (((d₁ * d₂' : ℤ)) : ZMod p) = 1 := by
        rw [← hrz₃, hcong₃, chiRead_intCast, chi_one']
      have hchi₁ : quadraticChar (ZMod p) ((d₁ : ZMod p)) = -1 := by
        have hmul : quadraticChar (ZMod p) (((d₁ * d₂' : ℤ)) : ZMod p)
            = quadraticChar (ZMod p) ((d₁ : ZMod p)) *
              quadraticChar (ZMod p) ((d₂' : ZMod p)) := by
          rw [show (((d₁ * d₂' : ℤ)) : ZMod p)
              = ((d₁ : ZMod p)) * ((d₂' : ZMod p)) from by push_cast; ring, map_mul]
        rw [hmul, hchi₂'] at hchi₁₂'
        linarith
      rcases rung_char_neg_one hp8 h₁0 h₁v hfree₁ hchi₁ with rfl | rfl <;>
        rcases rung_char_neg_one hp8 hd₂'0 hd₂'v hd₂'free hchi₂' with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩))
      · exfalso
        rw [hd₂'] at h₁₂pos
        nlinarith [h₁₂pos]
      · exfalso
        rw [hd₂'] at h₁₂pos
        nlinarith [h₁₂pos]
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩)))
    · -- `V = 1`; the even slot is the second or the third
      have hV1 : V = 1 := by
        by_contra hc
        have hV2 : 2 ≤ V := by
          obtain ⟨w, hw⟩ := hVo
          omega
        have hv₂1 : v₂ = 1 := by
          by_contra hc2
          exact hpair₁₂ ⟨hV2, by omega⟩
        have hv₃1 : v₃ = 1 := by
          by_contra hc2
          exact hpair₁₃ ⟨hV2, by omega⟩
        obtain ⟨w, hw⟩ := hVo
        omega
      obtain ⟨d₁', hd₁', hd₁'free, hd₁'v, hd₁'0, -⟩ :
          ∃ d' : ℤ, d₁ = (p : ℤ) * d' ∧ ¬ (p : ℤ) ∣ d' ∧ d'.natAbs ∣ 2 * p ∧
            d' ≠ 0 ∧ padicValRat p ((d₁ : ℤ) : ℚ) = 1 := by
        rcases rung_split (by omega) h₁0 h₁v with ⟨hf, hv0⟩ | ⟨-, hr⟩
        · exfalso
          rw [hv0] at he₁
          omega
        · exact hr
      set z₁ : ℚ := x / ((p : ℕ) : ℚ) with hz₁
      have hz₁0 : z₁ ≠ 0 := div_ne_zero hx0 hpq0
      have hvz₁ : padicValRat p z₁ = 0 := by
        rw [hz₁, padicValRat.div hx0 hpq0, hvp]
        omega
      have hsqz₁ : Descent.SqCls z₁ ((d₁' : ℤ) : ℚ) := by
        obtain ⟨c, hc, hcv⟩ := h₁
        refine ⟨c, hc, ?_⟩
        rw [hz₁, hcv, hd₁']
        push_cast
        field_simp
        try ring
      have hrz₁ := chiRead_of_sqcls hz₁0 hvz₁ hd₁'free hsqz₁
      rcases Int.even_or_odd v₂ with hv₂e | hv₂o
      · -- `v₂` even: the cells `(p, 2)` and `(−2p, −1)`
        have hv₂2 : 2 ≤ v₂ := by
          obtain ⟨w, hw⟩ := hv₂e
          omega
        have hfree₂ : ¬ (p : ℤ) ∣ d₂ := by
          rcases rung_split (by omega) h₂0 h₂v with ⟨hf, -⟩ | ⟨-, d', -, -, -, -, hv1⟩
          · exact hf
          · rw [hv1] at he₂
            obtain ⟨w, hw⟩ := hv₂e
            omega
        set z₃ : ℚ := (x + ((p : ℕ) : ℚ)) / ((p : ℕ) : ℚ) with hz₃
        have hz₃0 : z₃ ≠ 0 := div_ne_zero hxp0 hpq0
        have hv₃1 : v₃ = 1 := by
          by_contra hc
          exact hpair₂₃ ⟨hv₂2, by omega⟩
        have hvz₃ : padicValRat p z₃ = 0 := by
          rw [hz₃, padicValRat.div hxp0 hpq0, hvp]
          omega
        have hsqz₃ : Descent.SqCls z₃ (((d₁' * d₂ : ℤ)) : ℚ) := by
          obtain ⟨c, hc, hcv⟩ := h₃
          refine ⟨c, hc, ?_⟩
          rw [hz₃, hcv, hd₁']
          push_cast
          field_simp
          try ring
        have hfree₁₂' : ¬ (p : ℤ) ∣ d₁' * d₂ := by
          intro hc
          rw [int_dvd_natAbs, Int.natAbs_mul] at hc
          rcases (Nat.Prime.dvd_mul hp).mp hc with h | h
          · exact hd₁'free (int_dvd_natAbs.mpr h)
          · exact hfree₂ (int_dvd_natAbs.mpr h)
        have hrz₃ := chiRead_of_sqcls hz₃0 hvz₃ hfree₁₂' hsqz₃
        have hcong₁ : chiRead p z₁ = chiRead p (((1 : ℤ)) : ℚ) := by
          refine chiRead_congr hz₁0 (by norm_num) hvz₁ (int_val_zero hnd1) ?_
          have hd : z₁ - (((1 : ℤ)) : ℚ) = (x - ((p : ℕ) : ℚ)) / ((p : ℕ) : ℚ) := by
            rw [hz₁]
            push_cast
            field_simp
            try ring
          rw [hd, padicValRat.div hxm0 hpq0, hvp]
          omega
        have hcong₃ : chiRead p z₃ = chiRead p (((2 : ℤ)) : ℚ) := by
          refine chiRead_congr hz₃0 (by norm_num) hvz₃ (int_val_zero hnd2) ?_
          have hd : z₃ - (((2 : ℤ)) : ℚ) = (x - ((p : ℕ) : ℚ)) / ((p : ℕ) : ℚ) := by
            rw [hz₃]
            push_cast
            field_simp
            try ring
          rw [hd, padicValRat.div hxm0 hpq0, hvp]
          omega
        have hchi₁' : quadraticChar (ZMod p) ((d₁' : ZMod p)) = 1 := by
          rw [← hrz₁, hcong₁, chiRead_intCast, chi_one']
        have hchi₁₂' : quadraticChar (ZMod p) (((d₁' * d₂ : ℤ)) : ZMod p) = -1 := by
          rw [← hrz₃, hcong₃, chiRead_intCast, chi_two' hp8]
        have hchi₂ : quadraticChar (ZMod p) ((d₂ : ZMod p)) = -1 := by
          have hmul : quadraticChar (ZMod p) (((d₁' * d₂ : ℤ)) : ZMod p)
              = quadraticChar (ZMod p) ((d₁' : ZMod p)) *
                quadraticChar (ZMod p) ((d₂ : ZMod p)) := by
            rw [show (((d₁' * d₂ : ℤ)) : ZMod p)
                = ((d₁' : ZMod p)) * ((d₂ : ZMod p)) from by push_cast; ring, map_mul]
          rw [hmul, hchi₁'] at hchi₁₂'
          linarith
        rcases rung_char_one hp8 hd₁'0 hd₁'v hd₁'free hchi₁' with rfl | rfl <;>
          rcases rung_char_neg_one hp8 h₂0 h₂v hfree₂ hchi₂ with rfl | rfl
        · exfalso
          rw [hd₁'] at h₁₂pos
          nlinarith [h₁₂pos]
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, rfl⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, rfl⟩)))))
        · exfalso
          rw [hd₁'] at h₁₂pos
          nlinarith [h₁₂pos]
      · -- `v₂ = 1` and `v₃` even: the cells `(2p, p)` and `(−p, −2p)`
        have hv₂1 : v₂ = 1 := by
          by_contra hc
          have hv₂2 : 2 ≤ v₂ := by
            obtain ⟨w, hw⟩ := hv₂o
            omega
          have hv₃1 : v₃ = 1 := by
            by_contra hc2
            exact hpair₂₃ ⟨hv₂2, by omega⟩
          obtain ⟨w, hw⟩ := hv₂o
          omega
        have hv₃e : Even v₃ := by
          rw [hV1, hv₂1] at hvsum
          exact ⟨padicValRat p y - 1, by omega⟩
        obtain ⟨d₂', hd₂', hd₂'free, hd₂'v, hd₂'0, -⟩ :
            ∃ d' : ℤ, d₂ = (p : ℤ) * d' ∧ ¬ (p : ℤ) ∣ d' ∧ d'.natAbs ∣ 2 * p ∧
              d' ≠ 0 ∧ padicValRat p ((d₂ : ℤ) : ℚ) = 1 := by
          rcases rung_split (by omega) h₂0 h₂v with ⟨hf, hv0⟩ | ⟨-, hr⟩
          · exfalso
            rw [hv0] at he₂
            omega
          · exact hr
        set z₂ : ℚ := (x - ((p : ℕ) : ℚ)) / ((p : ℕ) : ℚ) with hz₂
        have hz₂0 : z₂ ≠ 0 := div_ne_zero hxm0 hpq0
        have hvz₂ : padicValRat p z₂ = 0 := by
          rw [hz₂, padicValRat.div hxm0 hpq0, hvp]
          omega
        have hsqz₂ : Descent.SqCls z₂ ((d₂' : ℤ) : ℚ) := by
          obtain ⟨c, hc, hcv⟩ := h₂
          refine ⟨c, hc, ?_⟩
          rw [hz₂, hcv, hd₂']
          push_cast
          field_simp
          try ring
        have hrz₂ := chiRead_of_sqcls hz₂0 hvz₂ hd₂'free hsqz₂
        have hv₃2 : 2 ≤ v₃ := by
          obtain ⟨w, hw⟩ := hv₃e
          omega
        have hcong₁ : chiRead p z₁ = chiRead p (((-1 : ℤ)) : ℚ) := by
          refine chiRead_congr hz₁0 (by norm_num) hvz₁ (int_val_zero hndm1) ?_
          have hd : z₁ - (((-1 : ℤ)) : ℚ) = (x + ((p : ℕ) : ℚ)) / ((p : ℕ) : ℚ) := by
            rw [hz₁]
            push_cast
            field_simp
            try ring
          rw [hd, padicValRat.div hxp0 hpq0, hvp]
          omega
        have hcong₂ : chiRead p z₂ = chiRead p (((-2 : ℤ)) : ℚ) := by
          refine chiRead_congr hz₂0 (by norm_num) hvz₂ (int_val_zero hndm2) ?_
          have hd : z₂ - (((-2 : ℤ)) : ℚ) = (x + ((p : ℕ) : ℚ)) / ((p : ℕ) : ℚ) := by
            rw [hz₂]
            push_cast
            field_simp
            try ring
          rw [hd, padicValRat.div hxp0 hpq0, hvp]
          omega
        have hchi₁' : quadraticChar (ZMod p) ((d₁' : ZMod p)) = -1 := by
          rw [← hrz₁, hcong₁, chiRead_intCast, chi_neg_one hp8]
        have hchi₂' : quadraticChar (ZMod p) ((d₂' : ZMod p)) = 1 := by
          rw [← hrz₂, hcong₂, chiRead_intCast, chi_neg_two hp8]
        rcases rung_char_neg_one hp8 hd₁'0 hd₁'v hd₁'free hchi₁' with rfl | rfl <;>
          rcases rung_char_one hp8 hd₂'0 hd₂'v hd₂'free hchi₂' with rfl | rfl
        · exfalso
          rw [hd₁', hd₂'] at h₁₂pos
          nlinarith [h₁₂pos]
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨by omega, by omega⟩))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨by omega, by omega⟩))))))
        · exfalso
          rw [hd₁', hd₂'] at h₁₂pos
          nlinarith [h₁₂pos]



/-! ## 5. The two-adic refusal of the coset cell -/

private lemma odd_sq_mod_eight {A : ℤ} (h : A % 2 = 1) : A ^ 2 % 8 = 1 := by
  have h8 : A % 8 = 1 ∨ A % 8 = 3 ∨ A % 8 = 5 ∨ A % 8 = 7 := by omega
  conv_lhs => rw [pow_two, Int.mul_emod]
  rcases h8 with h | h | h | h <;> rw [h] <;> norm_num

private lemma odd_mul {A B : ℤ} (hA : A % 2 = 1) (hB : B % 2 = 1) :
    (A * B) % 2 = 1 := by
  rw [Int.mul_emod, hA, hB]
  norm_num

/-- The two-adic valuation of a difference of two-adic-unit squares is at least
three: odd squares agree mod eight. -/
private lemma unit_sq_diff_val {τ σ : ℚ} (hτ : τ ≠ 0) (hσ : σ ≠ 0)
    (hvτ : padicValRat 2 τ = 0) (hvσ : padicValRat 2 σ = 0)
    (hne : τ ^ 2 - σ ^ 2 ≠ 0) :
    3 ≤ padicValRat 2 (τ ^ 2 - σ ^ 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hτn, hτd⟩ := val_zero_parts (p := 2) hτ hvτ
  obtain ⟨hσn, hσd⟩ := val_zero_parts (p := 2) hσ hvσ
  have hA : τ.num % 2 = 1 := by omega
  have hC : σ.num % 2 = 1 := by omega
  have hB : (τ.den : ℤ) % 2 = 1 := by
    have h1 : ¬ (2 : ℤ) ∣ (τ.den : ℤ) := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, Int.natCast_dvd_natCast]
      exact hτd
    omega
  have hD : (σ.den : ℤ) % 2 = 1 := by
    have h1 : ¬ (2 : ℤ) ∣ (σ.den : ℤ) := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, Int.natCast_dvd_natCast]
      exact hσd
    omega
  set M : ℤ := τ.num ^ 2 * (σ.den : ℤ) ^ 2 - σ.num ^ 2 * (τ.den : ℤ) ^ 2 with hM
  have hτnum : (τ.num : ℚ) = τ * τ.den := (Rat.mul_den_eq_num τ).symm
  have hσnum : (σ.num : ℚ) = σ * σ.den := (Rat.mul_den_eq_num σ).symm
  have hMq : ((M : ℤ) : ℚ)
      = (τ ^ 2 - σ ^ 2) * ((τ.den : ℚ) ^ 2 * (σ.den : ℚ) ^ 2) := by
    rw [hM]
    push_cast
    rw [hτnum, hσnum]
    ring
  have hden1 : ((τ.den : ℚ)) ≠ 0 := by exact_mod_cast τ.den_nz
  have hden2 : ((σ.den : ℚ)) ≠ 0 := by exact_mod_cast σ.den_nz
  have hM0 : M ≠ 0 := by
    intro h0
    rw [h0] at hMq
    have h1 : (τ ^ 2 - σ ^ 2) * ((τ.den : ℚ) ^ 2 * (σ.den : ℚ) ^ 2) = 0 := by
      exact_mod_cast hMq.symm
    rcases mul_eq_zero.mp h1 with h | h
    · exact hne h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact hden1 (pow_eq_zero_iff two_ne_zero |>.mp h')
      · exact hden2 (pow_eq_zero_iff two_ne_zero |>.mp h')
  have hMsq : M = (τ.num * (σ.den : ℤ)) ^ 2 - (σ.num * (τ.den : ℤ)) ^ 2 := by
    rw [hM]
    ring
  have h1 := odd_sq_mod_eight (odd_mul hA hD)
  have h2 := odd_sq_mod_eight (odd_mul hC hB)
  have hdvd : (8 : ℤ) ∣ M := by
    rw [hMsq]
    omega
  have hvM : 3 ≤ padicValInt 2 M := by
    have h3 := (padicValInt_dvd_iff (p := 2) 3 M).mp (by
      norm_num
      exact hdvd)
    rcases h3 with h | h
    · exact absurd h hM0
    · exact h
  have hvden : padicValRat 2 (((τ.den : ℚ)) ^ 2 * ((σ.den : ℚ)) ^ 2) = 0 := by
    rw [padicValRat.mul (pow_ne_zero 2 hden1) (pow_ne_zero 2 hden2),
      padicValRat.pow hden1, padicValRat.pow hden2,
      nat_den_val_zero (p := 2) hτd, nat_den_val_zero (p := 2) hσd]
    ring
  have heq : τ ^ 2 - σ ^ 2
      = ((M : ℤ) : ℚ) / (((τ.den : ℚ)) ^ 2 * ((σ.den : ℚ)) ^ 2) := by
    rw [eq_div_iff (by positivity)]
    linear_combination -hMq
  rw [heq, padicValRat.div (by exact_mod_cast hM0) (by positivity), hvden,
    padicValRat.of_int]
  omega

set_option maxHeartbeats 1000000 in
/-- **THE COSET CELL IS REFUSED AT TWO**: no point of `y² = x³ − p²x` with `y ≠ 0`
carries the slot classes `(−2, −2)`, at any odd `p` — the two equations
`w² + 2s² = p` and `2t² − 2s² = p` are two-adically incompatible.  Since the descent
image is a group and the four non-torsion cells form one coset of the torsion image,
this single refusal empties the coset. -/
theorem theCosetCellIsRefusedAtTwo (hpodd : p % 2 = 1) {x y : ℚ}
    (hcurve : y ^ 2 = x ^ 3 - ((p : ℕ) : ℚ) ^ 2 * x) (hy : y ≠ 0)
    (h₁ : Descent.SqCls x ((-2 : ℤ) : ℚ))
    (h₂ : Descent.SqCls (x - ((p : ℕ) : ℚ)) ((-2 : ℤ) : ℚ)) :
    False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := Fact.out
  have hpq0 : (((p : ℕ) : ℚ)) ≠ 0 := by exact_mod_cast hp.pos.ne'
  obtain ⟨hx0, hxn, hxmn⟩ :=
    FaceHomomorphism.theNonzeroOrdinateAvoidsTheRoots hcurve hy
  have hxm0 : x - ((p : ℕ) : ℚ) ≠ 0 := sub_ne_zero.mpr hxn
  have hxp0 : x + ((p : ℕ) : ℚ) ≠ 0 := fun hc => hxmn (by linarith)
  have h₃ : Descent.SqCls (x + ((p : ℕ) : ℚ)) (((-2 * -2 : ℤ)) : ℚ) :=
    sqcls_third hcurve hy hx0 hxm0 h₁ h₂
  obtain ⟨s, hs, hsv⟩ := h₁
  obtain ⟨t, ht, htv⟩ := h₂
  obtain ⟨c, hc, hcv⟩ := h₃
  set w : ℚ := 2 * c with hw
  have hw0 : w ≠ 0 := by
    rw [hw]
    exact mul_ne_zero two_ne_zero hc
  have hwv : x + ((p : ℕ) : ℚ) = w ^ 2 := by
    rw [hw]
    push_cast at hcv
    linarith [hcv]
  have hxs : x = -2 * s ^ 2 := by
    push_cast at hsv
    linarith [hsv]
  have hxt : x - ((p : ℕ) : ℚ) = -2 * t ^ 2 := by
    push_cast at htv
    linarith [htv]
  have heq2 : w ^ 2 + 2 * s ^ 2 = ((p : ℕ) : ℚ) := by
    linarith [hwv, hxs]
  have heq1 : t ^ 2 - s ^ 2 = ((p : ℕ) : ℚ) / 2 := by
    field_simp
    linarith [hxt, hxs]
  -- valuations at two
  have hvp2 : padicValRat 2 (((p : ℕ) : ℚ)) = 0 := by
    have hnd : ¬ (2 : ℤ) ∣ ((p : ℕ) : ℤ) := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, Int.natCast_dvd_natCast]
      omega
    have := int_val_zero (p := 2) hnd
    push_cast at this ⊢
    exact this
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0] at hxs
    norm_num at hxs
    exact hx0 hxs
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0] at hxt
    norm_num at hxt
    exact hxm0 hxt
  have hv2 : padicValRat 2 ((2 : ℚ)) = 1 := by
    have := padicValRat.self (p := 2) (by norm_num)
    push_cast at this ⊢
    exact this
  set a : ℤ := padicValRat 2 s with ha
  set b : ℤ := padicValRat 2 t with hb
  set cw : ℤ := padicValRat 2 w with hcw
  have hv2s : padicValRat 2 (2 * s ^ 2) = 1 + 2 * a := by
    rw [padicValRat.mul two_ne_zero (pow_ne_zero 2 hs0), hv2,
      padicValRat.pow hs0]
    ring
  have hvw2 : padicValRat 2 (w ^ 2) = 2 * cw := by
    rw [padicValRat.pow hw0]
    ring
  -- the second equation forces `w` a unit and `s` integral
  have h2s0 : (2 : ℚ) * s ^ 2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hs0)
  have hcwa : cw = 0 ∧ 0 ≤ a := by
    rcases lt_trichotomy (2 * cw) (1 + 2 * a) with h | h | h
    · have hval := FamilySupport.val_add_left (ℓ := 2) (pow_ne_zero 2 hw0)
        (by rw [heq2]; exact hpq0) (by rw [hvw2, hv2s]; omega)
      rw [heq2, hvp2, hvw2] at hval
      omega
    · omega
    · have hval := FamilySupport.val_add_left (ℓ := 2) h2s0
        (by rw [show 2 * s ^ 2 + w ^ 2 = w ^ 2 + 2 * s ^ 2 from by ring, heq2]
            exact hpq0)
        (by rw [hvw2, hv2s]; omega)
      rw [show 2 * s ^ 2 + w ^ 2 = w ^ 2 + 2 * s ^ 2 from by ring, heq2, hvp2,
        hv2s] at hval
      omega
  obtain ⟨hcw0, ha0⟩ := hcwa
  -- the first equation forces valuation `−1` on the square difference
  have hdiff0 : t ^ 2 - s ^ 2 ≠ 0 := by
    rw [heq1]
    intro h0
    rcases div_eq_zero_iff.mp h0 with h | h
    · exact hpq0 h
    · norm_num at h
  have hvdiff : padicValRat 2 (t ^ 2 - s ^ 2) = -1 := by
    rw [heq1, padicValRat.div hpq0 two_ne_zero, hvp2, hv2]
    ring
  rcases eq_or_ne a b with hab | hab
  · -- equal valuations: the odd-square gap refuses
    set k : ℕ := a.toNat with hk
    have hka : (k : ℤ) = a := Int.toNat_of_nonneg ha0
    have h2k : ((2 : ℚ)) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
    set τ : ℚ := t / 2 ^ k with hτ
    set σ : ℚ := s / 2 ^ k with hσ
    have hτ0 : τ ≠ 0 := div_ne_zero ht0 h2k
    have hσ0 : σ ≠ 0 := div_ne_zero hs0 h2k
    have hv2k : padicValRat 2 (((2 : ℚ)) ^ k) = k := by
      rw [padicValRat.pow two_ne_zero, hv2]
      ring
    have hvτ : padicValRat 2 τ = 0 := by
      rw [hτ, padicValRat.div ht0 h2k, hv2k]
      omega
    have hvσ : padicValRat 2 σ = 0 := by
      rw [hσ, padicValRat.div hs0 h2k, hv2k]
      omega
    have hsplit : t ^ 2 - s ^ 2 = ((2 : ℚ)) ^ (2 * k) * (τ ^ 2 - σ ^ 2) := by
      rw [hτ, hσ]
      field_simp
      ring
    have hτσ0 : τ ^ 2 - σ ^ 2 ≠ 0 := by
      intro h0
      rw [hsplit, h0, mul_zero] at hdiff0
      exact hdiff0 rfl
    have hge := unit_sq_diff_val hτ0 hσ0 hvτ hvσ hτσ0
    have hvsplit : padicValRat 2 (t ^ 2 - s ^ 2)
        = 2 * k + padicValRat 2 (τ ^ 2 - σ ^ 2) := by
      rw [hsplit, padicValRat.mul (pow_ne_zero _ two_ne_zero) hτσ0,
        padicValRat.pow two_ne_zero, hv2]
      push_cast
      ring
    rw [hvdiff] at hvsplit
    omega
  · -- distinct valuations: the parity of the minimum refuses
    have hvt2 : padicValRat 2 (t ^ 2) = 2 * b := by
      rw [padicValRat.pow ht0]
      ring
    have hvs2 : padicValRat 2 (-(s ^ 2)) = 2 * a := by
      rw [padicValRat.neg, padicValRat.pow hs0]
      ring
    have hns0 : -(s ^ 2) ≠ 0 := neg_ne_zero.mpr (pow_ne_zero 2 hs0)
    rcases lt_or_gt_of_ne (show 2 * b ≠ 2 * a from by omega) with h | h
    · have hval := FamilySupport.val_add_left (ℓ := 2) (pow_ne_zero 2 ht0)
        (by rw [show t ^ 2 + -(s ^ 2) = t ^ 2 - s ^ 2 from by ring]
            exact hdiff0)
        (by rw [hvt2, hvs2]; omega)
      rw [show t ^ 2 + -(s ^ 2) = t ^ 2 - s ^ 2 from by ring, hvdiff, hvt2] at hval
      omega
    · have hval := FamilySupport.val_add_left (ℓ := 2) hns0
        (by rw [show -(s ^ 2) + t ^ 2 = t ^ 2 - s ^ 2 from by ring]
            exact hdiff0)
        (by rw [hvt2, hvs2]; omega)
      rw [show -(s ^ 2) + t ^ 2 = t ^ 2 - s ^ 2 from by ring, hvdiff, hvs2] at hval
      omega



/-! ## 6. The two-torsion points and the coset transport -/

open WeierstrassCurve.Affine
open Soma.Holonics.Millennium.FamilyKernel
open Soma.Holonics.Millennium.FamilySupport

private lemma hnq' (hp : p.Prime) : (0 : ℚ) < ((p : ℕ) : ℚ) := by
  exact_mod_cast hp.pos

private lemma nonsing00 (hp : p.Prime) :
    (FamilyFace.E (((p : ℕ) : ℚ))).Nonsingular 0 0 := by
  have h := hnq' hp
  rw [nonsingular_iff, equation_iff]
  constructor
  · simp [FamilyFace.E]
  · left
    simp only [FamilyFace.E]
    intro hc
    nlinarith [hc, h]

private lemma nonsingP (hp : p.Prime) :
    (FamilyFace.E (((p : ℕ) : ℚ))).Nonsingular (((p : ℕ) : ℚ)) 0 := by
  have h := hnq' hp
  rw [nonsingular_iff, equation_iff]
  constructor
  · simp only [FamilyFace.E]
    ring
  · left
    simp only [FamilyFace.E]
    intro hc
    nlinarith [hc, h]

private lemma nonsingMP (hp : p.Prime) :
    (FamilyFace.E (((p : ℕ) : ℚ))).Nonsingular (-((p : ℕ) : ℚ)) 0 := by
  have h := hnq' hp
  rw [nonsingular_iff, equation_iff]
  constructor
  · simp only [FamilyFace.E]
    ring
  · left
    simp only [FamilyFace.E]
    intro hc
    nlinarith [hc, h]

private lemma double_zero_of_Y_zero {x : ℚ}
    (h : (FamilyFace.E (((p : ℕ) : ℚ))).Nonsingular x 0) :
    Point.some h + Point.some h = 0 :=
  Point.add_self_of_Y_eq (by simp [negY, FamilyFace.E])

private lemma affine_not_two_torsion {x y : ℚ}
    (h : (FamilyFace.E (((p : ℕ) : ℚ))).Nonsingular x y) (hy : y ≠ 0) :
    Point.some h + Point.some h ≠ 0 := by
  intro h0
  have h1 : Point.some h = -(Point.some h) := eq_neg_of_add_eq_zero_left h0
  rw [Point.neg_some] at h1
  simp only [Point.some.injEq] at h1
  have hyy := h1.2
  simp only [negY, FamilyFace.E] at hyy
  apply hy
  linarith [hyy]

set_option maxHeartbeats 4000000 in
/-- **The coset is refused whole**: a `y ≠ 0` point carrying any of the four
non-torsion cells transports, by adding the matching two-torsion point, onto the
`(−2, −2)` cell — which is refused at two. -/
private theorem coset_refused (hp8 : p % 8 = 3) {x y : ℚ}
    (h : (FamilyFace.E (((p : ℕ) : ℚ))).Nonsingular x y) (hy : y ≠ 0)
    {d₁ d₂ : ℤ}
    (h₁ : Descent.SqCls x ((d₁ : ℤ) : ℚ))
    (h₂ : Descent.SqCls (x - ((p : ℕ) : ℚ)) ((d₂ : ℤ) : ℚ))
    (hcell : (d₁ = -2 ∧ d₂ = -2) ∨ (d₁ = 2 ∧ d₂ = 2 * p) ∨
      (d₁ = 2 * (p : ℤ) ∧ d₂ = (p : ℤ)) ∨ (d₁ = -2 * p ∧ d₂ = -1)) :
    False := by
  have hp : p.Prime := Fact.out
  have hpodd : p % 2 = 1 := by omega
  have hnq : (0 : ℚ) < ((p : ℕ) : ℚ) := hnq' hp
  have hpq0 : (((p : ℕ) : ℚ)) ≠ 0 := hnq.ne'
  obtain ⟨hx0, hxn, hxmn⟩ :=
    FaceHomomorphism.theNonzeroOrdinateAvoidsTheRoots (onCurveAt h) hy
  obtain ⟨c₁, hc₁, hv₁⟩ := h₁
  obtain ⟨c₂, hc₂, hv₂⟩ := h₂
  rcases hcell with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact theCosetCellIsRefusedAtTwo hpodd (onCurveAt h) hy
      ⟨c₁, hc₁, hv₁⟩ ⟨c₂, hc₂, hv₂⟩
  · -- cell (2, 2p): translate by (0, 0)
    have hT0 := nonsing00 hp
    have hT2 : Point.some hT0 + Point.some hT0 = 0 := double_zero_of_Y_zero hT0
    obtain ⟨hom1, hom2⟩ :=
      FamilyHom.theFaceIsAHomomorphismAtEveryModulus (((p : ℕ) : ℚ)) hnq
        (Point.some h) (Point.some hT0)
    rw [slotOneAt_some h, slotOneAt_some hT0, if_neg hx0, if_pos rfl] at hom1
    rw [slotTwoAt_some h, slotTwoAt_some hT0, if_neg hxn, if_neg hnq.ne] at hom2
    rcases hPT : Point.some h + Point.some hT0 with _ | @⟨x', y', h'⟩
    · have h1 : Point.some h = -(Point.some hT0) := eq_neg_of_add_eq_zero_left hPT
      rw [neg_eq_of_add_eq_zero_left hT2] at h1
      simp only [Point.some.injEq] at h1
      exact hx0 h1.1
    · rw [hPT] at hom1 hom2
      by_cases hy' : y' = 0
      · subst hy'
        have hP'2 : Point.some h' + Point.some h' = 0 := double_zero_of_Y_zero h'
        have hPP : Point.some h + Point.some h = 0 := by
          have he : Point.some h = Point.some h' - Point.some hT0 := by
            rw [← hPT]
            abel
          rw [he, show Point.some h' - Point.some hT0 +
              (Point.some h' - Point.some hT0)
              = Point.some h' + Point.some h' -
                (Point.some hT0 + Point.some hT0) from by abel,
            hP'2, hT2, sub_zero]
        exact affine_not_two_torsion h hy hPP
      · obtain ⟨hx'0, hx'n, -⟩ :=
          FaceHomomorphism.theNonzeroOrdinateAvoidsTheRoots (onCurveAt h') hy'
        rw [slotOneAt_some h', if_neg hx'0] at hom1
        rw [slotTwoAt_some h', if_neg hx'n] at hom2
        refine theCosetCellIsRefusedAtTwo hpodd (onCurveAt h') hy'
          (FamilyCollision.sqcls_trans hom1
            ⟨c₁ * ((p : ℕ) : ℚ), mul_ne_zero hc₁ hpq0, by
              rw [hv₁]; push_cast; ring⟩)
          (FamilyCollision.sqcls_trans hom2
            ⟨c₂ * ((p : ℕ) : ℚ), mul_ne_zero hc₂ hpq0, by
              rw [hv₂]; push_cast; ring⟩)
  · -- cell (2p, p): translate by (−p, 0)
    have hT0 := nonsingMP hp
    have hT2 : Point.some hT0 + Point.some hT0 = 0 := double_zero_of_Y_zero hT0
    obtain ⟨hom1, hom2⟩ :=
      FamilyHom.theFaceIsAHomomorphismAtEveryModulus (((p : ℕ) : ℚ)) hnq
        (Point.some h) (Point.some hT0)
    rw [slotOneAt_some h, slotOneAt_some hT0, if_neg hx0,
      if_neg (neg_ne_zero.mpr hpq0)] at hom1
    rw [slotTwoAt_some h, slotTwoAt_some hT0, if_neg hxn,
      if_neg (show ¬(-((p : ℕ) : ℚ)) = ((p : ℕ) : ℚ) from fun hc =>
        hpq0 (by linarith))] at hom2
    rcases hPT : Point.some h + Point.some hT0 with _ | @⟨x', y', h'⟩
    · have h1 : Point.some h = -(Point.some hT0) := eq_neg_of_add_eq_zero_left hPT
      rw [neg_eq_of_add_eq_zero_left hT2] at h1
      simp only [Point.some.injEq] at h1
      exact hxmn h1.1
    · rw [hPT] at hom1 hom2
      by_cases hy' : y' = 0
      · subst hy'
        have hP'2 : Point.some h' + Point.some h' = 0 := double_zero_of_Y_zero h'
        have hPP : Point.some h + Point.some h = 0 := by
          have he : Point.some h = Point.some h' - Point.some hT0 := by
            rw [← hPT]
            abel
          rw [he, show Point.some h' - Point.some hT0 +
              (Point.some h' - Point.some hT0)
              = Point.some h' + Point.some h' -
                (Point.some hT0 + Point.some hT0) from by abel,
            hP'2, hT2, sub_zero]
        exact affine_not_two_torsion h hy hPP
      · obtain ⟨hx'0, hx'n, -⟩ :=
          FaceHomomorphism.theNonzeroOrdinateAvoidsTheRoots (onCurveAt h') hy'
        rw [slotOneAt_some h', if_neg hx'0] at hom1
        rw [slotTwoAt_some h', if_neg hx'n] at hom2
        refine theCosetCellIsRefusedAtTwo hpodd (onCurveAt h') hy'
          (FamilyCollision.sqcls_trans hom1
            ⟨c₁ * ((p : ℕ) : ℚ), mul_ne_zero hc₁ hpq0, by
              rw [hv₁]; push_cast; ring⟩)
          (FamilyCollision.sqcls_trans hom2
            ⟨c₂ * ((p : ℕ) : ℚ), mul_ne_zero hc₂ hpq0, by
              rw [hv₂]; push_cast; ring⟩)
  · -- cell (−2p, −1): translate by (p, 0)
    have hT0 := nonsingP hp
    have hT2 : Point.some hT0 + Point.some hT0 = 0 := double_zero_of_Y_zero hT0
    obtain ⟨hom1, hom2⟩ :=
      FamilyHom.theFaceIsAHomomorphismAtEveryModulus (((p : ℕ) : ℚ)) hnq
        (Point.some h) (Point.some hT0)
    rw [slotOneAt_some h, slotOneAt_some hT0, if_neg hx0, if_neg hpq0] at hom1
    rw [slotTwoAt_some h, slotTwoAt_some hT0, if_neg hxn, if_pos rfl] at hom2
    rcases hPT : Point.some h + Point.some hT0 with _ | @⟨x', y', h'⟩
    · have h1 : Point.some h = -(Point.some hT0) := eq_neg_of_add_eq_zero_left hPT
      rw [neg_eq_of_add_eq_zero_left hT2] at h1
      simp only [Point.some.injEq] at h1
      exact hxn h1.1
    · rw [hPT] at hom1 hom2
      by_cases hy' : y' = 0
      · subst hy'
        have hP'2 : Point.some h' + Point.some h' = 0 := double_zero_of_Y_zero h'
        have hPP : Point.some h + Point.some h = 0 := by
          have he : Point.some h = Point.some h' - Point.some hT0 := by
            rw [← hPT]
            abel
          rw [he, show Point.some h' - Point.some hT0 +
              (Point.some h' - Point.some hT0)
              = Point.some h' + Point.some h' -
                (Point.some hT0 + Point.some hT0) from by abel,
            hP'2, hT2, sub_zero]
        exact affine_not_two_torsion h hy hPP
      · obtain ⟨hx'0, hx'n, -⟩ :=
          FaceHomomorphism.theNonzeroOrdinateAvoidsTheRoots (onCurveAt h') hy'
        rw [slotOneAt_some h', if_neg hx'0] at hom1
        rw [slotTwoAt_some h', if_neg hx'n] at hom2
        refine theCosetCellIsRefusedAtTwo hpodd (onCurveAt h') hy'
          (FamilyCollision.sqcls_trans hom1
            ⟨c₁ * ((p : ℕ) : ℚ), mul_ne_zero hc₁ hpq0, by
              rw [hv₁]; push_cast; ring⟩)
          (FamilyCollision.sqcls_trans hom2
            ⟨c₂ * ((p : ℕ) : ℚ), mul_ne_zero hc₂ hpq0, by
              rw [hv₂]; push_cast; ring⟩)


/-! ## 7. The descent step and Genocchi's law -/

set_option maxHeartbeats 4000000 in
/-- **THE DESCENT STEP ON THE THREE-MOD-EIGHT BRANCH**: every rational point of
`y² = x³ − p²x` is a double plus a two-torsion point — the four surviving cells are
exactly the two-torsion cells, and each strips off through the kernel. -/
theorem theDescentStepOnTheThreeModEightBranch (hp8 : p % 8 = 3)
    (P : (FamilyFace.E (((p : ℕ) : ℚ))).Point) :
    ∃ Q T : (FamilyFace.E (((p : ℕ) : ℚ))).Point, (T + T = 0) ∧ P = Q + Q + T := by
  have hp : p.Prime := Fact.out
  have hnq : (0 : ℚ) < ((p : ℕ) : ℚ) := hnq' hp
  have hpq0 : (((p : ℕ) : ℚ)) ≠ 0 := hnq.ne'
  rcases P with _ | @⟨x, y, h⟩
  · exact ⟨0, 0, by rw [add_zero], by rw [add_zero, add_zero, ← Point.zero_def]⟩
  · by_cases hy : y = 0
    · subst hy
      exact ⟨0, Point.some h, double_zero_of_Y_zero h, by rw [add_zero, zero_add]⟩
    · obtain ⟨hx0, hxn, hxmn⟩ :=
        FaceHomomorphism.theNonzeroOrdinateAvoidsTheRoots (onCurveAt h) hy
      obtain ⟨d₁, d₂, h₁0, h₂0, h₁v, h₂v, h₁s, h₂s⟩ :=
        FamilySupport.theSlotClassesAreSupportedAtEveryModulus p hp.pos
          (Point.some h)
      rw [slotOneAt_some h, if_neg hx0] at h₁s
      rw [slotTwoAt_some h, if_neg hxn] at h₂s
      have hcells := theSlotClassesCollapseOnTheThreeModEightBranch hp8
        (onCurveAt h) hy h₁0 h₂0 h₁v h₂v h₁s h₂s
      obtain ⟨c₁, hc₁, hv₁⟩ := h₁s
      obtain ⟨c₂, hc₂, hv₂⟩ := h₂s
      rcases hcells with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · -- cell (1, 1): the point is already a double
        obtain ⟨Q, hQ⟩ := theKernelIsTheDoublesAtEveryModulus (((p : ℕ) : ℚ)) hnq
          (Point.some h)
          (by rw [slotOneAt_some h, if_neg hx0, hv₁]
              exact ⟨c₁, hc₁, by push_cast; ring⟩)
          (by rw [slotTwoAt_some h, if_neg hxn, hv₂]
              exact ⟨c₂, hc₂, by push_cast; ring⟩)
        exact ⟨Q, 0, by rw [add_zero], by rw [add_zero, hQ]⟩
      · exact (coset_refused hp8 h hy
          ⟨c₁, hc₁, hv₁⟩ ⟨c₂, hc₂, hv₂⟩ (Or.inl ⟨rfl, rfl⟩)).elim
      · -- cell (−1, −p): strip the point (0, 0)
        have hT0 := nonsing00 hp
        have hT2 : Point.some hT0 + Point.some hT0 = 0 := double_zero_of_Y_zero hT0
        obtain ⟨hom1, hom2⟩ :=
          FamilyHom.theFaceIsAHomomorphismAtEveryModulus (((p : ℕ) : ℚ)) hnq
            (Point.some h) (Point.some hT0)
        rw [slotOneAt_some h, slotOneAt_some hT0, if_neg hx0, if_pos rfl] at hom1
        rw [slotTwoAt_some h, slotTwoAt_some hT0, if_neg hxn, if_neg hnq.ne]
          at hom2
        obtain ⟨Q, hQ⟩ := theKernelIsTheDoublesAtEveryModulus (((p : ℕ) : ℚ)) hnq
          (Point.some h + Point.some hT0)
          (FamilyCollision.sqcls_trans hom1
            ⟨c₁ * ((p : ℕ) : ℚ), mul_ne_zero hc₁ hpq0, by
              rw [hv₁]; push_cast; ring⟩)
          (FamilyCollision.sqcls_trans hom2
            ⟨c₂ * ((p : ℕ) : ℚ), mul_ne_zero hc₂ hpq0, by
              rw [hv₂]; push_cast; ring⟩)
        refine ⟨Q, Point.some hT0, hT2, ?_⟩
        have h1 : Point.some h = Q + Q - Point.some hT0 := eq_sub_of_add_eq hQ.symm
        rw [h1, sub_eq_add_neg, neg_eq_of_add_eq_zero_left hT2]
      · exact (coset_refused hp8 h hy
          ⟨c₁, hc₁, hv₁⟩ ⟨c₂, hc₂, hv₂⟩ (Or.inr (Or.inl ⟨rfl, rfl⟩))).elim
      · -- cell (p, 2): strip the point (p, 0)
        have hT0 := nonsingP hp
        have hT2 : Point.some hT0 + Point.some hT0 = 0 := double_zero_of_Y_zero hT0
        obtain ⟨hom1, hom2⟩ :=
          FamilyHom.theFaceIsAHomomorphismAtEveryModulus (((p : ℕ) : ℚ)) hnq
            (Point.some h) (Point.some hT0)
        rw [slotOneAt_some h, slotOneAt_some hT0, if_neg hx0, if_neg hpq0] at hom1
        rw [slotTwoAt_some h, slotTwoAt_some hT0, if_neg hxn, if_pos rfl] at hom2
        obtain ⟨Q, hQ⟩ := theKernelIsTheDoublesAtEveryModulus (((p : ℕ) : ℚ)) hnq
          (Point.some h + Point.some hT0)
          (FamilyCollision.sqcls_trans hom1
            ⟨c₁ * ((p : ℕ) : ℚ), mul_ne_zero hc₁ hpq0, by
              rw [hv₁]; push_cast; ring⟩)
          (FamilyCollision.sqcls_trans hom2
            ⟨2 * c₂ * ((p : ℕ) : ℚ),
              mul_ne_zero (mul_ne_zero two_ne_zero hc₂) hpq0, by
              rw [hv₂]; push_cast; ring⟩)
        refine ⟨Q, Point.some hT0, hT2, ?_⟩
        have h1 : Point.some h = Q + Q - Point.some hT0 := eq_sub_of_add_eq hQ.symm
        rw [h1, sub_eq_add_neg, neg_eq_of_add_eq_zero_left hT2]
      · exact (coset_refused hp8 h hy
          ⟨c₁, hc₁, hv₁⟩ ⟨c₂, hc₂, hv₂⟩ (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))).elim
      · exact (coset_refused hp8 h hy
          ⟨c₁, hc₁, hv₁⟩ ⟨c₂, hc₂, hv₂⟩ (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))).elim
      · -- cell (−p, −2p): strip the point (−p, 0)
        have hT0 := nonsingMP hp
        have hT2 : Point.some hT0 + Point.some hT0 = 0 := double_zero_of_Y_zero hT0
        obtain ⟨hom1, hom2⟩ :=
          FamilyHom.theFaceIsAHomomorphismAtEveryModulus (((p : ℕ) : ℚ)) hnq
            (Point.some h) (Point.some hT0)
        rw [slotOneAt_some h, slotOneAt_some hT0, if_neg hx0,
          if_neg (neg_ne_zero.mpr hpq0)] at hom1
        rw [slotTwoAt_some h, slotTwoAt_some hT0, if_neg hxn,
          if_neg (show ¬(-((p : ℕ) : ℚ)) = ((p : ℕ) : ℚ) from fun hc =>
            hpq0 (by linarith))] at hom2
        obtain ⟨Q, hQ⟩ := theKernelIsTheDoublesAtEveryModulus (((p : ℕ) : ℚ)) hnq
          (Point.some h + Point.some hT0)
          (FamilyCollision.sqcls_trans hom1
            ⟨c₁ * ((p : ℕ) : ℚ), mul_ne_zero hc₁ hpq0, by
              rw [hv₁]; push_cast; ring⟩)
          (FamilyCollision.sqcls_trans hom2
            ⟨2 * c₂ * ((p : ℕ) : ℚ),
              mul_ne_zero (mul_ne_zero two_ne_zero hc₂) hpq0, by
              rw [hv₂]; push_cast; ring⟩)
        refine ⟨Q, Point.some hT0, hT2, ?_⟩
        have h1 : Point.some h = Q + Q - Point.some hT0 := eq_sub_of_add_eq hQ.symm
        rw [h1, sub_eq_add_neg, neg_eq_of_add_eq_zero_left hT2]

open DirectSum in
set_option maxHeartbeats 4000000 in
/-- **GENOCCHI'S LAW, FAMILY-WISE: THE RANK VANISHES ON THE THREE-MOD-EIGHT
BRANCH.**  At every prime `p ≡ 3 (mod 8)`, no rational point of `y² = x³ − p²x` is
of infinite order: the free part of any point is infinitely two-divisible through
the descent step, hence zero.  Genocchi (1855), kernel-checked with the modulus a
parameter. -/
theorem theRankVanishesOnTheThreeModEightBranch (hp8 : p % 8 = 3) :
    ¬ BirchSwinnertonDyer.AlgebraicRankAtLeast p 1 := by
  intro hR
  unfold BirchSwinnertonDyer.AlgebraicRankAtLeast
    BirchSwinnertonDyer.IndependentModTorsion BirchSwinnertonDyer.IsTorsion at hR
  obtain ⟨Pts, hind⟩ := hR
  have hp : p.Prime := Fact.out
  haveI : AddGroup.FG ((FamilyFace.E (((p : ℕ) : ℚ))).Point) :=
    FamilyMordell.theMordellWeilTheoremAtEveryModulus p hp.pos
  obtain ⟨m, ι, hι, q, hq, e, ⟨F⟩⟩ :=
    AddCommGroup.equiv_free_prod_directSum_zmod ((FamilyFace.E (((p : ℕ) : ℚ))).Point)
  haveI := hι
  haveI : ∀ i, NeZero (q i ^ e i) := fun i => ⟨pow_ne_zero _ (hq i).pos.ne'⟩
  haveI : Finite (⨁ i, ZMod (q i ^ e i)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  have htor : ∀ X : (FamilyFace.E (((p : ℕ) : ℚ))).Point, (F X).1 = 0 →
      ∃ k : ℕ, 0 < k ∧ k • X = 0 := by
    intro X hX
    refine ⟨Nat.card (⨁ i, ZMod (q i ^ e i)), Nat.card_pos, ?_⟩
    apply F.injective
    rw [map_nsmul, map_zero]
    have h2 : (Nat.card (⨁ i, ZMod (q i ^ e i))) • F X
        = ((Nat.card (⨁ i, ZMod (q i ^ e i))) • (F X).1,
           (Nat.card (⨁ i, ZMod (q i ^ e i))) • (F X).2) := rfl
    rw [h2, hX, smul_zero, card_nsmul_eq_zero']
    rfl
  have hfreeT : ∀ T : (FamilyFace.E (((p : ℕ) : ℚ))).Point, T + T = 0 →
      (F T).1 = 0 := by
    intro T hT
    have h2 : F T + F T = 0 := by
      rw [← map_add, hT, map_zero]
    have h3 : (F T).1 + (F T).1 = 0 := by
      have h4 := congrArg Prod.fst h2
      simpa using h4
    ext j
    have h5 := DFunLike.congr_fun h3 j
    simp only [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply] at h5 ⊢
    omega
  have hdiv : ∀ (k : ℕ) (P : (FamilyFace.E (((p : ℕ) : ℚ))).Point),
      ∃ Q : (FamilyFace.E (((p : ℕ) : ℚ))).Point,
        (F P).1 = (2 ^ k : ℤ) • (F Q).1 := by
    intro k
    induction k with
    | zero => exact fun P => ⟨P, by simp⟩
    | succ n ih =>
        intro P
        obtain ⟨Q, T, hT2, hPQT⟩ := theDescentStepOnTheThreeModEightBranch hp8 P
        obtain ⟨R, hR⟩ := ih Q
        refine ⟨R, ?_⟩
        have hFP : (F P).1 = (F Q).1 + (F Q).1 + (F T).1 := by
          rw [hPQT, map_add, map_add]
          rfl
        rw [hfreeT T hT2, add_zero, hR] at hFP
        rw [hFP]
        rw [show ((2 : ℤ) ^ n • (F R).1 + (2 : ℤ) ^ n • (F R).1 : Fin m →₀ ℤ)
            = ((2 : ℤ) ^ (n + 1)) • (F R).1 from by
          rw [← two_smul ℤ, smul_smul]
          congr 1
          ring]
  have hP0 : (F (Pts 0)).1 = 0 := by
    ext j
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    by_contra hc0
    have hdvd : ∀ k : ℕ, (2 : ℤ) ^ k ∣ (F (Pts 0)).1 j := by
      intro k
      obtain ⟨Q, hQ⟩ := hdiv k (Pts 0)
      rw [hQ]
      simp only [Finsupp.smul_apply, smul_eq_mul]
      exact Dvd.intro _ rfl
    set c : ℤ := (F (Pts 0)).1 j with hc
    have hle := Int.le_of_dvd (abs_pos.mpr hc0) ((dvd_abs _ _).mpr (hdvd c.natAbs))
    have hlt : c.natAbs < 2 ^ c.natAbs := Nat.lt_two_pow_self
    rw [Int.abs_eq_natAbs] at hle
    have : ((2 : ℤ)) ^ c.natAbs = ((2 ^ c.natAbs : ℕ) : ℤ) := by push_cast; ring
    omega
  obtain ⟨k, hk0, hkP⟩ := htor (Pts 0) hP0
  have hsum : (∑ i, (fun _ : Fin 1 => (1 : ℤ)) i • Pts i) = Pts 0 := by
    rw [Fin.sum_univ_one, one_smul]
  have := hind (fun _ => 1) (by rw [hsum]; exact ⟨k, hk0, hkP⟩) 0
  norm_num at this

/-- The rank is at least zero, vacuously. -/
private lemma rank_zero_trivial :
    BirchSwinnertonDyer.AlgebraicRankAtLeast p 0 :=
  ⟨fun i => i.elim0, fun c _ i => i.elim0⟩

/-- **GENOCCHI'S THEOREM AT EVERY PRIME `p ≡ 3 (mod 8)`**: the algebraic rank of
`y² = x³ − p²x` is exactly zero — the historical first theorem of the congruent
number problem, family-wise and kernel-checked. -/
theorem theGenocchiLawHoldsOnTheThreeModEightBranch (hp8 : p % 8 = 3) :
    BirchSwinnertonDyer.AlgebraicRankIs p 0 :=
  ⟨rank_zero_trivial, by
    have h := theRankVanishesOnTheThreeModEightBranch hp8
    simpa using h⟩

end Soma.Holonics.Millennium.FamilyGenocchi

