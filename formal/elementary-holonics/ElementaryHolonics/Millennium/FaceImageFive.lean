import ElementaryHolonics.Millennium.FamilyFace
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-!
# FaceImageFive: the two-descent of the five-curve is complete

**The second Ш[2]-vanishing certificate of the mod-two Birch–Swinnerton-Dyer
programme.**  On the rank-one curve `y² = x³ − 25x` the descent face `P ↦ (x, x − 5)`
mod squares has image **exactly the eight realized classes** — four torsion classes and
the coset the realized direction `P = (−4, 6)` opens.  The architecture is the
thirty-four file's, instanced at five: the support law puts every slot class on
`±2^a·5^b`; the sign law kills the mixed-sign half; **three** canonical cosets survive
to arithmetic and each dies at the frame of eight — three primitive integer systems
with no solution mod eight (kernel `decide`s), closed under the halving descent — and
the remaining twenty-one refused classes translate onto the three canonicals through
the family homomorphism.

Read against the classical ledger: image eight = torsion four × one direction, so the
rank is **exactly one** in descent form and `Ш(E₅)[2]` sees nothing — the second
completed instance, after thirty-four, of the descent side of the mod-two programme.
The Mordell–Weil translation is `interpretation`; the theorems are the image
computation.

Every `theorem` is discharged and none depends on `sorryAx`.  **Boundary**: nothing
about the Birch–Swinnerton-Dyer conjecture; the classical rank vocabulary enters only
through exterior Mordell–Weil finiteness.
-/

namespace Soma.Holonics.Millennium.FaceImageFive

open WeierstrassCurve.Affine

private lemma sqcls_trans {a b c : ℚ} (h₁ : Descent.SqCls a b) (h₂ : Descent.SqCls b c) :
    Descent.SqCls a c := by
  obtain ⟨k, hk, hkv⟩ := h₁
  obtain ⟨m, hm, hmv⟩ := h₂
  exact ⟨k * m, mul_ne_zero hk hm, by rw [hkv, hmv]; ring⟩

private lemma sqcls_mul {a b c d : ℚ} (h₁ : Descent.SqCls a c) (h₂ : Descent.SqCls b d) :
    Descent.SqCls (a * b) (c * d) := by
  obtain ⟨k, hk, hkv⟩ := h₁
  obtain ⟨m, hm, hmv⟩ := h₂
  exact ⟨k * m, mul_ne_zero hk hm, by rw [hkv, hmv]; ring⟩

private lemma sqcls_sign {a d : ℚ} (h : Descent.SqCls a d) : (0 < a ↔ 0 < d) := by
  obtain ⟨c, hc, hval⟩ := h
  have hc2 : 0 < c ^ 2 := by positivity
  constructor
  · intro ha
    nlinarith
  · intro hd
    nlinarith

/-! ## 1. The curve data at five -/

private lemma onCurve5 {x y : ℚ} (h : RankOne.E5.Nonsingular x y) :
    y ^ 2 = x ^ 3 - 25 * x := by
  have h1 := ((nonsingular_iff x y).mp h).1
  rw [equation_iff] at h1
  simp only [RankOne.E5] at h1
  linarith [h1]

private lemma avoid5 {x y : ℚ} (h : y ^ 2 = x ^ 3 - 25 * x) (hy : y ≠ 0) :
    x ≠ 0 ∧ x ≠ 5 ∧ x ≠ -5 :=
  FaceHomomorphism.theNonzeroOrdinateAvoidsTheRoots
    (n := 5) (by linear_combination h) hy

private lemma slot5One_some {x y : ℚ} (h : RankOne.E5.Nonsingular x y) :
    RankOne.slotOne (.some x y h) = if x = 0 then -25 else x := rfl

private lemma slot5Two_some {x y : ℚ} (h : RankOne.E5.Nonsingular x y) :
    RankOne.slotTwo (.some x y h) = if x = 5 then 50 else x - 5 := rfl

private lemma notSquareTen : ¬ IsSquare (10 : ℚ) := by
  rw [show (10 : ℚ) = ((10 : ℕ) : ℚ) by norm_num, Rat.isSquare_natCast_iff]
  rintro ⟨r, hr⟩
  have h3 : r ≤ 3 := by nlinarith
  interval_cases r <;> omega

/-! ## 2. The sign law -/

theorem theSignsAgreeAcrossTheFaceAtFive {x y d₁ d₂ : ℚ}
    (hcurve : y ^ 2 = x ^ 3 - 25 * x) (hy : y ≠ 0)
    (h₁ : Descent.SqCls x d₁) (h₂ : Descent.SqCls (x - 5) d₂) :
    (0 < d₁ ∧ 0 < d₂) ∨ (d₁ < 0 ∧ d₂ < 0) := by
  obtain ⟨hx0, hx5, hxm5⟩ := avoid5 hcurve hy
  have hy2 : 0 < y ^ 2 := by positivity
  have hs₁ := sqcls_sign h₁
  have hs₂ := sqcls_sign h₂
  rcases lt_or_gt_of_ne hx0 with hx | hx
  · right
    constructor
    · by_contra hcon
      push_neg at hcon
      rcases lt_or_eq_of_le hcon with hd | hd
      · exact absurd (hs₁.mpr hd) (by linarith)
      · obtain ⟨c, hc, hval⟩ := h₁
        rw [← hd] at hval
        exact hx0 (by linarith [hval])
    · by_contra hcon
      push_neg at hcon
      rcases lt_or_eq_of_le hcon with hd | hd
      · exact absurd (hs₂.mpr hd) (by linarith)
      · obtain ⟨c, hc, hval⟩ := h₂
        rw [← hd] at hval
        exact hx5 (by linarith [hval])
  · left
    have hx5' : 5 < x := by
      by_contra hcon
      push_neg at hcon
      have hlt : x < 5 := lt_of_le_of_ne hcon hx5
      have hx2 : x ^ 2 < 25 := by nlinarith
      have hpos : 0 < x * (25 - x ^ 2) := mul_pos hx (by linarith)
      nlinarith [hy2]
    exact ⟨hs₁.mp hx, hs₂.mp (by linarith)⟩

/-! ## 3. The support law at five -/

private lemma val_add_left5 {ℓ : ℕ} [Fact ℓ.Prime] {a b : ℚ} (ha : a ≠ 0)
    (hab : a + b ≠ 0) (h : padicValRat ℓ a < padicValRat ℓ b) :
    padicValRat ℓ (a + b) = padicValRat ℓ a := by
  have h1 : padicValRat ℓ a ≤ padicValRat ℓ (a + b) := by
    have hmin := padicValRat.min_le_padicValRat_add (p := ℓ) (q := a) (r := b) hab
    omega
  have h2 : padicValRat ℓ (a + b) ≤ padicValRat ℓ a := by
    by_contra hcon
    push_neg at hcon
    have hrw : a + b + -b = a := by ring
    have hmin := padicValRat.min_le_padicValRat_add (p := ℓ) (q := a + b) (r := -b)
      (by rw [hrw]; exact ha)
    rw [hrw, padicValRat.neg] at hmin
    omega
  omega

private lemma prime_not_dvd_20 {ℓ : ℕ} (hℓ : ℓ.Prime) (h2 : ℓ ≠ 2) (h5 : ℓ ≠ 5) :
    ¬ ℓ ∣ 20 := by
  intro hc
  have h4 : ℓ ∣ 4 * 5 := by simpa using hc
  rcases (Nat.Prime.dvd_mul hℓ).mp h4 with h | h
  · have : ℓ ∣ 2 := hℓ.dvd_of_dvd_pow (n := 2) (by simpa using h)
    exact h2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp this)
  · exact h5 ((Nat.prime_dvd_prime_iff_eq hℓ (by norm_num)).mp h)

private lemma val_const_zero5 {ℓ : ℕ} [hf : Fact ℓ.Prime] (h2 : ℓ ≠ 2) (h5 : ℓ ≠ 5) :
    padicValRat ℓ (5 : ℚ) = 0 ∧ padicValRat ℓ (-5 : ℚ) = 0 ∧
    padicValRat ℓ (10 : ℚ) = 0 := by
  have hℓ : ℓ.Prime := hf.out
  have key : ∀ m : ℤ, ¬ (ℓ : ℤ) ∣ m → padicValRat ℓ (m : ℚ) = 0 := by
    intro m hdvd
    rw [padicValRat.of_int, padicValInt.eq_zero_iff.mpr (Or.inr (Or.inr hdvd))]
    simp
  have hnd : ∀ m : ℤ, m.natAbs ∣ 20 → ¬ (ℓ : ℤ) ∣ m := by
    intro m hm hc
    refine prime_not_dvd_20 hℓ h2 h5 (dvd_trans ?_ hm)
    simpa using Int.natAbs_dvd_natAbs.mpr hc
  refine ⟨?_, ?_, ?_⟩
  · simpa using key 5 (hnd 5 (by norm_num))
  · simpa using key (-5) (hnd (-5) (by norm_num))
  · simpa using key 10 (hnd 10 (by norm_num))

private lemma even_slot_val5 {ℓ : ℕ} [Fact ℓ.Prime] (h2 : ℓ ≠ 2) (h5 : ℓ ≠ 5)
    {x y : ℚ} (hcurve : y ^ 2 = x ^ 3 - 25 * x) (hy : y ≠ 0) :
    Even (padicValRat ℓ x) ∧ Even (padicValRat ℓ (x - 5)) := by
  obtain ⟨hx0, hx5, hxm5⟩ := avoid5 hcurve hy
  have hxm : x - 5 ≠ 0 := sub_ne_zero.mpr hx5
  have hxp : x + 5 ≠ 0 := fun hc => hxm5 (by linarith)
  have hfact : y ^ 2 = x * (x - 5) * (x + 5) := by linear_combination hcurve
  have hprod : 2 * padicValRat ℓ y =
      padicValRat ℓ x + padicValRat ℓ (x - 5) + padicValRat ℓ (x + 5) := by
    have hmul1 : padicValRat ℓ (x * (x - 5) * (x + 5)) =
        padicValRat ℓ x + padicValRat ℓ (x - 5) + padicValRat ℓ (x + 5) := by
      rw [padicValRat.mul (mul_ne_zero hx0 hxm) hxp, padicValRat.mul hx0 hxm]
    have hpow : padicValRat ℓ (y ^ 2) = 2 * padicValRat ℓ y := by
      rw [pow_two, padicValRat.mul hy hy]
      ring
    rw [← hpow, hfact, hmul1]
  obtain ⟨v5, vm5, v10⟩ := val_const_zero5 (ℓ := ℓ) h2 h5
  constructor
  · rcases lt_trichotomy (padicValRat ℓ x) 0 with hv | hv | hv
    · have e1 : padicValRat ℓ (x - 5) = padicValRat ℓ x := by
        have := val_add_left5 (ℓ := ℓ) hx0
          (by rw [show x + -5 = x - 5 by ring]; exact hxm) (by rw [vm5]; exact hv)
        rw [show x + -5 = x - 5 by ring] at this
        exact this
      have e2 : padicValRat ℓ (x + 5) = padicValRat ℓ x := by
        exact val_add_left5 (ℓ := ℓ) hx0 hxp (by rw [v5]; exact hv)
      rw [e1, e2] at hprod
      refine ⟨padicValRat ℓ y - padicValRat ℓ x, by linarith⟩
    · exact ⟨0, by rw [hv]; ring⟩
    · have e1 : padicValRat ℓ (x - 5) = 0 := by
        have := val_add_left5 (ℓ := ℓ) (by norm_num : (-5 : ℚ) ≠ 0)
          (by rw [show -5 + x = x - 5 by ring]; exact hxm) (by rw [vm5]; exact hv)
        rw [show (-5 : ℚ) + x = x - 5 by ring, vm5] at this
        exact this
      have e2 : padicValRat ℓ (x + 5) = 0 := by
        have := val_add_left5 (ℓ := ℓ) (by norm_num : (5 : ℚ) ≠ 0)
          (by rw [show (5 : ℚ) + x = x + 5 by ring]; exact hxp) (by rw [v5]; exact hv)
        rw [show (5 : ℚ) + x = x + 5 by ring, v5] at this
        exact this
      rw [e1, e2] at hprod
      exact ⟨padicValRat ℓ y, by linarith⟩
  · rcases lt_trichotomy (padicValRat ℓ (x - 5)) 0 with hv | hv | hv
    · have e1 : padicValRat ℓ x = padicValRat ℓ (x - 5) := by
        have := val_add_left5 (ℓ := ℓ) hxm
          (by rw [show x - 5 + 5 = x by ring]; exact hx0) (by rw [v5]; exact hv)
        rw [show x - 5 + 5 = x by ring] at this
        exact this
      have e2 : padicValRat ℓ (x + 5) = padicValRat ℓ (x - 5) := by
        have := val_add_left5 (ℓ := ℓ) hxm
          (by rw [show x - 5 + 10 = x + 5 by ring]; exact hxp) (by rw [v10]; exact hv)
        rw [show x - 5 + 10 = x + 5 by ring] at this
        exact this
      rw [e1, e2] at hprod
      refine ⟨padicValRat ℓ y - padicValRat ℓ (x - 5), by linarith⟩
    · exact ⟨0, by rw [hv]; ring⟩
    · have e1 : padicValRat ℓ x = 0 := by
        have := val_add_left5 (ℓ := ℓ) (by norm_num : (5 : ℚ) ≠ 0)
          (by rw [show (5 : ℚ) + (x - 5) = x by ring]; exact hx0) (by rw [v5]; exact hv)
        rw [show (5 : ℚ) + (x - 5) = x by ring, v5] at this
        exact this
      have e2 : padicValRat ℓ (x + 5) = 0 := by
        have := val_add_left5 (ℓ := ℓ) (by norm_num : (10 : ℚ) ≠ 0)
          (by rw [show (10 : ℚ) + (x - 5) = x + 5 by ring]; exact hxp)
          (by rw [v10]; exact hv)
        rw [show (10 : ℚ) + (x - 5) = x + 5 by ring, v10] at this
        exact this
      rw [e1, e2] at hprod
      exact ⟨padicValRat ℓ y, by linarith⟩

/-- The eight candidate classes at five: `±1, ±2, ±5, ±10`. -/
def OnDiscriminantFive (d : ℚ) : Prop :=
  d = 1 ∨ d = -1 ∨ d = 2 ∨ d = -2 ∨ d = 5 ∨ d = -5 ∨ d = 10 ∨ d = -10

private lemma classFromEvenValuations5 {x : ℚ} (hx : x ≠ 0)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ≠ 5 → Even (padicValRat ℓ x)) :
    ∃ d : ℚ, OnDiscriminantFive d ∧ Descent.SqCls x d := by
  have hnum : x.num ≠ 0 := Rat.num_ne_zero.mpr hx
  have hden : (x.den : ℤ) ≠ 0 := by exact_mod_cast x.den_nz
  have hdenQ : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
  have hm0 : x.num * (x.den : ℤ) ≠ 0 := mul_ne_zero hnum hden
  have hcls : Descent.SqCls x ((x.num * (x.den : ℤ) : ℤ) : ℚ) := by
    refine ⟨1 / (x.den : ℚ), one_div_ne_zero hdenQ, ?_⟩
    have hxd : x * (x.den : ℚ) = x.num := Rat.mul_den_eq_num x
    push_cast
    field_simp
    linear_combination hxd
  have hmv : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ≠ 5 →
      Even ((x.num * (x.den : ℤ)).natAbs.factorization ℓ) := by
    intro ℓ hℓ h2 h5
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    have hval := h ℓ hℓ h2 h5
    have hunfold : padicValRat ℓ x =
        (padicValNat ℓ x.num.natAbs : ℤ) - padicValNat ℓ x.den := rfl
    rw [hunfold] at hval
    have habs : (x.num * (x.den : ℤ)).natAbs = x.num.natAbs * x.den := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
    rw [habs, Nat.factorization_def _ hℓ,
      padicValNat.mul (Int.natAbs_ne_zero.mpr hnum) x.den_nz]
    have h1 : Even ((padicValNat ℓ x.num.natAbs : ℤ) + padicValNat ℓ x.den) := by
      obtain ⟨k, hk⟩ := hval
      exact ⟨k + padicValNat ℓ x.den, by linarith⟩
    exact_mod_cast h1
  obtain ⟨a, b, hab, hsq⟩ := Nat.sq_mul_squarefree (x.num * (x.den : ℤ)).natAbs
  have hn0 : (x.num * (x.den : ℤ)).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hm0
  have ha0 : a ≠ 0 := by
    intro hc
    rw [hc, mul_zero] at hab
    exact hn0 hab.symm
  have hb0 : b ≠ 0 := by
    intro hc
    rw [hc] at hab
    simp at hab
    exact hn0 hab.symm
  have hadvd : a ∣ 10 := by
    rw [← Nat.factorization_le_iff_dvd ha0 (by norm_num)]
    rw [Finsupp.le_def]
    intro ℓ
    by_cases hℓp : ℓ.Prime
    · by_cases hdvd : ℓ ∣ a
      · have hle1 : a.factorization ℓ ≤ 1 :=
          (Nat.squarefree_iff_factorization_le_one ha0).mp hsq ℓ
        have hmem : ℓ = 2 ∨ ℓ = 5 := by
          by_contra hcon
          push_neg at hcon
          obtain ⟨h2, h5⟩ := hcon
          have heven := hmv ℓ hℓp h2 h5
          rw [← hab, Nat.factorization_mul (pow_ne_zero 2 hb0) ha0,
            Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply,
            smul_eq_mul] at heven
          have hpos : 0 < a.factorization ℓ :=
            Nat.Prime.factorization_pos_of_dvd hℓp ha0 hdvd
          obtain ⟨k, hk⟩ := heven
          omega
        rcases hmem with rfl | rfl
        · have h2f : (10 : ℕ).factorization 2 = 1 := by
            rw [show (10 : ℕ) = 2 * 5 by norm_num,
              Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
              Nat.Prime.factorization_self (by norm_num),
              Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
          rw [h2f]
          exact hle1
        · have h5f : (10 : ℕ).factorization 5 = 1 := by
            rw [show (10 : ℕ) = 2 * 5 by norm_num,
              Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
              Nat.factorization_eq_zero_of_not_dvd (by norm_num),
              Nat.Prime.factorization_self (by norm_num)]
          rw [h5f]
          exact hle1
      · rw [Nat.factorization_eq_zero_of_not_dvd hdvd]
        exact Nat.zero_le _
    · rw [Nat.factorization_eq_zero_of_not_prime _ hℓp]
      exact Nat.zero_le _
  have hamem : a = 1 ∨ a = 2 ∨ a = 5 ∨ a = 10 := by
    have hle : a ≤ 10 := Nat.le_of_dvd (by norm_num) hadvd
    interval_cases a <;> revert hadvd <;> decide
  rcases Int.natAbs_eq (x.num * (x.den : ℤ)) with hs | hs
  · refine ⟨(a : ℚ), ?_, ?_⟩
    · rcases hamem with rfl | rfl | rfl | rfl
      · exact Or.inl (by norm_num)
      · exact Or.inr (Or.inr (Or.inl (by norm_num)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by norm_num)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by norm_num)))))))
    · refine sqcls_trans hcls ⟨(b : ℚ), by exact_mod_cast hb0, ?_⟩
      rw [hs]
      push_cast [← hab]
      ring
  · refine ⟨-(a : ℚ), ?_, ?_⟩
    · rcases hamem with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl (by norm_num))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by norm_num))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by norm_num))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by norm_num)))))))
    · refine sqcls_trans hcls ⟨(b : ℚ), by exact_mod_cast hb0, ?_⟩
      rw [hs]
      push_cast [← hab]
      ring

theorem theSlotClassesAreSupportedOnTheDiscriminantAtFive {x y : ℚ}
    (hcurve : y ^ 2 = x ^ 3 - 25 * x) (hy : y ≠ 0) :
    (∃ d₁ : ℚ, OnDiscriminantFive d₁ ∧ Descent.SqCls x d₁) ∧
    (∃ d₂ : ℚ, OnDiscriminantFive d₂ ∧ Descent.SqCls (x - 5) d₂) := by
  obtain ⟨hx0, hx5, -⟩ := avoid5 hcurve hy
  constructor
  · exact classFromEvenValuations5 hx0 fun ℓ hℓ h2 h5 =>
      haveI : Fact ℓ.Prime := ⟨hℓ⟩
      (even_slot_val5 h2 h5 hcurve hy).1
  · exact classFromEvenValuations5 (sub_ne_zero.mpr hx5) fun ℓ hℓ h2 h5 =>
      haveI : Fact ℓ.Prime := ⟨hℓ⟩
      (even_slot_val5 h2 h5 hcurve hy).2

/-! ## 4. The three canonical refusals: each dies at the frame of eight -/

private lemma theHalvingDiesA : ∀ (n : ℕ), ∀ C E F D : ℤ, D.natAbs = n → D ≠ 0 →
    C ^ 2 - 5 * D ^ 2 = 2 * E ^ 2 → C ^ 2 + 5 * D ^ 2 = 2 * F ^ 2 → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C E F D hD hD0 h1 h2
    have hdec : ∀ a b c d : ZMod 8, a ^ 2 - 5 * d ^ 2 = 2 * b ^ 2 →
        a ^ 2 + 5 * d ^ 2 = 2 * c ^ 2 →
        (4 * a = 0 ∧ 4 * b = 0 ∧ 4 * c = 0 ∧ 4 * d = 0) := by decide
    have h1z : (C : ZMod 8) ^ 2 - 5 * (D : ZMod 8) ^ 2 = 2 * (E : ZMod 8) ^ 2 := by
      exact_mod_cast congrArg (Int.cast : ℤ → ZMod 8) h1
    have h2z : (C : ZMod 8) ^ 2 + 5 * (D : ZMod 8) ^ 2 = 2 * (F : ZMod 8) ^ 2 := by
      exact_mod_cast congrArg (Int.cast : ℤ → ZMod 8) h2
    obtain ⟨hA, hB, hC, hD8⟩ := hdec _ _ _ _ h1z h2z
    have hdvd : ∀ m : ℤ, 4 * (m : ZMod 8) = 0 → 2 ∣ m := by
      intro m hm
      have hz : ((4 * m : ℤ) : ZMod 8) = 0 := by push_cast; rw [hm]
      have h8 : (8 : ℤ) ∣ 4 * m := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp hz
      omega
    obtain ⟨C', rfl⟩ := hdvd C hA
    obtain ⟨E', rfl⟩ := hdvd E hB
    obtain ⟨F', rfl⟩ := hdvd F hC
    obtain ⟨D', rfl⟩ := hdvd D hD8
    have hD'0 : D' ≠ 0 := fun hc => hD0 (by rw [hc]; ring)
    have h1' : C' ^ 2 - 5 * D' ^ 2 = 2 * E' ^ 2 := by linarith [h1]
    have h2' : C' ^ 2 + 5 * D' ^ 2 = 2 * F' ^ 2 := by linarith [h2]
    have hlt : D'.natAbs < n := by
      have h2n : (2 * D').natAbs = 2 * D'.natAbs := by
        rw [Int.natAbs_mul]
        norm_num
      have hne : D'.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD'0
      omega
    exact ih D'.natAbs hlt C' E' F' D' rfl hD'0 h1' h2'

private lemma theHalvingDiesB : ∀ (n : ℕ), ∀ C E F D : ℤ, D.natAbs = n → D ≠ 0 →
    2 * C ^ 2 - 5 * D ^ 2 = 2 * E ^ 2 → 2 * C ^ 2 + 5 * D ^ 2 = F ^ 2 → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C E F D hD hD0 h1 h2
    have hdec : ∀ a b c d : ZMod 8, 2 * a ^ 2 - 5 * d ^ 2 = 2 * b ^ 2 →
        2 * a ^ 2 + 5 * d ^ 2 = c ^ 2 →
        (4 * a = 0 ∧ 4 * b = 0 ∧ 4 * c = 0 ∧ 4 * d = 0) := by decide
    have h1z : 2 * (C : ZMod 8) ^ 2 - 5 * (D : ZMod 8) ^ 2 = 2 * (E : ZMod 8) ^ 2 := by
      exact_mod_cast congrArg (Int.cast : ℤ → ZMod 8) h1
    have h2z : 2 * (C : ZMod 8) ^ 2 + 5 * (D : ZMod 8) ^ 2 = (F : ZMod 8) ^ 2 := by
      exact_mod_cast congrArg (Int.cast : ℤ → ZMod 8) h2
    obtain ⟨hA, hB, hC, hD8⟩ := hdec _ _ _ _ h1z h2z
    have hdvd : ∀ m : ℤ, 4 * (m : ZMod 8) = 0 → 2 ∣ m := by
      intro m hm
      have hz : ((4 * m : ℤ) : ZMod 8) = 0 := by push_cast; rw [hm]
      have h8 : (8 : ℤ) ∣ 4 * m := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp hz
      omega
    obtain ⟨C', rfl⟩ := hdvd C hA
    obtain ⟨E', rfl⟩ := hdvd E hB
    obtain ⟨F', rfl⟩ := hdvd F hC
    obtain ⟨D', rfl⟩ := hdvd D hD8
    have hD'0 : D' ≠ 0 := fun hc => hD0 (by rw [hc]; ring)
    have h1' : 2 * C' ^ 2 - 5 * D' ^ 2 = 2 * E' ^ 2 := by linarith [h1]
    have h2' : 2 * C' ^ 2 + 5 * D' ^ 2 = F' ^ 2 := by linarith [h2]
    have hlt : D'.natAbs < n := by
      have h2n : (2 * D').natAbs = 2 * D'.natAbs := by
        rw [Int.natAbs_mul]
        norm_num
      have hne : D'.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD'0
      omega
    exact ih D'.natAbs hlt C' E' F' D' rfl hD'0 h1' h2'

private lemma theHalvingDiesC : ∀ (n : ℕ), ∀ C E F D : ℤ, D.natAbs = n → D ≠ 0 →
    2 * C ^ 2 - 5 * D ^ 2 = E ^ 2 → 2 * C ^ 2 + 5 * D ^ 2 = 2 * F ^ 2 → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C E F D hD hD0 h1 h2
    have hdec : ∀ a b c d : ZMod 8, 2 * a ^ 2 - 5 * d ^ 2 = b ^ 2 →
        2 * a ^ 2 + 5 * d ^ 2 = 2 * c ^ 2 →
        (4 * a = 0 ∧ 4 * b = 0 ∧ 4 * c = 0 ∧ 4 * d = 0) := by decide
    have h1z : 2 * (C : ZMod 8) ^ 2 - 5 * (D : ZMod 8) ^ 2 = (E : ZMod 8) ^ 2 := by
      exact_mod_cast congrArg (Int.cast : ℤ → ZMod 8) h1
    have h2z : 2 * (C : ZMod 8) ^ 2 + 5 * (D : ZMod 8) ^ 2 = 2 * (F : ZMod 8) ^ 2 := by
      exact_mod_cast congrArg (Int.cast : ℤ → ZMod 8) h2
    obtain ⟨hA, hB, hC, hD8⟩ := hdec _ _ _ _ h1z h2z
    have hdvd : ∀ m : ℤ, 4 * (m : ZMod 8) = 0 → 2 ∣ m := by
      intro m hm
      have hz : ((4 * m : ℤ) : ZMod 8) = 0 := by push_cast; rw [hm]
      have h8 : (8 : ℤ) ∣ 4 * m := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp hz
      omega
    obtain ⟨C', rfl⟩ := hdvd C hA
    obtain ⟨E', rfl⟩ := hdvd E hB
    obtain ⟨F', rfl⟩ := hdvd F hC
    obtain ⟨D', rfl⟩ := hdvd D hD8
    have hD'0 : D' ≠ 0 := fun hc => hD0 (by rw [hc]; ring)
    have h1' : 2 * C' ^ 2 - 5 * D' ^ 2 = E' ^ 2 := by linarith [h1]
    have h2' : 2 * C' ^ 2 + 5 * D' ^ 2 = 2 * F' ^ 2 := by linarith [h2]
    have hlt : D'.natAbs < n := by
      have h2n : (2 * D').natAbs = 2 * D'.natAbs := by
        rw [Int.natAbs_mul]
        norm_num
      have hne : D'.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD'0
      omega
    exact ih D'.natAbs hlt C' E' F' D' rfl hD'0 h1' h2'

theorem theFirstCanonicalCosetIsRefusedAtFive (P : RankOne.E5.Point) :
    ¬ (Descent.SqCls (RankOne.slotOne P) 1 ∧ Descent.SqCls (RankOne.slotTwo P) 2) := by
  rintro ⟨hs1, hs2⟩
  rcases P with _ | @⟨x, y, hP⟩
  · obtain ⟨c, hc, hval⟩ := hs2
    have h1 : (1 : ℚ) = c ^ 2 * 2 := hval
    refine Descent.notSquareTwo ⟨1 / c, ?_⟩
    field_simp
    linear_combination -h1
  · have hcurve := onCurve5 hP
    by_cases hy : y = 0
    · rw [hy] at hcurve
      have h0 : x * (x - 5) * (x + 5) = 0 := by linear_combination -hcurve
      have hx3 : x = 0 ∨ x = 5 ∨ x = -5 := by
        rcases mul_eq_zero.mp h0 with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl (by linarith))
        · exact Or.inr (Or.inr (by linarith))
      rcases hx3 with rfl | rfl | rfl
      · rw [slot5One_some, if_pos rfl] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        nlinarith [sq_nonneg c, hval]
      · rw [slot5One_some, if_neg (by norm_num)] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        exact RankOne.notSquareFive ⟨c, by rw [hval]; ring⟩
      · rw [slot5One_some, if_neg (by norm_num)] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        nlinarith [sq_nonneg c, hval]
    · obtain ⟨hx0, hx5, hxm5⟩ := avoid5 hcurve hy
      rw [slot5One_some, if_neg hx0] at hs1
      rw [slot5Two_some, if_neg hx5] at hs2
      obtain ⟨c, hc0, hcv⟩ := hs1
      obtain ⟨e, he0, hev⟩ := hs2
      rw [mul_one] at hcv
      have hce : (2 : ℚ) * c * e ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero hc0) he0
      have hf : x + 5 = 2 * (y / (2 * c * e)) ^ 2 := by
        have hs1' : (x + 5) * (2 * c * e) ^ 2 = (x + 5) * (4 * x * e ^ 2) := by
          linear_combination (-4 * (x + 5) * e ^ 2) * hcv
        have hs2' : (x + 5) * (4 * x * e ^ 2) = 2 * x * (x - 5) * (x + 5) := by
          linear_combination (-2 * x * (x + 5)) * hev
        have hs3' : 2 * x * (x - 5) * (x + 5) = 2 * y ^ 2 := by
          linear_combination -2 * hcurve
        have hkey : (x + 5) * (2 * c * e) ^ 2 = 2 * y ^ 2 :=
          hs1'.trans (hs2'.trans hs3')
        rw [div_pow, mul_div_assoc', eq_div_iff (pow_ne_zero 2 hce)]
        exact hkey
      have hcd : c * (c.den : ℚ) = c.num := Rat.mul_den_eq_num c
      have hed : e * (e.den : ℚ) = e.num := Rat.mul_den_eq_num e
      have hfd : (y / (2 * c * e)) * ((y / (2 * c * e)).den : ℚ) =
          (y / (2 * c * e)).num := Rat.mul_den_eq_num _
      set f := y / (2 * c * e) with hfdef
      set N : ℕ := c.den * e.den * f.den with hN
      have hN0 : (N : ℚ) ≠ 0 := by
        rw [hN]
        push_cast
        positivity
      have hCQ : ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) = c * N := by
        push_cast
        rw [hN]
        push_cast
        linear_combination (-(e.den : ℚ) * (f.den : ℚ)) * hcd
      have hEQ : ((e.num * (c.den * f.den : ℕ) : ℤ) : ℚ) = e * N := by
        push_cast
        rw [hN]
        push_cast
        linear_combination (-(c.den : ℚ) * (f.den : ℚ)) * hed
      have hFQ : ((f.num * (c.den * e.den : ℕ) : ℤ) : ℚ) = f * N := by
        push_cast
        rw [hN]
        push_cast
        linear_combination (-(c.den : ℚ) * (e.den : ℚ)) * hfd
      have hint1 : (c.num * (e.den * f.den : ℕ) : ℤ) ^ 2 - 5 * (N : ℤ) ^ 2 =
          2 * (e.num * (c.den * f.den : ℕ) : ℤ) ^ 2 := by
        have hQ : (c * N) ^ 2 - 5 * (N : ℚ) ^ 2 = 2 * (e * N) ^ 2 := by
          have hsub : c ^ 2 - 5 = 2 * e ^ 2 := by
            linear_combination -hcv + hev
          linear_combination (N : ℚ) ^ 2 * hsub
        exact_mod_cast (by rw [hCQ, hEQ]; exact_mod_cast hQ :
          ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) ^ 2 - 5 * (N : ℚ) ^ 2 =
          2 * ((e.num * (c.den * f.den : ℕ) : ℤ) : ℚ) ^ 2)
      have hint2 : (c.num * (e.den * f.den : ℕ) : ℤ) ^ 2 + 5 * (N : ℤ) ^ 2 =
          2 * (f.num * (c.den * e.den : ℕ) : ℤ) ^ 2 := by
        have hQ : (c * N) ^ 2 + 5 * (N : ℚ) ^ 2 = 2 * (f * N) ^ 2 := by
          have hsub : c ^ 2 + 5 = 2 * f ^ 2 := by
            linear_combination -hcv + hf
          linear_combination (N : ℚ) ^ 2 * hsub
        exact_mod_cast (by rw [hCQ, hFQ]; exact_mod_cast hQ :
          ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) ^ 2 + 5 * (N : ℚ) ^ 2 =
          2 * ((f.num * (c.den * e.den : ℕ) : ℤ) : ℚ) ^ 2)
      have hNnat : N ≠ 0 := by
        rw [hN]
        exact Nat.mul_ne_zero (Nat.mul_ne_zero c.den_nz e.den_nz) f.den_nz
      have hNne : ((N : ℤ)) ≠ 0 := by exact_mod_cast hNnat
      exact theHalvingDiesA (N : ℤ).natAbs _ _ _ _ rfl hNne hint1 hint2

theorem theSecondCanonicalCosetIsRefusedAtFive (P : RankOne.E5.Point) :
    ¬ (Descent.SqCls (RankOne.slotOne P) 2 ∧ Descent.SqCls (RankOne.slotTwo P) 2) := by
  rintro ⟨hs1, hs2⟩
  rcases P with _ | @⟨x, y, hP⟩
  · obtain ⟨c, hc, hval⟩ := hs1
    have h1 : (1 : ℚ) = c ^ 2 * 2 := hval
    refine Descent.notSquareTwo ⟨1 / c, ?_⟩
    field_simp
    linear_combination -h1
  · have hcurve := onCurve5 hP
    by_cases hy : y = 0
    · rw [hy] at hcurve
      have h0 : x * (x - 5) * (x + 5) = 0 := by linear_combination -hcurve
      have hx3 : x = 0 ∨ x = 5 ∨ x = -5 := by
        rcases mul_eq_zero.mp h0 with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl (by linarith))
        · exact Or.inr (Or.inr (by linarith))
      rcases hx3 with rfl | rfl | rfl
      · rw [slot5One_some, if_pos rfl] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        nlinarith [sq_nonneg c, hval]
      · rw [slot5One_some, if_neg (by norm_num)] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        refine notSquareTen ⟨2 * c, ?_⟩
        linear_combination 2 * hval
      · rw [slot5One_some, if_neg (by norm_num)] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        nlinarith [sq_nonneg c, hval]
    · obtain ⟨hx0, hx5, hxm5⟩ := avoid5 hcurve hy
      rw [slot5One_some, if_neg hx0] at hs1
      rw [slot5Two_some, if_neg hx5] at hs2
      obtain ⟨c, hc0, hcv⟩ := hs1
      obtain ⟨e, he0, hev⟩ := hs2
      have hce : (2 : ℚ) * c * e ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero hc0) he0
      have hf : x + 5 = (y / (2 * c * e)) ^ 2 := by
        have hs1' : (x + 5) * (2 * c * e) ^ 2 = (x + 5) * (2 * x * e ^ 2) := by
          linear_combination (-2 * (x + 5) * e ^ 2) * hcv
        have hs2' : (x + 5) * (2 * x * e ^ 2) = x * (x - 5) * (x + 5) := by
          linear_combination (-(x * (x + 5))) * hev
        have hs3' : x * (x - 5) * (x + 5) = y ^ 2 := by
          linear_combination -hcurve
        have hkey : (x + 5) * (2 * c * e) ^ 2 = y ^ 2 :=
          hs1'.trans (hs2'.trans hs3')
        rw [div_pow, eq_div_iff (pow_ne_zero 2 hce)]
        exact hkey
      have hcd : c * (c.den : ℚ) = c.num := Rat.mul_den_eq_num c
      have hed : e * (e.den : ℚ) = e.num := Rat.mul_den_eq_num e
      have hfd : (y / (2 * c * e)) * ((y / (2 * c * e)).den : ℚ) =
          (y / (2 * c * e)).num := Rat.mul_den_eq_num _
      set f := y / (2 * c * e) with hfdef
      set N : ℕ := c.den * e.den * f.den with hN
      have hN0 : (N : ℚ) ≠ 0 := by
        rw [hN]
        push_cast
        positivity
      have hCQ : ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) = c * N := by
        push_cast
        rw [hN]
        push_cast
        linear_combination (-(e.den : ℚ) * (f.den : ℚ)) * hcd
      have hEQ : ((e.num * (c.den * f.den : ℕ) : ℤ) : ℚ) = e * N := by
        push_cast
        rw [hN]
        push_cast
        linear_combination (-(c.den : ℚ) * (f.den : ℚ)) * hed
      have hFQ : ((f.num * (c.den * e.den : ℕ) : ℤ) : ℚ) = f * N := by
        push_cast
        rw [hN]
        push_cast
        linear_combination (-(c.den : ℚ) * (e.den : ℚ)) * hfd
      have hint1 : 2 * (c.num * (e.den * f.den : ℕ) : ℤ) ^ 2 - 5 * (N : ℤ) ^ 2 =
          2 * (e.num * (c.den * f.den : ℕ) : ℤ) ^ 2 := by
        have hQ : 2 * (c * N) ^ 2 - 5 * (N : ℚ) ^ 2 = 2 * (e * N) ^ 2 := by
          have hsub : 2 * c ^ 2 - 5 = 2 * e ^ 2 := by
            linear_combination -hcv + hev
          linear_combination (N : ℚ) ^ 2 * hsub
        exact_mod_cast (by rw [hCQ, hEQ]; exact_mod_cast hQ :
          2 * ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) ^ 2 - 5 * (N : ℚ) ^ 2 =
          2 * ((e.num * (c.den * f.den : ℕ) : ℤ) : ℚ) ^ 2)
      have hint2 : 2 * (c.num * (e.den * f.den : ℕ) : ℤ) ^ 2 + 5 * (N : ℤ) ^ 2 =
          (f.num * (c.den * e.den : ℕ) : ℤ) ^ 2 := by
        have hQ : 2 * (c * N) ^ 2 + 5 * (N : ℚ) ^ 2 = (f * N) ^ 2 := by
          have hsub : 2 * c ^ 2 + 5 = f ^ 2 := by
            linear_combination -hcv + hf
          linear_combination (N : ℚ) ^ 2 * hsub
        exact_mod_cast (by rw [hCQ, hFQ]; exact_mod_cast hQ :
          2 * ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) ^ 2 + 5 * (N : ℚ) ^ 2 =
          ((f.num * (c.den * e.den : ℕ) : ℤ) : ℚ) ^ 2)
      have hNnat : N ≠ 0 := by
        rw [hN]
        exact Nat.mul_ne_zero (Nat.mul_ne_zero c.den_nz e.den_nz) f.den_nz
      have hNne : ((N : ℤ)) ≠ 0 := by exact_mod_cast hNnat
      exact theHalvingDiesB (N : ℤ).natAbs _ _ _ _ rfl hNne hint1 hint2

theorem theThirdCanonicalCosetIsRefusedAtFive (P : RankOne.E5.Point) :
    ¬ (Descent.SqCls (RankOne.slotOne P) 2 ∧ Descent.SqCls (RankOne.slotTwo P) 1) := by
  rintro ⟨hs1, hs2⟩
  rcases P with _ | @⟨x, y, hP⟩
  · obtain ⟨c, hc, hval⟩ := hs1
    have h1 : (1 : ℚ) = c ^ 2 * 2 := hval
    refine Descent.notSquareTwo ⟨1 / c, ?_⟩
    field_simp
    linear_combination -h1
  · have hcurve := onCurve5 hP
    by_cases hy : y = 0
    · rw [hy] at hcurve
      have h0 : x * (x - 5) * (x + 5) = 0 := by linear_combination -hcurve
      have hx3 : x = 0 ∨ x = 5 ∨ x = -5 := by
        rcases mul_eq_zero.mp h0 with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl (by linarith))
        · exact Or.inr (Or.inr (by linarith))
      rcases hx3 with rfl | rfl | rfl
      · rw [slot5One_some, if_pos rfl] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        nlinarith [sq_nonneg c, hval]
      · rw [slot5One_some, if_neg (by norm_num)] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        refine notSquareTen ⟨2 * c, ?_⟩
        linear_combination 2 * hval
      · rw [slot5One_some, if_neg (by norm_num)] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        nlinarith [sq_nonneg c, hval]
    · obtain ⟨hx0, hx5, hxm5⟩ := avoid5 hcurve hy
      rw [slot5One_some, if_neg hx0] at hs1
      rw [slot5Two_some, if_neg hx5] at hs2
      obtain ⟨c, hc0, hcv⟩ := hs1
      obtain ⟨e, he0, hev⟩ := hs2
      rw [mul_one] at hev
      have hce : (2 : ℚ) * c * e ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero hc0) he0
      have hf : x + 5 = 2 * (y / (2 * c * e)) ^ 2 := by
        have hs1' : (x + 5) * (2 * c * e) ^ 2 = (x + 5) * (2 * x * e ^ 2) := by
          linear_combination (-2 * (x + 5) * e ^ 2) * hcv
        have hs2' : (x + 5) * (2 * x * e ^ 2) = 2 * x * (x - 5) * (x + 5) := by
          linear_combination (-2 * (x * (x + 5))) * hev
        have hs3' : 2 * x * (x - 5) * (x + 5) = 2 * y ^ 2 := by
          linear_combination -2 * hcurve
        have hkey : (x + 5) * (2 * c * e) ^ 2 = 2 * y ^ 2 :=
          hs1'.trans (hs2'.trans hs3')
        rw [div_pow, mul_div_assoc', eq_div_iff (pow_ne_zero 2 hce)]
        exact hkey
      have hcd : c * (c.den : ℚ) = c.num := Rat.mul_den_eq_num c
      have hed : e * (e.den : ℚ) = e.num := Rat.mul_den_eq_num e
      have hfd : (y / (2 * c * e)) * ((y / (2 * c * e)).den : ℚ) =
          (y / (2 * c * e)).num := Rat.mul_den_eq_num _
      set f := y / (2 * c * e) with hfdef
      set N : ℕ := c.den * e.den * f.den with hN
      have hN0 : (N : ℚ) ≠ 0 := by
        rw [hN]
        push_cast
        positivity
      have hCQ : ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) = c * N := by
        push_cast
        rw [hN]
        push_cast
        linear_combination (-(e.den : ℚ) * (f.den : ℚ)) * hcd
      have hEQ : ((e.num * (c.den * f.den : ℕ) : ℤ) : ℚ) = e * N := by
        push_cast
        rw [hN]
        push_cast
        linear_combination (-(c.den : ℚ) * (f.den : ℚ)) * hed
      have hFQ : ((f.num * (c.den * e.den : ℕ) : ℤ) : ℚ) = f * N := by
        push_cast
        rw [hN]
        push_cast
        linear_combination (-(c.den : ℚ) * (e.den : ℚ)) * hfd
      have hint1 : 2 * (c.num * (e.den * f.den : ℕ) : ℤ) ^ 2 - 5 * (N : ℤ) ^ 2 =
          (e.num * (c.den * f.den : ℕ) : ℤ) ^ 2 := by
        have hQ : 2 * (c * N) ^ 2 - 5 * (N : ℚ) ^ 2 = (e * N) ^ 2 := by
          have hsub : 2 * c ^ 2 - 5 = e ^ 2 := by
            linear_combination -hcv + hev
          linear_combination (N : ℚ) ^ 2 * hsub
        exact_mod_cast (by rw [hCQ, hEQ]; exact_mod_cast hQ :
          2 * ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) ^ 2 - 5 * (N : ℚ) ^ 2 =
          ((e.num * (c.den * f.den : ℕ) : ℤ) : ℚ) ^ 2)
      have hint2 : 2 * (c.num * (e.den * f.den : ℕ) : ℤ) ^ 2 + 5 * (N : ℤ) ^ 2 =
          2 * (f.num * (c.den * e.den : ℕ) : ℤ) ^ 2 := by
        have hQ : 2 * (c * N) ^ 2 + 5 * (N : ℚ) ^ 2 = 2 * (f * N) ^ 2 := by
          have hsub : 2 * c ^ 2 + 5 = 2 * f ^ 2 := by
            linear_combination -hcv + hf
          linear_combination (N : ℚ) ^ 2 * hsub
        exact_mod_cast (by rw [hCQ, hFQ]; exact_mod_cast hQ :
          2 * ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) ^ 2 + 5 * (N : ℚ) ^ 2 =
          2 * ((f.num * (c.den * e.den : ℕ) : ℤ) : ℚ) ^ 2)
      have hNnat : N ≠ 0 := by
        rw [hN]
        exact Nat.mul_ne_zero (Nat.mul_ne_zero c.den_nz e.den_nz) f.den_nz
      have hNne : ((N : ℤ)) ≠ 0 := by exact_mod_cast hNnat
      exact theHalvingDiesC (N : ℤ).natAbs _ _ _ _ rfl hNne hint1 hint2

/-! ## 5. The realizer faces and the translated refusals -/

private lemma hom5 (P Q : RankOne.E5.Point) :
    Descent.SqCls (RankOne.slotOne (P + Q)) (RankOne.slotOne P * RankOne.slotOne Q) ∧
    Descent.SqCls (RankOne.slotTwo (P + Q)) (RankOne.slotTwo P * RankOne.slotTwo Q) := by
  obtain ⟨g₁, g₂⟩ := FaceHomomorphism.theRankOneFaceIsAHomomorphismEverywhereHolds P Q
  rw [← FaithfulFace.theTwoFilesDeclareOneSquareClass] at g₁ g₂
  exact ⟨g₁, g₂⟩

private lemma face_add5 {P Q : RankOne.E5.Point} {a b a' b' t₁ t₂ : ℚ}
    (hP : Descent.SqCls (RankOne.slotOne P) a ∧ Descent.SqCls (RankOne.slotTwo P) b)
    (hQ : Descent.SqCls (RankOne.slotOne Q) a' ∧ Descent.SqCls (RankOne.slotTwo Q) b')
    (h₁ : Descent.SqCls (a * a') t₁) (h₂ : Descent.SqCls (b * b') t₂) :
    Descent.SqCls (RankOne.slotOne (P + Q)) t₁ ∧
    Descent.SqCls (RankOne.slotTwo (P + Q)) t₂ := by
  obtain ⟨g₁, g₂⟩ := hom5 P Q
  exact ⟨sqcls_trans g₁ (sqcls_trans (sqcls_mul hP.1 hQ.1) h₁),
    sqcls_trans g₂ (sqcls_trans (sqcls_mul hP.2 hQ.2) h₂)⟩

private lemma face_zero0 :
    Descent.SqCls (RankOne.slotOne (0 : RankOne.E5.Point)) 1 ∧
    Descent.SqCls (RankOne.slotTwo (0 : RankOne.E5.Point)) 1 :=
  ⟨Descent.sqClsRefl 1, Descent.sqClsRefl 1⟩

private lemma face_T0 :
    Descent.SqCls (RankOne.slotOne RankOne.T0) (-1) ∧
    Descent.SqCls (RankOne.slotTwo RankOne.T0) (-5) := by
  constructor
  · rw [show RankOne.T0 = Point.some 0 0 RankOne.nonsingular00 from rfl,
      slot5One_some, if_pos rfl]
    exact ⟨5, by norm_num, by norm_num⟩
  · rw [show RankOne.T0 = Point.some 0 0 RankOne.nonsingular00 from rfl,
      slot5Two_some, if_neg (by norm_num)]
    exact ⟨1, one_ne_zero, by norm_num⟩

private lemma face_T5 :
    Descent.SqCls (RankOne.slotOne RankOne.T5) 5 ∧
    Descent.SqCls (RankOne.slotTwo RankOne.T5) 2 := by
  constructor
  · rw [show RankOne.T5 = Point.some 5 0 RankOne.nonsingular50 from rfl,
      slot5One_some, if_neg (by norm_num)]
    exact ⟨1, one_ne_zero, by norm_num⟩
  · rw [show RankOne.T5 = Point.some 5 0 RankOne.nonsingular50 from rfl,
      slot5Two_some, if_pos rfl]
    exact ⟨5, by norm_num, by norm_num⟩

private lemma face_P :
    Descent.SqCls (RankOne.slotOne RankOne.P) (-1) ∧
    Descent.SqCls (RankOne.slotTwo RankOne.P) (-1) := by
  constructor
  · rw [show RankOne.P = Point.some (-4) 6 RankOne.nonsingularP from rfl,
      slot5One_some, if_neg (by norm_num)]
    exact ⟨2, by norm_num, by norm_num⟩
  · rw [show RankOne.P = Point.some (-4) 6 RankOne.nonsingularP from rfl,
      slot5Two_some, if_neg (by norm_num)]
    exact ⟨3, by norm_num, by norm_num⟩

private lemma face_T0T5 :
    Descent.SqCls (RankOne.slotOne (RankOne.T0 + RankOne.T5)) (-5) ∧
    Descent.SqCls (RankOne.slotTwo (RankOne.T0 + RankOne.T5)) (-10) :=
  face_add5 face_T0 face_T5 ⟨1, one_ne_zero, by norm_num⟩ ⟨1, one_ne_zero, by norm_num⟩

private lemma face_T0P :
    Descent.SqCls (RankOne.slotOne (RankOne.T0 + RankOne.P)) 1 ∧
    Descent.SqCls (RankOne.slotTwo (RankOne.T0 + RankOne.P)) 5 :=
  face_add5 face_T0 face_P ⟨1, one_ne_zero, by norm_num⟩ ⟨1, one_ne_zero, by norm_num⟩

private lemma face_T5P :
    Descent.SqCls (RankOne.slotOne (RankOne.T5 + RankOne.P)) (-5) ∧
    Descent.SqCls (RankOne.slotTwo (RankOne.T5 + RankOne.P)) (-2) :=
  face_add5 face_T5 face_P ⟨1, one_ne_zero, by norm_num⟩ ⟨1, one_ne_zero, by norm_num⟩

private lemma face_T0T5P :
    Descent.SqCls (RankOne.slotOne (RankOne.T0 + RankOne.T5 + RankOne.P)) 5 ∧
    Descent.SqCls (RankOne.slotTwo (RankOne.T0 + RankOne.T5 + RankOne.P)) 10 :=
  face_add5 face_T0T5 face_P ⟨1, one_ne_zero, by norm_num⟩ ⟨1, one_ne_zero, by norm_num⟩

private lemma refuseA {d₁ d₂ k₁ k₂ : ℚ} (P R : RankOne.E5.Point)
    (hR : Descent.SqCls (RankOne.slotOne R) k₁ ∧ Descent.SqCls (RankOne.slotTwo R) k₂)
    (hc₁ : Descent.SqCls (RankOne.slotOne P) d₁)
    (hc₂ : Descent.SqCls (RankOne.slotTwo P) d₂)
    (ht₁ : Descent.SqCls (d₁ * k₁) 1) (ht₂ : Descent.SqCls (d₂ * k₂) 2) : False := by
  obtain ⟨g₁, g₂⟩ := hom5 P R
  exact theFirstCanonicalCosetIsRefusedAtFive (P + R)
    ⟨sqcls_trans g₁ (sqcls_trans (sqcls_mul hc₁ hR.1) ht₁),
     sqcls_trans g₂ (sqcls_trans (sqcls_mul hc₂ hR.2) ht₂)⟩

private lemma refuseB {d₁ d₂ k₁ k₂ : ℚ} (P R : RankOne.E5.Point)
    (hR : Descent.SqCls (RankOne.slotOne R) k₁ ∧ Descent.SqCls (RankOne.slotTwo R) k₂)
    (hc₁ : Descent.SqCls (RankOne.slotOne P) d₁)
    (hc₂ : Descent.SqCls (RankOne.slotTwo P) d₂)
    (ht₁ : Descent.SqCls (d₁ * k₁) 2) (ht₂ : Descent.SqCls (d₂ * k₂) 2) : False := by
  obtain ⟨g₁, g₂⟩ := hom5 P R
  exact theSecondCanonicalCosetIsRefusedAtFive (P + R)
    ⟨sqcls_trans g₁ (sqcls_trans (sqcls_mul hc₁ hR.1) ht₁),
     sqcls_trans g₂ (sqcls_trans (sqcls_mul hc₂ hR.2) ht₂)⟩

private lemma refuseC {d₁ d₂ k₁ k₂ : ℚ} (P R : RankOne.E5.Point)
    (hR : Descent.SqCls (RankOne.slotOne R) k₁ ∧ Descent.SqCls (RankOne.slotTwo R) k₂)
    (hc₁ : Descent.SqCls (RankOne.slotOne P) d₁)
    (hc₂ : Descent.SqCls (RankOne.slotTwo P) d₂)
    (ht₁ : Descent.SqCls (d₁ * k₁) 2) (ht₂ : Descent.SqCls (d₂ * k₂) 1) : False := by
  obtain ⟨g₁, g₂⟩ := hom5 P R
  exact theThirdCanonicalCosetIsRefusedAtFive (P + R)
    ⟨sqcls_trans g₁ (sqcls_trans (sqcls_mul hc₁ hR.1) ht₁),
     sqcls_trans g₂ (sqcls_trans (sqcls_mul hc₂ hR.2) ht₂)⟩

/-! ## 6. The image theorems at five -/

/-- The eight realized square-class pairs of the five-curve. -/
def RealizedFive (d₁ d₂ : ℚ) : Prop :=
  (d₁ = 1 ∧ d₂ = 1) ∨ (d₁ = 1 ∧ d₂ = 5) ∨ (d₁ = 5 ∧ d₂ = 2) ∨ (d₁ = 5 ∧ d₂ = 10) ∨
  (d₁ = -1 ∧ d₂ = -1) ∨ (d₁ = -1 ∧ d₂ = -5) ∨ (d₁ = -5 ∧ d₂ = -2) ∨ (d₁ = -5 ∧ d₂ = -10)

/-- **THE FACE IMAGE AT FIVE IS THE REALIZED EIGHT**: every point of `y² = x³ − 25x` has
its face in the eight classes realized by the half-turns and the direction `(−4, 6)` —
the two-descent upper bound at five, rank exactly one in descent form. -/
theorem theFaceImageAtFiveIsTheRealizedEight (P : RankOne.E5.Point) :
    ∃ d₁ d₂ : ℚ, RealizedFive d₁ d₂ ∧
      Descent.SqCls (RankOne.slotOne P) d₁ ∧
      Descent.SqCls (RankOne.slotTwo P) d₂ := by
  rcases P with _ | @⟨x, y, hP⟩
  · exact ⟨1, 1, by simp [RealizedFive], Descent.sqClsRefl 1, Descent.sqClsRefl 1⟩
  · have hcurve := onCurve5 hP
    by_cases hy : y = 0
    · rw [hy] at hcurve
      have h0 : x * (x - 5) * (x + 5) = 0 := by linear_combination -hcurve
      have hx3 : x = 0 ∨ x = 5 ∨ x = -5 := by
        rcases mul_eq_zero.mp h0 with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl (by linarith))
        · exact Or.inr (Or.inr (by linarith))
      rcases hx3 with rfl | rfl | rfl
      · refine ⟨-1, -5, by simp [RealizedFive], ?_, ?_⟩
        · rw [slot5One_some, if_pos rfl]
          exact ⟨5, by norm_num, by norm_num⟩
        · rw [slot5Two_some, if_neg (by norm_num)]
          exact ⟨1, one_ne_zero, by norm_num⟩
      · refine ⟨5, 2, by simp [RealizedFive], ?_, ?_⟩
        · rw [slot5One_some, if_neg (by norm_num)]
          exact ⟨1, one_ne_zero, by norm_num⟩
        · rw [slot5Two_some, if_pos rfl]
          exact ⟨5, by norm_num, by norm_num⟩
      · refine ⟨-5, -10, by simp [RealizedFive], ?_, ?_⟩
        · rw [slot5One_some, if_neg (by norm_num)]
          exact ⟨1, one_ne_zero, by norm_num⟩
        · rw [slot5Two_some, if_neg (by norm_num)]
          exact ⟨1, one_ne_zero, by norm_num⟩
    · obtain ⟨hx0, hx5, hxm5⟩ := avoid5 hcurve hy
      obtain ⟨⟨d₁, hd₁, hc₁⟩, ⟨d₂, hd₂, hc₂⟩⟩ :=
        theSlotClassesAreSupportedOnTheDiscriminantAtFive hcurve hy
      have hsig := theSignsAgreeAcrossTheFaceAtFive hcurve hy hc₁ hc₂
      have hs1 : Descent.SqCls (RankOne.slotOne (Point.some _ _ hP)) d₁ := by
        rw [slot5One_some, if_neg hx0]
        exact hc₁
      have hs2 : Descent.SqCls (RankOne.slotTwo (Point.some _ _ hP)) d₂ := by
        rw [slot5Two_some, if_neg hx5]
        exact hc₂
      clear hc₁ hc₂
      rcases hd₁ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases hd₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · -- (1, 1): realized
        exact ⟨1, 1, by simp [RealizedFive], hs1, hs2⟩
      · -- (1, -1): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (1, 2): translated onto the canonical coset and refused
        exact absurd (refuseA _ (0 : RankOne.E5.Point) face_zero0 hs1 hs2
          ⟨1, by norm_num, by norm_num⟩ ⟨1, by norm_num, by norm_num⟩) not_false
      · -- (1, -2): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (1, 5): realized
        exact ⟨1, 5, by simp [RealizedFive], hs1, hs2⟩
      · -- (1, -5): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (1, 10): translated onto the canonical coset and refused
        exact absurd (refuseA _ (RankOne.T0 + RankOne.P) face_T0P hs1 hs2
          ⟨1, by norm_num, by norm_num⟩ ⟨5, by norm_num, by norm_num⟩) not_false
      · -- (1, -10): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (-1, 1): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-1, -1): realized
        exact ⟨-1, -1, by simp [RealizedFive], hs1, hs2⟩
      · -- (-1, 2): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-1, -2): translated onto the canonical coset and refused
        exact absurd (refuseA _ RankOne.P face_P hs1 hs2
          ⟨1, by norm_num, by norm_num⟩ ⟨1, by norm_num, by norm_num⟩) not_false
      · -- (-1, 5): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-1, -5): realized
        exact ⟨-1, -5, by simp [RealizedFive], hs1, hs2⟩
      · -- (-1, 10): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-1, -10): translated onto the canonical coset and refused
        exact absurd (refuseA _ RankOne.T0 face_T0 hs1 hs2
          ⟨1, by norm_num, by norm_num⟩ ⟨5, by norm_num, by norm_num⟩) not_false
      · -- (2, 1): translated onto the canonical coset and refused
        exact absurd (refuseC _ (0 : RankOne.E5.Point) face_zero0 hs1 hs2
          ⟨1, by norm_num, by norm_num⟩ ⟨1, by norm_num, by norm_num⟩) not_false
      · -- (2, -1): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (2, 2): translated onto the canonical coset and refused
        exact absurd (refuseB _ (0 : RankOne.E5.Point) face_zero0 hs1 hs2
          ⟨1, by norm_num, by norm_num⟩ ⟨1, by norm_num, by norm_num⟩) not_false
      · -- (2, -2): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (2, 5): translated onto the canonical coset and refused
        exact absurd (refuseC _ (RankOne.T0 + RankOne.P) face_T0P hs1 hs2
          ⟨1, by norm_num, by norm_num⟩ ⟨5, by norm_num, by norm_num⟩) not_false
      · -- (2, -5): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (2, 10): translated onto the canonical coset and refused
        exact absurd (refuseB _ (RankOne.T0 + RankOne.P) face_T0P hs1 hs2
          ⟨1, by norm_num, by norm_num⟩ ⟨5, by norm_num, by norm_num⟩) not_false
      · -- (2, -10): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (-2, 1): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-2, -1): translated onto the canonical coset and refused
        exact absurd (refuseC _ RankOne.P face_P hs1 hs2
          ⟨1, by norm_num, by norm_num⟩ ⟨1, by norm_num, by norm_num⟩) not_false
      · -- (-2, 2): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-2, -2): translated onto the canonical coset and refused
        exact absurd (refuseB _ RankOne.P face_P hs1 hs2
          ⟨1, by norm_num, by norm_num⟩ ⟨1, by norm_num, by norm_num⟩) not_false
      · -- (-2, 5): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-2, -5): translated onto the canonical coset and refused
        exact absurd (refuseC _ RankOne.T0 face_T0 hs1 hs2
          ⟨1, by norm_num, by norm_num⟩ ⟨5, by norm_num, by norm_num⟩) not_false
      · -- (-2, 10): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-2, -10): translated onto the canonical coset and refused
        exact absurd (refuseB _ RankOne.T0 face_T0 hs1 hs2
          ⟨1, by norm_num, by norm_num⟩ ⟨5, by norm_num, by norm_num⟩) not_false
      · -- (5, 1): translated onto the canonical coset and refused
        exact absurd (refuseA _ RankOne.T5 face_T5 hs1 hs2
          ⟨5, by norm_num, by norm_num⟩ ⟨1, by norm_num, by norm_num⟩) not_false
      · -- (5, -1): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (5, 2): realized
        exact ⟨5, 2, by simp [RealizedFive], hs1, hs2⟩
      · -- (5, -2): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (5, 5): translated onto the canonical coset and refused
        exact absurd (refuseA _ (RankOne.T0 + RankOne.T5 + RankOne.P) face_T0T5P hs1 hs2
          ⟨5, by norm_num, by norm_num⟩ ⟨5, by norm_num, by norm_num⟩) not_false
      · -- (5, -5): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (5, 10): realized
        exact ⟨5, 10, by simp [RealizedFive], hs1, hs2⟩
      · -- (5, -10): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (-5, 1): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-5, -1): translated onto the canonical coset and refused
        exact absurd (refuseA _ (RankOne.T5 + RankOne.P) face_T5P hs1 hs2
          ⟨5, by norm_num, by norm_num⟩ ⟨1, by norm_num, by norm_num⟩) not_false
      · -- (-5, 2): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-5, -2): realized
        exact ⟨-5, -2, by simp [RealizedFive], hs1, hs2⟩
      · -- (-5, 5): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-5, -5): translated onto the canonical coset and refused
        exact absurd (refuseA _ (RankOne.T0 + RankOne.T5) face_T0T5 hs1 hs2
          ⟨5, by norm_num, by norm_num⟩ ⟨5, by norm_num, by norm_num⟩) not_false
      · -- (-5, 10): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-5, -10): realized
        exact ⟨-5, -10, by simp [RealizedFive], hs1, hs2⟩
      · -- (10, 1): translated onto the canonical coset and refused
        exact absurd (refuseB _ RankOne.T5 face_T5 hs1 hs2
          ⟨5, by norm_num, by norm_num⟩ ⟨1, by norm_num, by norm_num⟩) not_false
      · -- (10, -1): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (10, 2): translated onto the canonical coset and refused
        exact absurd (refuseC _ RankOne.T5 face_T5 hs1 hs2
          ⟨5, by norm_num, by norm_num⟩ ⟨2, by norm_num, by norm_num⟩) not_false
      · -- (10, -2): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (10, 5): translated onto the canonical coset and refused
        exact absurd (refuseB _ (RankOne.T0 + RankOne.T5 + RankOne.P) face_T0T5P hs1 hs2
          ⟨5, by norm_num, by norm_num⟩ ⟨5, by norm_num, by norm_num⟩) not_false
      · -- (10, -5): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (10, 10): translated onto the canonical coset and refused
        exact absurd (refuseC _ (RankOne.T0 + RankOne.T5 + RankOne.P) face_T0T5P hs1 hs2
          ⟨5, by norm_num, by norm_num⟩ ⟨10, by norm_num, by norm_num⟩) not_false
      · -- (10, -10): mixed signs, refused in the real frame
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (-10, 1): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-10, -1): translated onto the canonical coset and refused
        exact absurd (refuseB _ (RankOne.T5 + RankOne.P) face_T5P hs1 hs2
          ⟨5, by norm_num, by norm_num⟩ ⟨1, by norm_num, by norm_num⟩) not_false
      · -- (-10, 2): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-10, -2): translated onto the canonical coset and refused
        exact absurd (refuseC _ (RankOne.T5 + RankOne.P) face_T5P hs1 hs2
          ⟨5, by norm_num, by norm_num⟩ ⟨2, by norm_num, by norm_num⟩) not_false
      · -- (-10, 5): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-10, -5): translated onto the canonical coset and refused
        exact absurd (refuseB _ (RankOne.T0 + RankOne.T5) face_T0T5 hs1 hs2
          ⟨5, by norm_num, by norm_num⟩ ⟨5, by norm_num, by norm_num⟩) not_false
      · -- (-10, 10): mixed signs, refused in the real frame
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-10, -10): translated onto the canonical coset and refused
        exact absurd (refuseC _ (RankOne.T0 + RankOne.T5) face_T0T5 hs1 hs2
          ⟨5, by norm_num, by norm_num⟩ ⟨10, by norm_num, by norm_num⟩) not_false

/-- **THE REALIZED EIGHT ARE IN THE IMAGE**: with the upper bound, the image of the
descent face on `E₅(ℚ)` is exactly the realized group — the two-descent of the
five-curve is complete, the second Ш[2]-vanishing certificate of the mod-two
programme. -/
theorem theRealizedEightAreInTheImage (d₁ d₂ : ℚ) (h : RealizedFive d₁ d₂) :
    ∃ P : RankOne.E5.Point,
      Descent.SqCls (RankOne.slotOne P) d₁ ∧ Descent.SqCls (RankOne.slotTwo P) d₂ := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨0, face_zero0⟩
  · exact ⟨_, face_T0P⟩
  · exact ⟨_, face_T5⟩
  · exact ⟨_, face_T0T5P⟩
  · exact ⟨_, face_P⟩
  · exact ⟨_, face_T0⟩
  · exact ⟨_, face_T5P⟩
  · exact ⟨_, face_T0T5⟩

end Soma.Holonics.Millennium.FaceImageFive
