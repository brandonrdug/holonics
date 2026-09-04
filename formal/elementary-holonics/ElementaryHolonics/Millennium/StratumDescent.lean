import ElementaryHolonics.Millennium.FamilyFace
import ElementaryHolonics.Millennium.Congruum
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-!
# StratumDescent: the completed descent for every prime in the three-mod-eight class

**The governance law, family-wise — component one of the mod-two Birch–Swinnerton-Dyer
programme.**  For **every** prime `p ≡ 3 (mod 8)`, the descent face of the twist
`y² = x³ − p²x` has image **exactly the four torsion classes**

```text
(1, 1)   (−1, −p)   (p, 2)   (−p, −2p)
```

— corank zero across an infinite family, decided by the two governing characters: the
quarter-turn invisible (`−1` a non-square mod `p`) and two invisible (`2` a non-square
mod `p`).  These are the entries of the stratum's governance matrix, and the corank law
holds with the completed descent as its content: **infinitely many Ш[2]-vanishing
certificates in one theorem**, the family-wise sibling of the per-instance descents at
five and thirty-four.

The architecture is the instanced files' at a symbolic prime: the support law (distant
primes see even valuations, so slot classes live on `±{1, 2, p, 2p}`), the sign law
(mixed signs die in the real frame), and **seven** canonical coset refusals — six by
`p`-adic infinite descent riding the two character lemmas of `Congruum.lean`
(`theSumOfSquaresDescendsToTheFrame`, `theDoubledSquareDescendsToTheFrame`), one by a
family-wise mod-eight refusal (`p ≡ 3` fixes the coefficients, so one kernel `decide`
covers the whole class).  The remaining twenty-eight refused classes translate onto
the canonicals through the family homomorphism by adding torsion points.

Every `theorem` is discharged and none depends on `sorryAx`.  **Boundary**: the words
"Selmer", "Ш" and "rank" are classical readings carried as `interpretation`; the
stratum is `p ≡ 3 (mod 8)` and no other congruence class is claimed; nothing about the
Birch–Swinnerton-Dyer conjecture.
-/

set_option maxHeartbeats 1600000

namespace Soma.Holonics.Millennium.StratumDescent

open WeierstrassCurve.Affine

variable {p : ℕ}

/-! ## 1. Square-class helpers and the governing characters -/

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

private lemma prime_int (hp : p.Prime) : Prime (p : ℤ) :=
  Nat.prime_iff_prime_int.mp hp

private lemma p_pos (hp : p.Prime) : (0 : ℚ) < p := by
  exact_mod_cast hp.pos

private lemma pQ_ne (hp : p.Prime) : ((p : ℚ)) ≠ 0 := ne_of_gt (p_pos hp)

/-- The prime is not a rational square. -/
private lemma notSquareP (hp : p.Prime) : ¬ IsSquare ((p : ℕ) : ℚ) := by
  rw [Rat.isSquare_natCast_iff]
  exact hp.not_isSquare

/-- Twice the prime is not a rational square (the prime is odd on the stratum). -/
private lemma notSquareTwoP (_hp : p.Prime) (h8 : p % 8 = 3) :
    ¬ IsSquare (((2 * p : ℕ) : ℚ)) := by
  rw [Rat.isSquare_natCast_iff]
  rintro ⟨r, hr⟩
  have h2 : 2 ∣ r * r := ⟨p, by linarith⟩
  have hr2 : 2 ∣ r := (Nat.Prime.dvd_mul Nat.prime_two).mp h2 |>.elim id id
  obtain ⟨s, rfl⟩ := hr2
  have hps : p = 2 * s ^ 2 := by nlinarith
  omega

/-! ## 2. The curve, the slots, the torsion faces -/

private lemma onCurveP {x y : ℚ} (h : (FamilyFace.E p).Nonsingular x y) :
    y ^ 2 = x ^ 3 - (p : ℚ) ^ 2 * x := by
  have h1 := ((nonsingular_iff x y).mp h).1
  rw [equation_iff] at h1
  simp only [FamilyFace.E] at h1
  linarith [h1]

private lemma avoidP {x y : ℚ} (h : y ^ 2 = x ^ 3 - (p : ℚ) ^ 2 * x) (hy : y ≠ 0) :
    x ≠ 0 ∧ x ≠ (p : ℚ) ∧ x ≠ -(p : ℚ) :=
  FaceHomomorphism.theNonzeroOrdinateAvoidsTheRoots (n := (p : ℚ)) h hy

private lemma slotPOne_some {x y : ℚ} (h : (FamilyFace.E p).Nonsingular x y) :
    FamilyFace.slotOne p (.some x y h) = if x = 0 then -(p : ℚ) ^ 2 else x := rfl

private lemma slotPTwo_some {x y : ℚ} (h : (FamilyFace.E p).Nonsingular x y) :
    FamilyFace.slotTwo p (.some x y h) = if x = (p : ℚ) then 2 * (p : ℚ) ^ 2 else x - p := rfl

/-! ## 3. The sign law on the stratum -/

theorem theSignsAgreeOnTheStratum (hp : p.Prime) {x y d₁ d₂ : ℚ}
    (hcurve : y ^ 2 = x ^ 3 - (p : ℚ) ^ 2 * x) (hy : y ≠ 0)
    (h₁ : Descent.SqCls x d₁) (h₂ : Descent.SqCls (x - p) d₂) :
    (0 < d₁ ∧ 0 < d₂) ∨ (d₁ < 0 ∧ d₂ < 0) := by
  obtain ⟨hx0, hxp, hxmp⟩ := avoidP hcurve hy
  have hppos := p_pos hp
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
        exact hxp (by linarith [hval])
  · left
    have hxp' : (p : ℚ) < x := by
      by_contra hcon
      push_neg at hcon
      have hlt : x < p := lt_of_le_of_ne hcon hxp
      have hx2 : x ^ 2 < (p : ℚ) ^ 2 := by nlinarith
      have hpos : 0 < x * ((p : ℚ) ^ 2 - x ^ 2) := mul_pos hx (by linarith)
      nlinarith [hy2]
    exact ⟨hs₁.mp hx, hs₂.mp (by linarith)⟩

/-! ## 4. The support law on the stratum -/

private lemma val_add_leftP {ℓ : ℕ} [Fact ℓ.Prime] {a b : ℚ} (ha : a ≠ 0)
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

private lemma prime_not_dvd_2p (hp : p.Prime) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (h2 : ℓ ≠ 2) (hne : ℓ ≠ p) : ¬ ℓ ∣ 2 * p := by
  intro hc
  rcases (Nat.Prime.dvd_mul hℓ).mp hc with h | h
  · exact h2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h)
  · exact hne ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h)

private lemma val_const_zeroP (hp : p.Prime) {ℓ : ℕ} [hf : Fact ℓ.Prime]
    (h2 : ℓ ≠ 2) (hne : ℓ ≠ p) :
    padicValRat ℓ ((p : ℚ)) = 0 ∧ padicValRat ℓ (-(p : ℚ)) = 0 ∧
    padicValRat ℓ (2 * (p : ℚ)) = 0 := by
  have hℓ : ℓ.Prime := hf.out
  have key : ∀ m : ℤ, ¬ (ℓ : ℤ) ∣ m → padicValRat ℓ (m : ℚ) = 0 := by
    intro m hdvd
    rw [padicValRat.of_int, padicValInt.eq_zero_iff.mpr (Or.inr (Or.inr hdvd))]
    simp
  have hnd : ∀ m : ℤ, m.natAbs ∣ 2 * p → ¬ (ℓ : ℤ) ∣ m := by
    intro m hm hc
    refine prime_not_dvd_2p hp hℓ h2 hne (dvd_trans ?_ hm)
    simpa using Int.natAbs_dvd_natAbs.mpr hc
  refine ⟨?_, ?_, ?_⟩
  · simpa using key (p : ℤ) (hnd (p : ℤ) (by simp))
  · have := key (-(p : ℤ)) (hnd (-(p : ℤ)) (by simp))
    push_cast at this
    exact this
  · have := key (2 * (p : ℤ)) (hnd (2 * (p : ℤ)) (by simp [Int.natAbs_mul]))
    push_cast at this
    exact this

private lemma even_slot_valP (hp : p.Prime) {ℓ : ℕ} [Fact ℓ.Prime]
    (h2 : ℓ ≠ 2) (hne : ℓ ≠ p)
    {x y : ℚ} (hcurve : y ^ 2 = x ^ 3 - (p : ℚ) ^ 2 * x) (hy : y ≠ 0) :
    Even (padicValRat ℓ x) ∧ Even (padicValRat ℓ (x - p)) := by
  obtain ⟨hx0, hxp, hxmp⟩ := avoidP hcurve hy
  have hxm : x - p ≠ 0 := sub_ne_zero.mpr hxp
  have hxpl : x + p ≠ 0 := fun hc => hxmp (by linarith)
  have hpne := pQ_ne hp
  have hfact : y ^ 2 = x * (x - p) * (x + p) := by linear_combination hcurve
  have hprod : 2 * padicValRat ℓ y =
      padicValRat ℓ x + padicValRat ℓ (x - p) + padicValRat ℓ (x + p) := by
    have hmul1 : padicValRat ℓ (x * (x - p) * (x + p)) =
        padicValRat ℓ x + padicValRat ℓ (x - p) + padicValRat ℓ (x + p) := by
      rw [padicValRat.mul (mul_ne_zero hx0 hxm) hxpl, padicValRat.mul hx0 hxm]
    have hpow : padicValRat ℓ (y ^ 2) = 2 * padicValRat ℓ y := by
      rw [pow_two, padicValRat.mul hy hy]
      ring
    rw [← hpow, hfact, hmul1]
  obtain ⟨vp, vmp, v2p⟩ := val_const_zeroP hp (ℓ := ℓ) h2 hne
  constructor
  · rcases lt_trichotomy (padicValRat ℓ x) 0 with hv | hv | hv
    · have e1 : padicValRat ℓ (x - p) = padicValRat ℓ x := by
        have := val_add_leftP (ℓ := ℓ) hx0
          (by rw [show x + -(p : ℚ) = x - p by ring]; exact hxm)
          (by rw [vmp]; exact hv)
        rw [show x + -(p : ℚ) = x - p by ring] at this
        exact this
      have e2 : padicValRat ℓ (x + p) = padicValRat ℓ x :=
        val_add_leftP (ℓ := ℓ) hx0 hxpl (by rw [vp]; exact hv)
      rw [e1, e2] at hprod
      exact ⟨padicValRat ℓ y - padicValRat ℓ x, by linarith⟩
    · exact ⟨0, by rw [hv]; ring⟩
    · have e1 : padicValRat ℓ (x - p) = 0 := by
        have := val_add_leftP (ℓ := ℓ) (neg_ne_zero.mpr hpne)
          (by rw [show -(p : ℚ) + x = x - p by ring]; exact hxm)
          (by rw [vmp]; exact hv)
        rw [show -(p : ℚ) + x = x - p by ring, vmp] at this
        exact this
      have e2 : padicValRat ℓ (x + p) = 0 := by
        have := val_add_leftP (ℓ := ℓ) hpne
          (by rw [show (p : ℚ) + x = x + p by ring]; exact hxpl)
          (by rw [vp]; exact hv)
        rw [show (p : ℚ) + x = x + p by ring, vp] at this
        exact this
      rw [e1, e2] at hprod
      exact ⟨padicValRat ℓ y, by linarith⟩
  · rcases lt_trichotomy (padicValRat ℓ (x - p)) 0 with hv | hv | hv
    · have e1 : padicValRat ℓ x = padicValRat ℓ (x - p) := by
        have := val_add_leftP (ℓ := ℓ) hxm
          (by rw [show x - p + p = x by ring]; exact hx0)
          (by rw [vp]; exact hv)
        rw [show x - (p : ℚ) + p = x by ring] at this
        exact this
      have e2 : padicValRat ℓ (x + p) = padicValRat ℓ (x - p) := by
        have := val_add_leftP (ℓ := ℓ) hxm
          (by rw [show x - p + 2 * (p : ℚ) = x + p by ring]; exact hxpl)
          (by rw [v2p]; exact hv)
        rw [show x - (p : ℚ) + 2 * (p : ℚ) = x + p by ring] at this
        exact this
      rw [e1, e2] at hprod
      exact ⟨padicValRat ℓ y - padicValRat ℓ (x - p), by linarith⟩
    · exact ⟨0, by rw [hv]; ring⟩
    · have e1 : padicValRat ℓ x = 0 := by
        have := val_add_leftP (ℓ := ℓ) hpne
          (by rw [show (p : ℚ) + (x - p) = x by ring]; exact hx0)
          (by rw [vp]; exact hv)
        rw [show (p : ℚ) + (x - p) = x by ring, vp] at this
        exact this
      have e2 : padicValRat ℓ (x + p) = 0 := by
        have := val_add_leftP (ℓ := ℓ) (by positivity : 2 * (p : ℚ) ≠ 0)
          (by rw [show 2 * (p : ℚ) + (x - p) = x + p by ring]; exact hxpl)
          (by rw [v2p]; exact hv)
        rw [show 2 * (p : ℚ) + (x - p) = x + p by ring, v2p] at this
        exact this
      rw [e1, e2] at hprod
      exact ⟨padicValRat ℓ y, by linarith⟩

/-- The eight candidate classes on the stratum: `±1, ±2, ±p, ±2p`. -/
def OnDiscriminantP (p : ℕ) (d : ℚ) : Prop :=
  d = 1 ∨ d = -1 ∨ d = 2 ∨ d = -2 ∨ d = (p : ℚ) ∨ d = -(p : ℚ) ∨
  d = 2 * (p : ℚ) ∨ d = -(2 * (p : ℚ))

private lemma dvd_two_mul_prime (hp : p.Prime) {a : ℕ}
    (h : a ∣ 2 * p) : a = 1 ∨ a = 2 ∨ a = p ∨ a = 2 * p := by
  by_cases h2 : 2 ∣ a
  · obtain ⟨a', rfl⟩ := h2
    have ha' : a' ∣ p := by
      have := (mul_dvd_mul_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp h
      exact this
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp a' ha') with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr rfl))
  · have hcop : Nat.Coprime a 2 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2).symm
    have ha : a ∣ p := (Nat.Coprime.dvd_of_dvd_mul_left hcop h)
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp a ha) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl rfl))

private lemma classFromEvenValuationsP (hp : p.Prime) (hne2 : p ≠ 2) {x : ℚ}
    (hx : x ≠ 0)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ≠ p → Even (padicValRat ℓ x)) :
    ∃ d : ℚ, OnDiscriminantP p d ∧ Descent.SqCls x d := by
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
  have hmv : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ≠ p →
      Even ((x.num * (x.den : ℤ)).natAbs.factorization ℓ) := by
    intro ℓ hℓ h2 hnep
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    have hval := h ℓ hℓ h2 hnep
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
  have hadvd : a ∣ 2 * p := by
    rw [← Nat.factorization_le_iff_dvd ha0 (by
      have := hp.pos
      positivity)]
    rw [Finsupp.le_def]
    intro ℓ
    by_cases hℓp : ℓ.Prime
    · by_cases hdvd : ℓ ∣ a
      · have hle1 : a.factorization ℓ ≤ 1 :=
          (Nat.squarefree_iff_factorization_le_one ha0).mp hsq ℓ
        have hmem : ℓ = 2 ∨ ℓ = p := by
          by_contra hcon
          push_neg at hcon
          obtain ⟨h2, hnep⟩ := hcon
          have heven := hmv ℓ hℓp h2 hnep
          rw [← hab, Nat.factorization_mul (pow_ne_zero 2 hb0) ha0,
            Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply,
            smul_eq_mul] at heven
          have hpos : 0 < a.factorization ℓ :=
            Nat.Prime.factorization_pos_of_dvd hℓp ha0 hdvd
          obtain ⟨k, hk⟩ := heven
          omega
        have hfac2p : (2 * p).factorization ℓ = 1 := by
          rcases hmem with rfl | rfl
          · rw [Nat.factorization_mul (by norm_num) hp.pos.ne', Finsupp.add_apply,
              Nat.Prime.factorization_self (by norm_num),
              Nat.factorization_eq_zero_of_not_dvd (by
                intro hc
                exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hc)
                  (by omega))]
          · rw [Nat.factorization_mul (by norm_num) hp.pos.ne', Finsupp.add_apply,
              Nat.Prime.factorization_self hp,
              Nat.factorization_eq_zero_of_not_dvd (by
                intro hc
                exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hc)
                  (by omega))]
        rw [hfac2p]
        exact hle1
      · rw [Nat.factorization_eq_zero_of_not_dvd hdvd]
        exact Nat.zero_le _
    · rw [Nat.factorization_eq_zero_of_not_prime _ hℓp]
      exact Nat.zero_le _
  have hamem := dvd_two_mul_prime hp hadvd
  rcases Int.natAbs_eq (x.num * (x.den : ℤ)) with hs | hs
  · refine ⟨(a : ℚ), ?_, ?_⟩
    · rcases hamem with rfl | rfl | rfl | rfl
      · exact Or.inl (by norm_num)
      · exact Or.inr (Or.inr (Or.inl (by norm_num)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by push_cast; ring)))))))
    · refine sqcls_trans hcls ⟨(b : ℚ), by exact_mod_cast hb0, ?_⟩
      rw [hs]
      push_cast [← hab]
      ring
  · refine ⟨-(a : ℚ), ?_, ?_⟩
    · rcases hamem with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl (by norm_num))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by norm_num))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by push_cast; ring)))))))
    · refine sqcls_trans hcls ⟨(b : ℚ), by exact_mod_cast hb0, ?_⟩
      rw [hs]
      push_cast [← hab]
      ring

theorem theSlotClassesAreSupportedOnTheStratum (hp : p.Prime) (hne2 : p ≠ 2)
    {x y : ℚ} (hcurve : y ^ 2 = x ^ 3 - (p : ℚ) ^ 2 * x) (hy : y ≠ 0) :
    (∃ d₁ : ℚ, OnDiscriminantP p d₁ ∧ Descent.SqCls x d₁) ∧
    (∃ d₂ : ℚ, OnDiscriminantP p d₂ ∧ Descent.SqCls (x - p) d₂) := by
  obtain ⟨hx0, hxp, -⟩ := avoidP hcurve hy
  constructor
  · exact classFromEvenValuationsP hp hne2 hx0 fun ℓ hℓ h2 hnep =>
      haveI : Fact ℓ.Prime := ⟨hℓ⟩
      (even_slot_valP hp h2 hnep hcurve hy).1
  · exact classFromEvenValuationsP hp hne2 (sub_ne_zero.mpr hxp) fun ℓ hℓ h2 hnep =>
      haveI : Fact ℓ.Prime := ⟨hℓ⟩
      (even_slot_valP hp h2 hnep hcurve hy).2

/-! ## 5. The seven refusal kernels -/

private lemma p_ge_three (h8 : p % 8 = 3) : 3 ≤ p := by omega

private lemma pZ_ne (hp : p.Prime) : ((p : ℤ)) ≠ 0 := by
  exact_mod_cast hp.pos.ne'

private lemma p_not_dvd_two (h8 : p % 8 = 3) : ¬ (p : ℤ) ∣ 2 := by
  intro hc
  have h1 : p ∣ 2 := by
    have := Int.natAbs_dvd_natAbs.mpr hc
    simpa using this
  have := Nat.le_of_dvd (by norm_num) h1
  omega

private lemma pdvd_of_dvd_two_mul (hp : p.Prime) (h8 : p % 8 = 3) {m : ℤ}
    (h : (p : ℤ) ∣ 2 * m ^ 2) : (p : ℤ) ∣ m := by
  have hpz := prime_int hp
  rcases hpz.dvd_mul.mp h with h' | h'
  · exact absurd h' (p_not_dvd_two h8)
  · exact hpz.dvd_of_dvd_pow h'

private lemma pdvd_sq (hp : p.Prime) {m : ℤ} (h : (p : ℤ) ∣ m ^ 2) : (p : ℤ) ∣ m :=
  (prime_int hp).dvd_of_dvd_pow h

private lemma natAbs_lt_mul (_hp : p.Prime) (h8 : p % 8 = 3) {N : ℤ} (hN : N ≠ 0) :
    N.natAbs < ((p : ℤ) * N).natAbs := by
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  have h3 := p_ge_three h8
  have hne : N.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hN
  nlinarith [Nat.pos_of_ne_zero hne]

private lemma kernelOneTwo (hp : p.Prime) (h8 : p % 8 = 3) [Fact p.Prime] :
    ∀ (n : ℕ), ∀ C E F N : ℤ, N.natAbs = n → N ≠ 0 →
    C ^ 2 - (p : ℤ) * N ^ 2 = 2 * E ^ 2 → C ^ 2 + (p : ℤ) * N ^ 2 = 2 * F ^ 2 → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C E F N hNa hN0 h1 h2
    obtain ⟨hE, hC⟩ := Congruum.theDoubledSquareDescendsToTheFrame h8 (a := E) (d := C)
      ⟨N ^ 2, by linarith⟩
    obtain ⟨C', rfl⟩ := hC
    obtain ⟨E', rfl⟩ := hE
    have hF : (p : ℤ) ∣ F := by
      refine pdvd_of_dvd_two_mul hp h8 ⟨(p : ℤ) * C' ^ 2 + N ^ 2, ?_⟩
      rw [← h2]
      ring
    obtain ⟨F', rfl⟩ := hF
    have hN : (p : ℤ) ∣ N := by
      refine pdvd_sq hp ⟨C' ^ 2 - 2 * E' ^ 2, ?_⟩
      have hcan : (p : ℤ) * N ^ 2 =
          (p : ℤ) * ((p : ℤ) * (C' ^ 2 - 2 * E' ^ 2)) := by
        linear_combination -h1
      exact mul_left_cancel₀ (pZ_ne hp) hcan
    obtain ⟨N', rfl⟩ := hN
    have hN'0 : N' ≠ 0 := fun hc => hN0 (by rw [hc]; ring)
    have hp2 : ((p : ℤ)) ^ 2 ≠ 0 := pow_ne_zero 2 (pZ_ne hp)
    have h1' : C' ^ 2 - (p : ℤ) * N' ^ 2 = 2 * E' ^ 2 := by
      have hfac : ((p : ℤ)) ^ 2 * (C' ^ 2 - (p : ℤ) * N' ^ 2) =
          ((p : ℤ)) ^ 2 * (2 * E' ^ 2) := by linear_combination h1
      exact mul_left_cancel₀ hp2 hfac
    have h2' : C' ^ 2 + (p : ℤ) * N' ^ 2 = 2 * F' ^ 2 := by
      have hfac : ((p : ℤ)) ^ 2 * (C' ^ 2 + (p : ℤ) * N' ^ 2) =
          ((p : ℤ)) ^ 2 * (2 * F' ^ 2) := by linear_combination h2
      exact mul_left_cancel₀ hp2 hfac
    exact ih N'.natAbs (hNa ▸ natAbs_lt_mul hp h8 hN'0) C' E' F' N' rfl hN'0 h1' h2'

private lemma kernelOneP (hp : p.Prime) (h8 : p % 8 = 3) [Fact p.Prime] :
    ∀ (n : ℕ), ∀ C E F N : ℤ, N.natAbs = n → N ≠ 0 →
    C ^ 2 - (p : ℤ) * N ^ 2 = (p : ℤ) * E ^ 2 →
    C ^ 2 + (p : ℤ) * N ^ 2 = (p : ℤ) * F ^ 2 → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C E F N hNa hN0 h1 h2
    have hC : (p : ℤ) ∣ C := pdvd_sq hp ⟨N ^ 2 + E ^ 2, by linarith⟩
    obtain ⟨C', rfl⟩ := hC
    have hmid : (p : ℤ) * C' ^ 2 = N ^ 2 + E ^ 2 := by
      have hcan : (p : ℤ) * ((p : ℤ) * C' ^ 2) = (p : ℤ) * (N ^ 2 + E ^ 2) := by
        linear_combination h1
      exact mul_left_cancel₀ (pZ_ne hp) hcan
    obtain ⟨hN, hE⟩ := Congruum.theSumOfSquaresDescendsToTheFrame h8 (c := N) (d := E)
      ⟨C' ^ 2, hmid.symm⟩
    obtain ⟨N', rfl⟩ := hN
    obtain ⟨E', rfl⟩ := hE
    have hF : (p : ℤ) ∣ F := by
      refine pdvd_sq hp ⟨C' ^ 2 + (p : ℤ) * N' ^ 2, ?_⟩
      have hcan : (p : ℤ) * F ^ 2 =
          (p : ℤ) * ((p : ℤ) * (C' ^ 2 + (p : ℤ) * N' ^ 2)) := by
        linear_combination -h2
      exact mul_left_cancel₀ (pZ_ne hp) hcan
    obtain ⟨F', rfl⟩ := hF
    have hN'0 : N' ≠ 0 := fun hc => hN0 (by rw [hc]; ring)
    have hp2 : ((p : ℤ)) ^ 2 ≠ 0 := pow_ne_zero 2 (pZ_ne hp)
    have h1' : C' ^ 2 - (p : ℤ) * N' ^ 2 = (p : ℤ) * E' ^ 2 := by
      have hfac : ((p : ℤ)) ^ 2 * (C' ^ 2 - (p : ℤ) * N' ^ 2) =
          ((p : ℤ)) ^ 2 * ((p : ℤ) * E' ^ 2) := by linear_combination h1
      exact mul_left_cancel₀ hp2 hfac
    have h2' : C' ^ 2 + (p : ℤ) * N' ^ 2 = (p : ℤ) * F' ^ 2 := by
      have hfac : ((p : ℤ)) ^ 2 * (C' ^ 2 + (p : ℤ) * N' ^ 2) =
          ((p : ℤ)) ^ 2 * ((p : ℤ) * F' ^ 2) := by linear_combination h2
      exact mul_left_cancel₀ hp2 hfac
    exact ih N'.natAbs (hNa ▸ natAbs_lt_mul hp h8 hN'0) C' E' F' N' rfl hN'0 h1' h2'

private lemma kernelOneTwoP (hp : p.Prime) (h8 : p % 8 = 3) [Fact p.Prime] :
    ∀ (n : ℕ), ∀ C E F N : ℤ, N.natAbs = n → N ≠ 0 →
    C ^ 2 - (p : ℤ) * N ^ 2 = 2 * (p : ℤ) * E ^ 2 →
    C ^ 2 + (p : ℤ) * N ^ 2 = 2 * (p : ℤ) * F ^ 2 → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C E F N hNa hN0 h1 h2
    have hC : (p : ℤ) ∣ C := pdvd_sq hp ⟨N ^ 2 + 2 * E ^ 2, by linarith⟩
    obtain ⟨C', rfl⟩ := hC
    have hi : (p : ℤ) * C' ^ 2 - N ^ 2 = 2 * E ^ 2 := by
      have hcan : (p : ℤ) * ((p : ℤ) * C' ^ 2 - N ^ 2) = (p : ℤ) * (2 * E ^ 2) := by
        linear_combination h1
      exact mul_left_cancel₀ (pZ_ne hp) hcan
    have hii : (p : ℤ) * C' ^ 2 + N ^ 2 = 2 * F ^ 2 := by
      have hcan : (p : ℤ) * ((p : ℤ) * C' ^ 2 + N ^ 2) = (p : ℤ) * (2 * F ^ 2) := by
        linear_combination h2
      exact mul_left_cancel₀ (pZ_ne hp) hcan
    have hmid : (p : ℤ) * C' ^ 2 = E ^ 2 + F ^ 2 := by linarith
    obtain ⟨hE, hF⟩ := Congruum.theSumOfSquaresDescendsToTheFrame h8 (c := E) (d := F)
      ⟨C' ^ 2, hmid.symm⟩
    obtain ⟨E', rfl⟩ := hE
    obtain ⟨F', rfl⟩ := hF
    have hN : (p : ℤ) ∣ N := by
      refine pdvd_sq hp ⟨C' ^ 2 - 2 * (p : ℤ) * E' ^ 2, ?_⟩
      linear_combination -hi
    obtain ⟨N', rfl⟩ := hN
    have hN'0 : N' ≠ 0 := fun hc => hN0 (by rw [hc]; ring)
    have hp2 : ((p : ℤ)) ^ 2 ≠ 0 := pow_ne_zero 2 (pZ_ne hp)
    have h1' : C' ^ 2 - (p : ℤ) * N' ^ 2 = 2 * (p : ℤ) * E' ^ 2 := by
      have hfac : ((p : ℤ)) ^ 2 * (C' ^ 2 - (p : ℤ) * N' ^ 2) =
          ((p : ℤ)) ^ 2 * (2 * (p : ℤ) * E' ^ 2) := by linear_combination h1
      exact mul_left_cancel₀ hp2 hfac
    have h2' : C' ^ 2 + (p : ℤ) * N' ^ 2 = 2 * (p : ℤ) * F' ^ 2 := by
      have hfac : ((p : ℤ)) ^ 2 * (C' ^ 2 + (p : ℤ) * N' ^ 2) =
          ((p : ℤ)) ^ 2 * (2 * (p : ℤ) * F' ^ 2) := by linear_combination h2
      exact mul_left_cancel₀ hp2 hfac
    exact ih N'.natAbs (hNa ▸ natAbs_lt_mul hp h8 hN'0) C' E' F' N' rfl hN'0 h1' h2'

private lemma kernelTwoOne (hp : p.Prime) (h8 : p % 8 = 3) [Fact p.Prime] :
    ∀ (n : ℕ), ∀ C E F N : ℤ, N.natAbs = n → N ≠ 0 →
    2 * C ^ 2 - (p : ℤ) * N ^ 2 = E ^ 2 →
    2 * C ^ 2 + (p : ℤ) * N ^ 2 = 2 * F ^ 2 → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C E F N hNa hN0 h1 h2
    obtain ⟨hC, hE⟩ := Congruum.theDoubledSquareDescendsToTheFrame h8 (a := C) (d := E)
      ⟨-N ^ 2, by linarith⟩
    obtain ⟨C', rfl⟩ := hC
    obtain ⟨E', rfl⟩ := hE
    have hF : (p : ℤ) ∣ F := by
      refine pdvd_of_dvd_two_mul hp h8 ⟨2 * (p : ℤ) * C' ^ 2 + N ^ 2, ?_⟩
      rw [← h2]
      ring
    obtain ⟨F', rfl⟩ := hF
    have hN : (p : ℤ) ∣ N := by
      refine pdvd_sq hp ⟨2 * C' ^ 2 - E' ^ 2, ?_⟩
      have hcan : (p : ℤ) * N ^ 2 =
          (p : ℤ) * ((p : ℤ) * (2 * C' ^ 2 - E' ^ 2)) := by
        linear_combination -h1
      exact mul_left_cancel₀ (pZ_ne hp) hcan
    obtain ⟨N', rfl⟩ := hN
    have hN'0 : N' ≠ 0 := fun hc => hN0 (by rw [hc]; ring)
    have hp2 : ((p : ℤ)) ^ 2 ≠ 0 := pow_ne_zero 2 (pZ_ne hp)
    have h1' : 2 * C' ^ 2 - (p : ℤ) * N' ^ 2 = E' ^ 2 := by
      have hfac : ((p : ℤ)) ^ 2 * (2 * C' ^ 2 - (p : ℤ) * N' ^ 2) =
          ((p : ℤ)) ^ 2 * (E' ^ 2) := by linear_combination h1
      exact mul_left_cancel₀ hp2 hfac
    have h2' : 2 * C' ^ 2 + (p : ℤ) * N' ^ 2 = 2 * F' ^ 2 := by
      have hfac : ((p : ℤ)) ^ 2 * (2 * C' ^ 2 + (p : ℤ) * N' ^ 2) =
          ((p : ℤ)) ^ 2 * (2 * F' ^ 2) := by linear_combination h2
      exact mul_left_cancel₀ hp2 hfac
    exact ih N'.natAbs (hNa ▸ natAbs_lt_mul hp h8 hN'0) C' E' F' N' rfl hN'0 h1' h2'

private lemma kernelTwoTwo (hp : p.Prime) (h8 : p % 8 = 3) [Fact p.Prime] :
    ∀ (n : ℕ), ∀ C E F N : ℤ, N.natAbs = n → N ≠ 0 →
    2 * C ^ 2 - (p : ℤ) * N ^ 2 = 2 * E ^ 2 →
    2 * C ^ 2 + (p : ℤ) * N ^ 2 = F ^ 2 → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C E F N hNa hN0 h1 h2
    obtain ⟨hC, hF⟩ := Congruum.theDoubledSquareDescendsToTheFrame h8 (a := C) (d := F)
      ⟨N ^ 2, by linarith⟩
    obtain ⟨C', rfl⟩ := hC
    obtain ⟨F', rfl⟩ := hF
    have hE : (p : ℤ) ∣ E := by
      refine pdvd_of_dvd_two_mul hp h8 ⟨2 * (p : ℤ) * C' ^ 2 - N ^ 2, ?_⟩
      rw [← h1]
      ring
    obtain ⟨E', rfl⟩ := hE
    have hN : (p : ℤ) ∣ N := by
      refine pdvd_sq hp ⟨2 * C' ^ 2 - 2 * E' ^ 2, ?_⟩
      have hcan : (p : ℤ) * N ^ 2 =
          (p : ℤ) * ((p : ℤ) * (2 * C' ^ 2 - 2 * E' ^ 2)) := by
        linear_combination -h1
      exact mul_left_cancel₀ (pZ_ne hp) hcan
    obtain ⟨N', rfl⟩ := hN
    have hN'0 : N' ≠ 0 := fun hc => hN0 (by rw [hc]; ring)
    have hp2 : ((p : ℤ)) ^ 2 ≠ 0 := pow_ne_zero 2 (pZ_ne hp)
    have h1' : 2 * C' ^ 2 - (p : ℤ) * N' ^ 2 = 2 * E' ^ 2 := by
      have hfac : ((p : ℤ)) ^ 2 * (2 * C' ^ 2 - (p : ℤ) * N' ^ 2) =
          ((p : ℤ)) ^ 2 * (2 * E' ^ 2) := by linear_combination h1
      exact mul_left_cancel₀ hp2 hfac
    have h2' : 2 * C' ^ 2 + (p : ℤ) * N' ^ 2 = F' ^ 2 := by
      have hfac : ((p : ℤ)) ^ 2 * (2 * C' ^ 2 + (p : ℤ) * N' ^ 2) =
          ((p : ℤ)) ^ 2 * (F' ^ 2) := by linear_combination h2
      exact mul_left_cancel₀ hp2 hfac
    exact ih N'.natAbs (hNa ▸ natAbs_lt_mul hp h8 hN'0) C' E' F' N' rfl hN'0 h1' h2'

private lemma kernelTwoP (hp : p.Prime) (h8 : p % 8 = 3) [Fact p.Prime] :
    ∀ (n : ℕ), ∀ C E F N : ℤ, N.natAbs = n → N ≠ 0 →
    2 * C ^ 2 - (p : ℤ) * N ^ 2 = (p : ℤ) * E ^ 2 →
    2 * C ^ 2 + (p : ℤ) * N ^ 2 = 2 * (p : ℤ) * F ^ 2 → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C E F N hNa hN0 h1 h2
    have hC : (p : ℤ) ∣ C :=
      pdvd_of_dvd_two_mul hp h8 ⟨N ^ 2 + E ^ 2, by linarith⟩
    obtain ⟨C', rfl⟩ := hC
    have hi : 2 * (p : ℤ) * C' ^ 2 - N ^ 2 = E ^ 2 := by
      have hcan : (p : ℤ) * (2 * (p : ℤ) * C' ^ 2 - N ^ 2) = (p : ℤ) * E ^ 2 := by
        linear_combination h1
      exact mul_left_cancel₀ (pZ_ne hp) hcan
    have hmid : (p : ℤ) * (2 * C' ^ 2) = N ^ 2 + E ^ 2 := by linarith
    obtain ⟨hN, hE⟩ := Congruum.theSumOfSquaresDescendsToTheFrame h8 (c := N) (d := E)
      ⟨2 * C' ^ 2, hmid.symm⟩
    obtain ⟨N', rfl⟩ := hN
    obtain ⟨E', rfl⟩ := hE
    have hF : (p : ℤ) ∣ F := by
      refine pdvd_of_dvd_two_mul hp h8 ⟨2 * C' ^ 2 + (p : ℤ) * N' ^ 2, ?_⟩
      have hcan : (p : ℤ) * (2 * F ^ 2) =
          (p : ℤ) * ((p : ℤ) * (2 * C' ^ 2 + (p : ℤ) * N' ^ 2)) := by
        linear_combination -h2
      exact mul_left_cancel₀ (pZ_ne hp) hcan
    obtain ⟨F', rfl⟩ := hF
    have hN'0 : N' ≠ 0 := fun hc => hN0 (by rw [hc]; ring)
    have hp2 : ((p : ℤ)) ^ 2 ≠ 0 := pow_ne_zero 2 (pZ_ne hp)
    have h1' : 2 * C' ^ 2 - (p : ℤ) * N' ^ 2 = (p : ℤ) * E' ^ 2 := by
      have hfac : ((p : ℤ)) ^ 2 * (2 * C' ^ 2 - (p : ℤ) * N' ^ 2) =
          ((p : ℤ)) ^ 2 * ((p : ℤ) * E' ^ 2) := by linear_combination h1
      exact mul_left_cancel₀ hp2 hfac
    have h2' : 2 * C' ^ 2 + (p : ℤ) * N' ^ 2 = 2 * (p : ℤ) * F' ^ 2 := by
      have hfac : ((p : ℤ)) ^ 2 * (2 * C' ^ 2 + (p : ℤ) * N' ^ 2) =
          ((p : ℤ)) ^ 2 * (2 * (p : ℤ) * F' ^ 2) := by linear_combination h2
      exact mul_left_cancel₀ hp2 hfac
    exact ih N'.natAbs (hNa ▸ natAbs_lt_mul hp h8 hN'0) C' E' F' N' rfl hN'0 h1' h2'

private lemma zmod8_of_stratum (h8 : p % 8 = 3) : ((p : ℕ) : ZMod 8) = 3 := by
  have hsplit : p = 8 * (p / 8) + 3 := by omega
  rw [hsplit]
  push_cast
  rw [show (8 : ZMod 8) = 0 by decide]
  ring

private lemma kernelTwoTwoPInner (_hp : p.Prime) (h8 : p % 8 = 3) :
    ∀ (n : ℕ), ∀ A E F N : ℤ, N.natAbs = n → N ≠ 0 →
    2 * (p : ℤ) * A ^ 2 - N ^ 2 = 2 * E ^ 2 →
    2 * (p : ℤ) * A ^ 2 + N ^ 2 = F ^ 2 → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A E F N hNa hN0 h1 h2
    have hdec : ∀ a nn e f : ZMod 8, 2 * 3 * a ^ 2 - nn ^ 2 = 2 * e ^ 2 →
        2 * 3 * a ^ 2 + nn ^ 2 = f ^ 2 →
        (4 * a = 0 ∧ 4 * nn = 0 ∧ 4 * e = 0 ∧ 4 * f = 0) := by decide
    have hp8 : ((p : ℕ) : ZMod 8) = 3 := zmod8_of_stratum h8
    have h1z : 2 * 3 * (A : ZMod 8) ^ 2 - (N : ZMod 8) ^ 2 = 2 * (E : ZMod 8) ^ 2 := by
      have hc := congrArg (Int.cast : ℤ → ZMod 8) h1
      push_cast at hc
      rw [hp8] at hc
      exact hc
    have h2z : 2 * 3 * (A : ZMod 8) ^ 2 + (N : ZMod 8) ^ 2 = (F : ZMod 8) ^ 2 := by
      have hc := congrArg (Int.cast : ℤ → ZMod 8) h2
      push_cast at hc
      rw [hp8] at hc
      exact hc
    obtain ⟨hA, hN8, hE, hF⟩ := hdec _ _ _ _ h1z h2z
    have hdvd : ∀ m : ℤ, 4 * (m : ZMod 8) = 0 → 2 ∣ m := by
      intro m hm
      have hz : ((4 * m : ℤ) : ZMod 8) = 0 := by push_cast; rw [hm]
      have h8' : (8 : ℤ) ∣ 4 * m := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp hz
      omega
    obtain ⟨A', rfl⟩ := hdvd A hA
    obtain ⟨N', rfl⟩ := hdvd N hN8
    obtain ⟨E', rfl⟩ := hdvd E hE
    obtain ⟨F', rfl⟩ := hdvd F hF
    have hN'0 : N' ≠ 0 := fun hc => hN0 (by rw [hc]; ring)
    have h1' : 2 * (p : ℤ) * A' ^ 2 - N' ^ 2 = 2 * E' ^ 2 := by linarith [h1]
    have h2' : 2 * (p : ℤ) * A' ^ 2 + N' ^ 2 = F' ^ 2 := by linarith [h2]
    have hlt : N'.natAbs < n := by
      have h2n : (2 * N').natAbs = 2 * N'.natAbs := by
        rw [Int.natAbs_mul]
        norm_num
      have hne : N'.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hN'0
      omega
    exact ih N'.natAbs hlt A' E' F' N' rfl hN'0 h1' h2'

private lemma kernelTwoTwoP (hp : p.Prime) (h8 : p % 8 = 3) [Fact p.Prime] :
    ∀ C E F N : ℤ, N ≠ 0 →
    2 * C ^ 2 - (p : ℤ) * N ^ 2 = 2 * (p : ℤ) * E ^ 2 →
    2 * C ^ 2 + (p : ℤ) * N ^ 2 = (p : ℤ) * F ^ 2 → False := by
  intro C E F N hN0 h1 h2
  have hC : (p : ℤ) ∣ C :=
    pdvd_of_dvd_two_mul hp h8 ⟨F ^ 2 - N ^ 2, by linarith⟩
  obtain ⟨C', rfl⟩ := hC
  have hi : 2 * (p : ℤ) * C' ^ 2 - N ^ 2 = 2 * E ^ 2 := by
    have hcan : (p : ℤ) * (2 * (p : ℤ) * C' ^ 2 - N ^ 2) = (p : ℤ) * (2 * E ^ 2) := by
      linear_combination h1
    exact mul_left_cancel₀ (pZ_ne hp) hcan
  have hii : 2 * (p : ℤ) * C' ^ 2 + N ^ 2 = F ^ 2 := by
    have hcan : (p : ℤ) * (2 * (p : ℤ) * C' ^ 2 + N ^ 2) = (p : ℤ) * F ^ 2 := by
      linear_combination h2
    exact mul_left_cancel₀ (pZ_ne hp) hcan
  exact kernelTwoTwoPInner hp h8 N.natAbs C' E F N rfl hN0 hi hii

/-! ## 6. The seven refusal theorems -/

private lemma refuseOneTwo (hp : p.Prime) (h8 : p % 8 = 3) [Fact p.Prime]
    (P : (FamilyFace.E p).Point) :
    ¬ (Descent.SqCls (FamilyFace.slotOne p P) 1 ∧
       Descent.SqCls (FamilyFace.slotTwo p P) (2)) := by
  rintro ⟨hs1, hs2⟩
  have hppos := p_pos hp
  rcases P with _ | @⟨x, y, hP⟩
  · obtain ⟨c, hc, hval⟩ := hs2
    have h1 : (1 : ℚ) = c ^ 2 * 2 := hval
    refine Descent.notSquareTwo ⟨1 / c, ?_⟩
    field_simp
    linear_combination -h1
  · have hcurve := onCurveP hP
    by_cases hy : y = 0
    · rw [hy] at hcurve
      have h0 : x * (x - p) * (x + p) = 0 := by linear_combination -hcurve
      have hx3 : x = 0 ∨ x = (p : ℚ) ∨ x = -(p : ℚ) := by
        rcases mul_eq_zero.mp h0 with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl (by linarith))
        · exact Or.inr (Or.inr (by linarith))
      rcases hx3 with rfl | rfl | rfl
      · rw [slotPOne_some, if_pos rfl] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        nlinarith [sq_nonneg c, hval, hppos]
      · rw [slotPOne_some, if_neg (pQ_ne hp)] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        rw [mul_one] at hval
        exact notSquareP hp ⟨c, by rw [hval]; ring⟩
      · rw [slotPOne_some, if_neg (by intro hc; nlinarith)] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        nlinarith [sq_nonneg c, hval, hppos]
    · obtain ⟨hx0, hxp, hxmp⟩ := avoidP hcurve hy
      rw [slotPOne_some, if_neg hx0] at hs1
      rw [slotPTwo_some, if_neg hxp] at hs2
      obtain ⟨c, hc0, hcv⟩ := hs1
      rw [mul_one] at hcv
      obtain ⟨e, he0, hev⟩ := hs2
      have hmQ : (2 : ℚ) ≠ 0 := by positivity
      have hmce : (2) * c * e ≠ 0 := mul_ne_zero (mul_ne_zero hmQ hc0) he0
      have hf : x + p = 2 * (y / (2 * c * e)) ^ 2 := by
        have hcA : x = c ^ 2 * 1 := by linear_combination hcv
        have hcB : x - p = e ^ 2 * (2) := by linear_combination hev
        have hchain : (x + p) * ((2) * c * e) ^ 2 = (2) * y ^ 2 := by
          have hstep1 : (x + p) * ((2) * c * e) ^ 2 = (x + p) * ((4) * x * e ^ 2) := by
            linear_combination (-(4) * (x + p) * e ^ 2) * hcA
          have hstep2 : (x + p) * ((4) * x * e ^ 2) = (2) * (x * (x - p) * (x + p)) := by
            linear_combination (-(2) * x * (x + p)) * hcB
          have hstep3 : (2) * (x * (x - p) * (x + p)) = (2) * y ^ 2 := by
            linear_combination -(2) * hcurve
          exact hstep1.trans (hstep2.trans hstep3)
        rw [div_pow, mul_div_assoc', eq_div_iff (pow_ne_zero 2 hmce)]
        exact hchain
      have hcd : c * (c.den : ℚ) = c.num := Rat.mul_den_eq_num c
      have hed : e * (e.den : ℚ) = e.num := Rat.mul_den_eq_num e
      have hfd : (y / ((2) * c * e)) * ((y / ((2) * c * e)).den : ℚ) =
          (y / ((2) * c * e)).num := Rat.mul_den_eq_num _
      set f := y / ((2) * c * e) with hfdef
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
      have hsub1 : (1) * c ^ 2 - (2) * e ^ 2 = (p : ℚ) := by
        have hcA : x = c ^ 2 * 1 := by linear_combination hcv
        have hcB : x - p = e ^ 2 * (2) := by linear_combination hev
        linear_combination hcB - hcA
      have hsub2 : (1) * c ^ 2 + (p : ℚ) = (2) * f ^ 2 := by
        have hcA : x = c ^ 2 * 1 := by linear_combination hcv
        rw [hfdef]
        linear_combination hf - hcA
      have hint1 : (c.num * (e.den * f.den : ℕ) : ℤ) ^ 2 - (p : ℤ) * ((N : ℕ) : ℤ) ^ 2 =
          2 * (e.num * (c.den * f.den : ℕ) : ℤ) ^ 2 := by
        have hQ : (c * (N : ℚ)) ^ 2 - (p : ℚ) * ((N : ℕ) : ℚ) ^ 2 =
            (2) * (e * (N : ℚ)) ^ 2 := by
          linear_combination ((N : ℕ) : ℚ) ^ 2 * hsub1
        exact_mod_cast (by rw [hCQ, hEQ]; exact_mod_cast hQ :
          ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) ^ 2 - (p : ℚ) * ((N : ℕ) : ℚ) ^ 2 =
          (2) * ((e.num * (c.den * f.den : ℕ) : ℤ) : ℚ) ^ 2)
      have hint2 : (c.num * (e.den * f.den : ℕ) : ℤ) ^ 2 + (p : ℤ) * ((N : ℕ) : ℤ) ^ 2 =
          2 * (f.num * (c.den * e.den : ℕ) : ℤ) ^ 2 := by
        have hQ : (c * (N : ℚ)) ^ 2 + (p : ℚ) * ((N : ℕ) : ℚ) ^ 2 =
            (2) * (f * (N : ℚ)) ^ 2 := by
          linear_combination ((N : ℕ) : ℚ) ^ 2 * hsub2
        exact_mod_cast (by rw [hCQ, hFQ]; exact_mod_cast hQ :
          ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) ^ 2 + (p : ℚ) * ((N : ℕ) : ℚ) ^ 2 =
          (2) * ((f.num * (c.den * e.den : ℕ) : ℤ) : ℚ) ^ 2)
      have hNnat : N ≠ 0 := by
        rw [hN]
        exact Nat.mul_ne_zero (Nat.mul_ne_zero c.den_nz e.den_nz) f.den_nz
      have hNne : (((N : ℕ) : ℤ)) ≠ 0 := by exact_mod_cast hNnat
      exact kernelOneTwo hp h8 ((N : ℤ)).natAbs _ _ _ _ rfl hNne hint1 hint2

private lemma refuseOneP (hp : p.Prime) (h8 : p % 8 = 3) [Fact p.Prime]
    (P : (FamilyFace.E p).Point) :
    ¬ (Descent.SqCls (FamilyFace.slotOne p P) 1 ∧
       Descent.SqCls (FamilyFace.slotTwo p P) ((p : ℚ))) := by
  rintro ⟨hs1, hs2⟩
  have hppos := p_pos hp
  rcases P with _ | @⟨x, y, hP⟩
  · obtain ⟨c, hc, hval⟩ := hs2
    have h1 : (1 : ℚ) = c ^ 2 * p := hval
    refine notSquareP hp ⟨1 / c, ?_⟩
    field_simp
    linear_combination -h1
  · have hcurve := onCurveP hP
    by_cases hy : y = 0
    · rw [hy] at hcurve
      have h0 : x * (x - p) * (x + p) = 0 := by linear_combination -hcurve
      have hx3 : x = 0 ∨ x = (p : ℚ) ∨ x = -(p : ℚ) := by
        rcases mul_eq_zero.mp h0 with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl (by linarith))
        · exact Or.inr (Or.inr (by linarith))
      rcases hx3 with rfl | rfl | rfl
      · rw [slotPOne_some, if_pos rfl] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        nlinarith [sq_nonneg c, hval, hppos]
      · rw [slotPOne_some, if_neg (pQ_ne hp)] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        rw [mul_one] at hval
        exact notSquareP hp ⟨c, by rw [hval]; ring⟩
      · rw [slotPOne_some, if_neg (by intro hc; nlinarith)] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        nlinarith [sq_nonneg c, hval, hppos]
    · obtain ⟨hx0, hxp, hxmp⟩ := avoidP hcurve hy
      rw [slotPOne_some, if_neg hx0] at hs1
      rw [slotPTwo_some, if_neg hxp] at hs2
      obtain ⟨c, hc0, hcv⟩ := hs1
      rw [mul_one] at hcv
      obtain ⟨e, he0, hev⟩ := hs2
      have hmQ : ((p : ℚ) : ℚ) ≠ 0 := by positivity
      have hmce : ((p : ℚ)) * c * e ≠ 0 := mul_ne_zero (mul_ne_zero hmQ hc0) he0
      have hf : x + p = (p : ℚ) * (y / ((p : ℚ) * c * e)) ^ 2 := by
        have hcA : x = c ^ 2 * 1 := by linear_combination hcv
        have hcB : x - p = e ^ 2 * ((p : ℚ)) := by linear_combination hev
        have hchain : (x + p) * (((p : ℚ)) * c * e) ^ 2 = ((p : ℚ)) * y ^ 2 := by
          have hstep1 : (x + p) * (((p : ℚ)) * c * e) ^ 2 = (x + p) * (((p : ℚ) ^ 2) * x * e ^ 2) := by
            linear_combination (-((p : ℚ) ^ 2) * (x + p) * e ^ 2) * hcA
          have hstep2 : (x + p) * (((p : ℚ) ^ 2) * x * e ^ 2) = ((p : ℚ)) * (x * (x - p) * (x + p)) := by
            linear_combination (-((p : ℚ)) * x * (x + p)) * hcB
          have hstep3 : ((p : ℚ)) * (x * (x - p) * (x + p)) = ((p : ℚ)) * y ^ 2 := by
            linear_combination -((p : ℚ)) * hcurve
          exact hstep1.trans (hstep2.trans hstep3)
        rw [div_pow, mul_div_assoc', eq_div_iff (pow_ne_zero 2 hmce)]
        exact hchain
      have hcd : c * (c.den : ℚ) = c.num := Rat.mul_den_eq_num c
      have hed : e * (e.den : ℚ) = e.num := Rat.mul_den_eq_num e
      have hfd : (y / (((p : ℚ)) * c * e)) * ((y / (((p : ℚ)) * c * e)).den : ℚ) =
          (y / (((p : ℚ)) * c * e)).num := Rat.mul_den_eq_num _
      set f := y / (((p : ℚ)) * c * e) with hfdef
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
      have hsub1 : (1) * c ^ 2 - ((p : ℚ)) * e ^ 2 = (p : ℚ) := by
        have hcA : x = c ^ 2 * 1 := by linear_combination hcv
        have hcB : x - p = e ^ 2 * ((p : ℚ)) := by linear_combination hev
        linear_combination hcB - hcA
      have hsub2 : (1) * c ^ 2 + (p : ℚ) = ((p : ℚ)) * f ^ 2 := by
        have hcA : x = c ^ 2 * 1 := by linear_combination hcv
        rw [hfdef]
        linear_combination hf - hcA
      have hint1 : (c.num * (e.den * f.den : ℕ) : ℤ) ^ 2 - (p : ℤ) * ((N : ℕ) : ℤ) ^ 2 =
          (p : ℤ) * (e.num * (c.den * f.den : ℕ) : ℤ) ^ 2 := by
        have hQ : (c * (N : ℚ)) ^ 2 - (p : ℚ) * ((N : ℕ) : ℚ) ^ 2 =
            ((p : ℚ)) * (e * (N : ℚ)) ^ 2 := by
          linear_combination ((N : ℕ) : ℚ) ^ 2 * hsub1
        exact_mod_cast (by rw [hCQ, hEQ]; exact_mod_cast hQ :
          ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) ^ 2 - (p : ℚ) * ((N : ℕ) : ℚ) ^ 2 =
          ((p : ℚ)) * ((e.num * (c.den * f.den : ℕ) : ℤ) : ℚ) ^ 2)
      have hint2 : (c.num * (e.den * f.den : ℕ) : ℤ) ^ 2 + (p : ℤ) * ((N : ℕ) : ℤ) ^ 2 =
          (p : ℤ) * (f.num * (c.den * e.den : ℕ) : ℤ) ^ 2 := by
        have hQ : (c * (N : ℚ)) ^ 2 + (p : ℚ) * ((N : ℕ) : ℚ) ^ 2 =
            ((p : ℚ)) * (f * (N : ℚ)) ^ 2 := by
          linear_combination ((N : ℕ) : ℚ) ^ 2 * hsub2
        exact_mod_cast (by rw [hCQ, hFQ]; exact_mod_cast hQ :
          ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) ^ 2 + (p : ℚ) * ((N : ℕ) : ℚ) ^ 2 =
          ((p : ℚ)) * ((f.num * (c.den * e.den : ℕ) : ℤ) : ℚ) ^ 2)
      have hNnat : N ≠ 0 := by
        rw [hN]
        exact Nat.mul_ne_zero (Nat.mul_ne_zero c.den_nz e.den_nz) f.den_nz
      have hNne : (((N : ℕ) : ℤ)) ≠ 0 := by exact_mod_cast hNnat
      exact kernelOneP hp h8 ((N : ℤ)).natAbs _ _ _ _ rfl hNne hint1 hint2

private lemma refuseOneTwoP (hp : p.Prime) (h8 : p % 8 = 3) [Fact p.Prime]
    (P : (FamilyFace.E p).Point) :
    ¬ (Descent.SqCls (FamilyFace.slotOne p P) 1 ∧
       Descent.SqCls (FamilyFace.slotTwo p P) (2 * (p : ℚ))) := by
  rintro ⟨hs1, hs2⟩
  have hppos := p_pos hp
  rcases P with _ | @⟨x, y, hP⟩
  · obtain ⟨c, hc, hval⟩ := hs2
    have h1 : (1 : ℚ) = c ^ 2 * (2 * p) := hval
    refine notSquareTwoP hp h8 ?_
    refine ⟨1 / c, ?_⟩
    push_cast
    field_simp
    linear_combination -h1
  · have hcurve := onCurveP hP
    by_cases hy : y = 0
    · rw [hy] at hcurve
      have h0 : x * (x - p) * (x + p) = 0 := by linear_combination -hcurve
      have hx3 : x = 0 ∨ x = (p : ℚ) ∨ x = -(p : ℚ) := by
        rcases mul_eq_zero.mp h0 with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl (by linarith))
        · exact Or.inr (Or.inr (by linarith))
      rcases hx3 with rfl | rfl | rfl
      · rw [slotPOne_some, if_pos rfl] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        nlinarith [sq_nonneg c, hval, hppos]
      · rw [slotPOne_some, if_neg (pQ_ne hp)] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        rw [mul_one] at hval
        exact notSquareP hp ⟨c, by rw [hval]; ring⟩
      · rw [slotPOne_some, if_neg (by intro hc; nlinarith)] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        nlinarith [sq_nonneg c, hval, hppos]
    · obtain ⟨hx0, hxp, hxmp⟩ := avoidP hcurve hy
      rw [slotPOne_some, if_neg hx0] at hs1
      rw [slotPTwo_some, if_neg hxp] at hs2
      obtain ⟨c, hc0, hcv⟩ := hs1
      rw [mul_one] at hcv
      obtain ⟨e, he0, hev⟩ := hs2
      have hmQ : (2 * (p : ℚ) : ℚ) ≠ 0 := by positivity
      have hmce : (2 * (p : ℚ)) * c * e ≠ 0 := mul_ne_zero (mul_ne_zero hmQ hc0) he0
      have hf : x + p = 2 * (p : ℚ) * (y / (2 * (p : ℚ) * c * e)) ^ 2 := by
        have hcA : x = c ^ 2 * 1 := by linear_combination hcv
        have hcB : x - p = e ^ 2 * (2 * (p : ℚ)) := by linear_combination hev
        have hchain : (x + p) * ((2 * (p : ℚ)) * c * e) ^ 2 = (2 * (p : ℚ)) * y ^ 2 := by
          have hstep1 : (x + p) * ((2 * (p : ℚ)) * c * e) ^ 2 = (x + p) * ((4 * (p : ℚ) ^ 2) * x * e ^ 2) := by
            linear_combination (-(4 * (p : ℚ) ^ 2) * (x + p) * e ^ 2) * hcA
          have hstep2 : (x + p) * ((4 * (p : ℚ) ^ 2) * x * e ^ 2) = (2 * (p : ℚ)) * (x * (x - p) * (x + p)) := by
            linear_combination (-(2 * (p : ℚ)) * x * (x + p)) * hcB
          have hstep3 : (2 * (p : ℚ)) * (x * (x - p) * (x + p)) = (2 * (p : ℚ)) * y ^ 2 := by
            linear_combination -(2 * (p : ℚ)) * hcurve
          exact hstep1.trans (hstep2.trans hstep3)
        rw [div_pow, mul_div_assoc', eq_div_iff (pow_ne_zero 2 hmce)]
        exact hchain
      have hcd : c * (c.den : ℚ) = c.num := Rat.mul_den_eq_num c
      have hed : e * (e.den : ℚ) = e.num := Rat.mul_den_eq_num e
      have hfd : (y / ((2 * (p : ℚ)) * c * e)) * ((y / ((2 * (p : ℚ)) * c * e)).den : ℚ) =
          (y / ((2 * (p : ℚ)) * c * e)).num := Rat.mul_den_eq_num _
      set f := y / ((2 * (p : ℚ)) * c * e) with hfdef
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
      have hsub1 : (1) * c ^ 2 - (2 * (p : ℚ)) * e ^ 2 = (p : ℚ) := by
        have hcA : x = c ^ 2 * 1 := by linear_combination hcv
        have hcB : x - p = e ^ 2 * (2 * (p : ℚ)) := by linear_combination hev
        linear_combination hcB - hcA
      have hsub2 : (1) * c ^ 2 + (p : ℚ) = (2 * (p : ℚ)) * f ^ 2 := by
        have hcA : x = c ^ 2 * 1 := by linear_combination hcv
        rw [hfdef]
        linear_combination hf - hcA
      have hint1 : (c.num * (e.den * f.den : ℕ) : ℤ) ^ 2 - (p : ℤ) * ((N : ℕ) : ℤ) ^ 2 =
          2 * (p : ℤ) * (e.num * (c.den * f.den : ℕ) : ℤ) ^ 2 := by
        have hQ : (c * (N : ℚ)) ^ 2 - (p : ℚ) * ((N : ℕ) : ℚ) ^ 2 =
            (2 * (p : ℚ)) * (e * (N : ℚ)) ^ 2 := by
          linear_combination ((N : ℕ) : ℚ) ^ 2 * hsub1
        exact_mod_cast (by rw [hCQ, hEQ]; exact_mod_cast hQ :
          ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) ^ 2 - (p : ℚ) * ((N : ℕ) : ℚ) ^ 2 =
          (2 * (p : ℚ)) * ((e.num * (c.den * f.den : ℕ) : ℤ) : ℚ) ^ 2)
      have hint2 : (c.num * (e.den * f.den : ℕ) : ℤ) ^ 2 + (p : ℤ) * ((N : ℕ) : ℤ) ^ 2 =
          2 * (p : ℤ) * (f.num * (c.den * e.den : ℕ) : ℤ) ^ 2 := by
        have hQ : (c * (N : ℚ)) ^ 2 + (p : ℚ) * ((N : ℕ) : ℚ) ^ 2 =
            (2 * (p : ℚ)) * (f * (N : ℚ)) ^ 2 := by
          linear_combination ((N : ℕ) : ℚ) ^ 2 * hsub2
        exact_mod_cast (by rw [hCQ, hFQ]; exact_mod_cast hQ :
          ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) ^ 2 + (p : ℚ) * ((N : ℕ) : ℚ) ^ 2 =
          (2 * (p : ℚ)) * ((f.num * (c.den * e.den : ℕ) : ℤ) : ℚ) ^ 2)
      have hNnat : N ≠ 0 := by
        rw [hN]
        exact Nat.mul_ne_zero (Nat.mul_ne_zero c.den_nz e.den_nz) f.den_nz
      have hNne : (((N : ℕ) : ℤ)) ≠ 0 := by exact_mod_cast hNnat
      exact kernelOneTwoP hp h8 ((N : ℤ)).natAbs _ _ _ _ rfl hNne hint1 hint2

private lemma refuseTwoOne (hp : p.Prime) (h8 : p % 8 = 3) [Fact p.Prime]
    (P : (FamilyFace.E p).Point) :
    ¬ (Descent.SqCls (FamilyFace.slotOne p P) 2 ∧
       Descent.SqCls (FamilyFace.slotTwo p P) (1)) := by
  rintro ⟨hs1, hs2⟩
  have hppos := p_pos hp
  rcases P with _ | @⟨x, y, hP⟩
  · obtain ⟨c, hc, hval⟩ := hs1
    have h1 : (1 : ℚ) = c ^ 2 * 2 := hval
    refine Descent.notSquareTwo ⟨1 / c, ?_⟩
    field_simp
    linear_combination -h1
  · have hcurve := onCurveP hP
    by_cases hy : y = 0
    · rw [hy] at hcurve
      have h0 : x * (x - p) * (x + p) = 0 := by linear_combination -hcurve
      have hx3 : x = 0 ∨ x = (p : ℚ) ∨ x = -(p : ℚ) := by
        rcases mul_eq_zero.mp h0 with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl (by linarith))
        · exact Or.inr (Or.inr (by linarith))
      rcases hx3 with rfl | rfl | rfl
      · rw [slotPOne_some, if_pos rfl] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        nlinarith [sq_nonneg c, hval, hppos]
      · rw [slotPOne_some, if_neg (pQ_ne hp)] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        refine notSquareTwoP hp h8 ?_
        refine ⟨2 * c, ?_⟩
        push_cast
        linear_combination 2 * hval
      · rw [slotPOne_some, if_neg (by intro hc; nlinarith)] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        nlinarith [sq_nonneg c, hval, hppos]
    · obtain ⟨hx0, hxp, hxmp⟩ := avoidP hcurve hy
      rw [slotPOne_some, if_neg hx0] at hs1
      rw [slotPTwo_some, if_neg hxp] at hs2
      obtain ⟨c, hc0, hcv⟩ := hs1
      obtain ⟨e, he0, hev⟩ := hs2
      rw [mul_one] at hev
      have hmQ : (2 : ℚ) ≠ 0 := by positivity
      have hmce : (2) * c * e ≠ 0 := mul_ne_zero (mul_ne_zero hmQ hc0) he0
      have hf : x + p = 2 * (y / (2 * c * e)) ^ 2 := by
        have hcA : x = c ^ 2 * 2 := by linear_combination hcv
        have hcB : x - p = e ^ 2 * (1) := by linear_combination hev
        have hchain : (x + p) * ((2) * c * e) ^ 2 = (2) * y ^ 2 := by
          have hstep1 : (x + p) * ((2) * c * e) ^ 2 = (x + p) * ((2) * x * e ^ 2) := by
            linear_combination (-(2) * (x + p) * e ^ 2) * hcA
          have hstep2 : (x + p) * ((2) * x * e ^ 2) = (2) * (x * (x - p) * (x + p)) := by
            linear_combination (-(2) * x * (x + p)) * hcB
          have hstep3 : (2) * (x * (x - p) * (x + p)) = (2) * y ^ 2 := by
            linear_combination -(2) * hcurve
          exact hstep1.trans (hstep2.trans hstep3)
        rw [div_pow, mul_div_assoc', eq_div_iff (pow_ne_zero 2 hmce)]
        exact hchain
      have hcd : c * (c.den : ℚ) = c.num := Rat.mul_den_eq_num c
      have hed : e * (e.den : ℚ) = e.num := Rat.mul_den_eq_num e
      have hfd : (y / ((2) * c * e)) * ((y / ((2) * c * e)).den : ℚ) =
          (y / ((2) * c * e)).num := Rat.mul_den_eq_num _
      set f := y / ((2) * c * e) with hfdef
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
      have hsub1 : (2) * c ^ 2 - (1) * e ^ 2 = (p : ℚ) := by
        have hcA : x = c ^ 2 * 2 := by linear_combination hcv
        have hcB : x - p = e ^ 2 * (1) := by linear_combination hev
        linear_combination hcB - hcA
      have hsub2 : (2) * c ^ 2 + (p : ℚ) = (2) * f ^ 2 := by
        have hcA : x = c ^ 2 * 2 := by linear_combination hcv
        rw [hfdef]
        linear_combination hf - hcA
      have hint1 : 2 * (c.num * (e.den * f.den : ℕ) : ℤ) ^ 2 - (p : ℤ) * ((N : ℕ) : ℤ) ^ 2 =
          (e.num * (c.den * f.den : ℕ) : ℤ) ^ 2 := by
        have hQ : (2) * (c * (N : ℚ)) ^ 2 - (p : ℚ) * ((N : ℕ) : ℚ) ^ 2 =
            (e * (N : ℚ)) ^ 2 := by
          linear_combination ((N : ℕ) : ℚ) ^ 2 * hsub1
        exact_mod_cast (by rw [hCQ, hEQ]; exact_mod_cast hQ :
          (2) * ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) ^ 2 - (p : ℚ) * ((N : ℕ) : ℚ) ^ 2 =
          ((e.num * (c.den * f.den : ℕ) : ℤ) : ℚ) ^ 2)
      have hint2 : 2 * (c.num * (e.den * f.den : ℕ) : ℤ) ^ 2 + (p : ℤ) * ((N : ℕ) : ℤ) ^ 2 =
          2 * (f.num * (c.den * e.den : ℕ) : ℤ) ^ 2 := by
        have hQ : (2) * (c * (N : ℚ)) ^ 2 + (p : ℚ) * ((N : ℕ) : ℚ) ^ 2 =
            (2) * (f * (N : ℚ)) ^ 2 := by
          linear_combination ((N : ℕ) : ℚ) ^ 2 * hsub2
        exact_mod_cast (by rw [hCQ, hFQ]; exact_mod_cast hQ :
          (2) * ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) ^ 2 + (p : ℚ) * ((N : ℕ) : ℚ) ^ 2 =
          (2) * ((f.num * (c.den * e.den : ℕ) : ℤ) : ℚ) ^ 2)
      have hNnat : N ≠ 0 := by
        rw [hN]
        exact Nat.mul_ne_zero (Nat.mul_ne_zero c.den_nz e.den_nz) f.den_nz
      have hNne : (((N : ℕ) : ℤ)) ≠ 0 := by exact_mod_cast hNnat
      exact kernelTwoOne hp h8 ((N : ℤ)).natAbs _ _ _ _ rfl hNne hint1 hint2

private lemma refuseTwoTwo (hp : p.Prime) (h8 : p % 8 = 3) [Fact p.Prime]
    (P : (FamilyFace.E p).Point) :
    ¬ (Descent.SqCls (FamilyFace.slotOne p P) 2 ∧
       Descent.SqCls (FamilyFace.slotTwo p P) (2)) := by
  rintro ⟨hs1, hs2⟩
  have hppos := p_pos hp
  rcases P with _ | @⟨x, y, hP⟩
  · obtain ⟨c, hc, hval⟩ := hs1
    have h1 : (1 : ℚ) = c ^ 2 * 2 := hval
    refine Descent.notSquareTwo ⟨1 / c, ?_⟩
    field_simp
    linear_combination -h1
  · have hcurve := onCurveP hP
    by_cases hy : y = 0
    · rw [hy] at hcurve
      have h0 : x * (x - p) * (x + p) = 0 := by linear_combination -hcurve
      have hx3 : x = 0 ∨ x = (p : ℚ) ∨ x = -(p : ℚ) := by
        rcases mul_eq_zero.mp h0 with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl (by linarith))
        · exact Or.inr (Or.inr (by linarith))
      rcases hx3 with rfl | rfl | rfl
      · rw [slotPOne_some, if_pos rfl] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        nlinarith [sq_nonneg c, hval, hppos]
      · rw [slotPOne_some, if_neg (pQ_ne hp)] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        refine notSquareTwoP hp h8 ?_
        refine ⟨2 * c, ?_⟩
        push_cast
        linear_combination 2 * hval
      · rw [slotPOne_some, if_neg (by intro hc; nlinarith)] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        nlinarith [sq_nonneg c, hval, hppos]
    · obtain ⟨hx0, hxp, hxmp⟩ := avoidP hcurve hy
      rw [slotPOne_some, if_neg hx0] at hs1
      rw [slotPTwo_some, if_neg hxp] at hs2
      obtain ⟨c, hc0, hcv⟩ := hs1
      obtain ⟨e, he0, hev⟩ := hs2
      have hmQ : (2 : ℚ) ≠ 0 := by positivity
      have hmce : (2) * c * e ≠ 0 := mul_ne_zero (mul_ne_zero hmQ hc0) he0
      have hf : x + p = (y / (2 * c * e)) ^ 2 := by
        have hcA : x = c ^ 2 * 2 := by linear_combination hcv
        have hcB : x - p = e ^ 2 * (2) := by linear_combination hev
        have hchain : (x + p) * ((2) * c * e) ^ 2 = (1) * y ^ 2 := by
          have hstep1 : (x + p) * ((2) * c * e) ^ 2 = (x + p) * ((2) * x * e ^ 2) := by
            linear_combination (-(2) * (x + p) * e ^ 2) * hcA
          have hstep2 : (x + p) * ((2) * x * e ^ 2) = (1) * (x * (x - p) * (x + p)) := by
            linear_combination (-(1) * x * (x + p)) * hcB
          have hstep3 : (1) * (x * (x - p) * (x + p)) = (1) * y ^ 2 := by
            linear_combination -(1) * hcurve
          exact hstep1.trans (hstep2.trans hstep3)
        rw [div_pow, eq_div_iff (pow_ne_zero 2 hmce)]
        linear_combination hchain
      have hcd : c * (c.den : ℚ) = c.num := Rat.mul_den_eq_num c
      have hed : e * (e.den : ℚ) = e.num := Rat.mul_den_eq_num e
      have hfd : (y / ((2) * c * e)) * ((y / ((2) * c * e)).den : ℚ) =
          (y / ((2) * c * e)).num := Rat.mul_den_eq_num _
      set f := y / ((2) * c * e) with hfdef
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
      have hsub1 : (2) * c ^ 2 - (2) * e ^ 2 = (p : ℚ) := by
        have hcA : x = c ^ 2 * 2 := by linear_combination hcv
        have hcB : x - p = e ^ 2 * (2) := by linear_combination hev
        linear_combination hcB - hcA
      have hsub2 : (2) * c ^ 2 + (p : ℚ) = (1) * f ^ 2 := by
        have hcA : x = c ^ 2 * 2 := by linear_combination hcv
        rw [hfdef]
        linear_combination hf - hcA
      have hint1 : 2 * (c.num * (e.den * f.den : ℕ) : ℤ) ^ 2 - (p : ℤ) * ((N : ℕ) : ℤ) ^ 2 =
          2 * (e.num * (c.den * f.den : ℕ) : ℤ) ^ 2 := by
        have hQ : (2) * (c * (N : ℚ)) ^ 2 - (p : ℚ) * ((N : ℕ) : ℚ) ^ 2 =
            (2) * (e * (N : ℚ)) ^ 2 := by
          linear_combination ((N : ℕ) : ℚ) ^ 2 * hsub1
        exact_mod_cast (by rw [hCQ, hEQ]; exact_mod_cast hQ :
          (2) * ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) ^ 2 - (p : ℚ) * ((N : ℕ) : ℚ) ^ 2 =
          (2) * ((e.num * (c.den * f.den : ℕ) : ℤ) : ℚ) ^ 2)
      have hint2 : 2 * (c.num * (e.den * f.den : ℕ) : ℤ) ^ 2 + (p : ℤ) * ((N : ℕ) : ℤ) ^ 2 =
          (f.num * (c.den * e.den : ℕ) : ℤ) ^ 2 := by
        have hQ : (2) * (c * (N : ℚ)) ^ 2 + (p : ℚ) * ((N : ℕ) : ℚ) ^ 2 =
            (f * (N : ℚ)) ^ 2 := by
          linear_combination ((N : ℕ) : ℚ) ^ 2 * hsub2
        exact_mod_cast (by rw [hCQ, hFQ]; exact_mod_cast hQ :
          (2) * ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) ^ 2 + (p : ℚ) * ((N : ℕ) : ℚ) ^ 2 =
          ((f.num * (c.den * e.den : ℕ) : ℤ) : ℚ) ^ 2)
      have hNnat : N ≠ 0 := by
        rw [hN]
        exact Nat.mul_ne_zero (Nat.mul_ne_zero c.den_nz e.den_nz) f.den_nz
      have hNne : (((N : ℕ) : ℤ)) ≠ 0 := by exact_mod_cast hNnat
      exact kernelTwoTwo hp h8 ((N : ℤ)).natAbs _ _ _ _ rfl hNne hint1 hint2

private lemma refuseTwoP (hp : p.Prime) (h8 : p % 8 = 3) [Fact p.Prime]
    (P : (FamilyFace.E p).Point) :
    ¬ (Descent.SqCls (FamilyFace.slotOne p P) 2 ∧
       Descent.SqCls (FamilyFace.slotTwo p P) ((p : ℚ))) := by
  rintro ⟨hs1, hs2⟩
  have hppos := p_pos hp
  rcases P with _ | @⟨x, y, hP⟩
  · obtain ⟨c, hc, hval⟩ := hs1
    have h1 : (1 : ℚ) = c ^ 2 * 2 := hval
    refine Descent.notSquareTwo ⟨1 / c, ?_⟩
    field_simp
    linear_combination -h1
  · have hcurve := onCurveP hP
    by_cases hy : y = 0
    · rw [hy] at hcurve
      have h0 : x * (x - p) * (x + p) = 0 := by linear_combination -hcurve
      have hx3 : x = 0 ∨ x = (p : ℚ) ∨ x = -(p : ℚ) := by
        rcases mul_eq_zero.mp h0 with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl (by linarith))
        · exact Or.inr (Or.inr (by linarith))
      rcases hx3 with rfl | rfl | rfl
      · rw [slotPOne_some, if_pos rfl] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        nlinarith [sq_nonneg c, hval, hppos]
      · rw [slotPOne_some, if_neg (pQ_ne hp)] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        refine notSquareTwoP hp h8 ?_
        refine ⟨2 * c, ?_⟩
        push_cast
        linear_combination 2 * hval
      · rw [slotPOne_some, if_neg (by intro hc; nlinarith)] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        nlinarith [sq_nonneg c, hval, hppos]
    · obtain ⟨hx0, hxp, hxmp⟩ := avoidP hcurve hy
      rw [slotPOne_some, if_neg hx0] at hs1
      rw [slotPTwo_some, if_neg hxp] at hs2
      obtain ⟨c, hc0, hcv⟩ := hs1
      obtain ⟨e, he0, hev⟩ := hs2
      have hmQ : (2 * (p : ℚ) : ℚ) ≠ 0 := by positivity
      have hmce : (2 * (p : ℚ)) * c * e ≠ 0 := mul_ne_zero (mul_ne_zero hmQ hc0) he0
      have hf : x + p = 2 * (p : ℚ) * (y / (2 * (p : ℚ) * c * e)) ^ 2 := by
        have hcA : x = c ^ 2 * 2 := by linear_combination hcv
        have hcB : x - p = e ^ 2 * ((p : ℚ)) := by linear_combination hev
        have hchain : (x + p) * ((2 * (p : ℚ)) * c * e) ^ 2 = (2 * (p : ℚ)) * y ^ 2 := by
          have hstep1 : (x + p) * ((2 * (p : ℚ)) * c * e) ^ 2 = (x + p) * ((2 * (p : ℚ) ^ 2) * x * e ^ 2) := by
            linear_combination (-(2 * (p : ℚ) ^ 2) * (x + p) * e ^ 2) * hcA
          have hstep2 : (x + p) * ((2 * (p : ℚ) ^ 2) * x * e ^ 2) = (2 * (p : ℚ)) * (x * (x - p) * (x + p)) := by
            linear_combination (-(2 * (p : ℚ)) * x * (x + p)) * hcB
          have hstep3 : (2 * (p : ℚ)) * (x * (x - p) * (x + p)) = (2 * (p : ℚ)) * y ^ 2 := by
            linear_combination -(2 * (p : ℚ)) * hcurve
          exact hstep1.trans (hstep2.trans hstep3)
        rw [div_pow, mul_div_assoc', eq_div_iff (pow_ne_zero 2 hmce)]
        exact hchain
      have hcd : c * (c.den : ℚ) = c.num := Rat.mul_den_eq_num c
      have hed : e * (e.den : ℚ) = e.num := Rat.mul_den_eq_num e
      have hfd : (y / ((2 * (p : ℚ)) * c * e)) * ((y / ((2 * (p : ℚ)) * c * e)).den : ℚ) =
          (y / ((2 * (p : ℚ)) * c * e)).num := Rat.mul_den_eq_num _
      set f := y / ((2 * (p : ℚ)) * c * e) with hfdef
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
      have hsub1 : (2) * c ^ 2 - ((p : ℚ)) * e ^ 2 = (p : ℚ) := by
        have hcA : x = c ^ 2 * 2 := by linear_combination hcv
        have hcB : x - p = e ^ 2 * ((p : ℚ)) := by linear_combination hev
        linear_combination hcB - hcA
      have hsub2 : (2) * c ^ 2 + (p : ℚ) = (2 * (p : ℚ)) * f ^ 2 := by
        have hcA : x = c ^ 2 * 2 := by linear_combination hcv
        rw [hfdef]
        linear_combination hf - hcA
      have hint1 : 2 * (c.num * (e.den * f.den : ℕ) : ℤ) ^ 2 - (p : ℤ) * ((N : ℕ) : ℤ) ^ 2 =
          (p : ℤ) * (e.num * (c.den * f.den : ℕ) : ℤ) ^ 2 := by
        have hQ : (2) * (c * (N : ℚ)) ^ 2 - (p : ℚ) * ((N : ℕ) : ℚ) ^ 2 =
            ((p : ℚ)) * (e * (N : ℚ)) ^ 2 := by
          linear_combination ((N : ℕ) : ℚ) ^ 2 * hsub1
        exact_mod_cast (by rw [hCQ, hEQ]; exact_mod_cast hQ :
          (2) * ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) ^ 2 - (p : ℚ) * ((N : ℕ) : ℚ) ^ 2 =
          ((p : ℚ)) * ((e.num * (c.den * f.den : ℕ) : ℤ) : ℚ) ^ 2)
      have hint2 : 2 * (c.num * (e.den * f.den : ℕ) : ℤ) ^ 2 + (p : ℤ) * ((N : ℕ) : ℤ) ^ 2 =
          2 * (p : ℤ) * (f.num * (c.den * e.den : ℕ) : ℤ) ^ 2 := by
        have hQ : (2) * (c * (N : ℚ)) ^ 2 + (p : ℚ) * ((N : ℕ) : ℚ) ^ 2 =
            (2 * (p : ℚ)) * (f * (N : ℚ)) ^ 2 := by
          linear_combination ((N : ℕ) : ℚ) ^ 2 * hsub2
        exact_mod_cast (by rw [hCQ, hFQ]; exact_mod_cast hQ :
          (2) * ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) ^ 2 + (p : ℚ) * ((N : ℕ) : ℚ) ^ 2 =
          (2 * (p : ℚ)) * ((f.num * (c.den * e.den : ℕ) : ℤ) : ℚ) ^ 2)
      have hNnat : N ≠ 0 := by
        rw [hN]
        exact Nat.mul_ne_zero (Nat.mul_ne_zero c.den_nz e.den_nz) f.den_nz
      have hNne : (((N : ℕ) : ℤ)) ≠ 0 := by exact_mod_cast hNnat
      exact kernelTwoP hp h8 ((N : ℤ)).natAbs _ _ _ _ rfl hNne hint1 hint2

private lemma refuseTwoTwoP (hp : p.Prime) (h8 : p % 8 = 3) [Fact p.Prime]
    (P : (FamilyFace.E p).Point) :
    ¬ (Descent.SqCls (FamilyFace.slotOne p P) 2 ∧
       Descent.SqCls (FamilyFace.slotTwo p P) (2 * (p : ℚ))) := by
  rintro ⟨hs1, hs2⟩
  have hppos := p_pos hp
  rcases P with _ | @⟨x, y, hP⟩
  · obtain ⟨c, hc, hval⟩ := hs1
    have h1 : (1 : ℚ) = c ^ 2 * 2 := hval
    refine Descent.notSquareTwo ⟨1 / c, ?_⟩
    field_simp
    linear_combination -h1
  · have hcurve := onCurveP hP
    by_cases hy : y = 0
    · rw [hy] at hcurve
      have h0 : x * (x - p) * (x + p) = 0 := by linear_combination -hcurve
      have hx3 : x = 0 ∨ x = (p : ℚ) ∨ x = -(p : ℚ) := by
        rcases mul_eq_zero.mp h0 with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl (by linarith))
        · exact Or.inr (Or.inr (by linarith))
      rcases hx3 with rfl | rfl | rfl
      · rw [slotPOne_some, if_pos rfl] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        nlinarith [sq_nonneg c, hval, hppos]
      · rw [slotPOne_some, if_neg (pQ_ne hp)] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        refine notSquareTwoP hp h8 ?_
        refine ⟨2 * c, ?_⟩
        push_cast
        linear_combination 2 * hval
      · rw [slotPOne_some, if_neg (by intro hc; nlinarith)] at hs1
        obtain ⟨c, hc, hval⟩ := hs1
        nlinarith [sq_nonneg c, hval, hppos]
    · obtain ⟨hx0, hxp, hxmp⟩ := avoidP hcurve hy
      rw [slotPOne_some, if_neg hx0] at hs1
      rw [slotPTwo_some, if_neg hxp] at hs2
      obtain ⟨c, hc0, hcv⟩ := hs1
      obtain ⟨e, he0, hev⟩ := hs2
      have hmQ : (2 * (p : ℚ) : ℚ) ≠ 0 := by positivity
      have hmce : (2 * (p : ℚ)) * c * e ≠ 0 := mul_ne_zero (mul_ne_zero hmQ hc0) he0
      have hf : x + p = (p : ℚ) * (y / (2 * (p : ℚ) * c * e)) ^ 2 := by
        have hcA : x = c ^ 2 * 2 := by linear_combination hcv
        have hcB : x - p = e ^ 2 * (2 * (p : ℚ)) := by linear_combination hev
        have hchain : (x + p) * ((2 * (p : ℚ)) * c * e) ^ 2 = ((p : ℚ)) * y ^ 2 := by
          have hstep1 : (x + p) * ((2 * (p : ℚ)) * c * e) ^ 2 = (x + p) * ((2 * (p : ℚ) ^ 2) * x * e ^ 2) := by
            linear_combination (-(2 * (p : ℚ) ^ 2) * (x + p) * e ^ 2) * hcA
          have hstep2 : (x + p) * ((2 * (p : ℚ) ^ 2) * x * e ^ 2) = ((p : ℚ)) * (x * (x - p) * (x + p)) := by
            linear_combination (-((p : ℚ)) * x * (x + p)) * hcB
          have hstep3 : ((p : ℚ)) * (x * (x - p) * (x + p)) = ((p : ℚ)) * y ^ 2 := by
            linear_combination -((p : ℚ)) * hcurve
          exact hstep1.trans (hstep2.trans hstep3)
        rw [div_pow, mul_div_assoc', eq_div_iff (pow_ne_zero 2 hmce)]
        exact hchain
      have hcd : c * (c.den : ℚ) = c.num := Rat.mul_den_eq_num c
      have hed : e * (e.den : ℚ) = e.num := Rat.mul_den_eq_num e
      have hfd : (y / ((2 * (p : ℚ)) * c * e)) * ((y / ((2 * (p : ℚ)) * c * e)).den : ℚ) =
          (y / ((2 * (p : ℚ)) * c * e)).num := Rat.mul_den_eq_num _
      set f := y / ((2 * (p : ℚ)) * c * e) with hfdef
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
      have hsub1 : (2) * c ^ 2 - (2 * (p : ℚ)) * e ^ 2 = (p : ℚ) := by
        have hcA : x = c ^ 2 * 2 := by linear_combination hcv
        have hcB : x - p = e ^ 2 * (2 * (p : ℚ)) := by linear_combination hev
        linear_combination hcB - hcA
      have hsub2 : (2) * c ^ 2 + (p : ℚ) = ((p : ℚ)) * f ^ 2 := by
        have hcA : x = c ^ 2 * 2 := by linear_combination hcv
        rw [hfdef]
        linear_combination hf - hcA
      have hint1 : 2 * (c.num * (e.den * f.den : ℕ) : ℤ) ^ 2 - (p : ℤ) * ((N : ℕ) : ℤ) ^ 2 =
          2 * (p : ℤ) * (e.num * (c.den * f.den : ℕ) : ℤ) ^ 2 := by
        have hQ : (2) * (c * (N : ℚ)) ^ 2 - (p : ℚ) * ((N : ℕ) : ℚ) ^ 2 =
            (2 * (p : ℚ)) * (e * (N : ℚ)) ^ 2 := by
          linear_combination ((N : ℕ) : ℚ) ^ 2 * hsub1
        exact_mod_cast (by rw [hCQ, hEQ]; exact_mod_cast hQ :
          (2) * ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) ^ 2 - (p : ℚ) * ((N : ℕ) : ℚ) ^ 2 =
          (2 * (p : ℚ)) * ((e.num * (c.den * f.den : ℕ) : ℤ) : ℚ) ^ 2)
      have hint2 : 2 * (c.num * (e.den * f.den : ℕ) : ℤ) ^ 2 + (p : ℤ) * ((N : ℕ) : ℤ) ^ 2 =
          (p : ℤ) * (f.num * (c.den * e.den : ℕ) : ℤ) ^ 2 := by
        have hQ : (2) * (c * (N : ℚ)) ^ 2 + (p : ℚ) * ((N : ℕ) : ℚ) ^ 2 =
            ((p : ℚ)) * (f * (N : ℚ)) ^ 2 := by
          linear_combination ((N : ℕ) : ℚ) ^ 2 * hsub2
        exact_mod_cast (by rw [hCQ, hFQ]; exact_mod_cast hQ :
          (2) * ((c.num * (e.den * f.den : ℕ) : ℤ) : ℚ) ^ 2 + (p : ℚ) * ((N : ℕ) : ℚ) ^ 2 =
          ((p : ℚ)) * ((f.num * (c.den * e.den : ℕ) : ℤ) : ℚ) ^ 2)
      have hNnat : N ≠ 0 := by
        rw [hN]
        exact Nat.mul_ne_zero (Nat.mul_ne_zero c.den_nz e.den_nz) f.den_nz
      have hNne : (((N : ℕ) : ℤ)) ≠ 0 := by exact_mod_cast hNnat
      exact kernelTwoTwoP hp h8 _ _ _ _ hNne hint1 hint2

/-! ## 7. The torsion realizers and their faces -/

private lemma nonsingularZeroP (hp : p.Prime) : (FamilyFace.E p).Nonsingular 0 0 := by
  have hpn : (p : ℚ) ≠ 0 := pQ_ne hp
  rw [nonsingular_iff, equation_iff]
  refine ⟨by simp [FamilyFace.E], Or.inl ?_⟩
  simp only [FamilyFace.E]
  intro hc
  exact hpn (pow_eq_zero_iff two_ne_zero |>.mp (by linarith))

private lemma nonsingularRightP (hp : p.Prime) :
    (FamilyFace.E p).Nonsingular (p : ℚ) 0 := by
  have hppos := p_pos hp
  rw [nonsingular_iff, equation_iff]
  refine ⟨by simp [FamilyFace.E]; ring, Or.inl ?_⟩
  simp only [FamilyFace.E]
  intro hc
  nlinarith [hppos]

/-- The half-turn at zero on the stratum twist. -/
def torsionZeroP (hp : p.Prime) : (FamilyFace.E p).Point := .some 0 0 (nonsingularZeroP hp)

/-- The half-turn at the prime. -/
def torsionRightP (hp : p.Prime) : (FamilyFace.E p).Point :=
  .some p 0 (nonsingularRightP hp)

private lemma face_zeroP (_hp : p.Prime) :
    Descent.SqCls (FamilyFace.slotOne p (0 : (FamilyFace.E p).Point)) 1 ∧
    Descent.SqCls (FamilyFace.slotTwo p (0 : (FamilyFace.E p).Point)) 1 :=
  ⟨Descent.sqClsRefl 1, Descent.sqClsRefl 1⟩

private lemma face_T0 (hp : p.Prime) :
    Descent.SqCls (FamilyFace.slotOne p (torsionZeroP hp)) (-1) ∧
    Descent.SqCls (FamilyFace.slotTwo p (torsionZeroP hp)) (-(p : ℚ)) := by
  constructor
  · rw [show torsionZeroP hp = Point.some 0 0 (nonsingularZeroP hp) from rfl,
      slotPOne_some, if_pos rfl]
    exact ⟨(p : ℚ), pQ_ne hp, by ring⟩
  · rw [show torsionZeroP hp = Point.some 0 0 (nonsingularZeroP hp) from rfl,
      slotPTwo_some, if_neg (fun hc => pQ_ne hp hc.symm), zero_sub]
    exact ⟨1, one_ne_zero, by ring⟩

private lemma face_Tp (hp : p.Prime) :
    Descent.SqCls (FamilyFace.slotOne p (torsionRightP hp)) (p : ℚ) ∧
    Descent.SqCls (FamilyFace.slotTwo p (torsionRightP hp)) 2 := by
  constructor
  · rw [show torsionRightP hp = Point.some (p : ℚ) 0 (nonsingularRightP hp) from rfl,
      slotPOne_some, if_neg (pQ_ne hp)]
    exact ⟨1, one_ne_zero, by ring⟩
  · rw [show torsionRightP hp = Point.some (p : ℚ) 0 (nonsingularRightP hp) from rfl,
      slotPTwo_some, if_pos rfl]
    exact ⟨(p : ℚ), pQ_ne hp, by ring⟩

private lemma face_addP (hp : p.Prime) {P Q : (FamilyFace.E p).Point} {a b a' b' t₁ t₂ : ℚ}
    (hP : Descent.SqCls (FamilyFace.slotOne p P) a ∧
      Descent.SqCls (FamilyFace.slotTwo p P) b)
    (hQ : Descent.SqCls (FamilyFace.slotOne p Q) a' ∧
      Descent.SqCls (FamilyFace.slotTwo p Q) b')
    (h₁ : Descent.SqCls (a * a') t₁) (h₂ : Descent.SqCls (b * b') t₂) :
    Descent.SqCls (FamilyFace.slotOne p (P + Q)) t₁ ∧
    Descent.SqCls (FamilyFace.slotTwo p (P + Q)) t₂ := by
  obtain ⟨g₁, g₂⟩ := FamilyFace.theFaceIsAHomomorphismOnEveryTwist (pQ_ne hp) P Q
  exact ⟨sqcls_trans g₁ (sqcls_trans (sqcls_mul hP.1 hQ.1) h₁),
    sqcls_trans g₂ (sqcls_trans (sqcls_mul hP.2 hQ.2) h₂)⟩

private lemma face_T0Tp (hp : p.Prime) :
    Descent.SqCls (FamilyFace.slotOne p (torsionZeroP hp + torsionRightP hp)) (-(p : ℚ)) ∧
    Descent.SqCls (FamilyFace.slotTwo p (torsionZeroP hp + torsionRightP hp))
      (-(2 * (p : ℚ))) :=
  face_addP hp (face_T0 hp) (face_Tp hp)
    ⟨1, one_ne_zero, by ring⟩ ⟨1, one_ne_zero, by ring⟩

private lemma refuse_by_translation (hp : p.Prime) {d₁ d₂ k₁ k₂ A B : ℚ}
    (P R : (FamilyFace.E p).Point)
    (href : ∀ Q : (FamilyFace.E p).Point,
      ¬ (Descent.SqCls (FamilyFace.slotOne p Q) A ∧
         Descent.SqCls (FamilyFace.slotTwo p Q) B))
    (hR : Descent.SqCls (FamilyFace.slotOne p R) k₁ ∧
      Descent.SqCls (FamilyFace.slotTwo p R) k₂)
    (hc₁ : Descent.SqCls (FamilyFace.slotOne p P) d₁)
    (hc₂ : Descent.SqCls (FamilyFace.slotTwo p P) d₂)
    (ht₁ : Descent.SqCls (d₁ * k₁) A) (ht₂ : Descent.SqCls (d₂ * k₂) B) : False := by
  obtain ⟨g₁, g₂⟩ := FamilyFace.theFaceIsAHomomorphismOnEveryTwist (pQ_ne hp) P R
  exact href (P + R)
    ⟨sqcls_trans g₁ (sqcls_trans (sqcls_mul hc₁ hR.1) ht₁),
     sqcls_trans g₂ (sqcls_trans (sqcls_mul hc₂ hR.2) ht₂)⟩

/-! ## 8. The completed descent on the stratum -/

/-- The four torsion classes of the stratum twist. -/
def RealizedP (p : ℕ) (d₁ d₂ : ℚ) : Prop :=
  (d₁ = 1 ∧ d₂ = 1) ∨ (d₁ = -1 ∧ d₂ = -(p : ℚ)) ∨
  (d₁ = (p : ℚ) ∧ d₂ = 2) ∨ (d₁ = -(p : ℚ) ∧ d₂ = -(2 * (p : ℚ)))

/-- **THE STRATUM DESCENT IS COMPLETE**: for every prime `p ≡ 3 (mod 8)` and every
point of `y² = x³ − p²x`, the face lies in the four torsion classes — corank zero
across the infinite family, infinitely many Ш[2]-vanishing certificates in one
theorem. -/
theorem theStratumDescentIsComplete (hp : p.Prime) (h8 : p % 8 = 3) [Fact p.Prime]
    (P : (FamilyFace.E p).Point) :
    ∃ d₁ d₂ : ℚ, RealizedP p d₁ d₂ ∧
      Descent.SqCls (FamilyFace.slotOne p P) d₁ ∧
      Descent.SqCls (FamilyFace.slotTwo p P) d₂ := by
  have hppos := p_pos hp
  rcases P with _ | @⟨x, y, hP⟩
  · exact ⟨1, 1, Or.inl ⟨rfl, rfl⟩, Descent.sqClsRefl 1, Descent.sqClsRefl 1⟩
  · have hcurve := onCurveP hP
    by_cases hy : y = 0
    · rw [hy] at hcurve
      have h0 : x * (x - p) * (x + p) = 0 := by linear_combination -hcurve
      have hx3 : x = 0 ∨ x = (p : ℚ) ∨ x = -(p : ℚ) := by
        rcases mul_eq_zero.mp h0 with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl (by linarith))
        · exact Or.inr (Or.inr (by linarith))
      rcases hx3 with rfl | rfl | rfl
      · refine ⟨-1, -(p : ℚ), Or.inr (Or.inl ⟨rfl, rfl⟩), ?_, ?_⟩
        · rw [slotPOne_some, if_pos rfl]
          exact ⟨(p : ℚ), pQ_ne hp, by ring⟩
        · rw [slotPTwo_some, if_neg (fun hc => pQ_ne hp hc.symm), zero_sub]
          exact ⟨1, one_ne_zero, by ring⟩
      · refine ⟨(p : ℚ), 2, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), ?_, ?_⟩
        · rw [slotPOne_some, if_neg (pQ_ne hp)]
          exact ⟨1, one_ne_zero, by ring⟩
        · rw [slotPTwo_some, if_pos rfl]
          exact ⟨(p : ℚ), pQ_ne hp, by ring⟩
      · refine ⟨-(p : ℚ), -(2 * (p : ℚ)), Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)), ?_, ?_⟩
        · rw [slotPOne_some, if_neg (by intro hc; exact pQ_ne hp (by linarith))]
          exact ⟨1, one_ne_zero, by ring⟩
        · rw [slotPTwo_some, if_neg (by intro hc; exact pQ_ne hp (by linarith))]
          exact ⟨1, one_ne_zero, by ring⟩
    · obtain ⟨hx0, hxp, hxmp⟩ := avoidP hcurve hy
      obtain ⟨⟨d₁, hd₁, hc₁⟩, ⟨d₂, hd₂, hc₂⟩⟩ :=
        theSlotClassesAreSupportedOnTheStratum hp (by omega) hcurve hy
      have hsig := theSignsAgreeOnTheStratum hp hcurve hy hc₁ hc₂
      have hs1 : Descent.SqCls (FamilyFace.slotOne p (Point.some _ _ hP)) d₁ := by
        rw [slotPOne_some, if_neg hx0]
        exact hc₁
      have hs2 : Descent.SqCls (FamilyFace.slotTwo p (Point.some _ _ hP)) d₂ := by
        rw [slotPTwo_some, if_neg hxp]
        exact hc₂
      clear hc₁ hc₂
      rcases hd₁ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases hd₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · -- (1, 1): realized
        exact ⟨_, _, Or.inl ⟨rfl, rfl⟩, hs1, hs2⟩
      · -- (1, -1): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (1, 2): translated and refused
        exact absurd (refuse_by_translation hp _ (0 : (FamilyFace.E p).Point)
          (refuseOneTwo hp h8) (face_zeroP hp) hs1 hs2
          ⟨1, one_ne_zero, by ring⟩ ⟨1, one_ne_zero, by ring⟩) not_false
      · -- (1, -2): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (1, (p : ℚ)): translated and refused
        exact absurd (refuse_by_translation hp _ (0 : (FamilyFace.E p).Point)
          (refuseOneP hp h8) (face_zeroP hp) hs1 hs2
          ⟨1, one_ne_zero, by ring⟩ ⟨1, one_ne_zero, by ring⟩) not_false
      · -- (1, -(p : ℚ)): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by linarith)
        · exact absurd hA (by norm_num)
      · -- (1, 2 * (p : ℚ)): translated and refused
        exact absurd (refuse_by_translation hp _ (0 : (FamilyFace.E p).Point)
          (refuseOneTwoP hp h8) (face_zeroP hp) hs1 hs2
          ⟨1, one_ne_zero, by ring⟩ ⟨1, one_ne_zero, by ring⟩) not_false
      · -- (1, -(2 * (p : ℚ))): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by linarith)
        · exact absurd hA (by norm_num)
      · -- (-1, 1): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-1, -1): translated and refused
        exact absurd (refuse_by_translation hp _ (torsionZeroP hp)
          (refuseOneP hp h8) (face_T0 hp) hs1 hs2
          ⟨1, one_ne_zero, by ring⟩ ⟨1, one_ne_zero, by ring⟩) not_false
      · -- (-1, 2): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-1, -2): translated and refused
        exact absurd (refuse_by_translation hp _ (torsionZeroP hp)
          (refuseOneTwoP hp h8) (face_T0 hp) hs1 hs2
          ⟨1, one_ne_zero, by ring⟩ ⟨1, one_ne_zero, by ring⟩) not_false
      · -- (-1, (p : ℚ)): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by linarith)
      · -- (-1, -(p : ℚ)): realized
        exact ⟨_, _, Or.inr (Or.inl ⟨rfl, rfl⟩), hs1, hs2⟩
      · -- (-1, 2 * (p : ℚ)): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by linarith)
      · -- (-1, -(2 * (p : ℚ))): translated and refused
        exact absurd (refuse_by_translation hp _ (torsionZeroP hp)
          (refuseOneTwo hp h8) (face_T0 hp) hs1 hs2
          ⟨1, one_ne_zero, by ring⟩ ⟨(p : ℚ), (pQ_ne hp), by ring⟩) not_false
      · -- (2, 1): translated and refused
        exact absurd (refuse_by_translation hp _ (0 : (FamilyFace.E p).Point)
          (refuseTwoOne hp h8) (face_zeroP hp) hs1 hs2
          ⟨1, one_ne_zero, by ring⟩ ⟨1, one_ne_zero, by ring⟩) not_false
      · -- (2, -1): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (2, 2): translated and refused
        exact absurd (refuse_by_translation hp _ (0 : (FamilyFace.E p).Point)
          (refuseTwoTwo hp h8) (face_zeroP hp) hs1 hs2
          ⟨1, one_ne_zero, by ring⟩ ⟨1, one_ne_zero, by ring⟩) not_false
      · -- (2, -2): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by norm_num)
      · -- (2, (p : ℚ)): translated and refused
        exact absurd (refuse_by_translation hp _ (0 : (FamilyFace.E p).Point)
          (refuseTwoP hp h8) (face_zeroP hp) hs1 hs2
          ⟨1, one_ne_zero, by ring⟩ ⟨1, one_ne_zero, by ring⟩) not_false
      · -- (2, -(p : ℚ)): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by linarith)
        · exact absurd hA (by norm_num)
      · -- (2, 2 * (p : ℚ)): translated and refused
        exact absurd (refuse_by_translation hp _ (0 : (FamilyFace.E p).Point)
          (refuseTwoTwoP hp h8) (face_zeroP hp) hs1 hs2
          ⟨1, one_ne_zero, by ring⟩ ⟨1, one_ne_zero, by ring⟩) not_false
      · -- (2, -(2 * (p : ℚ))): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by linarith)
        · exact absurd hA (by norm_num)
      · -- (-2, 1): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-2, -1): translated and refused
        exact absurd (refuse_by_translation hp _ (torsionZeroP hp)
          (refuseTwoP hp h8) (face_T0 hp) hs1 hs2
          ⟨1, one_ne_zero, by ring⟩ ⟨1, one_ne_zero, by ring⟩) not_false
      · -- (-2, 2): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by norm_num)
      · -- (-2, -2): translated and refused
        exact absurd (refuse_by_translation hp _ (torsionZeroP hp)
          (refuseTwoTwoP hp h8) (face_T0 hp) hs1 hs2
          ⟨1, one_ne_zero, by ring⟩ ⟨1, one_ne_zero, by ring⟩) not_false
      · -- (-2, (p : ℚ)): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by linarith)
      · -- (-2, -(p : ℚ)): translated and refused
        exact absurd (refuse_by_translation hp _ (torsionZeroP hp)
          (refuseTwoOne hp h8) (face_T0 hp) hs1 hs2
          ⟨1, one_ne_zero, by ring⟩ ⟨(p : ℚ), (pQ_ne hp), by ring⟩) not_false
      · -- (-2, 2 * (p : ℚ)): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by norm_num)
        · exact absurd hB (by linarith)
      · -- (-2, -(2 * (p : ℚ))): translated and refused
        exact absurd (refuse_by_translation hp _ (torsionZeroP hp)
          (refuseTwoTwo hp h8) (face_T0 hp) hs1 hs2
          ⟨1, one_ne_zero, by ring⟩ ⟨(p : ℚ), (pQ_ne hp), by ring⟩) not_false
      · -- ((p : ℚ), 1): translated and refused
        exact absurd (refuse_by_translation hp _ (torsionRightP hp)
          (refuseOneTwo hp h8) (face_Tp hp) hs1 hs2
          ⟨(p : ℚ), (pQ_ne hp), by ring⟩ ⟨1, one_ne_zero, by ring⟩) not_false
      · -- ((p : ℚ), -1): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by linarith)
      · -- ((p : ℚ), 2): realized
        exact ⟨_, _, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), hs1, hs2⟩
      · -- ((p : ℚ), -2): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by linarith)
      · -- ((p : ℚ), (p : ℚ)): translated and refused
        exact absurd (refuse_by_translation hp _ (torsionRightP hp)
          (refuseOneTwoP hp h8) (face_Tp hp) hs1 hs2
          ⟨(p : ℚ), (pQ_ne hp), by ring⟩ ⟨1, one_ne_zero, by ring⟩) not_false
      · -- ((p : ℚ), -(p : ℚ)): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by linarith)
        · exact absurd hA (by linarith)
      · -- ((p : ℚ), 2 * (p : ℚ)): translated and refused
        exact absurd (refuse_by_translation hp _ (torsionRightP hp)
          (refuseOneP hp h8) (face_Tp hp) hs1 hs2
          ⟨(p : ℚ), (pQ_ne hp), by ring⟩ ⟨2, two_ne_zero, by ring⟩) not_false
      · -- ((p : ℚ), -(2 * (p : ℚ))): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by linarith)
        · exact absurd hA (by linarith)
      · -- (-(p : ℚ), 1): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by linarith)
        · exact absurd hB (by norm_num)
      · -- (-(p : ℚ), -1): translated and refused
        exact absurd (refuse_by_translation hp _ (torsionZeroP hp + torsionRightP hp)
          (refuseOneTwoP hp h8) (face_T0Tp hp) hs1 hs2
          ⟨(p : ℚ), (pQ_ne hp), by ring⟩ ⟨1, one_ne_zero, by ring⟩) not_false
      · -- (-(p : ℚ), 2): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by linarith)
        · exact absurd hB (by norm_num)
      · -- (-(p : ℚ), -2): translated and refused
        exact absurd (refuse_by_translation hp _ (torsionZeroP hp + torsionRightP hp)
          (refuseOneP hp h8) (face_T0Tp hp) hs1 hs2
          ⟨(p : ℚ), (pQ_ne hp), by ring⟩ ⟨2, two_ne_zero, by ring⟩) not_false
      · -- (-(p : ℚ), (p : ℚ)): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by linarith)
        · exact absurd hB (by linarith)
      · -- (-(p : ℚ), -(p : ℚ)): translated and refused
        exact absurd (refuse_by_translation hp _ (torsionZeroP hp + torsionRightP hp)
          (refuseOneTwo hp h8) (face_T0Tp hp) hs1 hs2
          ⟨(p : ℚ), (pQ_ne hp), by ring⟩ ⟨(p : ℚ), (pQ_ne hp), by ring⟩) not_false
      · -- (-(p : ℚ), 2 * (p : ℚ)): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by linarith)
        · exact absurd hB (by linarith)
      · -- (-(p : ℚ), -(2 * (p : ℚ))): realized
        exact ⟨_, _, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)), hs1, hs2⟩
      · -- (2 * (p : ℚ), 1): translated and refused
        exact absurd (refuse_by_translation hp _ (torsionRightP hp)
          (refuseTwoTwo hp h8) (face_Tp hp) hs1 hs2
          ⟨(p : ℚ), (pQ_ne hp), by ring⟩ ⟨1, one_ne_zero, by ring⟩) not_false
      · -- (2 * (p : ℚ), -1): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by linarith)
      · -- (2 * (p : ℚ), 2): translated and refused
        exact absurd (refuse_by_translation hp _ (torsionRightP hp)
          (refuseTwoOne hp h8) (face_Tp hp) hs1 hs2
          ⟨(p : ℚ), (pQ_ne hp), by ring⟩ ⟨2, two_ne_zero, by ring⟩) not_false
      · -- (2 * (p : ℚ), -2): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by norm_num)
        · exact absurd hA (by linarith)
      · -- (2 * (p : ℚ), (p : ℚ)): translated and refused
        exact absurd (refuse_by_translation hp _ (torsionRightP hp)
          (refuseTwoTwoP hp h8) (face_Tp hp) hs1 hs2
          ⟨(p : ℚ), (pQ_ne hp), by ring⟩ ⟨1, one_ne_zero, by ring⟩) not_false
      · -- (2 * (p : ℚ), -(p : ℚ)): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by linarith)
        · exact absurd hA (by linarith)
      · -- (2 * (p : ℚ), 2 * (p : ℚ)): translated and refused
        exact absurd (refuse_by_translation hp _ (torsionRightP hp)
          (refuseTwoP hp h8) (face_Tp hp) hs1 hs2
          ⟨(p : ℚ), (pQ_ne hp), by ring⟩ ⟨2, two_ne_zero, by ring⟩) not_false
      · -- (2 * (p : ℚ), -(2 * (p : ℚ))): mixed signs
        rcases hsig with ⟨-, hB⟩ | ⟨hA, -⟩
        · exact absurd hB (by linarith)
        · exact absurd hA (by linarith)
      · -- (-(2 * (p : ℚ)), 1): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by linarith)
        · exact absurd hB (by norm_num)
      · -- (-(2 * (p : ℚ)), -1): translated and refused
        exact absurd (refuse_by_translation hp _ (torsionZeroP hp + torsionRightP hp)
          (refuseTwoTwoP hp h8) (face_T0Tp hp) hs1 hs2
          ⟨(p : ℚ), (pQ_ne hp), by ring⟩ ⟨1, one_ne_zero, by ring⟩) not_false
      · -- (-(2 * (p : ℚ)), 2): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by linarith)
        · exact absurd hB (by norm_num)
      · -- (-(2 * (p : ℚ)), -2): translated and refused
        exact absurd (refuse_by_translation hp _ (torsionZeroP hp + torsionRightP hp)
          (refuseTwoP hp h8) (face_T0Tp hp) hs1 hs2
          ⟨(p : ℚ), (pQ_ne hp), by ring⟩ ⟨2, two_ne_zero, by ring⟩) not_false
      · -- (-(2 * (p : ℚ)), (p : ℚ)): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by linarith)
        · exact absurd hB (by linarith)
      · -- (-(2 * (p : ℚ)), -(p : ℚ)): translated and refused
        exact absurd (refuse_by_translation hp _ (torsionZeroP hp + torsionRightP hp)
          (refuseTwoTwo hp h8) (face_T0Tp hp) hs1 hs2
          ⟨(p : ℚ), (pQ_ne hp), by ring⟩ ⟨(p : ℚ), (pQ_ne hp), by ring⟩) not_false
      · -- (-(2 * (p : ℚ)), 2 * (p : ℚ)): mixed signs
        rcases hsig with ⟨hA, -⟩ | ⟨-, hB⟩
        · exact absurd hA (by linarith)
        · exact absurd hB (by linarith)
      · -- (-(2 * (p : ℚ)), -(2 * (p : ℚ))): translated and refused
        exact absurd (refuse_by_translation hp _ (torsionZeroP hp + torsionRightP hp)
          (refuseTwoOne hp h8) (face_T0Tp hp) hs1 hs2
          ⟨(p : ℚ), (pQ_ne hp), by ring⟩ ⟨2 * (p : ℚ), (by have := p_pos hp; positivity), by ring⟩) not_false

/-- **THE REALIZED FOUR ARE IN THE IMAGE**: each torsion class is the face of its
half-turn, so the image is exactly the four — the descent of every stratum twist is
complete. -/
theorem theRealizedFourAreInTheImageOnTheStratum (hp : p.Prime) (d₁ d₂ : ℚ)
    (h : RealizedP p d₁ d₂) :
    ∃ P : (FamilyFace.E p).Point,
      Descent.SqCls (FamilyFace.slotOne p P) d₁ ∧
      Descent.SqCls (FamilyFace.slotTwo p P) d₂ := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨0, face_zeroP hp⟩
  · exact ⟨_, face_T0 hp⟩
  · exact ⟨_, face_Tp hp⟩
  · exact ⟨_, face_T0Tp hp⟩

/-! ## 9. The governance matrix and its corank law -/

open scoped Classical in
/-- The governance matrix of an odd-prime twist: the diagonal 𝔽₂ matrix of the two
governing characters — the quarter-turn bit and the two bit.  Its corank reads the
descent: on the stratum both characters refuse, the matrix is the identity, and the
completed descent above is the corank-zero content. -/
noncomputable def governanceMatrix (p : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![if IsSquare (-1 : ZMod p) then 0 else 1, 0],
    ![0, if IsSquare (2 : ZMod p) then 0 else 1]]

/-- **THE GOVERNANCE LAW ON THE STRATUM**: for every prime `p ≡ 3 (mod 8)` the
governance matrix is the identity — both governing characters refuse — **and** the
descent image is exactly the four torsion classes.  Corank zero, proved family-wise,
with the completed descent as its content rather than a declaration. -/
theorem theGovernanceCorankLawOnTheStratum (hp : p.Prime) (h8 : p % 8 = 3)
    [Fact p.Prime] :
    governanceMatrix p = 1 ∧
    (∀ P : (FamilyFace.E p).Point, ∃ d₁ d₂ : ℚ, RealizedP p d₁ d₂ ∧
      Descent.SqCls (FamilyFace.slotOne p P) d₁ ∧
      Descent.SqCls (FamilyFace.slotTwo p P) d₂) := by
  constructor
  · unfold governanceMatrix
    rw [if_neg (Congruum.theQuarterTurnIsInvisibleAtEight h8),
      if_neg (Congruum.theTwoIsInvisible h8)]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · exact theStratumDescentIsComplete hp h8

end Soma.Holonics.Millennium.StratumDescent
