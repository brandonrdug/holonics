import ElementaryHolonics.Millennium.FamilySevenDescent

/-!
# FamilyOddDescent: the rank is at most two at every odd prime

**The character-free collapse.**  With no residue character at all — only the
valuation ledger at `p`, the uniform two-adic kill, and the archimedean sign —
the slot classes of `y² = x³ − p²x` collapse to **sixteen** cells at every odd
prime, and the pigeonhole `3·2^r ≤ 16` bounds the rank by **two** uniformly.
This sharpens the sixty-four-cell bound of four and is exactly the generic
two-descent (2-Selmer) bound; the branch files then cut it to one at
`p ≡ 5, 7 (mod 8)` and to zero at `p ≡ 3 (mod 8)`.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyOddDescent

open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.FamilyGenocchi
open Soma.Holonics.Millennium.FamilyFiveDescent

variable {p : ℕ} [Fact p.Prime]

open WeierstrassCurve.Affine
open DirectSum
open Soma.Holonics.Millennium.FamilyKernel
open Soma.Holonics.Millennium.FamilySupport

set_option maxHeartbeats 4000000 in
/-- **THE SLOT CLASSES COLLAPSE AT EVERY ODD PRIME**: with no character input at
all, the valuation ledger, the uniform two-adic kill, and the archimedean sign
collapse the slot-class pair of any point of `y² = x³ − p²x` with `y ≠ 0` to
**sixteen** named cells — the generic two-descent bound, uniformly in the odd
prime. -/
theorem theSlotClassesCollapseAtEveryOddPrime
    (hp2'' : p ≠ 2) {x y : ℚ}
    (hcurve : y ^ 2 = x ^ 3 - ((p : ℕ) : ℚ) ^ 2 * x) (hy : y ≠ 0)
    {d₁ d₂ : ℤ} (h₁0 : d₁ ≠ 0) (h₂0 : d₂ ≠ 0)
    (h₁v : d₁.natAbs ∣ 2 * p) (h₂v : d₂.natAbs ∣ 2 * p)
    (h₁ : Descent.SqCls x ((d₁ : ℤ) : ℚ))
    (h₂ : Descent.SqCls (x - ((p : ℕ) : ℚ)) ((d₂ : ℤ) : ℚ)) :
    (d₁ = 1 ∧ d₂ = 1) ∨ (d₁ = 1 ∧ d₂ = 2) ∨
    (d₁ = -1 ∧ d₂ = -1) ∨ (d₁ = -1 ∧ d₂ = -2) ∨
    (d₁ = 1 ∧ d₂ = (p : ℤ)) ∨ (d₁ = 1 ∧ d₂ = 2 * p) ∨
    (d₁ = -1 ∧ d₂ = -(p : ℤ)) ∨ (d₁ = -1 ∧ d₂ = -2 * p) ∨
    (d₁ = (p : ℤ) ∧ d₂ = 1) ∨ (d₁ = (p : ℤ) ∧ d₂ = 2) ∨
    (d₁ = -(p : ℤ) ∧ d₂ = -1) ∨ (d₁ = -(p : ℤ) ∧ d₂ = -2) ∨
    (d₁ = (p : ℤ) ∧ d₂ = (p : ℤ)) ∨ (d₁ = (p : ℤ) ∧ d₂ = 2 * p) ∨
    (d₁ = -(p : ℤ) ∧ d₂ = -(p : ℤ)) ∨ (d₁ = -(p : ℤ) ∧ d₂ = -2 * p) := by
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
  have hp3 : 2 < p := by have := hp.two_le; omega
  have hd₁odd : ¬ (2 : ℤ) ∣ d₁ :=
    FamilySevenDescent.theFirstSlotIsOddAtEveryOddPrime hp2'' hx0 hxm0 hxp0
      h₁0 h₂0 h₁v h₂v h₁ h₂ h₃
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
    -- eliminate the candidates by parity, the two-adic kill, and the sign
    have hd₁c : d₁ = 1 ∨ d₁ = -1 := by
      rcases rung_cases hp3 h₁0 h₁v with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd ⟨1, by ring⟩ hd₁odd
      · exact absurd ⟨-1, by ring⟩ hd₁odd
      · exact absurd (dvd_refl _) hfree₁
      · exact absurd (dvd_neg.mpr (dvd_refl _)) hfree₁
      · exact absurd ⟨2, by ring⟩ hfree₁
      · exact absurd (dvd_neg.mpr ⟨2, by ring⟩) hfree₁
    have hd₂c : d₂ = 1 ∨ d₂ = -1 ∨ d₂ = 2 ∨ d₂ = -2 := by
      rcases rung_cases hp3 h₂0 h₂v with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact absurd (dvd_refl _) hfree₂
      · exact absurd (dvd_neg.mpr (dvd_refl _)) hfree₂
      · exact absurd ⟨2, by ring⟩ hfree₂
      · exact absurd (dvd_neg.mpr ⟨2, by ring⟩) hfree₂
    rcases hd₁c with rfl | rfl <;> rcases hd₂c with rfl | rfl | rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exfalso; omega
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exfalso; omega
    · exfalso; omega
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exfalso; omega
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
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
      -- candidates by parity, the two-adic kill, and the sign
      have hd₁c : d₁ = 1 ∨ d₁ = -1 := by
        rcases rung_cases hp3 h₁0 h₁v with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd ⟨1, by ring⟩ hd₁odd
        · exact absurd ⟨-1, by ring⟩ hd₁odd
        · exact absurd (dvd_refl _) hfree₁
        · exact absurd (dvd_neg.mpr (dvd_refl _)) hfree₁
        · exact absurd ⟨2, by ring⟩ hfree₁
        · exact absurd (dvd_neg.mpr ⟨2, by ring⟩) hfree₁
      have hd₂'c : d₂' = 1 ∨ d₂' = -1 ∨ d₂' = 2 ∨ d₂' = -2 := by
        rcases rung_cases hp3 hd₂'0 hd₂'v with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
        · exact absurd (dvd_refl _) hd₂'free
        · exact absurd (dvd_neg.mpr (dvd_refl _)) hd₂'free
        · exact absurd ⟨2, by ring⟩ hd₂'free
        · exact absurd (dvd_neg.mpr ⟨2, by ring⟩) hd₂'free
      rcases hd₁c with rfl | rfl <;> rcases hd₂'c with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, by omega⟩)))))
      · exfalso
        rw [hd₂'] at h₁₂pos
        nlinarith [h₁₂pos]
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, by omega⟩))))))
      · exfalso
        rw [hd₂'] at h₁₂pos
        nlinarith [h₁₂pos]
      · exfalso
        rw [hd₂'] at h₁₂pos
        nlinarith [h₁₂pos]
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, by omega⟩)))))))
      · exfalso
        rw [hd₂'] at h₁₂pos
        nlinarith [h₁₂pos]
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, by omega⟩))))))))
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
        have hd₁'c : d₁' = 1 ∨ d₁' = -1 := by
          rcases rung_cases hp3 hd₁'0 hd₁'v with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
          · exact absurd (by rw [hd₁']; exact ⟨(p : ℤ), by ring⟩ : (2 : ℤ) ∣ d₁) hd₁odd
          · exact absurd (by rw [hd₁']; exact ⟨-(p : ℤ), by ring⟩ : (2 : ℤ) ∣ d₁) hd₁odd
          · exact absurd (dvd_refl _) hd₁'free
          · exact absurd (dvd_neg.mpr (dvd_refl _)) hd₁'free
          · exact absurd ⟨2, by ring⟩ hd₁'free
          · exact absurd (dvd_neg.mpr ⟨2, by ring⟩) hd₁'free
        have hd₂c : d₂ = 1 ∨ d₂ = -1 ∨ d₂ = 2 ∨ d₂ = -2 := by
          rcases rung_cases hp3 h₂0 h₂v with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr rfl))
          · exact absurd (dvd_refl _) hfree₂
          · exact absurd (dvd_neg.mpr (dvd_refl _)) hfree₂
          · exact absurd ⟨2, by ring⟩ hfree₂
          · exact absurd (dvd_neg.mpr ⟨2, by ring⟩) hfree₂
        rcases hd₁'c with rfl | rfl <;> rcases hd₂c with rfl | rfl | rfl | rfl
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, rfl⟩)))))))))
        · exfalso
          rw [hd₁'] at h₁₂pos
          nlinarith [h₁₂pos]
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, rfl⟩))))))))))
        · exfalso
          rw [hd₁'] at h₁₂pos
          nlinarith [h₁₂pos]
        · exfalso
          rw [hd₁'] at h₁₂pos
          nlinarith [h₁₂pos]
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, rfl⟩)))))))))))
        · exfalso
          rw [hd₁'] at h₁₂pos
          nlinarith [h₁₂pos]
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, rfl⟩))))))))))))
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
        have hd₁'c : d₁' = 1 ∨ d₁' = -1 := by
          rcases rung_cases hp3 hd₁'0 hd₁'v with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
          · exact absurd (by rw [hd₁']; exact ⟨(p : ℤ), by ring⟩ : (2 : ℤ) ∣ d₁) hd₁odd
          · exact absurd (by rw [hd₁']; exact ⟨-(p : ℤ), by ring⟩ : (2 : ℤ) ∣ d₁) hd₁odd
          · exact absurd (dvd_refl _) hd₁'free
          · exact absurd (dvd_neg.mpr (dvd_refl _)) hd₁'free
          · exact absurd ⟨2, by ring⟩ hd₁'free
          · exact absurd (dvd_neg.mpr ⟨2, by ring⟩) hd₁'free
        have hd₂'c : d₂' = 1 ∨ d₂' = -1 ∨ d₂' = 2 ∨ d₂' = -2 := by
          rcases rung_cases hp3 hd₂'0 hd₂'v with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr rfl))
          · exact absurd (dvd_refl _) hd₂'free
          · exact absurd (dvd_neg.mpr (dvd_refl _)) hd₂'free
          · exact absurd ⟨2, by ring⟩ hd₂'free
          · exact absurd (dvd_neg.mpr ⟨2, by ring⟩) hd₂'free
        rcases hd₁'c with rfl | rfl <;> rcases hd₂'c with rfl | rfl | rfl | rfl
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))))))))
        · exfalso
          rw [hd₁', hd₂'] at h₁₂pos
          nlinarith [h₁₂pos]
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))))))))
        · exfalso
          rw [hd₁', hd₂'] at h₁₂pos
          nlinarith [h₁₂pos]
        · exfalso
          rw [hd₁', hd₂'] at h₁₂pos
          nlinarith [h₁₂pos]
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))))))))))
        · exfalso
          rw [hd₁', hd₂'] at h₁₂pos
          nlinarith [h₁₂pos]
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega⟩)))))))))))))))







/-! ## The sixteen cells and the collision -/

/-- The sixteen admitted cells at every odd prime. -/
def cells16 (p : ℕ) : Finset (ℤ × ℤ) :=
  {((1 : ℤ), (1 : ℤ)), ((1 : ℤ), (2 : ℤ)), ((-1 : ℤ), (-1 : ℤ)),
   ((-1 : ℤ), (-2 : ℤ)), ((1 : ℤ), (p : ℤ)), ((1 : ℤ), 2 * (p : ℤ)),
   ((-1 : ℤ), -(p : ℤ)), ((-1 : ℤ), -2 * (p : ℤ)), ((p : ℤ), (1 : ℤ)),
   ((p : ℤ), (2 : ℤ)), (-(p : ℤ), (-1 : ℤ)), (-(p : ℤ), (-2 : ℤ)),
   ((p : ℤ), (p : ℤ)), ((p : ℤ), 2 * (p : ℤ)), (-(p : ℤ), -(p : ℤ)),
   (-(p : ℤ), -2 * (p : ℤ))}

lemma cells16_card_le (p : ℕ) : (cells16 p).card ≤ 16 := by
  unfold cells16
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine Nat.succ_le_succ ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine Nat.succ_le_succ ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine Nat.succ_le_succ ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine Nat.succ_le_succ ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine Nat.succ_le_succ ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine Nat.succ_le_succ ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine Nat.succ_le_succ ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine Nat.succ_le_succ ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine Nat.succ_le_succ ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine Nat.succ_le_succ ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine Nat.succ_le_succ ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine Nat.succ_le_succ ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine Nat.succ_le_succ ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine Nat.succ_le_succ ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine Nat.succ_le_succ ?_
  exact Finset.card_singleton _ |>.le

set_option maxHeartbeats 2000000 in
/-- **Every point lands in the sixteen cells**: the collapse places the moving
points, and the pins place the torsion. -/
lemma classOf_mem_cells16 (hp2' : p ≠ 2)
    (P : (FamilyFace.E (((p : ℕ) : ℚ))).Point) :
    FamilyCollision.classOf (Fact.out : p.Prime).pos P ∈ cells16 p := by
  have hp : p.Prime := Fact.out
  have hn : 0 < p := hp.pos
  have hpq0 : (((p : ℕ) : ℚ)) ≠ 0 := by exact_mod_cast hp.pos.ne'
  have hpqpos : (0 : ℚ) < ((p : ℕ) : ℚ) := by exact_mod_cast hp.pos
  obtain ⟨h10, h20, h1d, h2d, hsq1, hsq2⟩ := FamilyCollision.classOf_spec hn P
  set d₁ := (FamilyCollision.classOf hn P).1 with hd₁def
  set d₂ := (FamilyCollision.classOf hn P).2 with hd₂def
  simp only [cells16, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  rcases P with _ | @⟨x, y, hns⟩
  · -- the zero point: both slots read `1`
    have hs1 : slotOneAt (((p : ℕ) : ℚ)) 0 = 1 := rfl
    have hs2 : slotTwoAt (((p : ℕ) : ℚ)) 0 = 1 := rfl
    rw [← Point.zero_def] at hsq1 hsq2
    rw [hs1] at hsq1
    rw [hs2] at hsq2
    left
    rw [Prod.ext_iff]
    constructor
    · exact pin_one' hp2' one_ne_zero h10 h1d hsq1 one_pos
        (by rw [padicValRat.one]; exact ⟨0, by ring⟩)
        (by rw [padicValRat.one]; exact ⟨0, by ring⟩)
    · exact pin_one' hp2' one_ne_zero h20 h2d hsq2 one_pos
        (by rw [padicValRat.one]; exact ⟨0, by ring⟩)
        (by rw [padicValRat.one]; exact ⟨0, by ring⟩)
  · by_cases hy : y = 0
    · -- torsion abscissae: `x ∈ {0, p, −p}`
      have hcurve := onCurveAt hns
      rw [hy] at hcurve
      have hroots : x * (x - ((p : ℕ) : ℚ)) * (x + ((p : ℕ) : ℚ)) = 0 := by
        have : (0 : ℚ) ^ 2 = 0 := by norm_num
        nlinarith [hcurve]
      rcases mul_eq_zero.mp hroots with hxa | hxp
      rcases mul_eq_zero.mp hxa with hx0 | hxm
      · -- x = 0 : slots read (−p², −p)
        rw [slotOneAt_some, if_pos hx0] at hsq1
        rw [slotTwoAt_some, if_neg (by rw [hx0]; exact fun hc => hpq0 hc.symm)] at hsq2
        have hs2v : x - ((p : ℕ) : ℚ) = -((p : ℕ) : ℚ) := by rw [hx0]; ring
        rw [hs2v] at hsq2
        right; right; right; right; right; right; left
        rw [Prod.ext_iff]
        constructor
        · exact pin_neg_one' hp2' (neg_ne_zero.mpr (pow_ne_zero 2 hpq0)) h10 h1d hsq1
            (neg_lt_zero.mpr (by positivity)) (by rw [vp_neg_psq]; exact ⟨1, by ring⟩)
            (by rw [v2_neg_psq hp2']; exact ⟨0, by ring⟩)
        · exact pin_neg_p' hp2' (neg_ne_zero.mpr hpq0) h20 h2d hsq2
            (neg_lt_zero.mpr hpqpos) (by rw [vp_neg_p]; exact ⟨0, by ring⟩)
            (by rw [v2_neg_p hp2']; exact ⟨0, by ring⟩)
      · -- x = p : slots read (p, 2p²)
        have hxp' : x = ((p : ℕ) : ℚ) := by linarith [sub_eq_zero.mp hxm]
        rw [slotOneAt_some, if_neg (by rw [hxp']; exact hpq0)] at hsq1
        rw [slotTwoAt_some, if_pos hxp'] at hsq2
        rw [hxp'] at hsq1
        right; right; right; right; right; right; right; right; right; left
        rw [Prod.ext_iff]
        constructor
        · exact pin_p' hp2' hpq0 h10 h1d hsq1 hpqpos
            (by rw [val_p hp]; exact ⟨0, by ring⟩)
            (by rw [val2_p hp2']; exact ⟨0, by ring⟩)
        · exact pin_two' hp2' (by positivity) h20 h2d hsq2 (by positivity)
            (by rw [vp_two_psq hp2']; exact ⟨1, by ring⟩)
            (by rw [v2_two_psq hp2']; exact ⟨0, by ring⟩)
      · -- x = −p : slots read (−p, −2p)
        have hxm' : x = -((p : ℕ) : ℚ) := by linarith [eq_neg_of_add_eq_zero_left hxp]
        rw [slotOneAt_some, if_neg (by rw [hxm']; exact neg_ne_zero.mpr hpq0)] at hsq1
        rw [slotTwoAt_some, if_neg (by rw [hxm']; intro hc; apply hpq0; linarith)] at hsq2
        rw [hxm'] at hsq1
        have hs2v : x - ((p : ℕ) : ℚ) = -((2 : ℚ) * ((p : ℕ) : ℚ)) := by
          rw [hxm']; ring
        rw [hs2v] at hsq2
        right; right; right; right; right; right; right; right
        right; right; right; right; right; right; right
        rw [Prod.ext_iff]
        constructor
        · exact pin_neg_p' hp2' (neg_ne_zero.mpr hpq0) h10 h1d hsq1
            (neg_lt_zero.mpr hpqpos) (by rw [vp_neg_p]; exact ⟨0, by ring⟩)
            (by rw [v2_neg_p hp2']; exact ⟨0, by ring⟩)
        · have h := pin_neg_2p' hp2' (neg_ne_zero.mpr (by positivity)) h20 h2d hsq2
            (neg_lt_zero.mpr (by positivity)) (by rw [vp_neg_2p hp2']; exact ⟨0, by ring⟩)
            (by rw [v2_neg_2p hp2']; exact ⟨0, by ring⟩)
          exact h.trans (by ring)
    · -- moving points: the collapse
      have hcurve := onCurveAt hns
      rw [slotOneAt_some] at hsq1
      rw [slotTwoAt_some] at hsq2
      obtain ⟨hx0, hxn, -⟩ :=
        FaceHomomorphism.theNonzeroOrdinateAvoidsTheRoots hcurve hy
      rw [if_neg hx0] at hsq1
      rw [if_neg hxn] at hsq2
      rcases theSlotClassesCollapseAtEveryOddPrime hp2' hcurve hy
          h10 h20 h1d h2d hsq1 hsq2 with
        ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ |
          ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ |
          ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ |
          ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inl (Prod.ext_iff.mpr ⟨ha, hb⟩)
      · exact Or.inr (Or.inl (Prod.ext_iff.mpr ⟨ha, hb⟩))
      · exact Or.inr (Or.inr (Or.inl (Prod.ext_iff.mpr ⟨ha, hb⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (Prod.ext_iff.mpr ⟨ha, hb⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Prod.ext_iff.mpr ⟨ha, hb⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Prod.ext_iff.mpr ⟨ha, hb⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Prod.ext_iff.mpr ⟨ha, hb⟩)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Prod.ext_iff.mpr ⟨ha, hb⟩))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Prod.ext_iff.mpr ⟨ha, hb⟩)))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Prod.ext_iff.mpr ⟨ha, hb⟩))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Prod.ext_iff.mpr ⟨ha, hb⟩)))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Prod.ext_iff.mpr ⟨ha, hb⟩))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Prod.ext_iff.mpr ⟨ha, hb⟩)))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Prod.ext_iff.mpr ⟨ha, hb⟩))))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Prod.ext_iff.mpr ⟨ha, hb⟩)))))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Prod.ext_iff.mpr ⟨ha, hb⟩)))))))))))))))

/-- **THE CLASSES COLLIDE AT EVERY ODD PRIME**: any family of more than `16`
points contains two whose difference is a double. -/
theorem theClassesCollideAtEveryOddPrime (hp2'' : p ≠ 2) {α : Type}
    [Fintype α] (hcard : 16 < Fintype.card α)
    (f : α → (FamilyFace.E (((p : ℕ) : ℚ))).Point) :
    ∃ a b, a ≠ b ∧ ∃ Q : (FamilyFace.E (((p : ℕ) : ℚ))).Point, f a - f b = Q + Q := by
  have hp : p.Prime := Fact.out
  have hp2' : p ≠ 2 := hp2''
  have hn : 0 < p := hp.pos
  have hmaps : ∀ a : α, FamilyCollision.classOf hn (f a) ∈ cells16 p := fun a =>
    classOf_mem_cells16 hp2' (f a)
  have hlt : (cells16 p).card < Fintype.card α :=
    lt_of_le_of_lt (cells16_card_le p) hcard
  have hcard2 : Fintype.card (↥(cells16 p)) < Fintype.card α := by
    rw [Fintype.card_coe]
    exact hlt
  obtain ⟨a, b, hab, hg⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun a : α => (⟨FamilyCollision.classOf hn (f a), hmaps a⟩ : ↥(cells16 p))) hcard2
  have hfab : FamilyCollision.classOf hn (f a) = FamilyCollision.classOf hn (f b) :=
    congrArg Subtype.val hg
  exact ⟨a, b, hab, FamilyCollision.sameClass_double hn (f a) (f b) hfab⟩


/-! ## 6. The rank is at most one -/

set_option maxHeartbeats 2000000 in
/-- **THE ALGEBRAIC RANK IS BOUNDED AT EVERY ODD PRIME**: whenever `16 < 3·2^r`,
no `r` points are independent modulo torsion. -/
theorem theAlgebraicRankIsBoundedAtEveryOddPrime (r : ℕ)
    (hp2'' : p ≠ 2) (hr : 16 < 3 * 2 ^ r) :
    ¬ BirchSwinnertonDyer.AlgebraicRankAtLeast p r := by
  have hnp : p.Prime := Fact.out
  have hn : 0 < p := hnp.pos
  intro hR
  unfold BirchSwinnertonDyer.AlgebraicRankAtLeast
    BirchSwinnertonDyer.IndependentModTorsion BirchSwinnertonDyer.IsTorsion at hR
  obtain ⟨Pts, hind⟩ := hR
  have hnq : (0 : ℚ) < ((p : ℕ) : ℚ) := by exact_mod_cast hn
  haveI : AddGroup.FG ((FamilyFace.E (((p : ℕ) : ℚ))).Point) :=
    FamilyMordell.theMordellWeilTheoremAtEveryModulus p hn
  obtain ⟨m, ι, hι, qq, hqq, e, ⟨F⟩⟩ :=
    AddCommGroup.equiv_free_prod_directSum_zmod ((FamilyFace.E (((p : ℕ) : ℚ))).Point)
  haveI := hι
  haveI : ∀ i, NeZero (qq i ^ e i) := fun i => ⟨pow_ne_zero _ (hqq i).pos.ne'⟩
  haveI : Finite (⨁ i, ZMod (qq i ^ e i)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  have htor : ∀ X : (FamilyFace.E (((p : ℕ) : ℚ))).Point, (F X).1 = 0 →
      ∃ k : ℕ, 0 < k ∧ k • X = 0 := by
    intro X hX
    refine ⟨Nat.card (⨁ i, ZMod (qq i ^ e i)), Nat.card_pos, ?_⟩
    apply F.injective
    rw [map_nsmul, map_zero]
    have h2 : (Nat.card (⨁ i, ZMod (qq i ^ e i))) • F X
        = ((Nat.card (⨁ i, ZMod (qq i ^ e i))) • (F X).1,
           (Nat.card (⨁ i, ZMod (qq i ^ e i))) • (F X).2) := rfl
    rw [h2, hX, smul_zero, card_nsmul_eq_zero']
    rfl
  -- the free parts are independent, so the free rank dominates `r`
  set v : Fin r → (Fin m →₀ ℤ) := fun i => (F (Pts i)).1 with hv
  have hindZ : ∀ c : Fin r → ℤ, (∑ i, c i • v i) = 0 → ∀ i, c i = 0 := by
    intro c hczero i
    refine hind c ?_ i
    apply htor
    have hmap : F (∑ i, c i • Pts i) = ∑ i, c i • F (Pts i) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_zsmul]
    have h1 : (F (∑ i, c i • Pts i)).1 = ∑ i, c i • v i := by
      rw [hmap]
      have h2 := map_sum (AddMonoidHom.fst (Fin m →₀ ℤ) (⨁ i, ZMod (qq i ^ e i)))
        (fun i => c i • F (Pts i)) Finset.univ
      calc (∑ i, c i • F (Pts i)).1
          = ∑ i, (c i • F (Pts i)).1 := h2
        _ = ∑ i, c i • v i :=
            Finset.sum_congr rfl fun j _ => by rw [Prod.smul_fst]
    rw [h1, hczero]
  set castHom : (Fin m →₀ ℤ) →+ (Fin m →₀ ℚ) :=
    Finsupp.mapRange.addMonoidHom (Int.castAddHom ℚ) with hcastHom
  have hcastInj : Function.Injective castHom := by
    intro g h hgh
    ext j
    have h1 := DFunLike.congr_fun hgh j
    rw [hcastHom] at h1
    simp only [Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_apply,
      Int.coe_castAddHom] at h1
    exact_mod_cast h1
  set w : Fin r → (Fin m →₀ ℚ) := fun i => castHom (v i) with hw
  have hindW : LinearIndependent ℚ w := by
    rw [← LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)]
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    refine hindZ c ?_ i
    apply hcastInj
    rw [map_sum, map_zero]
    have hterm : ∀ j : Fin r, castHom (c j • v j) = c j • w j := by
      intro j
      rw [map_zsmul, hw]
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    exact hc
  have hrm : r ≤ m := by
    have h1 := hindW.fintype_card_le_finrank
    rw [Module.finrank_finsupp_self] at h1
    simpa using h1
  -- the torsion trio and its free-part vanishing
  have h00 : (FamilyFace.E (((p : ℕ) : ℚ))).Nonsingular 0 0 := by
    rw [nonsingular_iff, equation_iff]
    constructor
    · simp [FamilyFace.E]
    · left
      simp only [FamilyFace.E]
      intro hc
      nlinarith [hc, hnq]
  have hn0 : (FamilyFace.E (((p : ℕ) : ℚ))).Nonsingular (((p : ℕ) : ℚ)) 0 := by
    rw [nonsingular_iff, equation_iff]
    constructor
    · simp only [FamilyFace.E]
      ring
    · left
      simp only [FamilyFace.E]
      intro hc
      nlinarith [hc, hnq]
  set T : Fin 3 → (FamilyFace.E (((p : ℕ) : ℚ))).Point :=
    ![0, Point.some _ _ h00, Point.some _ _ hn0] with hT
  have hT0 : T 0 = 0 := rfl
  have hT1 : T 1 = Point.some _ _ h00 := rfl
  have hT2 : T 2 = Point.some _ _ hn0 := rfl
  have htrio2 : ∀ b : Fin 3, T b + T b = 0 := by
    intro b
    rcases FamilyRankFin3.fin3_cases b with rfl | rfl | rfl
    · rw [hT0, add_zero]
    · rw [hT1]
      exact Point.add_self_of_Y_eq (by simp [negY, FamilyFace.E])
    · rw [hT2]
      exact Point.add_self_of_Y_eq (by simp [negY, FamilyFace.E])
  have hfree : ∀ b : Fin 3, (F (T b)).1 = 0 := by
    intro b
    have h2 : F (T b) + F (T b) = 0 := by
      rw [← map_add, htrio2 b, map_zero]
    have h3 : (F (T b)).1 + (F (T b)).1 = 0 := by
      have h4 := congrArg Prod.fst h2
      simpa using h4
    ext j
    have h5 := DFunLike.congr_fun h3 j
    simp only [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply] at h5 ⊢
    omega
  set tt : Fin 3 → (⨁ i, ZMod (qq i ^ e i)) := fun b => (F (T b)).2 with htt
  have hFT : ∀ b : Fin 3, F (T b) = (0, tt b) := fun b =>
    Prod.ext_iff.mpr ⟨hfree b, rfl⟩
  -- the sign-vector free parts
  set wv : (Fin r → Bool) → (Fin m →₀ ℤ) := fun ε =>
    ∑ i : Fin r, if ε i then Finsupp.single (Fin.castLE hrm i) (1 : ℤ) else 0
    with hwv
  have hwv_apply : ∀ (ε : Fin r → Bool) (i : Fin r),
      wv ε (Fin.castLE hrm i) = if ε i then 1 else 0 := by
    intro ε i
    rw [hwv]
    simp only
    rw [Finsupp.finset_sum_apply]
    rw [Finset.sum_eq_single i]
    · by_cases hb : ε i
      · rw [if_pos hb, if_pos hb, Finsupp.single_eq_same]
      · rw [if_neg hb, if_neg hb, Finsupp.coe_zero, Pi.zero_apply]
    · intro j _ hji
      by_cases hb : ε j
      · rw [if_pos hb]
        exact Finsupp.single_eq_of_ne
          (fun hc => hji (Fin.castLE_injective hrm hc).symm)
      · rw [if_neg hb, Finsupp.coe_zero, Pi.zero_apply]
    · intro habs
      exact absurd (Finset.mem_univ i) habs
  -- the colliding family of `3·2^r` points
  obtain ⟨x, x', hnexx, Q, hQ⟩ :=
    theClassesCollideAtEveryOddPrime hp2''
      (α := (Fin r → Bool) × Fin 3)
      (by
        simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
          Fintype.card_bool]
        omega)
      (fun ab => F.symm (wv ab.1, tt ab.2))
  obtain ⟨ε, b⟩ := x
  obtain ⟨δ, b'⟩ := x'
  dsimp only at hQ
  have himg : ((wv ε, tt b) : (Fin m →₀ ℤ) × (⨁ i, ZMod (qq i ^ e i)))
      - (wv δ, tt b') = F Q + F Q := by
    have h1 := congrArg F hQ
    rwa [map_sub, map_add, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at h1
  have hfst : wv ε - wv δ = (F Q).1 + (F Q).1 := by
    have h2 := congrArg Prod.fst himg
    simpa using h2
  by_cases hεδ : ε = δ
  · -- same signs: the torsion trio collides — refused
    subst hεδ
    have hbb : b ≠ b' := by
      intro h
      exact hnexx (by rw [h])
    have hFb : F (T b) = (0, tt b) := hFT b
    have hFb' : F (T b') = (0, tt b') := hFT b'
    have htdiff : T b - T b' = F.symm (0, (F Q).2) + F.symm (0, (F Q).2) := by
      have hsnd : tt b - tt b' = (F Q).2 + (F Q).2 := by
        have h2 := congrArg Prod.snd himg
        simpa using h2
      apply F.injective
      rw [map_sub, map_add, AddEquiv.apply_symm_apply, hFb, hFb',
        Prod.mk_sub_mk, Prod.mk_add_mk]
      exact Prod.ext_iff.mpr ⟨by simp, hsnd⟩
    exact FamilyCollision.theTorsionTrioDoesNotCollideAtEveryModulus hn T hT0 hT1
      hT2 b b' hbb (F.symm (0, (F Q).2)) htdiff
  · -- different signs: parity at the first differing coordinate refuses the double
    have hex : ∃ i : Fin r, ε i ≠ δ i := by
      by_contra hall
      push_neg at hall
      exact hεδ (funext hall)
    obtain ⟨i₀, hi₀⟩ := hex
    have hev := DFunLike.congr_fun hfst (Fin.castLE hrm i₀)
    rw [Finsupp.sub_apply, Finsupp.add_apply, hwv_apply, hwv_apply] at hev
    rcases Bool.eq_false_or_eq_true (ε i₀) with hε | hε <;>
      rcases Bool.eq_false_or_eq_true (δ i₀) with hδ | hδ
    · exact hi₀ (hε.trans hδ.symm)
    · rw [hε, hδ] at hev
      simp only [Bool.false_eq_true, if_false, if_pos] at hev
      omega
    · rw [hε, hδ] at hev
      simp only [Bool.false_eq_true, if_false, if_pos] at hev
      omega
    · exact hi₀ (hε.trans hδ.symm)

/-- **THE RANK IS AT MOST TWO AT EVERY ODD PRIME**: no three points of
`y² = x³ − p²x` are independent modulo torsion — the sixteen-cell collapse forces
`3·2^r ≤ 16`, so `r ≤ 2`, the generic two-descent bound, uniformly. -/
theorem theRankIsAtMostTwoAtEveryOddPrime (hp2'' : p ≠ 2) :
    ¬ BirchSwinnertonDyer.AlgebraicRankAtLeast p 3 :=
  theAlgebraicRankIsBoundedAtEveryOddPrime 3 hp2'' (by norm_num)



end Soma.Holonics.Millennium.FamilyOddDescent

