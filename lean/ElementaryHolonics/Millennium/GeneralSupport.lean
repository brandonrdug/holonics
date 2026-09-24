import ElementaryHolonics.Millennium.GeneralHom
import ElementaryHolonics.Millennium.FamilyGenocchi

/-!
# GeneralSupport: the slot classes are supported on the discriminant, on every
full-2-torsion curve

For an integral model `y² = x(x−a)(x−b)` the two descent slots of any rational point
carry square classes supported on the divisors of `|a·b·(a−b)|` — the primes of bad
reduction and no others.  The argument is uniform in the prime, `2` included:

* off `a`, `b` and `a−b`, **at most one** of `v(x)`, `v(x−a)`, `v(x−b)` is positive,
  since two would force the prime into a difference; the others vanish, and the sum is
  `2v(y)`, so every one of them is even;
* a negative `v(x)` forces all three equal, and `3v(x) = 2v(y)` makes it even.

* **`classFromEvenValuations`** — even valuations off a modulus give a class dividing
  that modulus (the family lemma, freed of the family).
* **`theSlotValuationsAreEvenOffTheDiscriminant`** — the valuation law above.
* **`theSlotClassesAreSupportedOnEveryFullTwoTorsionCurve`** — the support theorem.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.GeneralSupport

open WeierstrassCurve.Affine
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.GeneralFace

/-! ## 1. From even valuations to a supported class -/

private lemma sqcls_trans {u v w : ℚ} (h₁ : Descent.SqCls u v) (h₂ : Descent.SqCls v w) :
    Descent.SqCls u w := by
  obtain ⟨c, hc, hv⟩ := h₁
  obtain ⟨d, hd, hw⟩ := h₂
  exact ⟨c * d, mul_ne_zero hc hd, by rw [hv, hw]; ring⟩


lemma classFromEvenValuations {K : ℕ} (hK : K ≠ 0) {x : ℚ} (hx : x ≠ 0)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ K → Even (padicValRat ℓ x)) :
    ∃ d : ℤ, d ≠ 0 ∧ d.natAbs ∣ K ∧ Descent.SqCls x (d : ℚ) := by
  have h2n0 : K ≠ 0 := hK
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
  have hmv : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ K →
      Even ((x.num * (x.den : ℤ)).natAbs.factorization ℓ) := by
    intro ℓ hℓ hnd
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    have hval := h ℓ hℓ hnd
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
  obtain ⟨sfA, sfB, hab, hsq⟩ := Nat.sq_mul_squarefree (x.num * (x.den : ℤ)).natAbs
  have hn0' : (x.num * (x.den : ℤ)).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hm0
  have ha0 : sfA ≠ 0 := by
    intro hc
    rw [hc, mul_zero] at hab
    exact hn0' hab.symm
  have hb0 : sfB ≠ 0 := by
    intro hc
    rw [hc] at hab
    simp at hab
    exact hn0' hab.symm
  -- the squarefree part divides `2n`
  have hadvd : sfA ∣ K := by
    rw [← Nat.factorization_le_iff_dvd ha0 h2n0, Finsupp.le_def]
    intro ℓ
    by_cases hℓp : ℓ.Prime
    · by_cases hdvd : ℓ ∣ sfA
      · have hle1 : sfA.factorization ℓ ≤ 1 :=
          (Nat.squarefree_iff_factorization_le_one ha0).mp hsq ℓ
        by_cases hnd : ℓ ∣ K
        · have hpos : 0 < (K).factorization ℓ :=
            Nat.Prime.factorization_pos_of_dvd hℓp h2n0 hnd
          omega
        · exfalso
          have heven := hmv ℓ hℓp hnd
          rw [← hab, Nat.factorization_mul (pow_ne_zero 2 hb0) ha0,
            Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply,
            smul_eq_mul] at heven
          have hpos : 0 < sfA.factorization ℓ :=
            Nat.Prime.factorization_pos_of_dvd hℓp ha0 hdvd
          obtain ⟨k, hk⟩ := heven
          omega
      · rw [Nat.factorization_eq_zero_of_not_dvd hdvd]
        omega
    · rw [Nat.factorization_eq_zero_of_not_prime _ hℓp]
      omega
  -- assemble the signed class
  rcases lt_trichotomy (x.num * (x.den : ℤ)) 0 with hs | hs | hs
  · refine ⟨-(sfA : ℤ), by simpa using ha0, by simpa using hadvd, ?_⟩
    have habs : x.num * (x.den : ℤ) = -((sfB : ℤ) ^ 2 * (sfA : ℤ)) := by
      have h1 : (((x.num * (x.den : ℤ)).natAbs : ℤ)) = -(x.num * (x.den : ℤ)) :=
        Int.ofNat_natAbs_of_nonpos hs.le
      have h2 : ((sfB : ℤ)) ^ 2 * (sfA : ℤ) = (((x.num * (x.den : ℤ)).natAbs : ℤ)) := by
        exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) hab
      linarith [h1, h2]
    have hstep : Descent.SqCls (((x.num * (x.den : ℤ) : ℤ) : ℚ)) ((-(sfA : ℤ) : ℤ) : ℚ) := by
      refine ⟨(sfB : ℚ), by exact_mod_cast hb0, ?_⟩
      rw [show ((x.num * (x.den : ℤ) : ℤ) : ℚ) = ((-((sfB : ℤ) ^ 2 * (sfA : ℤ)) : ℤ) : ℚ) from
        by exact_mod_cast congrArg (fun m : ℤ => (m : ℚ)) habs]
      push_cast
      ring
    exact sqcls_trans hcls hstep
  · exact absurd hs hm0
  · refine ⟨(sfA : ℤ), by exact_mod_cast ha0, by simpa using hadvd, ?_⟩
    have habs : x.num * (x.den : ℤ) = (sfB : ℤ) ^ 2 * (sfA : ℤ) := by
      have h1 : (((x.num * (x.den : ℤ)).natAbs : ℤ)) = x.num * (x.den : ℤ) :=
        Int.natAbs_of_nonneg hs.le
      have h2 : ((sfB : ℤ)) ^ 2 * (sfA : ℤ) = (((x.num * (x.den : ℤ)).natAbs : ℤ)) := by
        exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) hab
      linarith [h1, h2]
    have hstep : Descent.SqCls (((x.num * (x.den : ℤ) : ℤ) : ℚ)) (((sfA : ℤ) : ℤ) : ℚ) := by
      refine ⟨(sfB : ℚ), by exact_mod_cast hb0, ?_⟩
      rw [show ((x.num * (x.den : ℤ) : ℤ) : ℚ) = (((sfB : ℤ) ^ 2 * (sfA : ℤ) : ℤ) : ℚ) from
        by exact_mod_cast congrArg (fun m : ℤ => (m : ℚ)) habs]
      push_cast
      ring
    exact sqcls_trans hcls hstep



/-! ## 2. The valuation law off the discriminant -/

variable {a b : ℤ}

/-- **THE SLOT VALUATIONS ARE EVEN OFF THE DISCRIMINANT**: at every prime missing
`a·b·(a−b)`, all three slot valuations of a point with nonzero ordinate are even.
Two positive valuations would force the prime into a difference of roots, so at most
one is positive; the sum is `2v(y)`; a negative one makes all three equal. -/
theorem theSlotValuationsAreEvenOffTheDiscriminant {ℓ : ℕ} [Fact ℓ.Prime]
    (hnd : ¬ (ℓ : ℤ) ∣ a * b * (a - b)) {x y : ℚ}
    (hcurve : y ^ 2 = x * (x - (a : ℚ)) * (x - (b : ℚ))) (hy : y ≠ 0)
    (hx0 : x ≠ 0) (hxa : x - (a : ℚ) ≠ 0) (hxb : x - (b : ℚ) ≠ 0) :
    Even (padicValRat ℓ x) ∧ Even (padicValRat ℓ (x - (a : ℚ))) := by
  have hℓ : ℓ.Prime := Fact.out
  -- the three roots are units at `ℓ`
  have hda : ¬ (ℓ : ℤ) ∣ a := fun hc => hnd (Dvd.dvd.mul_right (Dvd.dvd.mul_right hc b) _)
  have hdb : ¬ (ℓ : ℤ) ∣ b := fun hc => hnd (Dvd.dvd.mul_right (Dvd.dvd.mul_left hc a) _)
  have hdab : ¬ (ℓ : ℤ) ∣ (a - b) := fun hc => hnd (Dvd.dvd.mul_left hc _)
  have hva : padicValRat ℓ ((a : ℚ)) = 0 := by
    have := Soma.Holonics.Millennium.FamilyGenocchi.int_val_zero (p := ℓ) hda
    push_cast at this ⊢
    exact this
  have hvb : padicValRat ℓ ((b : ℚ)) = 0 := by
    have := Soma.Holonics.Millennium.FamilyGenocchi.int_val_zero (p := ℓ) hdb
    push_cast at this ⊢
    exact this
  have hvab : padicValRat ℓ (((a : ℚ)) - ((b : ℚ))) = 0 := by
    have := Soma.Holonics.Millennium.FamilyGenocchi.int_val_zero (p := ℓ) hdab
    push_cast at this ⊢
    exact this
  have haq : ((a : ℚ)) ≠ 0 := by
    intro hc
    exact hda (by exact_mod_cast (by exact_mod_cast hc : (a : ℤ) = 0) ▸ dvd_zero _)
  have hbq : ((b : ℚ)) ≠ 0 := by
    intro hc
    exact hdb (by exact_mod_cast (by exact_mod_cast hc : (b : ℤ) = 0) ▸ dvd_zero _)
  -- the valuation ledger
  have hsum : padicValRat ℓ x + padicValRat ℓ (x - (a : ℚ)) + padicValRat ℓ (x - (b : ℚ))
      = 2 * padicValRat ℓ y := by
    have h1 : padicValRat ℓ (y ^ 2) = 2 * padicValRat ℓ y := by
      rw [pow_two, padicValRat.mul hy hy]
      ring
    rw [← h1, hcurve, padicValRat.mul (mul_ne_zero hx0 hxa) hxb,
      padicValRat.mul hx0 hxa]
  set V := padicValRat ℓ x with hV
  set Va := padicValRat ℓ (x - (a : ℚ)) with hVa
  set Vb := padicValRat ℓ (x - (b : ℚ)) with hVb
  by_cases hneg : V < 0
  · -- below zero the three agree
    have h1 : Va = V := by
      have he : x - (a : ℚ) = x + (-(a : ℚ)) := by ring
      rw [hVa, he]
      refine Soma.Holonics.Millennium.FamilySupport.val_add_left hx0 (by rw [← he]; exact hxa) ?_
      rw [padicValRat.neg, hva]
      omega
    have h2 : Vb = V := by
      have he : x - (b : ℚ) = x + (-(b : ℚ)) := by ring
      rw [hVb, he]
      refine Soma.Holonics.Millennium.FamilySupport.val_add_left hx0 (by rw [← he]; exact hxb) ?_
      rw [padicValRat.neg, hvb]
      omega
    rw [h1, h2] at hsum
    refine ⟨⟨padicValRat ℓ y - V, by omega⟩, ?_⟩
    rw [h1]
    exact ⟨padicValRat ℓ y - V, by omega⟩
  · push_neg at hneg
    -- at or above zero, two positives would put the prime in a difference
    have hVa0 : 0 ≤ Va := by
      by_contra hc
      push_neg at hc
      have he : x = (x - (a : ℚ)) + (a : ℚ) := by ring
      have := Soma.Holonics.Millennium.FamilySupport.val_add_left (ℓ := ℓ) hxa (by rw [← he]; exact hx0)
        (by rw [hva]; omega)
      rw [← he] at this
      omega
    have hVb0 : 0 ≤ Vb := by
      by_contra hc
      push_neg at hc
      have he : x = (x - (b : ℚ)) + (b : ℚ) := by ring
      have := Soma.Holonics.Millennium.FamilySupport.val_add_left (ℓ := ℓ) hxb (by rw [← he]; exact hx0)
        (by rw [hvb]; omega)
      rw [← he] at this
      omega
    have hpair : ∀ {u v : ℚ}, u - v ≠ 0 → 0 < padicValRat ℓ u →
        0 < padicValRat ℓ v → padicValRat ℓ (u - v) > 0 := by
      intro u v huv h1 h2
      have hmin := padicValRat.min_le_padicValRat_add (p := ℓ) (q := u) (r := -v)
        (by rw [← sub_eq_add_neg]; exact huv)
      rw [padicValRat.neg, ← sub_eq_add_neg] at hmin
      omega
    have hnot12 : ¬ (0 < V ∧ 0 < Va) := by
      rintro ⟨h1, h2⟩
      have he : x - (x - (a : ℚ)) = (a : ℚ) := by ring
      have := hpair (by rw [he]; exact haq) h1 h2
      rw [he, hva] at this
      omega
    have hnot13 : ¬ (0 < V ∧ 0 < Vb) := by
      rintro ⟨h1, h2⟩
      have he : x - (x - (b : ℚ)) = (b : ℚ) := by ring
      have := hpair (by rw [he]; exact hbq) h1 h2
      rw [he, hvb] at this
      omega
    have hnot23 : ¬ (0 < Va ∧ 0 < Vb) := by
      rintro ⟨h1, h2⟩
      have he : (x - (a : ℚ)) - (x - (b : ℚ)) = ((b : ℚ)) - ((a : ℚ)) := by ring
      have hbane : ((b : ℚ)) - ((a : ℚ)) ≠ 0 := by
        intro hc
        refine hdab ?_
        have : ((a : ℚ)) = ((b : ℚ)) := by linarith
        have hz : (a : ℤ) = b := by exact_mod_cast this
        rw [hz]
        simp
      have := hpair (by rw [he]; exact hbane) h1 h2
      rw [he] at this
      have hneg' : padicValRat ℓ (((b : ℚ)) - ((a : ℚ)))
          = padicValRat ℓ (((a : ℚ)) - ((b : ℚ))) := by
        rw [show ((b : ℚ)) - ((a : ℚ)) = -(((a : ℚ)) - ((b : ℚ))) from by ring,
          padicValRat.neg]
      rw [hneg', hvab] at this
      omega
    -- at most one is positive, so each is even
    rcases Nat.lt_or_ge 0 1 with _ | _ <;>
    · by_cases h1 : 0 < V
      · have h2 : Va = 0 := by omega
        have h3 : Vb = 0 := by omega
        rw [h2, h3] at hsum
        exact ⟨⟨padicValRat ℓ y, by omega⟩, by rw [h2]; exact ⟨0, by ring⟩⟩
      · have hV0 : V = 0 := by omega
        by_cases h2 : 0 < Va
        · have h3 : Vb = 0 := by omega
          rw [hV0, h3] at hsum
          exact ⟨by rw [hV0]; exact ⟨0, by ring⟩, ⟨padicValRat ℓ y, by omega⟩⟩
        · exact ⟨by rw [hV0]; exact ⟨0, by ring⟩,
            by have : Va = 0 := by omega
               rw [this]; exact ⟨0, by ring⟩⟩


/-! ## 3. The support theorem -/

/-- **THE SLOT CLASSES ARE SUPPORTED ON THE DISCRIMINANT, ON EVERY FULL-TWO-TORSION
CURVE**: for an integral model `y² = x(x−a)(x−b)`, both descent slots of every
rational point carry a class dividing `|a·b·(a−b)|`.  The torsion points carry the
convention values, which divide it by construction. -/
theorem theSlotClassesAreSupportedOnEveryFullTwoTorsionCurve
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0)
    (P : (E ((a : ℚ)) ((b : ℚ))).Point) :
    ∃ d₁ d₂ : ℤ, d₁ ≠ 0 ∧ d₂ ≠ 0 ∧
      d₁.natAbs ∣ (a * b * (a - b)).natAbs ∧ d₂.natAbs ∣ (a * b * (a - b)).natAbs ∧
      Descent.SqCls (slotOne ((a : ℚ)) ((b : ℚ)) P) (d₁ : ℚ) ∧
      Descent.SqCls (slotTwo ((a : ℚ)) ((b : ℚ)) P) (d₂ : ℚ) := by
  set K : ℕ := (a * b * (a - b)).natAbs with hK
  have hK0 : K ≠ 0 := by
    rw [hK, Int.natAbs_ne_zero]
    exact mul_ne_zero (mul_ne_zero ha hb) hab
  have haq : ((a : ℚ)) ≠ 0 := by exact_mod_cast ha
  have hbq : ((b : ℚ)) ≠ 0 := by exact_mod_cast hb
  have habq : ((a : ℚ)) - ((b : ℚ)) ≠ 0 := by
    intro hc
    refine hab ?_
    have : ((a : ℚ)) = ((b : ℚ)) := by linarith
    have hz : (a : ℤ) = b := by exact_mod_cast this
    omega
  -- the divisibilities of the convention values
  have hdA : a.natAbs ∣ K := by
    rw [hK]
    exact Int.natAbs_dvd_natAbs.mpr ⟨b * (a - b), by ring⟩
  have hdB : b.natAbs ∣ K := by
    rw [hK]
    exact Int.natAbs_dvd_natAbs.mpr ⟨a * (a - b), by ring⟩
  have hdAB : (a - b).natAbs ∣ K := by
    rw [hK]
    exact Int.natAbs_dvd_natAbs.mpr ⟨a * b, by ring⟩
  have hdAmulB : (a * b).natAbs ∣ K := by
    rw [hK]
    exact Int.natAbs_dvd_natAbs.mpr ⟨a - b, by ring⟩
  have hdAmulAB : (a * (a - b)).natAbs ∣ K := by
    rw [hK]
    exact Int.natAbs_dvd_natAbs.mpr ⟨b, by ring⟩
  have hdBmulBA : (b - a).natAbs ∣ K := by
    have : (b - a).natAbs = (a - b).natAbs := by
      rw [show b - a = -(a - b) from by ring, Int.natAbs_neg]
    rw [this]
    exact hdAB
  rcases P with _ | @⟨x, y, h⟩
  · exact ⟨1, 1, one_ne_zero, one_ne_zero, by simpa using one_dvd K, by simpa using one_dvd K,
      Descent.sqClsRefl _, Descent.sqClsRefl _⟩
  · by_cases hy : y = 0
    · -- the three two-torsion points, with their convention classes
      have hcurve := onCurve h
      rw [hy] at hcurve
      have hroots : x * (x - (a : ℚ)) * (x - (b : ℚ)) = 0 := by linear_combination -hcurve
      have hx3 : x = 0 ∨ x = (a : ℚ) ∨ x = (b : ℚ) := by
        rcases mul_eq_zero.mp hroots with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl (by linarith [sub_eq_zero.mp h'']))
        · exact Or.inr (Or.inr (by linarith [sub_eq_zero.mp h']))
      rcases hx3 with h' | h' | h'
      · refine ⟨a * b, -a, mul_ne_zero ha hb, neg_ne_zero.mpr ha, hdAmulB,
          by rw [Int.natAbs_neg]; exact hdA, ?_, ?_⟩
        · rw [slotOne_some, if_pos h']
          exact ⟨1, one_ne_zero, by push_cast; ring⟩
        · rw [slotTwo_some, if_neg (by rw [h']; exact fun hc => haq hc.symm), h']
          exact ⟨1, one_ne_zero, by push_cast; ring⟩
      · refine ⟨a, a * (a - b), ha, mul_ne_zero ha hab, hdA, hdAmulAB, ?_, ?_⟩
        · rw [slotOne_some, if_neg (by rw [h']; exact haq), h']
          exact ⟨1, one_ne_zero, by push_cast; ring⟩
        · rw [slotTwo_some, if_pos h']
          exact ⟨1, one_ne_zero, by push_cast; ring⟩
      · have hxa' : x ≠ (a : ℚ) := by
          rw [h']
          intro hc
          exact habq (by linarith)
        refine ⟨b, b - a, hb, sub_ne_zero.mpr (fun hc => hab (by omega)), hdB, hdBmulBA,
          ?_, ?_⟩
        · rw [slotOne_some, if_neg (by rw [h']; exact hbq), h']
          exact ⟨1, one_ne_zero, by push_cast; ring⟩
        · rw [slotTwo_some, if_neg hxa', h']
          exact ⟨1, one_ne_zero, by push_cast; ring⟩
    · -- the general point
      have hcurve := onCurve h
      have hx0 : x ≠ 0 := by
        intro hc
        refine hy ?_
        rw [hc] at hcurve
        have : y ^ 2 = 0 := by rw [hcurve]; ring
        exact pow_eq_zero_iff two_ne_zero |>.mp this
      have hxa : x - (a : ℚ) ≠ 0 := by
        intro hc
        refine hy ?_
        rw [hc, mul_zero, zero_mul] at hcurve
        exact pow_eq_zero_iff two_ne_zero |>.mp hcurve
      have hxb : x - (b : ℚ) ≠ 0 := by
        intro hc
        refine hy ?_
        rw [hc, mul_zero] at hcurve
        exact pow_eq_zero_iff two_ne_zero |>.mp hcurve
      have hbridge : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ K → ¬ (ℓ : ℤ) ∣ a * b * (a - b) := by
        intro ℓ _ hnd hc
        refine hnd ?_
        rw [hK]
        have := Int.natAbs_dvd_natAbs.mpr hc
        simpa using this
      have hmain : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ K →
          Even (padicValRat ℓ x) ∧ Even (padicValRat ℓ (x - (a : ℚ))) := by
        intro ℓ hℓ hnd
        haveI : Fact ℓ.Prime := ⟨hℓ⟩
        exact theSlotValuationsAreEvenOffTheDiscriminant (hbridge ℓ hℓ hnd)
          hcurve hy hx0 hxa hxb
      obtain ⟨d₁, hd₁0, hd₁v, hcls₁⟩ :=
        classFromEvenValuations hK0 hx0 fun ℓ hℓ hnd => (hmain ℓ hℓ hnd).1
      obtain ⟨d₂, hd₂0, hd₂v, hcls₂⟩ :=
        classFromEvenValuations hK0 hxa fun ℓ hℓ hnd => (hmain ℓ hℓ hnd).2
      refine ⟨d₁, d₂, hd₁0, hd₂0, hd₁v, hd₂v, ?_, ?_⟩
      · rw [slotOne_some, if_neg hx0]
        exact hcls₁
      · rw [slotTwo_some, if_neg (fun hc => hxa (by rw [hc]; ring))]
        exact hcls₂

end Soma.Holonics.Millennium.GeneralSupport
