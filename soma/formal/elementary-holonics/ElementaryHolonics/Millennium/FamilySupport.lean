import ElementaryHolonics.Millennium.FamilyKernel
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-!
# FamilySupport: the slot classes are supported on the discriminant at every modulus

**The per-twist finiteness law.**  On every congruent-number curve `y² = x³ − n²x`
with `n ≥ 1`, both descent slots of every rational point lie in the square class of
an integer whose absolute value divides `2n`:

* **`theSlotClassesAreSupportedAtEveryModulus`** — for every point `P`, there are
  `d₁, d₂ : ℤ`, nonzero, with `|dᵢ| ∣ 2n`, and `slot_i(P) ~ dᵢ`.

The mechanism: off the primes of `2n` the curve equation forces both slot valuations
even (the three root-differences `n, −n, 2n` are units there), so the squarefree part
of each slot divides `2n`.  The face image is therefore contained in a **finite** set
of square-class pairs computable from the modulus alone — the finiteness that powers
the family Mordell–Weil descent.  Every `theorem` is discharged and none depends on
`sorryAx`.
-/

namespace Soma.Holonics.Millennium.FamilySupport

open WeierstrassCurve.Affine
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.FamilyKernel

/-! ## 1. Valuation plumbing -/

private lemma sqcls_trans {a b c : ℚ} (h₁ : Descent.SqCls a b) (h₂ : Descent.SqCls b c) :
    Descent.SqCls a c := by
  obtain ⟨k, hk, hkv⟩ := h₁
  obtain ⟨m, hm, hmv⟩ := h₂
  exact ⟨k * m, mul_ne_zero hk hm, by rw [hkv, hmv]; ring⟩

private lemma val_add_left {ℓ : ℕ} [Fact ℓ.Prime] {a b : ℚ} (ha : a ≠ 0)
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

private lemma val_const_zero {n ℓ : ℕ} [hf : Fact ℓ.Prime] (hn : 0 < n)
    (hnd : ¬ ℓ ∣ 2 * n) :
    padicValRat ℓ ((n : ℚ)) = 0 ∧ padicValRat ℓ (-(n : ℚ)) = 0 ∧
    padicValRat ℓ ((2 * n : ℕ) : ℚ) = 0 := by
  have key : ∀ m : ℤ, ¬ (ℓ : ℤ) ∣ m → padicValRat ℓ (m : ℚ) = 0 := by
    intro m hdvd
    rw [padicValRat.of_int, padicValInt.eq_zero_iff.mpr (Or.inr (Or.inr hdvd))]
    simp
  have hdn : ¬ (ℓ : ℤ) ∣ (n : ℤ) := by
    intro hc
    exact hnd (Dvd.dvd.mul_left (by exact_mod_cast hc) 2)
  have hd2n : ¬ (ℓ : ℤ) ∣ ((2 * n : ℕ) : ℤ) := by
    intro hc
    exact hnd (by exact_mod_cast hc)
  refine ⟨?_, ?_, ?_⟩
  · simpa using key (n : ℤ) hdn
  · have h1 := key (-(n : ℤ)) (by rwa [Int.dvd_neg])
    push_cast at h1 ⊢
    exact h1
  · simpa using key ((2 * n : ℕ) : ℤ) hd2n

/-- Off the primes of `2n`, both slot valuations are even. -/
private lemma even_slot_val {n ℓ : ℕ} [Fact ℓ.Prime] (hn : 0 < n)
    (hnd : ¬ ℓ ∣ 2 * n) {x y : ℚ}
    (hcurve : y ^ 2 = x ^ 3 - ((n : ℚ)) ^ 2 * x) (hy : y ≠ 0) :
    Even (padicValRat ℓ x) ∧ Even (padicValRat ℓ (x - (n : ℚ))) := by
  obtain ⟨hx0, hxn, hxmn⟩ :=
    FaceHomomorphism.theNonzeroOrdinateAvoidsTheRoots hcurve hy
  have hxm : x - (n : ℚ) ≠ 0 := sub_ne_zero.mpr hxn
  have hxp : x + (n : ℚ) ≠ 0 := fun hc => hxmn (by linarith)
  have hnq : ((n : ℚ)) ≠ 0 := by exact_mod_cast hn.ne'
  have h2nq : ((2 * n : ℕ) : ℚ) ≠ 0 := by
    push_cast
    positivity
  have hfact : y ^ 2 = x * (x - (n : ℚ)) * (x + (n : ℚ)) := by
    linear_combination hcurve
  have hprod : 2 * padicValRat ℓ y =
      padicValRat ℓ x + padicValRat ℓ (x - (n : ℚ)) + padicValRat ℓ (x + (n : ℚ)) := by
    have hmul1 : padicValRat ℓ (x * (x - (n : ℚ)) * (x + (n : ℚ))) =
        padicValRat ℓ x + padicValRat ℓ (x - (n : ℚ)) + padicValRat ℓ (x + (n : ℚ)) := by
      rw [padicValRat.mul (mul_ne_zero hx0 hxm) hxp, padicValRat.mul hx0 hxm]
    have hpow : padicValRat ℓ (y ^ 2) = 2 * padicValRat ℓ y := by
      rw [pow_two, padicValRat.mul hy hy]
      ring
    rw [← hpow, hfact, hmul1]
  obtain ⟨vn, vmn, v2n⟩ := val_const_zero (n := n) (ℓ := ℓ) hn hnd
  constructor
  · rcases lt_trichotomy (padicValRat ℓ x) 0 with hv | hv | hv
    · have e1 : padicValRat ℓ (x - (n : ℚ)) = padicValRat ℓ x := by
        have := val_add_left (ℓ := ℓ) hx0
          (by rw [show x + -(n : ℚ) = x - (n : ℚ) by ring]; exact hxm)
          (by rw [vmn]; exact hv)
        rw [show x + -(n : ℚ) = x - (n : ℚ) by ring] at this
        exact this
      have e2 : padicValRat ℓ (x + (n : ℚ)) = padicValRat ℓ x := by
        exact val_add_left (ℓ := ℓ) hx0 hxp (by rw [vn]; exact hv)
      rw [e1, e2] at hprod
      refine ⟨padicValRat ℓ y - padicValRat ℓ x, by linarith⟩
    · exact ⟨0, by rw [hv]; ring⟩
    · have e1 : padicValRat ℓ (x - (n : ℚ)) = 0 := by
        have := val_add_left (ℓ := ℓ) (neg_ne_zero.mpr hnq)
          (by rw [show -(n : ℚ) + x = x - (n : ℚ) by ring]; exact hxm)
          (by rw [vmn]; exact hv)
        rw [show -(n : ℚ) + x = x - (n : ℚ) by ring, vmn] at this
        exact this
      have e2 : padicValRat ℓ (x + (n : ℚ)) = 0 := by
        have := val_add_left (ℓ := ℓ) hnq
          (by rw [show (n : ℚ) + x = x + (n : ℚ) by ring]; exact hxp)
          (by rw [vn]; exact hv)
        rw [show (n : ℚ) + x = x + (n : ℚ) by ring, vn] at this
        exact this
      rw [e1, e2] at hprod
      exact ⟨padicValRat ℓ y, by linarith⟩
  · rcases lt_trichotomy (padicValRat ℓ (x - (n : ℚ))) 0 with hv | hv | hv
    · have e1 : padicValRat ℓ x = padicValRat ℓ (x - (n : ℚ)) := by
        have := val_add_left (ℓ := ℓ) hxm
          (by rw [show x - (n : ℚ) + (n : ℚ) = x by ring]; exact hx0)
          (by rw [vn]; exact hv)
        rw [show x - (n : ℚ) + (n : ℚ) = x by ring] at this
        exact this
      have e2 : padicValRat ℓ (x + (n : ℚ)) = padicValRat ℓ (x - (n : ℚ)) := by
        have := val_add_left (ℓ := ℓ) hxm
          (by rw [show x - (n : ℚ) + ((2 * n : ℕ) : ℚ) = x + (n : ℚ) by
              push_cast; ring]; exact hxp)
          (by rw [v2n]; exact hv)
        rw [show x - (n : ℚ) + ((2 * n : ℕ) : ℚ) = x + (n : ℚ) by
          push_cast; ring] at this
        exact this
      rw [e1, e2] at hprod
      refine ⟨padicValRat ℓ y - padicValRat ℓ (x - (n : ℚ)), by linarith⟩
    · exact ⟨0, by rw [hv]; ring⟩
    · have e1 : padicValRat ℓ x = 0 := by
        have := val_add_left (ℓ := ℓ) hnq
          (by rw [show (n : ℚ) + (x - (n : ℚ)) = x by ring]; exact hx0)
          (by rw [vn]; exact hv)
        rw [show (n : ℚ) + (x - (n : ℚ)) = x by ring, vn] at this
        exact this
      have e2 : padicValRat ℓ (x + (n : ℚ)) = 0 := by
        have := val_add_left (ℓ := ℓ) h2nq
          (by rw [show ((2 * n : ℕ) : ℚ) + (x - (n : ℚ)) = x + (n : ℚ) by
              push_cast; ring]; exact hxp)
          (by rw [v2n]; exact hv)
        rw [show ((2 * n : ℕ) : ℚ) + (x - (n : ℚ)) = x + (n : ℚ) by
          push_cast; ring, v2n] at this
        exact this
      rw [e1, e2] at hprod
      exact ⟨padicValRat ℓ y, by linarith⟩

/-! ## 2. From even valuations to a supported class -/

private lemma classFromEvenValuations {n : ℕ} (hn : 0 < n) {x : ℚ} (hx : x ≠ 0)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ 2 * n → Even (padicValRat ℓ x)) :
    ∃ d : ℤ, d ≠ 0 ∧ d.natAbs ∣ 2 * n ∧ Descent.SqCls x (d : ℚ) := by
  have h2n0 : 2 * n ≠ 0 := by omega
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
  have hmv : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ 2 * n →
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
  obtain ⟨a, b, hab, hsq⟩ := Nat.sq_mul_squarefree (x.num * (x.den : ℤ)).natAbs
  have hn0' : (x.num * (x.den : ℤ)).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hm0
  have ha0 : a ≠ 0 := by
    intro hc
    rw [hc, mul_zero] at hab
    exact hn0' hab.symm
  have hb0 : b ≠ 0 := by
    intro hc
    rw [hc] at hab
    simp at hab
    exact hn0' hab.symm
  -- the squarefree part divides `2n`
  have hadvd : a ∣ 2 * n := by
    rw [← Nat.factorization_le_iff_dvd ha0 h2n0, Finsupp.le_def]
    intro ℓ
    by_cases hℓp : ℓ.Prime
    · by_cases hdvd : ℓ ∣ a
      · have hle1 : a.factorization ℓ ≤ 1 :=
          (Nat.squarefree_iff_factorization_le_one ha0).mp hsq ℓ
        by_cases hnd : ℓ ∣ 2 * n
        · have hpos : 0 < (2 * n).factorization ℓ :=
            Nat.Prime.factorization_pos_of_dvd hℓp h2n0 hnd
          omega
        · exfalso
          have heven := hmv ℓ hℓp hnd
          rw [← hab, Nat.factorization_mul (pow_ne_zero 2 hb0) ha0,
            Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply,
            smul_eq_mul] at heven
          have hpos : 0 < a.factorization ℓ :=
            Nat.Prime.factorization_pos_of_dvd hℓp ha0 hdvd
          obtain ⟨k, hk⟩ := heven
          omega
      · rw [Nat.factorization_eq_zero_of_not_dvd hdvd]
        omega
    · rw [Nat.factorization_eq_zero_of_non_prime _ hℓp]
      omega
  -- assemble the signed class
  rcases lt_trichotomy (x.num * (x.den : ℤ)) 0 with hs | hs | hs
  · refine ⟨-(a : ℤ), by simpa using ha0, by simpa using hadvd, ?_⟩
    have habs : x.num * (x.den : ℤ) = -((b : ℤ) ^ 2 * (a : ℤ)) := by
      have h1 : (((x.num * (x.den : ℤ)).natAbs : ℤ)) = -(x.num * (x.den : ℤ)) :=
        Int.ofNat_natAbs_of_nonpos hs.le
      have h2 : ((b : ℤ)) ^ 2 * (a : ℤ) = (((x.num * (x.den : ℤ)).natAbs : ℤ)) := by
        exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) hab
      linarith [h1, h2]
    have hstep : Descent.SqCls (((x.num * (x.den : ℤ) : ℤ) : ℚ)) ((-(a : ℤ) : ℤ) : ℚ) := by
      refine ⟨(b : ℚ), by exact_mod_cast hb0, ?_⟩
      rw [show ((x.num * (x.den : ℤ) : ℤ) : ℚ) = ((-((b : ℤ) ^ 2 * (a : ℤ)) : ℤ) : ℚ) from
        by exact_mod_cast congrArg (fun m : ℤ => (m : ℚ)) habs]
      push_cast
      ring
    exact sqcls_trans hcls hstep
  · exact absurd hs hm0
  · refine ⟨(a : ℤ), by exact_mod_cast ha0, by simpa using hadvd, ?_⟩
    have habs : x.num * (x.den : ℤ) = (b : ℤ) ^ 2 * (a : ℤ) := by
      have h1 : (((x.num * (x.den : ℤ)).natAbs : ℤ)) = x.num * (x.den : ℤ) :=
        Int.natAbs_of_nonneg hs.le
      have h2 : ((b : ℤ)) ^ 2 * (a : ℤ) = (((x.num * (x.den : ℤ)).natAbs : ℤ)) := by
        exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) hab
      linarith [h1, h2]
    have hstep : Descent.SqCls (((x.num * (x.den : ℤ) : ℤ) : ℚ)) (((a : ℤ) : ℤ) : ℚ) := by
      refine ⟨(b : ℚ), by exact_mod_cast hb0, ?_⟩
      rw [show ((x.num * (x.den : ℤ) : ℤ) : ℚ) = (((b : ℤ) ^ 2 * (a : ℤ) : ℤ) : ℚ) from
        by exact_mod_cast congrArg (fun m : ℤ => (m : ℚ)) habs]
      push_cast
      ring
    exact sqcls_trans hcls hstep

/-! ## 3. The support theorem at every modulus -/

private lemma slotOneAt_some {n x y : ℚ} (h : (FamilyFace.E n).Nonsingular x y) :
    slotOneAt n (.some h) = if x = 0 then -n ^ 2 else x := rfl

private lemma slotTwoAt_some {n x y : ℚ} (h : (FamilyFace.E n).Nonsingular x y) :
    slotTwoAt n (.some h) = if x = n then 2 * n ^ 2 else x - n := rfl

private lemma onCurveAt {n x y : ℚ} (h : (FamilyFace.E n).Nonsingular x y) :
    y ^ 2 = x ^ 3 - n ^ 2 * x := by
  have h1 := ((WeierstrassCurve.Affine.nonsingular_iff x y).mp h).1
  rw [WeierstrassCurve.Affine.equation_iff] at h1
  simp only [FamilyFace.E] at h1
  linarith [h1]

set_option maxHeartbeats 1000000 in
/-- **THE SLOT CLASSES ARE SUPPORTED ON THE DISCRIMINANT AT EVERY MODULUS**: both
descent slots of every rational point lie in the square class of a nonzero integer
whose absolute value divides `2n` — the face image is finite, per twist, uniformly. -/
theorem theSlotClassesAreSupportedAtEveryModulus (n : ℕ) (hn : 0 < n)
    (P : (FamilyFace.E ((n : ℚ))).Point) :
    ∃ d₁ d₂ : ℤ, d₁ ≠ 0 ∧ d₂ ≠ 0 ∧ d₁.natAbs ∣ 2 * n ∧ d₂.natAbs ∣ 2 * n ∧
      Descent.SqCls (slotOneAt ((n : ℚ)) P) (d₁ : ℚ) ∧
      Descent.SqCls (slotTwoAt ((n : ℚ)) P) (d₂ : ℚ) := by
  have hnq : ((n : ℚ)) ≠ 0 := by exact_mod_cast hn.ne'
  rcases P with _ | @⟨x, y, h⟩
  · refine ⟨1, 1, one_ne_zero, one_ne_zero, one_dvd _, one_dvd _, ?_, ?_⟩
    · simpa using Descent.sqClsRefl (1 : ℚ)
    · simpa using Descent.sqClsRefl (1 : ℚ)
  · by_cases hy : y = 0
    · -- the half-turns, with their conventional classes
      have hcurve := onCurveAt h
      rw [hy] at hcurve
      have hroots : x * (x - (n : ℚ)) * (x + (n : ℚ)) = 0 := by
        linear_combination -hcurve
      have hx3 : x = 0 ∨ x = (n : ℚ) ∨ x = -(n : ℚ) := by
        rcases mul_eq_zero.mp hroots with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl (by linarith))
        · exact Or.inr (Or.inr (by linarith))
      rcases hx3 with h' | h' | h'
      · refine ⟨-1, -(n : ℤ), by norm_num, by simpa using hn.ne', by norm_num,
          by simpa using Dvd.intro 2 rfl, ?_, ?_⟩
        · rw [slotOneAt_some, if_pos h']
          exact ⟨(n : ℚ), hnq, by push_cast; ring⟩
        · rw [slotTwoAt_some, if_neg (by rw [h']; exact fun hc => hnq hc.symm), h']
          exact ⟨1, one_ne_zero, by push_cast; ring⟩
      · refine ⟨(n : ℤ), 2, by simpa using hn.ne', two_ne_zero, by
          simpa using Dvd.intro 2 rfl, by norm_num, ?_, ?_⟩
        · rw [slotOneAt_some, if_neg (by rw [h']; exact hnq), h']
          exact ⟨1, one_ne_zero, by push_cast; ring⟩
        · rw [slotTwoAt_some, if_pos h']
          exact ⟨(n : ℚ), hnq, by push_cast; ring⟩
      · have hmn0 : x ≠ 0 := by
          rw [h']
          intro hc
          exact hnq (by linarith)
        have hmnn : x ≠ (n : ℚ) := by
          rw [h']
          intro hc
          exact hnq (by linarith)
        refine ⟨-(n : ℤ), -(2 * n : ℤ), by simpa using hn.ne', by
          intro hc
          have : (2 * n : ℤ) = 0 := by linarith [neg_eq_zero.mp hc]
          omega, by simpa using Dvd.intro 2 rfl, by
          have habs : (-(2 * n : ℤ)).natAbs = 2 * n := by
            rw [Int.natAbs_neg]
            omega
          rw [habs], ?_, ?_⟩
        · rw [slotOneAt_some, if_neg hmn0, h']
          exact ⟨1, one_ne_zero, by push_cast; ring⟩
        · rw [slotTwoAt_some, if_neg hmnn, h']
          exact ⟨1, one_ne_zero, by push_cast; ring⟩
    · -- the general point: even valuations off the discriminant
      have hcurve := onCurveAt h
      obtain ⟨hx0, hxn, -⟩ :=
        FaceHomomorphism.theNonzeroOrdinateAvoidsTheRoots hcurve hy
      obtain ⟨d₁, hd₁0, hd₁v, hcls₁⟩ := classFromEvenValuations hn hx0
        fun ℓ hℓ hnd =>
          haveI : Fact ℓ.Prime := ⟨hℓ⟩
          (even_slot_val hn hnd hcurve hy).1
      obtain ⟨d₂, hd₂0, hd₂v, hcls₂⟩ := classFromEvenValuations hn
        (sub_ne_zero.mpr hxn)
        fun ℓ hℓ hnd =>
          haveI : Fact ℓ.Prime := ⟨hℓ⟩
          (even_slot_val hn hnd hcurve hy).2
      refine ⟨d₁, d₂, hd₁0, hd₂0, hd₁v, hd₂v, ?_, ?_⟩
      · rw [slotOneAt_some, if_neg hx0]
        exact hcls₁
      · rw [slotTwoAt_some, if_neg hxn]
        exact hcls₂

end Soma.Holonics.Millennium.FamilySupport
