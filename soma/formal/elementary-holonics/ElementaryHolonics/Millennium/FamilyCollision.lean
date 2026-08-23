import ElementaryHolonics.Millennium.FamilyMordell
import Mathlib.Tactic

/-!
# FamilyCollision: the class pigeonhole and the torsion trio at every modulus

**The two counting halves of the family rank bound.**  On every congruent-number
curve `y² = x³ − n²x` with `n ≥ 1`:

* **`theClassesCollideAtEveryModulus`** — any family of more than `(4n+1)²` points
  contains two whose difference is a double: the face image lives in the
  `(4n+1)²`-cell class box (`FamilySupport`), the face is a homomorphism
  (`FamilyHom`), and the kernel is the doubles (`FamilyKernel`);
* **`theTorsionTrioDoesNotCollideAtEveryModulus`** — the three points
  `0, (0,0), (n,0)` are pairwise not congruent modulo doubles, at every modulus:
  the three refusals are carried by the sign of `−n²`, by two not being a rational
  square against `2n²`, and by the sign of `−n³`.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

namespace Soma.Holonics.Millennium.FamilyRankFin3

lemma fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  rcases i with ⟨iv, hiv⟩
  interval_cases iv
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

end Soma.Holonics.Millennium.FamilyRankFin3

noncomputable section

namespace Soma.Holonics.Millennium.FamilyCollision

open WeierstrassCurve.Affine
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.FamilyKernel

variable {n : ℕ}

/-! ## 1. Plumbing -/

lemma sqcls_trans {a b c : ℚ} (h₁ : Descent.SqCls a b) (h₂ : Descent.SqCls b c) :
    Descent.SqCls a c := by
  obtain ⟨k, hk, hkv⟩ := h₁
  obtain ⟨m, hm, hmv⟩ := h₂
  exact ⟨k * m, mul_ne_zero hk hm, by rw [hkv, hmv]; ring⟩

lemma sqcls_symm {a b : ℚ} (h : Descent.SqCls a b) : Descent.SqCls b a := by
  obtain ⟨c, hc, hv⟩ := h
  exact ⟨c⁻¹, inv_ne_zero hc, by
    rw [hv, inv_pow, inv_mul_cancel_left₀ (pow_ne_zero 2 hc)]⟩

lemma sqcls_mul {a b c d : ℚ} (h₁ : Descent.SqCls a c) (h₂ : Descent.SqCls b d) :
    Descent.SqCls (a * b) (c * d) := by
  obtain ⟨k, hk, hkv⟩ := h₁
  obtain ⟨m, hm, hmv⟩ := h₂
  exact ⟨k * m, mul_ne_zero hk hm, by rw [hkv, hmv]; ring⟩

lemma sqcls_ne {a b : ℚ} (h : Descent.SqCls a b) (ha : a ≠ 0) : b ≠ 0 := by
  obtain ⟨c, hc, hv⟩ := h
  intro hb
  rw [hb, mul_zero] at hv
  exact ha hv

lemma slotOneAt_ne (hn : 0 < n) (P : (FamilyFace.E ((n : ℚ))).Point) :
    slotOneAt ((n : ℚ)) P ≠ 0 := by
  rcases P with _ | @⟨x, y, h⟩
  · exact one_ne_zero
  · show (if x = 0 then -((n : ℚ)) ^ 2 else x) ≠ 0
    split_ifs with hx
    · have h1 : ((n : ℚ)) ≠ 0 := by exact_mod_cast hn.ne'
      exact neg_ne_zero.mpr (pow_ne_zero 2 h1)
    · exact hx

lemma slotTwoAt_ne (hn : 0 < n) (P : (FamilyFace.E ((n : ℚ))).Point) :
    slotTwoAt ((n : ℚ)) P ≠ 0 := by
  rcases P with _ | @⟨x, y, h⟩
  · exact one_ne_zero
  · show (if x = (n : ℚ) then 2 * ((n : ℚ)) ^ 2 else x - (n : ℚ)) ≠ 0
    split_ifs with hx
    · have h1 : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
      positivity
    · exact sub_ne_zero.mpr hx

lemma slot_neg_one (P : (FamilyFace.E ((n : ℚ))).Point) :
    slotOneAt ((n : ℚ)) (-P) = slotOneAt ((n : ℚ)) P := by
  rcases P with _ | @⟨x, y, h⟩
  · rw [← Point.zero_def, neg_zero]
  · rw [Point.neg_some]
    rfl

lemma slot_neg_two (P : (FamilyFace.E ((n : ℚ))).Point) :
    slotTwoAt ((n : ℚ)) (-P) = slotTwoAt ((n : ℚ)) P := by
  rcases P with _ | @⟨x, y, h⟩
  · rw [← Point.zero_def, neg_zero]
  · rw [Point.neg_some]
    rfl

def classOf (hn : 0 < n) (P : (FamilyFace.E ((n : ℚ))).Point) : ℤ × ℤ :=
  ((FamilySupport.theSlotClassesAreSupportedAtEveryModulus n hn P).choose,
   (FamilySupport.theSlotClassesAreSupportedAtEveryModulus n hn P).choose_spec.choose)

lemma classOf_spec (hn : 0 < n) (P : (FamilyFace.E ((n : ℚ))).Point) :
    (classOf hn P).1 ≠ 0 ∧ (classOf hn P).2 ≠ 0 ∧
    (classOf hn P).1.natAbs ∣ 2 * n ∧ (classOf hn P).2.natAbs ∣ 2 * n ∧
    Descent.SqCls (slotOneAt ((n : ℚ)) P) (((classOf hn P).1 : ℤ) : ℚ) ∧
    Descent.SqCls (slotTwoAt ((n : ℚ)) P) (((classOf hn P).2 : ℤ) : ℚ) :=
  (FamilySupport.theSlotClassesAreSupportedAtEveryModulus n hn
    P).choose_spec.choose_spec

/-! ## 2. Same class means the difference is a double -/

lemma sameClass_double (hn : 0 < n)
    (X R : (FamilyFace.E ((n : ℚ))).Point) (hc : classOf hn X = classOf hn R) :
    ∃ Q : (FamilyFace.E ((n : ℚ))).Point, X - R = Q + Q := by
  have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  obtain ⟨-, -, -, -, hX1, hX2⟩ := classOf_spec hn X
  obtain ⟨-, -, -, -, hR1, hR2⟩ := classOf_spec hn R
  rw [← hc] at hR1 hR2
  have hd₁ : (((classOf hn X).1 : ℤ) : ℚ) ≠ 0 := sqcls_ne hX1 (slotOneAt_ne hn X)
  have hd₂ : (((classOf hn X).2 : ℤ) : ℚ) ≠ 0 := sqcls_ne hX2 (slotTwoAt_ne hn X)
  obtain ⟨hom1, hom2⟩ :=
    FamilyHom.theFaceIsAHomomorphismAtEveryModulus ((n : ℚ)) hnq X (-R)
  rw [slot_neg_one, ← sub_eq_add_neg] at hom1
  rw [slot_neg_two, ← sub_eq_add_neg] at hom2
  have h1 : Descent.SqCls (slotOneAt ((n : ℚ)) (X - R)) 1 :=
    sqcls_trans hom1 (sqcls_trans (sqcls_mul hX1 hR1)
      ⟨(((classOf hn X).1 : ℤ) : ℚ), hd₁, by ring⟩)
  have h2 : Descent.SqCls (slotTwoAt ((n : ℚ)) (X - R)) 1 :=
    sqcls_trans hom2 (sqcls_trans (sqcls_mul hX2 hR2)
      ⟨(((classOf hn X).2 : ℤ) : ℚ), hd₂, by ring⟩)
  obtain ⟨Q, hQ⟩ :=
    FamilyKernel.theKernelIsTheDoublesAtEveryModulus ((n : ℚ)) hnq (X - R) h1 h2
  exact ⟨Q, hQ.symm⟩

/-! ## 3. The class pigeonhole -/

set_option maxHeartbeats 1000000 in
/-- **THE CLASSES COLLIDE AT EVERY MODULUS**: any family of more than `(4n+1)²`
points contains two whose difference is a double. -/
theorem theClassesCollideAtEveryModulus (hn : 0 < n) {α : Type} [Fintype α]
    (hcard : (4 * n + 1) ^ 2 < Fintype.card α)
    (f : α → (FamilyFace.E ((n : ℚ))).Point) :
    ∃ a b, a ≠ b ∧ ∃ Q : (FamilyFace.E ((n : ℚ))).Point, f a - f b = Q + Q := by
  have h2n : 0 < 2 * n := by omega
  set box : Finset (ℤ × ℤ) :=
    Finset.Icc (-(2 * n : ℤ)) (2 * n) ×ˢ Finset.Icc (-(2 * n : ℤ)) (2 * n) with hbox
  have hmaps : ∀ a : α, classOf hn (f a) ∈ box := by
    intro a
    obtain ⟨-, -, h1d, h2d, -, -⟩ := classOf_spec hn (f a)
    have hb1 : (classOf hn (f a)).1.natAbs ≤ 2 * n := Nat.le_of_dvd h2n h1d
    have hb2 : (classOf hn (f a)).2.natAbs ≤ 2 * n := Nat.le_of_dvd h2n h2d
    rw [hbox]
    simp only [Finset.mem_product, Finset.mem_Icc]
    omega
  have hboxcard : box.card = (4 * n + 1) ^ 2 := by
    rw [hbox, Finset.card_product, Int.card_Icc]
    have h1 : (2 * n : ℤ) + 1 - -(2 * n : ℤ) = (4 * n + 1 : ℤ) := by ring
    rw [h1]
    have h2 : ((4 * n + 1 : ℤ)).toNat = 4 * n + 1 := by omega
    rw [h2]
    ring
  have hlt : box.card < Fintype.card α := by omega
  obtain ⟨a, -, b, -, hab, hfab⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (by rw [Finset.card_univ]; exact hlt) fun a _ => hmaps a
  exact ⟨a, b, hab, sameClass_double hn (f a) (f b) hfab⟩

/-! ## 4. The torsion trio -/

/-- The refusals feeding the trio: a double's slot class is trivial, so a
non-square slot product refutes the collision. -/
lemma diff_gives_sqcls (hn : 0 < n)
    {A B Q : (FamilyFace.E ((n : ℚ))).Point} (hAB : A - B = Q + Q)
    (useTwo : Bool) {pr : ℚ}
    (hpr : pr = if useTwo then slotTwoAt ((n : ℚ)) A * slotTwoAt ((n : ℚ)) B
      else slotOneAt ((n : ℚ)) A * slotOneAt ((n : ℚ)) B) :
    Descent.SqCls 1 pr := by
  have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  obtain ⟨hom1, hom2⟩ :=
    FamilyHom.theFaceIsAHomomorphismAtEveryModulus ((n : ℚ)) hnq A (-B)
  rw [slot_neg_one, ← sub_eq_add_neg, hAB] at hom1
  rw [slot_neg_two, ← sub_eq_add_neg, hAB] at hom2
  obtain ⟨k1, k2⟩ :=
    FamilyImage.theDoublesLandInTheKernelAtEveryModulus ((n : ℚ)) hnq Q
  cases useTwo with
  | false =>
    rw [hpr]
    simp only [Bool.false_eq_true, if_false]
    exact sqcls_trans (sqcls_symm k1) hom1
  | true =>
    rw [hpr]
    simp only [if_true]
    exact sqcls_trans (sqcls_symm k2) hom2

set_option maxHeartbeats 1000000 in
/-- **THE TORSION TRIO DOES NOT COLLIDE AT EVERY MODULUS**: `0`, `(0,0)` and
`(n,0)` are pairwise not congruent modulo doubles. -/
theorem theTorsionTrioDoesNotCollideAtEveryModulus (hn : 0 < n)
    (T : Fin 3 → (FamilyFace.E ((n : ℚ))).Point)
    (hT0 : T 0 = 0)
    (hT1 : T 1 = Point.some (show (FamilyFace.E ((n : ℚ))).Nonsingular 0 0 from by
      rw [nonsingular_iff, equation_iff]
      constructor
      · simp [FamilyFace.E]
      · left
        simp only [FamilyFace.E]
        have h1 : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
        intro hc
        nlinarith [hc, h1]))
    (hT2 : T 2 = Point.some (show (FamilyFace.E ((n : ℚ))).Nonsingular ((n : ℚ)) 0 from by
      rw [nonsingular_iff, equation_iff]
      constructor
      · simp only [FamilyFace.E]
        ring
      · left
        simp only [FamilyFace.E]
        have h1 : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
        intro hc
        nlinarith [hc]))
    (b b' : Fin 3) (hbb : b ≠ b') (Q : (FamilyFace.E ((n : ℚ))).Point) :
    T b - T b' ≠ Q + Q := by
  intro hc
  have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  have hnq0 : ((n : ℚ)) ≠ 0 := hnq.ne'
  -- the slot values of the trio
  have hz1 : slotOneAt ((n : ℚ)) (T 0) = 1 := by rw [hT0]; rfl
  have hz2 : slotTwoAt ((n : ℚ)) (T 0) = 1 := by rw [hT0]; rfl
  have ha1 : slotOneAt ((n : ℚ)) (T 1) = -((n : ℚ)) ^ 2 := by
    rw [hT1]
    show (if (0 : ℚ) = 0 then -((n : ℚ)) ^ 2 else 0) = -((n : ℚ)) ^ 2
    rw [if_pos rfl]
  have ha2 : slotTwoAt ((n : ℚ)) (T 1) = -(n : ℚ) := by
    rw [hT1]
    show (if (0 : ℚ) = (n : ℚ) then 2 * ((n : ℚ)) ^ 2 else 0 - (n : ℚ)) = -(n : ℚ)
    rw [if_neg (fun hcc => hnq0 hcc.symm)]
    ring
  have hb1 : slotOneAt ((n : ℚ)) (T 2) = (n : ℚ) := by
    rw [hT2]
    show (if ((n : ℚ)) = 0 then -((n : ℚ)) ^ 2 else ((n : ℚ))) = (n : ℚ)
    rw [if_neg hnq0]
  have hb2 : slotTwoAt ((n : ℚ)) (T 2) = 2 * ((n : ℚ)) ^ 2 := by
    rw [hT2]
    show (if ((n : ℚ)) = ((n : ℚ)) then 2 * ((n : ℚ)) ^ 2 else _) = 2 * ((n : ℚ)) ^ 2
    rw [if_pos rfl]
  -- the three refusals
  have refuse_neg : ∀ pr : ℚ, pr < 0 → ¬ Descent.SqCls 1 pr := by
    rintro pr hpr ⟨c, hc0, hcv⟩
    nlinarith [sq_nonneg c]
  have refuse_two : ¬ Descent.SqCls 1 (2 * ((n : ℚ)) ^ 2) := by
    rintro ⟨c, hc0, hcv⟩
    refine Descent.notSquareTwo ⟨1 / (c * (n : ℚ)), ?_⟩
    rw [div_mul_div_comm, eq_div_iff (by positivity : (c * (n : ℚ)) * (c * (n : ℚ)) ≠ 0)]
    linear_combination -hcv
  have hcases : ∀ (i j : Fin 3), i ≠ j → T i - T j = Q + Q → False := by
    intro i j hij hd
    rcases FamilyRankFin3.fin3_cases i with rfl | rfl | rfl <;>
      rcases FamilyRankFin3.fin3_cases j with rfl | rfl | rfl
    · exact hij rfl
    · have hs : Descent.SqCls 1 (1 * -((n : ℚ)) ^ 2) :=
        diff_gives_sqcls hn hd false (by rw [if_neg Bool.false_ne_true, hz1, ha1])
      exact refuse_neg _ (by nlinarith [hnq]) hs
    · have hs : Descent.SqCls 1 (1 * (2 * ((n : ℚ)) ^ 2)) :=
        diff_gives_sqcls hn hd true (by rw [if_pos rfl, hz2, hb2])
      rw [one_mul] at hs
      exact refuse_two hs
    · have hs : Descent.SqCls 1 (-((n : ℚ)) ^ 2 * 1) :=
        diff_gives_sqcls hn hd false (by rw [if_neg Bool.false_ne_true, ha1, hz1])
      exact refuse_neg _ (by nlinarith [hnq]) hs
    · exact hij rfl
    · have hs : Descent.SqCls 1 (-((n : ℚ)) ^ 2 * ((n : ℚ))) :=
        diff_gives_sqcls hn hd false (by rw [if_neg Bool.false_ne_true, ha1, hb1])
      exact refuse_neg _ (by nlinarith [hnq, mul_pos (mul_pos hnq hnq) hnq]) hs
    · have hs : Descent.SqCls 1 (2 * ((n : ℚ)) ^ 2 * 1) :=
        diff_gives_sqcls hn hd true (by rw [if_pos rfl, hb2, hz2])
      rw [mul_one] at hs
      exact refuse_two hs
    · have hs : Descent.SqCls 1 (((n : ℚ)) * -((n : ℚ)) ^ 2) :=
        diff_gives_sqcls hn hd false (by rw [if_neg Bool.false_ne_true, hb1, ha1])
      exact refuse_neg _ (by nlinarith [hnq, mul_pos (mul_pos hnq hnq) hnq]) hs
    · exact hij rfl
  exact hcases b b' hbb hc

end Soma.Holonics.Millennium.FamilyCollision
