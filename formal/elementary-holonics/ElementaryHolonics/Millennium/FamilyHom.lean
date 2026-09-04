import ElementaryHolonics.Millennium.FamilyImage
import ElementaryHolonics.Millennium.FaceHomomorphism
import Mathlib.Tactic

/-!
# FamilyHom: the face is a homomorphism at every modulus

**The last descent law of the family chart.**  On every congruent-number curve
`y² = x³ − n²x` with `n > 0`, the descent face is a homomorphism into square
classes on the whole point group:

* **`theFaceIsAHomomorphismAtEveryModulus`** — for all points `P, Q`,
  `slot(P + Q) ~ slot(P)·slot(Q)` in both slots.

The chord landing laws were already generic; this file assembles them through
mathlib's group law with the family slots, computes the half-turn translations by
their classical closed forms (`x ↦ −n²/x` at `(0,0)`, `x ↦ n(x+n)/(x−n)` at
`(n,0)`, `x ↦ −n(x−n)/(x+n)` at `(−n,0)`) with exhibited square-root witnesses,
and settles the Klein chords symbolically.  With family exactness
(`theTwoDescentIsExactAtEveryModulus`) the complete two-descent mechanism is now
family law.  Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyHom

open WeierstrassCurve.Affine
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.FamilyKernel

/-! ## 1. Plumbing -/

private lemma onCurveAt {n x y : ℚ} (h : (FamilyFace.E n).Nonsingular x y) :
    y ^ 2 = x ^ 3 - n ^ 2 * x := by
  have h1 := ((nonsingular_iff x y).mp h).1
  rw [equation_iff] at h1
  simp only [FamilyFace.E] at h1
  linarith [h1]

private lemma negYAt (n x y : ℚ) : (FamilyFace.E n).negY x y = -y := by
  simp [negY, FamilyFace.E]

private lemma someEqAt {n x₁ y₁ x₂ y₂ : ℚ} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : (FamilyFace.E n).Nonsingular x₁ y₁} {h₂ : (FamilyFace.E n).Nonsingular x₂ y₂} :
    (Point.some _ _ h₁ : (FamilyFace.E n).Point) = Point.some _ _ h₂ := by
  subst hx; subst hy; rfl

private lemma slotOneAt_some {n x y : ℚ} (h : (FamilyFace.E n).Nonsingular x y) :
    slotOneAt n (.some _ _ h) = if x = 0 then -n ^ 2 else x := rfl

private lemma slotTwoAt_some {n x y : ℚ} (h : (FamilyFace.E n).Nonsingular x y) :
    slotTwoAt n (.some _ _ h) = if x = n then 2 * n ^ 2 else x - n := rfl

private lemma slotOneAt_zero (n : ℚ) : slotOneAt n 0 = 1 := rfl

private lemma slotTwoAt_zero (n : ℚ) : slotTwoAt n 0 = 1 := rfl

private lemma slotOneAt_ne {n : ℚ} (hn : 0 < n) (P : (FamilyFace.E n).Point) :
    slotOneAt n P ≠ 0 := by
  rcases P with _ | @⟨x, y, h⟩
  · exact one_ne_zero
  · rw [slotOneAt_some]
    split_ifs with hx
    · exact neg_ne_zero.mpr (pow_ne_zero 2 hn.ne')
    · exact hx

private lemma slotTwoAt_ne {n : ℚ} (hn : 0 < n) (P : (FamilyFace.E n).Point) :
    slotTwoAt n P ≠ 0 := by
  rcases P with _ | @⟨x, y, h⟩
  · exact one_ne_zero
  · rw [slotTwoAt_some]
    split_ifs with hx
    · positivity
    · exact sub_ne_zero.mpr hx

private lemma sqcls_one_mul_self {s : ℚ} (hs : s ≠ 0) : Descent.SqCls 1 (s * s) := by
  refine ⟨1 / s, one_div_ne_zero hs, ?_⟩
  field_simp

private lemma sqcls_scale_sq {a s : ℚ} (h : Descent.SqCls a 1) (hs : s ≠ 0) :
    Descent.SqCls a (s * s) := by
  obtain ⟨c, hc, hval⟩ := h
  refine ⟨c / s, div_ne_zero hc hs, ?_⟩
  rw [hval]
  field_simp

private lemma sqcls_mul_sq_left {a b t : ℚ} (h : Descent.SqCls a b) (ht : t ≠ 0) :
    Descent.SqCls (t ^ 2 * a) b := by
  obtain ⟨c, hc, hval⟩ := h
  exact ⟨t * c, mul_ne_zero ht hc, by rw [hval]; ring⟩

private lemma slopeLineAt {n x₁ y₁ x₂ y₂ : ℚ} (hx : x₁ ≠ x₂) :
    (FamilyFace.E n).slope x₁ x₂ y₁ y₂ * (x₂ - x₁) = y₂ - y₁ := by
  rw [slope_of_X_ne hx]
  have h : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  field_simp
  ring

private lemma addXAt (n x₁ x₂ L : ℚ) :
    (FamilyFace.E n).addX x₁ x₂ L = L ^ 2 - x₁ - x₂ := by
  simp only [addX, FamilyFace.E]
  ring

private lemma halfTurnAbscissaAt {n x y : ℚ} (h : (FamilyFace.E n).Nonsingular x y)
    (hy : y = 0) : x = 0 ∨ x = n ∨ x = -n := by
  have hc := onCurveAt h
  rw [hy] at hc
  have h0 : x * (x - n) * (x + n) = 0 := by linear_combination -hc
  rcases mul_eq_zero.mp h0 with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact Or.inl h''
    · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (by linarith))

/-! ## 2. The chord through a half-turn -/

set_option maxHeartbeats 2000000 in
/-- The chord through a point off the two-torsion and a half-turn closes both slots,
at every modulus: the three half-turn translations are computed by their classical
closed forms with exhibited square-root witnesses. -/
private lemma chordHalfTurnRightAt {n x₁ y₁ x₂ : ℚ} (hn : 0 < n)
    (h₁ : (FamilyFace.E n).Nonsingular x₁ y₁) (h₂ : (FamilyFace.E n).Nonsingular x₂ 0)
    (hy₁ : y₁ ≠ 0) (hx : x₁ ≠ x₂) :
    Descent.SqCls (slotOneAt n (Point.some _ _ h₁ + Point.some _ _ h₂))
      (slotOneAt n (Point.some _ _ h₁) * slotOneAt n (Point.some _ _ h₂)) ∧
    Descent.SqCls (slotTwoAt n (Point.some _ _ h₁ + Point.some _ _ h₂))
      (slotTwoAt n (Point.some _ _ h₁) * slotTwoAt n (Point.some _ _ h₂)) := by
  have hcurve := onCurveAt h₁
  obtain ⟨ha1, ha2, ha3⟩ :=
    FaceHomomorphism.theNonzeroOrdinateAvoidsTheRoots hcurve hy₁
  have han : x₁ + n ≠ 0 := fun hc => ha3 (by linarith)
  have hamn : x₁ - n ≠ 0 := sub_ne_zero.mpr ha2
  have hs₁ : slotOneAt n (Point.some _ _ h₁) = x₁ := by rw [slotOneAt_some, if_neg ha1]
  have ht₁ : slotTwoAt n (Point.some _ _ h₁) = x₁ - n := by rw [slotTwoAt_some, if_neg ha2]
  rcases halfTurnAbscissaAt h₂ rfl with h0 | h0 | h0
  · -- translation by `(0, 0)`: `x ↦ −n²/x`
    subst h0
    rw [Point.add_of_X_ne hx]
    have hL : (FamilyFace.E n).slope x₁ 0 y₁ 0 = y₁ / x₁ := by
      rw [slope_of_X_ne hx, sub_zero, sub_zero]
    have hX3 : (FamilyFace.E n).addX x₁ 0 ((FamilyFace.E n).slope x₁ 0 y₁ 0)
        = -n ^ 2 / x₁ := by
      rw [addXAt, hL, div_pow, eq_div_iff ha1]
      field_simp
      linear_combination hcurve
    have hd0 : -n ^ 2 / x₁ ≠ 0 :=
      div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hn.ne')) ha1
    have hdn : -n ^ 2 / x₁ ≠ n := by
      intro hc
      rw [div_eq_iff ha1] at hc
      have h1 : n * (x₁ + n) = 0 := by linarith
      rcases mul_eq_zero.mp h1 with h | h
      · exact hn.ne' h
      · exact han h
    have hsQ : slotOneAt n (Point.some _ _ h₂) = -n ^ 2 := by
      rw [slotOneAt_some, if_pos rfl]
    have htQ : slotTwoAt n (Point.some _ _ h₂) = -n := by
      rw [slotTwoAt_some, if_neg (fun hc => hn.ne' hc.symm)]
      ring
    constructor
    · rw [slotOneAt_some, hX3, if_neg hd0, hs₁, hsQ]
      refine ⟨1 / x₁, one_div_ne_zero ha1, ?_⟩
      field_simp
    · rw [slotTwoAt_some, hX3, if_neg hdn, ht₁, htQ]
      refine ⟨(x₁ + n) / y₁, div_ne_zero han hy₁, ?_⟩
      field_simp
      linear_combination (-n - x₁) * hcurve
  · -- translation by `(n, 0)`: `x ↦ n(x+n)/(x−n)`
    have h₂' : (FamilyFace.E n).Nonsingular n 0 := h0 ▸ h₂
    rw [show (Point.some _ _ h₂ : (FamilyFace.E n).Point) = Point.some _ _ h₂' from
      someEqAt h0 rfl]
    replace hx : x₁ ≠ n := h0 ▸ hx
    rw [Point.add_of_X_ne hx]
    have hL : (FamilyFace.E n).slope x₁ n y₁ 0 = y₁ / (x₁ - n) := by
      rw [slope_of_X_ne hx, sub_zero]
    have hX3 : (FamilyFace.E n).addX x₁ n ((FamilyFace.E n).slope x₁ n y₁ 0)
        = n * (x₁ + n) / (x₁ - n) := by
      rw [addXAt, hL, div_pow]
      rw [eq_div_iff hamn]
      field_simp
      linear_combination hcurve
    have hd0 : n * (x₁ + n) / (x₁ - n) ≠ 0 :=
      div_ne_zero (mul_ne_zero hn.ne' han) hamn
    have hdn : n * (x₁ + n) / (x₁ - n) ≠ n := by
      intro hc
      rw [div_eq_iff hamn] at hc
      nlinarith [hn]
    have hsQ : slotOneAt n (Point.some _ _ h₂') = n := by
      rw [slotOneAt_some, if_neg hn.ne']
    have htQ : slotTwoAt n (Point.some _ _ h₂') = 2 * n ^ 2 := by
      rw [slotTwoAt_some, if_pos rfl]
    constructor
    · rw [slotOneAt_some, hX3, if_neg hd0, hs₁, hsQ]
      refine ⟨(x₁ + n) / y₁, div_ne_zero han hy₁, ?_⟩
      field_simp
      linear_combination hcurve
    · rw [slotTwoAt_some, hX3, if_neg hdn, ht₁, htQ]
      refine ⟨1 / (x₁ - n), one_div_ne_zero hamn, ?_⟩
      field_simp
      ring
  · -- translation by `(−n, 0)`: `x ↦ −n(x−n)/(x+n)`
    have h₂' : (FamilyFace.E n).Nonsingular (-n) 0 := h0 ▸ h₂
    rw [show (Point.some _ _ h₂ : (FamilyFace.E n).Point) = Point.some _ _ h₂' from
      someEqAt h0 rfl]
    replace hx : x₁ ≠ -n := h0 ▸ hx
    rw [Point.add_of_X_ne hx]
    have hL : (FamilyFace.E n).slope x₁ (-n) y₁ 0 = y₁ / (x₁ + n) := by
      rw [slope_of_X_ne hx, sub_zero, sub_neg_eq_add]
    have hX3 : (FamilyFace.E n).addX x₁ (-n) ((FamilyFace.E n).slope x₁ (-n) y₁ 0)
        = -n * (x₁ - n) / (x₁ + n) := by
      rw [addXAt, hL, div_pow]
      rw [eq_div_iff han]
      field_simp
      linear_combination hcurve
    have hd0 : -n * (x₁ - n) / (x₁ + n) ≠ 0 :=
      div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hn.ne') hamn) han
    have hdn : -n * (x₁ - n) / (x₁ + n) ≠ n := by
      intro hc
      rw [div_eq_iff han] at hc
      have h1 : n * x₁ = 0 := by linarith
      rcases mul_eq_zero.mp h1 with h | h
      · exact hn.ne' h
      · exact ha1 h
    have hsQ : slotOneAt n (Point.some _ _ h₂') = -n := by
      rw [slotOneAt_some, if_neg (by intro hc; exact hn.ne' (by linarith))]
    have htQ : slotTwoAt n (Point.some _ _ h₂') = -2 * n := by
      rw [slotTwoAt_some, if_neg (by intro hc; exact hn.ne' (by linarith))]
      ring
    constructor
    · rw [slotOneAt_some, hX3, if_neg hd0, hs₁, hsQ]
      refine ⟨(x₁ - n) / y₁, div_ne_zero hamn hy₁, ?_⟩
      field_simp
      linear_combination -hcurve
    · rw [slotTwoAt_some, hX3, if_neg hdn, ht₁, htQ]
      refine ⟨x₁ / y₁, div_ne_zero ha1 hy₁, ?_⟩
      field_simp
      linear_combination (-2 * x₁) * hcurve

/-! ## 3. The face homomorphism at every modulus -/

set_option maxHeartbeats 4000000 in
/-- **THE FACE IS A HOMOMORPHISM AT EVERY MODULUS**: on `y² = x³ − n²x` with
`n > 0`, both descent slots of a sum land in the square class of the product of the
slots.  The five-instance homomorphism is this law read at `n = 5`. -/
theorem theFaceIsAHomomorphismAtEveryModulus (n : ℚ) (hn : 0 < n)
    (P Q : (FamilyFace.E n).Point) :
    Descent.SqCls (slotOneAt n (P + Q)) (slotOneAt n P * slotOneAt n Q) ∧
    Descent.SqCls (slotTwoAt n (P + Q)) (slotTwoAt n P * slotTwoAt n Q) := by
  rcases P with _ | @⟨x₁, y₁, h₁⟩
  · rw [← Point.zero_def, zero_add, slotOneAt_zero, slotTwoAt_zero, one_mul, one_mul]
    exact ⟨Descent.sqClsRefl _, Descent.sqClsRefl _⟩
  rcases Q with _ | @⟨x₂, y₂, h₂⟩
  · rw [← Point.zero_def, add_zero, slotOneAt_zero, slotTwoAt_zero, mul_one, mul_one]
    exact ⟨Descent.sqClsRefl _, Descent.sqClsRefl _⟩
  by_cases hx : x₁ = x₂
  · subst hx
    have hyy : (y₂ - y₁) * (y₂ + y₁) = 0 := by
      have hA := onCurveAt h₁
      have hB := onCurveAt h₂
      linear_combination hB - hA
    rcases mul_eq_zero.mp hyy with hcase | hcase
    · have heq : (Point.some _ _ h₂ : (FamilyFace.E n).Point) = Point.some _ _ h₁ :=
        someEqAt rfl (by linarith)
      rw [heq]
      obtain ⟨k1, k2⟩ := FamilyImage.theDoublesLandInTheKernelAtEveryModulus n hn
        (Point.some _ _ h₁)
      exact ⟨sqcls_scale_sq k1 (slotOneAt_ne hn _),
        sqcls_scale_sq k2 (slotTwoAt_ne hn _)⟩
    · by_cases hy0 : y₁ = 0
      · have heq : (Point.some _ _ h₂ : (FamilyFace.E n).Point) = Point.some _ _ h₁ :=
          someEqAt rfl (by linarith)
        rw [heq]
        obtain ⟨k1, k2⟩ := FamilyImage.theDoublesLandInTheKernelAtEveryModulus n hn
          (Point.some _ _ h₁)
        exact ⟨sqcls_scale_sq k1 (slotOneAt_ne hn _),
          sqcls_scale_sq k2 (slotTwoAt_ne hn _)⟩
      · have hzero : (Point.some _ _ h₁ : (FamilyFace.E n).Point) + Point.some _ _ h₂ = 0 :=
          Point.add_of_Y_eq rfl (by rw [negYAt]; linarith)
        have hs : slotOneAt n (Point.some _ _ h₂) = slotOneAt n (Point.some _ _ h₁) := by
          rw [slotOneAt_some, slotOneAt_some]
        have ht : slotTwoAt n (Point.some _ _ h₂) = slotTwoAt n (Point.some _ _ h₁) := by
          rw [slotTwoAt_some, slotTwoAt_some]
        rw [hzero, slotOneAt_zero, slotTwoAt_zero, hs, ht]
        exact ⟨sqcls_one_mul_self (slotOneAt_ne hn _),
          sqcls_one_mul_self (slotTwoAt_ne hn _)⟩
  · by_cases hy1 : y₁ = 0
    · by_cases hy2 : y₂ = 0
      · -- both half-turns: the Klein chords, computed symbolically
        subst hy1; subst hy2
        have h2n : (2 : ℚ) * n ≠ 0 := mul_ne_zero two_ne_zero hn.ne'
        have hn0 : (0 : ℚ) ≠ n := fun hc => hn.ne' hc.symm
        have hmn0 : (-n : ℚ) ≠ 0 := fun hc => hn.ne' (by linarith)
        have hmnn : (-n : ℚ) ≠ n := fun hc => hn.ne' (by linarith)
        rcases halfTurnAbscissaAt h₁ rfl with hA | hA | hA <;>
          rcases halfTurnAbscissaAt h₂ rfl with hB | hB | hB
        · exact absurd (hA.trans hB.symm) hx
        · -- (0,0) + (n,0) lands at −n
          have h₁' : (FamilyFace.E n).Nonsingular 0 0 := hA ▸ h₁
          have h₂' : (FamilyFace.E n).Nonsingular n 0 := hB ▸ h₂
          rw [show (Point.some _ _ h₁ : (FamilyFace.E n).Point) = Point.some _ _ h₁' from
              someEqAt hA rfl,
            show (Point.some _ _ h₂ : (FamilyFace.E n).Point) = Point.some _ _ h₂' from
              someEqAt hB rfl, Point.add_of_X_ne hn0]
          have hsl : (FamilyFace.E n).slope 0 n 0 0 = 0 := by
            rw [slope_of_X_ne hn0]
            norm_num
          have hX3 : (FamilyFace.E n).addX 0 n ((FamilyFace.E n).slope 0 n 0 0)
              = -n := by rw [addXAt, hsl]; ring
          constructor
          · rw [slotOneAt_some, hX3, if_neg hmn0, slotOneAt_some, if_pos rfl,
              slotOneAt_some, if_neg hn.ne']
            exact ⟨1 / n, one_div_ne_zero hn.ne', by field_simp⟩
          · rw [slotTwoAt_some, hX3, if_neg hmnn, slotTwoAt_some, if_neg hn0,
              slotTwoAt_some, if_pos rfl]
            exact ⟨1 / n, one_div_ne_zero hn.ne', by field_simp; ring⟩
        · -- (0,0) + (−n,0) lands at n
          have h₁' : (FamilyFace.E n).Nonsingular 0 0 := hA ▸ h₁
          have h₂' : (FamilyFace.E n).Nonsingular (-n) 0 := hB ▸ h₂
          rw [show (Point.some _ _ h₁ : (FamilyFace.E n).Point) = Point.some _ _ h₁' from
              someEqAt hA rfl,
            show (Point.some _ _ h₂ : (FamilyFace.E n).Point) = Point.some _ _ h₂' from
              someEqAt hB rfl, Point.add_of_X_ne (Ne.symm hmn0)]
          have hsl : (FamilyFace.E n).slope 0 (-n) 0 0 = 0 := by
            rw [slope_of_X_ne (Ne.symm hmn0)]
            norm_num
          have hX3 : (FamilyFace.E n).addX 0 (-n) ((FamilyFace.E n).slope 0 (-n) 0 0)
              = n := by rw [addXAt, hsl]; ring
          constructor
          · rw [slotOneAt_some, hX3, if_neg hn.ne', slotOneAt_some, if_pos rfl,
              slotOneAt_some, if_neg hmn0]
            exact ⟨1 / n, one_div_ne_zero hn.ne', by field_simp⟩
          · rw [slotTwoAt_some, hX3, if_pos rfl, slotTwoAt_some, if_neg hn0,
              slotTwoAt_some, if_neg hmnn]
            exact ⟨1, one_ne_zero, by ring⟩
        · -- (n,0) + (0,0) lands at −n
          have h₁' : (FamilyFace.E n).Nonsingular n 0 := hA ▸ h₁
          have h₂' : (FamilyFace.E n).Nonsingular 0 0 := hB ▸ h₂
          rw [show (Point.some _ _ h₁ : (FamilyFace.E n).Point) = Point.some _ _ h₁' from
              someEqAt hA rfl,
            show (Point.some _ _ h₂ : (FamilyFace.E n).Point) = Point.some _ _ h₂' from
              someEqAt hB rfl, Point.add_of_X_ne hn.ne']
          have hsl : (FamilyFace.E n).slope n 0 0 0 = 0 := by
            rw [slope_of_X_ne hn.ne']
            norm_num
          have hX3 : (FamilyFace.E n).addX n 0 ((FamilyFace.E n).slope n 0 0 0)
              = -n := by rw [addXAt, hsl]; ring
          constructor
          · rw [slotOneAt_some, hX3, if_neg hmn0, slotOneAt_some, if_neg hn.ne',
              slotOneAt_some, if_pos rfl]
            exact ⟨1 / n, one_div_ne_zero hn.ne', by field_simp⟩
          · rw [slotTwoAt_some, hX3, if_neg hmnn, slotTwoAt_some, if_pos rfl,
              slotTwoAt_some, if_neg hn0]
            exact ⟨1 / n, one_div_ne_zero hn.ne', by field_simp; ring⟩
        · exact absurd (hA.trans hB.symm) hx
        · -- (n,0) + (−n,0) lands at 0
          have h₁' : (FamilyFace.E n).Nonsingular n 0 := hA ▸ h₁
          have h₂' : (FamilyFace.E n).Nonsingular (-n) 0 := hB ▸ h₂
          rw [show (Point.some _ _ h₁ : (FamilyFace.E n).Point) = Point.some _ _ h₁' from
              someEqAt hA rfl,
            show (Point.some _ _ h₂ : (FamilyFace.E n).Point) = Point.some _ _ h₂' from
              someEqAt hB rfl, Point.add_of_X_ne (Ne.symm hmnn)]
          have hsl : (FamilyFace.E n).slope n (-n) 0 0 = 0 := by
            rw [slope_of_X_ne (Ne.symm hmnn)]
            norm_num
          have hX3 : (FamilyFace.E n).addX n (-n) ((FamilyFace.E n).slope n (-n) 0 0)
              = 0 := by rw [addXAt, hsl]; ring
          constructor
          · rw [slotOneAt_some, hX3, if_pos rfl, slotOneAt_some, if_neg hn.ne',
              slotOneAt_some, if_neg hmn0]
            exact ⟨1, one_ne_zero, by ring⟩
          · rw [slotTwoAt_some, hX3, if_neg hn0, slotTwoAt_some, if_pos rfl,
              slotTwoAt_some, if_neg hmnn]
            exact ⟨1 / (2 * n), one_div_ne_zero h2n, by field_simp; ring⟩
        · -- (−n,0) + (0,0) lands at n
          have h₁' : (FamilyFace.E n).Nonsingular (-n) 0 := hA ▸ h₁
          have h₂' : (FamilyFace.E n).Nonsingular 0 0 := hB ▸ h₂
          rw [show (Point.some _ _ h₁ : (FamilyFace.E n).Point) = Point.some _ _ h₁' from
              someEqAt hA rfl,
            show (Point.some _ _ h₂ : (FamilyFace.E n).Point) = Point.some _ _ h₂' from
              someEqAt hB rfl, Point.add_of_X_ne hmn0]
          have hsl : (FamilyFace.E n).slope (-n) 0 0 0 = 0 := by
            rw [slope_of_X_ne hmn0]
            norm_num
          have hX3 : (FamilyFace.E n).addX (-n) 0 ((FamilyFace.E n).slope (-n) 0 0 0)
              = n := by rw [addXAt, hsl]; ring
          constructor
          · rw [slotOneAt_some, hX3, if_neg hn.ne', slotOneAt_some, if_neg hmn0,
              slotOneAt_some, if_pos rfl]
            exact ⟨1 / n, one_div_ne_zero hn.ne', by field_simp⟩
          · rw [slotTwoAt_some, hX3, if_pos rfl, slotTwoAt_some, if_neg hmnn,
              slotTwoAt_some, if_neg hn0]
            exact ⟨1, one_ne_zero, by ring⟩
        · -- (−n,0) + (n,0) lands at 0
          have h₁' : (FamilyFace.E n).Nonsingular (-n) 0 := hA ▸ h₁
          have h₂' : (FamilyFace.E n).Nonsingular n 0 := hB ▸ h₂
          rw [show (Point.some _ _ h₁ : (FamilyFace.E n).Point) = Point.some _ _ h₁' from
              someEqAt hA rfl,
            show (Point.some _ _ h₂ : (FamilyFace.E n).Point) = Point.some _ _ h₂' from
              someEqAt hB rfl, Point.add_of_X_ne hmnn]
          have hsl : (FamilyFace.E n).slope (-n) n 0 0 = 0 := by
            rw [slope_of_X_ne hmnn]
            norm_num
          have hX3 : (FamilyFace.E n).addX (-n) n ((FamilyFace.E n).slope (-n) n 0 0)
              = 0 := by rw [addXAt, hsl]; ring
          constructor
          · rw [slotOneAt_some, hX3, if_pos rfl, slotOneAt_some, if_neg hmn0,
              slotOneAt_some, if_neg hn.ne']
            exact ⟨1, one_ne_zero, by ring⟩
          · rw [slotTwoAt_some, hX3, if_neg hn0, slotTwoAt_some, if_neg hmnn,
              slotTwoAt_some, if_pos rfl]
            exact ⟨1 / (2 * n), one_div_ne_zero h2n, by field_simp; ring⟩
        · exact absurd (hA.trans hB.symm) hx
      · subst hy1
        obtain ⟨c1, c2⟩ := chordHalfTurnRightAt hn h₂ h₁ hy2 (Ne.symm hx)
        constructor
        · rw [add_comm, mul_comm]
          exact c1
        · rw [add_comm, mul_comm]
          exact c2
    · by_cases hy2 : y₂ = 0
      · subst hy2
        exact chordHalfTurnRightAt hn h₁ h₂ hy1 hx
      · -- the general chord, with its three landings
        have eA := onCurveAt h₁
        have eB := onCurveAt h₂
        obtain ⟨ha1, ha2, -⟩ := FaceHomomorphism.theNonzeroOrdinateAvoidsTheRoots eA hy1
        obtain ⟨hb1, hb2, -⟩ := FaceHomomorphism.theNonzeroOrdinateAvoidsTheRoots eB hy2
        rw [Point.add_of_X_ne hx]
        have hlam : (FamilyFace.E n).slope x₁ x₂ y₁ y₂ * (x₂ - x₁) = y₂ - y₁ :=
          slopeLineAt hx
        have hax := addXAt n x₁ x₂ ((FamilyFace.E n).slope x₁ x₂ y₁ y₂)
        have hs₁ : slotOneAt n (Point.some _ _ h₁) = x₁ := by
          rw [slotOneAt_some, if_neg ha1]
        have hs₂ : slotOneAt n (Point.some _ _ h₂) = x₂ := by
          rw [slotOneAt_some, if_neg hb1]
        have ht₁ : slotTwoAt n (Point.some _ _ h₁) = x₁ - n := by
          rw [slotTwoAt_some, if_neg ha2]
        have ht₂ : slotTwoAt n (Point.some _ _ h₂) = x₂ - n := by
          rw [slotTwoAt_some, if_neg hb2]
        rw [hs₁, hs₂, ht₁, ht₂]
        by_cases hX0 : (FamilyFace.E n).slope x₁ x₂ y₁ y₂ ^ 2 - x₁ - x₂ = 0
        · obtain ⟨-, c1, c2⟩ :=
            FaceHomomorphism.theChordLandsOnTheZeroHalfTurn hn.ne'
              eA eB hlam hx hy1 hy2 hX0
          constructor
          · rw [slotOneAt_some, hax, if_pos hX0,
              show (-n ^ 2 : ℚ) = n ^ 2 * -1 from by ring]
            exact sqcls_mul_sq_left c1 hn.ne'
          · rw [slotTwoAt_some, hax,
              if_neg (by rw [hX0]; exact fun hc => hn.ne' hc.symm), hX0,
              show (0 : ℚ) - n = -n from by ring]
            exact c2
        · by_cases hXn : (FamilyFace.E n).slope x₁ x₂ y₁ y₂ ^ 2 - x₁ - x₂ = n
          · obtain ⟨-, c1, c2⟩ :=
              FaceHomomorphism.theChordLandsOnTheSecondHalfTurn hn.ne'
                eA eB hlam hx hy1 hy2 hXn
            constructor
            · rw [slotOneAt_some, hax,
                if_neg (by rw [hXn]; exact hn.ne'), hXn]
              exact c1
            · rw [slotTwoAt_some, hax, if_pos hXn,
                show (2 * n ^ 2 : ℚ) = n ^ 2 * 2 from by ring]
              exact sqcls_mul_sq_left c2 hn.ne'
          · obtain ⟨c1, c2⟩ :=
              FaceHomomorphism.theChordLandsGenerically eA eB hlam hx hy1 hy2 hX0 hXn
            constructor
            · rw [slotOneAt_some, hax, if_neg hX0]
              exact c1
            · rw [slotTwoAt_some, hax, if_neg hXn]
              exact c2

end Soma.Holonics.Millennium.FamilyHom
