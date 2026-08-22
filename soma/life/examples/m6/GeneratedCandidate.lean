import ElementaryHolonics.Millennium.ChordFace
import ElementaryHolonics.Millennium.FaithfulFace

namespace Soma.Holonics.M6IndependentCandidate

set_option linter.unnecessarySeqFocus false

open WeierstrassCurve.Affine
open Soma.Holonics.Millennium

private theorem sqCls_of_eq_square_mul {a b c : ℚ} (hc : c ≠ 0)
    (h : a = c ^ 2 * b) : Descent.SqCls a b :=
  ⟨c, hc, h⟩

private theorem affine_curve {x y : ℚ} (h : Descent.E.Nonsingular x y) :
    y ^ 2 = x ^ 3 - x := by
  rw [WeierstrassCurve.Affine.nonsingular_iff,
    WeierstrassCurve.Affine.equation_iff] at h
  convert h.1 using 1 <;> simp [Descent.E] <;> ring

private theorem zero_ordinate_point {x y : ℚ} (h : Descent.E.Nonsingular x y) (hy : y = 0) :
    (Point.some h : Descent.E.Point) = Descent.P00 ∨
      (Point.some h : Descent.E.Point) = Descent.P10 ∨
      (Point.some h : Descent.E.Point) = Descent.Pm10 := by
  have hc := affine_curve h
  subst y
  have hz : x * (x - 1) * (x + 1) = 0 := by nlinarith [hc]
  rcases mul_eq_zero.mp hz with hroot | hroot
  · rcases mul_eq_zero.mp hroot with hroot | hroot
    · subst x
      exact Or.inl (by simp [Descent.P00])
    · have : x = 1 := sub_eq_zero.mp hroot
      subst x
      exact Or.inr (Or.inl (by simp [Descent.P10]))
  · have : x = -1 := by linarith
    subst x
    exact Or.inr (Or.inr (by simp [Descent.Pm10]))

private theorem half_turn_pair_closes {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : Descent.E.Nonsingular x₁ y₁) (h₂ : Descent.E.Nonsingular x₂ y₂)
    (hy₁ : y₁ = 0) (hy₂ : y₂ = 0) :
    Descent.SqCls (Descent.slotOne (Point.some h₁ + Point.some h₂))
        (Descent.slotOne (Point.some h₁) * Descent.slotOne (Point.some h₂)) ∧
      Descent.SqCls (Descent.slotTwo (Point.some h₁ + Point.some h₂))
        (Descent.slotTwo (Point.some h₁) * Descent.slotTwo (Point.some h₂)) := by
  rcases zero_ordinate_point h₁ hy₁ with hp | hp | hp <;>
    rcases zero_ordinate_point h₂ hy₂ with hq | hq | hq <;> rw [hp, hq]
  · exact Descent.theFaceIsMultiplicativeOnTheComputedPopulation.1
  · exact Descent.theFaceIsMultiplicativeOnTheComputedPopulation.2.2.1
  · exact Descent.theFaceIsMultiplicativeOnTheComputedPopulation.2.2.2.1
  · simpa [add_comm, mul_comm] using
      Descent.theFaceIsMultiplicativeOnTheComputedPopulation.2.2.1
  · exact Descent.theFaceIsMultiplicativeOnTheComputedPopulation.2.1
  · exact Descent.theFaceIsMultiplicativeOnTheComputedPopulation.2.2.2.2
  · simpa [add_comm, mul_comm] using
      Descent.theFaceIsMultiplicativeOnTheComputedPopulation.2.2.2.1
  · simpa [add_comm, mul_comm] using
      Descent.theFaceIsMultiplicativeOnTheComputedPopulation.2.2.2.2
  · obtain ⟨-, -, hhalf⟩ := Descent.theThreePointsAreHalfTurns
    obtain ⟨⟨e₁, e₂⟩, -, -, ⟨c₁, c₂⟩⟩ := Descent.theFourFaceValues
    rw [hhalf, e₁, e₂, c₁, c₂]
    exact ⟨⟨1, one_ne_zero, by norm_num⟩, ⟨1 / 2, by norm_num, by norm_num⟩⟩

private theorem half_turn_and_affine_closes {e z x y : ℚ}
    (hT : Descent.E.Nonsingular e z) (hP : Descent.E.Nonsingular x y)
    (hz : z = 0) (hy : y ≠ 0) :
    Descent.SqCls (Descent.slotOne (Point.some hT + Point.some hP))
        (Descent.slotOne (Point.some hT) * Descent.slotOne (Point.some hP)) ∧
      Descent.SqCls (Descent.slotTwo (Point.some hT + Point.some hP))
        (Descent.slotTwo (Point.some hT) * Descent.slotTwo (Point.some hP)) := by
  have hc := affine_curve hP
  obtain ⟨hx0, hx1, hxm1⟩ := FaithfulFace.theNonzeroOrdinateAvoidsTheThreeRoots hc hy
  obtain ⟨hn0, hn1, hnm1⟩ := FaithfulFace.theTranslatedPointIsNeverAHalfTurn hc hy
  have hall := FaithfulFace.theFaceLawClosesOnEveryHalfTurnTranslation hc hy
  rcases zero_ordinate_point hT hz with hp | hp | hp
  · rw [hp]
    simp only [Descent.P00]
    rw [add_comm,
      FaithfulFace.theTranslationIsTheGroupSum hP Descent.nonsingular00 hx0]
    simp only [Descent.slotOne, Descent.slotTwo]
    simp only [if_neg hn0.1, if_neg hn0.2.1, if_neg hx0, if_neg hx1]
    exact ⟨by simpa [Descent.P00, Descent.slotOne, mul_comm] using hall.1,
      by simpa [Descent.P00, Descent.slotTwo, mul_comm] using hall.2.1⟩
  · rw [hp]
    simp only [Descent.P10]
    rw [add_comm,
      FaithfulFace.theTranslationIsTheGroupSum hP Descent.nonsingular10 hx1]
    simp only [Descent.slotOne, Descent.slotTwo]
    simp only [if_neg hn1.1, if_neg hn1.2.1, if_neg hx0, if_neg hx1]
    exact ⟨by simpa [Descent.P10, Descent.slotOne, mul_comm] using hall.2.2.1,
      by simpa [Descent.P10, Descent.slotTwo, mul_comm] using hall.2.2.2.1⟩
  · rw [hp]
    simp only [Descent.Pm10]
    rw [add_comm,
      FaithfulFace.theTranslationIsTheGroupSum hP Descent.nonsingularNeg10 hxm1]
    simp only [Descent.slotOne, Descent.slotTwo]
    simp only [if_neg hnm1.1, if_neg hnm1.2.1, if_neg hx0, if_neg hx1]
    exact ⟨by simpa [Descent.Pm10, Descent.slotOne, mul_comm] using hall.2.2.2.2.1,
      by simpa [Descent.Pm10, Descent.slotTwo, mul_comm] using hall.2.2.2.2.2⟩

private theorem non_torsion_secant_closes {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : Descent.E.Nonsingular x₁ y₁) (h₂ : Descent.E.Nonsingular x₂ y₂)
    (hx : x₁ ≠ x₂) (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) :
    Descent.SqCls (Descent.slotOne (Point.some h₁ + Point.some h₂))
        (Descent.slotOne (Point.some h₁) * Descent.slotOne (Point.some h₂)) ∧
      Descent.SqCls (Descent.slotTwo (Point.some h₁ + Point.some h₂))
        (Descent.slotTwo (Point.some h₁) * Descent.slotTwo (Point.some h₂)) := by
  have hc₁ := affine_curve h₁
  have hc₂ := affine_curve h₂
  obtain ⟨hx₁0, hx₁1, hx₁m1⟩ :=
    FaithfulFace.theNonzeroOrdinateAvoidsTheThreeRoots hc₁ hy₁
  obtain ⟨hx₂0, hx₂1, -⟩ :=
    FaithfulFace.theNonzeroOrdinateAvoidsTheThreeRoots hc₂ hy₂
  let lam := Descent.E.slope x₁ x₂ y₁ y₂
  let x₃ := lam ^ 2 - x₁ - x₂
  have hlam : lam * (x₂ - x₁) = y₂ - y₁ := by
    dsimp [lam]
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
    field_simp [sub_ne_zero.mpr hx]
    ring
  have haddX : Descent.E.addX x₁ x₂ lam = x₃ := by
    simp [x₃, WeierstrassCurve.Affine.addX, Descent.E]
  have hc₁n : y₁ ^ 2 = x₁ ^ 3 - (1 : ℚ) ^ 2 * x₁ := by simpa using hc₁
  have hc₂n : y₂ ^ 2 = x₂ ^ 3 - (1 : ℚ) ^ 2 * x₂ := by simpa using hc₂
  have hslots := ChordFace.theChordClosesTheSlots
    (n := (1 : ℚ)) (lam := lam) hc₁n hc₂n hlam hx
  have hslot₀ : x₁ * x₂ * x₃ = (y₁ - lam * x₁) ^ 2 := by
    simpa [x₃] using hslots.1
  have hslot₁ : (x₁ - 1) * (x₂ - 1) * (x₃ - 1) =
      (lam + (y₁ - lam * x₁)) ^ 2 := by
    simpa [x₃] using hslots.2.1
  simp only [WeierstrassCurve.Affine.Point.add_of_X_ne hx,
    Descent.slotOne, Descent.slotTwo]
  rw [show Descent.E.addX x₁ x₂ (Descent.E.slope x₁ x₂ y₁ y₂) = x₃ by
    simpa [lam] using haddX]
  by_cases hx₃0 : x₃ = 0
  · have hx₃1 : x₃ ≠ 1 := by linarith
    simp only [if_pos hx₃0, if_neg hx₃1, if_neg hx₁0, if_neg hx₁1,
      if_neg hx₂0, if_neg hx₂1]
    simp only [hx₃0, zero_sub]
    have hb : y₁ - lam * x₁ = 0 := by
      apply sq_eq_zero_iff.mp
      rw [← hslot₀, hx₃0]
      ring
    have hyline : y₁ = lam * x₁ := by linarith
    have hpoly : lam ^ 2 * x₁ - x₁ ^ 2 + 1 = 0 := by
      have hfactor : x₁ * (lam ^ 2 * x₁ - x₁ ^ 2 + 1) = 0 := by
        rw [hyline] at hc₁
        nlinarith [hc₁]
      rcases mul_eq_zero.mp hfactor with hzero | hzero
      · exact (hx₁0 hzero).elim
      · exact hzero
    have hsum : lam ^ 2 - x₁ - x₂ = 0 := by simpa [x₃] using hx₃0
    have hprod : x₁ * x₂ = -1 := by
      linear_combination hpoly - x₁ * hsum
    have hprod₁ : (x₁ - 1) * (x₂ - 1) = -(lam ^ 2) := by
      linear_combination hprod + hsum
    have hlam0 : lam ≠ 0 := by
      intro hzero
      have hsquare : x₁ ^ 2 = 1 := by
        rw [hzero] at hsum
        nlinarith [hsum, hprod]
      have hfactor : (x₁ - 1) * (x₁ + 1) = 0 := by nlinarith [hsquare]
      rcases mul_eq_zero.mp hfactor with hroot | hroot
      · exact hx₁1 (sub_eq_zero.mp hroot)
      · exact hx₁m1 (by linarith)
    constructor
    · exact sqCls_of_eq_square_mul one_ne_zero (by rw [hprod]; norm_num)
    · refine sqCls_of_eq_square_mul (div_ne_zero one_ne_zero hlam0) ?_
      rw [hprod₁]
      field_simp
  · by_cases hx₃1 : x₃ = 1
    · simp only [if_neg hx₃0, if_pos hx₃1, if_neg hx₁0, if_neg hx₁1,
        if_neg hx₂0, if_neg hx₂1]
      simp only [hx₃1]
      have hsum : lam ^ 2 - x₁ - x₂ = 1 := by simpa [x₃] using hx₃1
      have hprod : x₁ * x₂ = (y₁ - lam * x₁) ^ 2 := by
        simpa [hx₃1] using hslot₀
      have hb : y₁ - lam * x₁ ≠ 0 := by
        intro hzero
        have : x₁ * x₂ = 0 := by rw [hprod, hzero]; norm_num
        exact (mul_ne_zero hx₁0 hx₂0) this
      have hland : lam + (y₁ - lam * x₁) = 0 := by
        apply sq_eq_zero_iff.mp
        rw [← hslot₁, hx₃1]
        ring
      have hprod_lam : x₁ * x₂ = lam ^ 2 := by
        rw [hprod]
        have hbneg : y₁ - lam * x₁ = -lam := by linarith [hland]
        rw [hbneg]
        ring
      have hprod₁ : (x₁ - 1) * (x₂ - 1) = 2 := by
        linear_combination hprod_lam + hsum
      constructor
      · refine sqCls_of_eq_square_mul (div_ne_zero one_ne_zero hb) ?_
        rw [hprod]
        field_simp
      · exact sqCls_of_eq_square_mul one_ne_zero (by rw [hprod₁]; norm_num)
    · simp only [if_neg hx₃0, if_neg hx₃1, if_neg hx₁0, if_neg hx₁1,
        if_neg hx₂0, if_neg hx₂1]
      have hz₁ : x₁ * x₂ ≠ 0 := mul_ne_zero hx₁0 hx₂0
      have hz₂ : (x₁ - 1) * (x₂ - 1) ≠ 0 :=
        mul_ne_zero (sub_ne_zero.mpr hx₁1) (sub_ne_zero.mpr hx₂1)
      have hb : y₁ - lam * x₁ ≠ 0 := by
        intro hzero
        have : x₁ * x₂ * x₃ = 0 := by rw [hslot₀, hzero]; norm_num
        exact (mul_ne_zero hz₁ hx₃0) this
      have hb₁ : lam + (y₁ - lam * x₁) ≠ 0 := by
        intro hzero
        have : (x₁ - 1) * (x₂ - 1) * (x₃ - 1) = 0 := by
          rw [hslot₁, hzero]
          norm_num
        exact (mul_ne_zero hz₂ (sub_ne_zero.mpr hx₃1)) this
      exact ChordFace.theChordClosesTheFaceGenerically
        (n := (1 : ℚ)) (lam := lam) hc₁n hc₂n hlam hx hz₁ hb hz₂
          (by simpa using hb₁)

theorem generatedFaceHomomorphism : Descent.TheFaceIsAHomomorphismEverywhere := by
  intro P Q
  rcases P with _ | @⟨x₁, y₁, h₁⟩
  · constructor
    · simpa [Descent.slotOne] using Descent.sqClsRefl (Descent.slotOne Q)
    · simpa [Descent.slotTwo] using Descent.sqClsRefl (Descent.slotTwo Q)
  rcases Q with _ | @⟨x₂, y₂, h₂⟩
  · constructor
    · simpa [Descent.slotOne] using Descent.sqClsRefl (Descent.slotOne (.some h₁))
    · simpa [Descent.slotTwo] using Descent.sqClsRefl (Descent.slotTwo (.some h₁))
  have hc₁ := affine_curve h₁
  have hc₂ := affine_curve h₂
  by_cases hx : x₁ = x₂
  · subst x₂
    by_cases hsame : y₁ = y₂
    · subst y₂
      by_cases hy₁ : y₁ = 0
      · subst y₁
        have hroot : x₁ = 0 ∨ x₁ = 1 ∨ x₁ = -1 := by
          have hz : x₁ * (x₁ - 1) * (x₁ + 1) = 0 := by nlinarith [hc₁]
          rcases mul_eq_zero.mp hz with h | h
          · rcases mul_eq_zero.mp h with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl (sub_eq_zero.mp h))
          · exact Or.inr (Or.inr (by linarith))
        rcases hroot with rfl | rfl | rfl
        · simpa [Descent.P00] using
            Descent.theFaceIsMultiplicativeOnTheComputedPopulation.1
        · simpa [Descent.P10] using
            Descent.theFaceIsMultiplicativeOnTheComputedPopulation.2.1
        · have hp : (Point.some h₁ : Descent.E.Point) = Descent.Pm10 := by
            simp [Descent.Pm10]
          rw [hp]
          obtain ⟨-, -, hhalf⟩ := Descent.theThreePointsAreHalfTurns
          obtain ⟨⟨e₁, e₂⟩, -, -, ⟨c₁, c₂⟩⟩ := Descent.theFourFaceValues
          rw [hhalf, e₁, e₂, c₁, c₂]
          exact ⟨⟨1, one_ne_zero, by norm_num⟩, ⟨1 / 2, by norm_num, by norm_num⟩⟩
      · have hneg : y₁ ≠ Descent.E.negY x₁ y₁ := by
          simpa [Descent.E, WeierstrassCurve.Affine.negY] using
            (show y₁ ≠ -y₁ by intro h; apply hy₁; linarith)
        rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg]
        obtain ⟨hx0, hx1, -⟩ := FaithfulFace.theNonzeroOrdinateAvoidsTheThreeRoots hc₁ hy₁
        obtain ⟨hd0, hd1, -⟩ := FaithfulFace.theDoubledPointIsNeverAHalfTurn hc₁ hy₁
        obtain ⟨⟨c₁, hc₁n, hc₁eq⟩, ⟨c₂, hc₂n, hc₂eq⟩⟩ :=
          FaithfulFace.theDoubledSlotsAreTheTrivialClass hc₁ hy₁
        have hcoord := FaithfulFace.theTangentCoordinateIsMathlibsAddX x₁ y₁ hy₁
        simp only [Descent.slotOne, Descent.slotTwo]
        rw [hcoord]
        simp only [if_neg hd0, if_neg hd1, if_neg hx0, if_neg hx1]
        constructor
        · refine ⟨c₁ / x₁, div_ne_zero hc₁n hx0, ?_⟩
          rw [hc₁eq]
          field_simp
        · refine ⟨c₂ / (x₁ - 1), div_ne_zero hc₂n (sub_ne_zero.mpr hx1), ?_⟩
          rw [hc₂eq]
          field_simp [sub_ne_zero.mpr hx1]
    · have hneg : y₁ = -y₂ := by
        have hp : (y₁ - y₂) * (y₁ + y₂) = 0 := by nlinarith [hc₁, hc₂]
        rcases mul_eq_zero.mp hp with h | h
        · exact (hsame (sub_eq_zero.mp h)).elim
        · linarith
      have hy₁ : y₁ ≠ 0 := by
        intro h
        apply hsame
        rw [h] at hneg ⊢
        linarith
      obtain ⟨hx0, hx1, -⟩ := FaithfulFace.theNonzeroOrdinateAvoidsTheThreeRoots hc₁ hy₁
      rw [WeierstrassCurve.Affine.Point.add_of_Y_eq rfl (by simpa [Descent.E] using hneg)]
      simp only [Descent.slotOne, Descent.slotTwo]
      simp only [if_neg hx0, if_neg hx1]
      constructor
      · refine ⟨1 / x₁, div_ne_zero one_ne_zero hx0, ?_⟩
        field_simp
      · refine ⟨1 / (x₁ - 1), div_ne_zero one_ne_zero (sub_ne_zero.mpr hx1), ?_⟩
        field_simp [sub_ne_zero.mpr hx1]
  · by_cases hy₁ : y₁ = 0
    · by_cases hy₂ : y₂ = 0
      · exact half_turn_pair_closes h₁ h₂ hy₁ hy₂
      · exact half_turn_and_affine_closes h₁ h₂ hy₁ hy₂
    · by_cases hy₂ : y₂ = 0
      · simpa [add_comm, mul_comm] using
          half_turn_and_affine_closes h₂ h₁ hy₂ hy₁
      · exact non_torsion_secant_closes h₁ h₂ hx hy₁ hy₂

end Soma.Holonics.M6IndependentCandidate
