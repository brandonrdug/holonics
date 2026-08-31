import ElementaryHolonics.Millennium.FiveHalving
import ElementaryHolonics.Millennium.FaceHomomorphism
import ElementaryHolonics.Millennium.FiveTranslation
import Mathlib.Tactic

/-!
# FiveDescent: the Mordell–Weil group at five is finitely generated

**The descent assembly.**  Three measuring laws meet here: the face image is the
realized eight (`FaceImageFive`), the kernel of the face is the doubles
(`FiveHalving`), duplication grows the height quartically (`FiveHeight`) while
translation by a fixed representative grows it only quadratically
(`FiveTranslation`).  Together they contract: every point of height above the
threshold is `Q + Q + R` with `R` one of eight bounded representatives and `Q`
strictly lower — so the bounded-height points generate, they are finitely many, and

* **`theMordellWeilGroupIsFinitelyGenerated`** — `AddGroup.FG E₅(ℚ)`:
  a fully formal Mordell–Weil instance, with no input beyond this tree.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FiveDescent

open WeierstrassCurve.Affine
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.FiveHeight

/-! ## 1. Local plumbing -/

private lemma onCurveFive {x y : ℚ} (h : RankOne.E5.Nonsingular x y) :
    y ^ 2 = x ^ 3 - 25 * x := by
  have h1 := ((nonsingular_iff x y).mp h).1
  rw [equation_iff] at h1
  simp only [RankOne.E5] at h1
  linarith [h1]

private lemma negYFive (x y : ℚ) : RankOne.E5.negY x y = -y := by
  simp [negY, RankOne.E5]

private lemma someEqFive {x₁ y₁ x₂ y₂ : ℚ} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : RankOne.E5.Nonsingular x₁ y₁} {h₂ : RankOne.E5.Nonsingular x₂ y₂} :
    (Point.some _ _ h₁ : RankOne.E5.Point) = Point.some _ _ h₂ := by
  subst hx; subst hy; rfl

private lemma slotOne5_some {x y : ℚ} (h : RankOne.E5.Nonsingular x y) :
    RankOne.slotOne (.some _ _ h) = if x = 0 then -25 else x := rfl

private lemma slotTwo5_some {x y : ℚ} (h : RankOne.E5.Nonsingular x y) :
    RankOne.slotTwo (.some _ _ h) = if x = 5 then 50 else x - 5 := rfl

private lemma slotOne5_ne (P : RankOne.E5.Point) : RankOne.slotOne P ≠ 0 := by
  rcases P with _ | @⟨x, y, h⟩
  · exact one_ne_zero
  · rw [slotOne5_some]
    split_ifs with hx
    · norm_num
    · exact hx

private lemma slotTwo5_ne (P : RankOne.E5.Point) : RankOne.slotTwo P ≠ 0 := by
  rcases P with _ | @⟨x, y, h⟩
  · exact one_ne_zero
  · rw [slotTwo5_some]
    split_ifs with hx
    · norm_num
    · exact sub_ne_zero.mpr hx

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

private lemma sqcls_ne {a b : ℚ} (h : Descent.SqCls a b) (ha : a ≠ 0) : b ≠ 0 := by
  obtain ⟨c, hc, hv⟩ := h
  intro hb
  rw [hb, mul_zero] at hv
  exact ha hv

/-! ## 2. The point height -/

/-- The naive height of a point: the height of its abscissa, zero at the identity. -/
def pheight : RankOne.E5.Point → ℕ
  | .zero => 0
  | .some x _ _ => hgt x

private lemma pheight_zero : pheight (0 : RankOne.E5.Point) = 0 := rfl

private lemma pheight_some {x y : ℚ} (h : RankOne.E5.Nonsingular x y) :
    pheight (Point.some _ _ h) = hgt x := rfl

/-- A rational presented as an integer fraction inherits the fraction's height bound. -/
private lemma hgt_le_of_eq_div {q : ℚ} (A B : ℤ) (hB : B ≠ 0)
    (h : q = (A : ℚ) / (B : ℚ)) {N : ℕ} (hN : max A.natAbs B.natAbs ≤ N) :
    hgt q ≤ N :=
  h ▸ le_trans (FiveTranslation.hgt_div_le A B hB) hN

/-! ## 3. The contraction core -/

set_option maxHeartbeats 1000000 in
/-- **The contraction core**: a point whose translate `X − R` has trivial face and
quadratically bounded height is `Q + Q + R` with `Q` strictly lower, once the height
clears the threshold.  The halving converse supplies `Q`; duplication growth converts
the bound on `X − R` into contraction of `Q`. -/
private lemma contract_core (X R : RankOne.E5.Point)
    (h1 : Descent.SqCls (RankOne.slotOne (X - R)) 1)
    (h2 : Descent.SqCls (RankOne.slotTwo (X - R)) 1)
    (hb : pheight (X - R) ≤ 105800 * pheight X ^ 2)
    (hbig : 163000 < pheight X) :
    ∃ Q, X = Q + Q + R ∧ pheight Q < pheight X := by
  obtain ⟨Q, hQ⟩ := FiveHalving.theKernelIsTheDoublesAtFive (X - R) h1 h2
  refine ⟨Q, by rw [hQ]; abel, ?_⟩
  rcases Q with _ | @⟨u, v, hQns⟩
  · have h0 : pheight (Point.zero : RankOne.E5.Point) = 0 := rfl
    omega
  · have hcurveQ := onCurveFive hQns
    by_cases hv : v = 0
    · -- a half-turn: its abscissa is a root of the cubic
      rw [hv] at hcurveQ
      have h0 : u * (u - 5) * (u + 5) = 0 := by linear_combination -hcurveQ
      have h3 : u = 0 ∨ u = 5 ∨ u = -5 := by
        rcases mul_eq_zero.mp h0 with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl (by linarith))
        · exact Or.inr (Or.inr (by linarith))
      have hub : hgt u ≤ 5 := by
        rcases h3 with rfl | rfl | rfl
        · exact hgt_le_of_eq_div 0 1 one_ne_zero (by norm_num) (by decide)
        · exact hgt_le_of_eq_div 5 1 one_ne_zero (by norm_num) (by decide)
        · exact hgt_le_of_eq_div (-5) 1 one_ne_zero (by norm_num) (by decide)
      have hp : pheight (Point.some _ _ hQns) = hgt u := rfl
      omega
    · -- the tangent case: duplication growth meets the translation bound
      have hu0 : u ≠ 0 := by
        intro hc
        rw [hc] at hcurveQ
        apply hv
        nlinarith [hcurveQ]
      have hu25 : u ^ 2 ≠ 25 := by
        intro hc
        apply hv
        have hval : v ^ 2 = u * (u ^ 2 - 25) := by linear_combination hcurveQ
        rw [hc] at hval
        simp only [sub_self, mul_zero] at hval
        exact pow_eq_zero_iff two_ne_zero |>.mp hval
      have hyne : v ≠ RankOne.E5.negY u v := by
        rw [negYFive]
        intro hc
        exact hv (by linarith)
      have hQQ : (Point.some _ _ hQns : RankOne.E5.Point) + Point.some _ _ hQns =
          Point.some _ _ (nonsingular_add hQns hQns fun hxy => hyne hxy.right) :=
        Point.add_self_of_Y_ne hyne
      have hs : RankOne.E5.slope u u v v = (3 * u ^ 2 - 25) / (2 * v) := by
        rw [slope_of_Y_ne rfl hyne, negYFive]
        simp only [RankOne.E5]
        ring_nf
      have h2v : (2 : ℚ) * v ≠ 0 := mul_ne_zero two_ne_zero hv
      have hden : (4 : ℚ) * u * (u ^ 2 - 25) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num) hu0) (sub_ne_zero.mpr hu25)
      have h4v : ((2 : ℚ) * v) ^ 2 = 4 * u * (u ^ 2 - 25) := by
        linear_combination 4 * hcurveQ
      have hxdup : RankOne.E5.addX u u (RankOne.E5.slope u u v v)
          = (u ^ 2 + 25) ^ 2 / (4 * u * (u ^ 2 - 25)) := by
        calc RankOne.E5.addX u u (RankOne.E5.slope u u v v)
            = ((3 * u ^ 2 - 25) / (2 * v)) ^ 2 - u - u := by
              rw [hs]
              simp only [addX, RankOne.E5]
              ring
          _ = (u ^ 2 + 25) ^ 2 / (4 * u * (u ^ 2 - 25)) := by
              rw [div_pow, sub_sub]
              have e2 : (3 * u ^ 2 - 25) ^ 2 / (2 * v) ^ 2 - (u + u)
                  = ((3 * u ^ 2 - 25) ^ 2 - (u + u) * (2 * v) ^ 2) / (2 * v) ^ 2 := by
                rw [sub_div, mul_div_assoc, div_self (pow_ne_zero 2 h2v), mul_one]
              rw [e2, div_eq_div_iff (pow_ne_zero 2 h2v) hden]
              linear_combination (-36 * u ^ 4 + 600 * u ^ 2 - 2500) * hcurveQ
      have hpQQ : pheight ((Point.some _ _ hQns : RankOne.E5.Point) + Point.some _ _ hQns)
          = hgt ((u ^ 2 + 25) ^ 2 / (4 * u * (u ^ 2 - 25))) := by
        rw [hQQ]
        show hgt (RankOne.E5.addX u u (RankOne.E5.slope u u v v)) = _
        rw [hxdup]
      have hdup := theDuplicationGrowsTheHeight u hu0 hu25
      have hlink : pheight ((Point.some _ _ hQns : RankOne.E5.Point) + Point.some _ _ hQns)
          = pheight (X - R) := congrArg pheight hQ
      -- the assembled chain
      have hchain : hgt u ^ 4 ≤ 26450000000 * pheight X ^ 2 := by
        calc hgt u ^ 4
            ≤ 250000 * hgt ((u ^ 2 + 25) ^ 2 / (4 * u * (u ^ 2 - 25))) := hdup
          _ = 250000 * pheight (X - R) := by rw [← hpQQ, hlink]
          _ ≤ 250000 * (105800 * pheight X ^ 2) := Nat.mul_le_mul_left _ hb
          _ = 26450000000 * pheight X ^ 2 := by ring
      have hp : pheight (Point.some _ _ hQns) = hgt u := rfl
      rw [hp]
      by_contra hge
      push_neg at hge
      have hH2 : 26450000000 < pheight X ^ 2 := by
        have h1 : 163001 ≤ pheight X := by omega
        have h2 : 163001 ^ 2 ≤ pheight X ^ 2 := Nat.pow_le_pow_left h1 2
        have h3 : (163001 : ℕ) ^ 2 = 26569326001 := by norm_num
        omega
      have h4 : pheight X ^ 4 ≤ hgt u ^ 4 := Nat.pow_le_pow_left hge 4
      have h5 : 26450000000 * pheight X ^ 2 < pheight X ^ 2 * pheight X ^ 2 :=
        Nat.mul_lt_mul_of_lt_of_le hH2 (le_refl _) (by positivity)
      have h6 : pheight X ^ 2 * pheight X ^ 2 = pheight X ^ 4 := by ring
      omega

set_option maxHeartbeats 1000000 in
/-- **The descent at a finite representative**: a point of large height whose face
class matches the representative's is `Q + Q + R` with `Q` strictly lower.  The face
homomorphism cancels the class, the halving converse halves, and the chord bound
contracts. -/
private lemma descent_finite_rep {x y xk yk d₁ d₂ : ℚ}
    (hX : RankOne.E5.Nonsingular x y) (hRk : RankOne.E5.Nonsingular xk yk)
    (α β : ℤ) (hβ : 0 < β) (hxkv : xk = (α : ℚ) / (β : ℚ))
    (hLb : α.natAbs + 25 * β.natAbs ≤ 230) (hhk : hgt xk ≤ 45)
    (hfX1 : Descent.SqCls (RankOne.slotOne (Point.some _ _ hX)) d₁)
    (hfX2 : Descent.SqCls (RankOne.slotTwo (Point.some _ _ hX)) d₂)
    (hfR1 : Descent.SqCls (RankOne.slotOne (Point.some _ _ hRk)) d₁)
    (hfR2 : Descent.SqCls (RankOne.slotTwo (Point.some _ _ hRk)) d₂)
    (hbig : 163000 < pheight (Point.some _ _ hX)) :
    ∃ Q, (Point.some _ _ hX : RankOne.E5.Point) = Q + Q + Point.some _ _ hRk ∧
      pheight Q < pheight (Point.some _ _ hX) := by
  have hpx : pheight (Point.some _ _ hX) = hgt x := rfl
  have hxne : x ≠ xk := by
    intro hc
    have h1 : hgt x ≤ 45 := hc ▸ hhk
    omega
  -- the negated representative, as coordinates
  have hNk : RankOne.E5.Nonsingular xk (-yk) := by
    have h := (nonsingular_neg (x := xk) (y := yk)).mpr hRk
    rwa [negYFive] at h
  have hNeg : -(Point.some _ _ hRk : RankOne.E5.Point) = Point.some _ _ hNk := by
    rw [Point.neg_some]
    exact someEqFive rfl (negYFive xk yk)
  have hsub : (Point.some _ _ hX : RankOne.E5.Point) - Point.some _ _ hRk =
      Point.some _ _ hX + Point.some _ _ hNk := by
    rw [sub_eq_add_neg, hNeg]
  -- the face of the translate is trivial
  have hslN1 : RankOne.slotOne (Point.some _ _ hNk) = RankOne.slotOne (Point.some _ _ hRk) := rfl
  have hslN2 : RankOne.slotTwo (Point.some _ _ hNk) = RankOne.slotTwo (Point.some _ _ hRk) := rfl
  have hd₁ : d₁ ≠ 0 := sqcls_ne hfR1 (slotOne5_ne _)
  have hd₂ : d₂ ≠ 0 := sqcls_ne hfR2 (slotTwo5_ne _)
  obtain ⟨hom1, hom2⟩ :=
    FaceHomomorphism.theRankOneFaceIsAHomomorphismEverywhereHolds
      (Point.some _ _ hX) (Point.some _ _ hNk)
  have h1' : Descent.SqCls
      (RankOne.slotOne ((Point.some _ _ hX : RankOne.E5.Point) - Point.some _ _ hRk)) 1 := by
    rw [hsub]
    refine sqcls_trans hom1 ?_
    rw [hslN1]
    exact sqcls_trans (sqcls_mul hfX1 hfR1) ⟨d₁, hd₁, by ring⟩
  have h2' : Descent.SqCls
      (RankOne.slotTwo ((Point.some _ _ hX : RankOne.E5.Point) - Point.some _ _ hRk)) 1 := by
    rw [hsub]
    refine sqcls_trans hom2 ?_
    rw [hslN2]
    exact sqcls_trans (sqcls_mul hfX2 hfR2) ⟨d₂, hd₂, by ring⟩
  -- the chord bound on the translate's height
  have hb : pheight ((Point.some _ _ hX : RankOne.E5.Point) - Point.some _ _ hRk)
      ≤ 105800 * pheight (Point.some _ _ hX) ^ 2 := by
    rw [hsub, Point.add_of_X_ne hxne, hpx]
    show hgt (RankOne.E5.addX x xk (RankOne.E5.slope x xk y (-yk)))
      ≤ 105800 * hgt x ^ 2
    have harg : RankOne.E5.addX x xk (RankOne.E5.slope x xk y (-yk))
        = ((y + yk) / (x - xk)) ^ 2 - x - xk := by
      rw [slope_of_X_ne hxne]
      simp only [addX, RankOne.E5]
      ring
    rw [harg]
    have hch := FiveTranslation.theChordRootIsBounded x y xk yk α β hβ hxkv
      (onCurveFive hX) (onCurveFive hRk) hxne
    calc hgt (((y + yk) / (x - xk)) ^ 2 - x - xk)
        ≤ 2 * (α.natAbs + 25 * β.natAbs) ^ 2 * hgt x ^ 2 := hch
      _ ≤ 2 * 230 ^ 2 * hgt x ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul (le_refl 2) (Nat.pow_le_pow_left hLb 2))
            (le_refl _)
      _ = 105800 * hgt x ^ 2 := by norm_num
  exact contract_core (Point.some _ _ hX) (Point.some _ _ hRk) h1' h2' hb hbig

set_option maxHeartbeats 2000000 in
/-- **THE DESCENT STEP**: every point of height above the threshold is `Q + Q + R`
with `R` of height at most forty-five and `Q` strictly lower — the face image is the
realized eight, each class carries a bounded representative, and the contraction
runs through it. -/
theorem theDescentStep (X : RankOne.E5.Point) (hbig : 163000 < pheight X) :
    ∃ Q R : RankOne.E5.Point,
      pheight R ≤ 45 ∧ X = Q + Q + R ∧ pheight Q < pheight X := by
  rcases X with _ | @⟨x, y, hX⟩
  · have h0 : pheight (Point.zero : RankOne.E5.Point) = 0 := rfl
    omega
  obtain ⟨d₁, d₂, hreal, hf1, hf2⟩ :=
    FaceImageFive.theFaceImageAtFiveIsTheRealizedEight (Point.some _ _ hX)
  rcases hreal with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- class (1, 1): the identity representative
    have hb : pheight ((Point.some _ _ hX : RankOne.E5.Point) - 0)
        ≤ 105800 * pheight (Point.some _ _ hX) ^ 2 := by
      rw [sub_zero]
      have h1 : pheight (Point.some _ _ hX) ≤ pheight (Point.some _ _ hX) ^ 2 :=
        Nat.le_self_pow two_ne_zero _
      have h2 : pheight (Point.some _ _ hX) ^ 2 ≤ 105800 * pheight (Point.some _ _ hX) ^ 2 :=
        Nat.le_mul_of_pos_left _ (by norm_num)
      omega
    obtain ⟨Q, hQeq, hQlt⟩ := contract_core (Point.some _ _ hX) 0
      (by rw [sub_zero]; exact hf1) (by rw [sub_zero]; exact hf2) hb hbig
    exact ⟨Q, 0, Nat.zero_le 45, hQeq, hQlt⟩
  · -- class (1, 5): the representative (25/4, 75/8)
    have hns : RankOne.E5.Nonsingular (25/4) (75/8) := by
      rw [nonsingular_iff, equation_iff]; norm_num [RankOne.E5]
    have hR1 : Descent.SqCls (RankOne.slotOne (Point.some _ _ hns)) 1 := by
      rw [slotOne5_some, if_neg (by norm_num)]
      exact ⟨5/2, by norm_num, by norm_num⟩
    have hR2 : Descent.SqCls (RankOne.slotTwo (Point.some _ _ hns)) 5 := by
      rw [slotTwo5_some, if_neg (by norm_num)]
      exact ⟨1/2, by norm_num, by norm_num⟩
    have hhk : hgt ((25 : ℚ)/4) ≤ 45 :=
      hgt_le_of_eq_div 25 4 (by norm_num) (by norm_num) (by decide)
    obtain ⟨Q, hQeq, hQlt⟩ := descent_finite_rep hX hns 25 4 (by norm_num)
      (by norm_num) (by decide) hhk hf1 hf2 hR1 hR2 hbig
    exact ⟨Q, Point.some _ _ hns, hhk, hQeq, hQlt⟩
  · -- class (5, 2): the representative (5, 0)
    have hns : RankOne.E5.Nonsingular 5 0 := RankOne.nonsingular50
    have hR1 : Descent.SqCls (RankOne.slotOne (Point.some _ _ hns)) 5 := by
      rw [slotOne5_some, if_neg (by norm_num)]
      exact ⟨1, by norm_num, by norm_num⟩
    have hR2 : Descent.SqCls (RankOne.slotTwo (Point.some _ _ hns)) 2 := by
      rw [slotTwo5_some, if_pos rfl]
      exact ⟨5, by norm_num, by norm_num⟩
    have hhk : hgt ((5 : ℚ)) ≤ 45 :=
      hgt_le_of_eq_div 5 1 (by norm_num) (by norm_num) (by decide)
    obtain ⟨Q, hQeq, hQlt⟩ := descent_finite_rep hX hns 5 1 (by norm_num)
      (by norm_num) (by decide) hhk hf1 hf2 hR1 hR2 hbig
    exact ⟨Q, Point.some _ _ hns, hhk, hQeq, hQlt⟩
  · -- class (5, 10): the representative (45, 300)
    have hns : RankOne.E5.Nonsingular 45 300 := by
      rw [nonsingular_iff, equation_iff]; norm_num [RankOne.E5]
    have hR1 : Descent.SqCls (RankOne.slotOne (Point.some _ _ hns)) 5 := by
      rw [slotOne5_some, if_neg (by norm_num)]
      exact ⟨3, by norm_num, by norm_num⟩
    have hR2 : Descent.SqCls (RankOne.slotTwo (Point.some _ _ hns)) 10 := by
      rw [slotTwo5_some, if_neg (by norm_num)]
      exact ⟨2, by norm_num, by norm_num⟩
    have hhk : hgt ((45 : ℚ)) ≤ 45 :=
      hgt_le_of_eq_div 45 1 (by norm_num) (by norm_num) (by decide)
    obtain ⟨Q, hQeq, hQlt⟩ := descent_finite_rep hX hns 45 1 (by norm_num)
      (by norm_num) (by decide) hhk hf1 hf2 hR1 hR2 hbig
    exact ⟨Q, Point.some _ _ hns, hhk, hQeq, hQlt⟩
  · -- class (−1, −1): the representative (−4, 6)
    have hns : RankOne.E5.Nonsingular (-4) 6 := RankOne.nonsingularP
    have hR1 : Descent.SqCls (RankOne.slotOne (Point.some _ _ hns)) (-1) := by
      rw [slotOne5_some, if_neg (by norm_num)]
      exact ⟨2, by norm_num, by norm_num⟩
    have hR2 : Descent.SqCls (RankOne.slotTwo (Point.some _ _ hns)) (-1) := by
      rw [slotTwo5_some, if_neg (by norm_num)]
      exact ⟨3, by norm_num, by norm_num⟩
    have hhk : hgt ((-4 : ℚ)) ≤ 45 :=
      hgt_le_of_eq_div (-4) 1 (by norm_num) (by norm_num) (by decide)
    obtain ⟨Q, hQeq, hQlt⟩ := descent_finite_rep hX hns (-4) 1 (by norm_num)
      (by norm_num) (by decide) hhk hf1 hf2 hR1 hR2 hbig
    exact ⟨Q, Point.some _ _ hns, hhk, hQeq, hQlt⟩
  · -- class (−1, −5): the representative (0, 0)
    have hns : RankOne.E5.Nonsingular 0 0 := RankOne.nonsingular00
    have hR1 : Descent.SqCls (RankOne.slotOne (Point.some _ _ hns)) (-1) := by
      rw [slotOne5_some, if_pos rfl]
      exact ⟨5, by norm_num, by norm_num⟩
    have hR2 : Descent.SqCls (RankOne.slotTwo (Point.some _ _ hns)) (-5) := by
      rw [slotTwo5_some, if_neg (by norm_num)]
      exact ⟨1, by norm_num, by norm_num⟩
    have hhk : hgt ((0 : ℚ)) ≤ 45 :=
      hgt_le_of_eq_div 0 1 (by norm_num) (by norm_num) (by decide)
    obtain ⟨Q, hQeq, hQlt⟩ := descent_finite_rep hX hns 0 1 (by norm_num)
      (by norm_num) (by decide) hhk hf1 hf2 hR1 hR2 hbig
    exact ⟨Q, Point.some _ _ hns, hhk, hQeq, hQlt⟩
  · -- class (−5, −2): the representative (−5/9, 100/27)
    have hns : RankOne.E5.Nonsingular (-5/9) (100/27) := by
      rw [nonsingular_iff, equation_iff]; norm_num [RankOne.E5]
    have hR1 : Descent.SqCls (RankOne.slotOne (Point.some _ _ hns)) (-5) := by
      rw [slotOne5_some, if_neg (by norm_num)]
      exact ⟨1/3, by norm_num, by norm_num⟩
    have hR2 : Descent.SqCls (RankOne.slotTwo (Point.some _ _ hns)) (-2) := by
      rw [slotTwo5_some, if_neg (by norm_num)]
      exact ⟨5/3, by norm_num, by norm_num⟩
    have hhk : hgt ((-5 : ℚ)/9) ≤ 45 :=
      hgt_le_of_eq_div (-5) 9 (by norm_num) (by norm_num) (by decide)
    obtain ⟨Q, hQeq, hQlt⟩ := descent_finite_rep hX hns (-5) 9 (by norm_num)
      (by norm_num) (by decide) hhk hf1 hf2 hR1 hR2 hbig
    exact ⟨Q, Point.some _ _ hns, hhk, hQeq, hQlt⟩
  · -- class (−5, −10): the representative (−5, 0)
    have hns : RankOne.E5.Nonsingular (-5) 0 := RankOne.nonsingularNeg50
    have hR1 : Descent.SqCls (RankOne.slotOne (Point.some _ _ hns)) (-5) := by
      rw [slotOne5_some, if_neg (by norm_num)]
      exact ⟨1, by norm_num, by norm_num⟩
    have hR2 : Descent.SqCls (RankOne.slotTwo (Point.some _ _ hns)) (-10) := by
      rw [slotTwo5_some, if_neg (by norm_num)]
      exact ⟨1, by norm_num, by norm_num⟩
    have hhk : hgt ((-5 : ℚ)) ≤ 45 :=
      hgt_le_of_eq_div (-5) 1 (by norm_num) (by norm_num) (by decide)
    obtain ⟨Q, hQeq, hQlt⟩ := descent_finite_rep hX hns (-5) 1 (by norm_num)
      (by norm_num) (by decide) hhk hf1 hf2 hR1 hR2 hbig
    exact ⟨Q, Point.some _ _ hns, hhk, hQeq, hQlt⟩

/-! ## 4. The bounded-height points are finite -/

private def coords : RankOne.E5.Point → Option (ℚ × ℚ)
  | .zero => none
  | .some (x := x) (y := y) _ => some (x, y)

private lemma coords_injective : Function.Injective coords := by
  intro P Q h
  rcases P with _ | @⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | @⟨x₂, y₂, h₂⟩
  · rfl
  · exact absurd h (by simp [coords])
  · exact absurd h (by simp [coords])
  · simp only [coords, Option.some.injEq, Prod.mk.injEq] at h
    exact someEqFive h.1 h.2

/-- **The rationals of bounded height are finite.** -/
theorem theBoundedRationalsAreFinite (N : ℕ) : {q : ℚ | hgt q ≤ N}.Finite := by
  have himg : (fun q : ℚ => (q.num, (q.den : ℤ))) '' {q | hgt q ≤ N} ⊆
      Set.Icc (-(N : ℤ)) (N : ℤ) ×ˢ Set.Icc (0 : ℤ) (N : ℤ) := by
    rintro ⟨a, b⟩ ⟨q, hq, heq⟩
    have ha : q.num = a := congrArg Prod.fst heq
    have hb : (q.den : ℤ) = b := congrArg Prod.snd heq
    have h1 : q.num.natAbs ≤ N := le_trans (num_natAbs_le_hgt q) hq
    have h2 : q.den ≤ N := le_trans (den_le_hgt q) hq
    simp only [Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega
  have hinj : Set.InjOn (fun q : ℚ => (q.num, (q.den : ℤ))) {q | hgt q ≤ N} := by
    intro p _ q _ h
    simp only [Prod.mk.injEq] at h
    exact Rat.ext h.1 (by exact_mod_cast h.2)
  exact Set.Finite.of_finite_image
    (Set.Finite.subset ((Set.finite_Icc _ _).prod (Set.finite_Icc _ _)) himg) hinj

/-- **The bounded-height points are finite**: each admissible abscissa carries at most
two ordinates, through the curve equation. -/
theorem theBoundedHeightsAreFinite (N : ℕ) :
    {X : RankOne.E5.Point | pheight X ≤ N}.Finite := by
  have hpair : {p : ℚ × ℚ | hgt p.1 ≤ N ∧ p.2 ^ 2 = p.1 ^ 3 - 25 * p.1}.Finite := by
    have hsub : {p : ℚ × ℚ | hgt p.1 ≤ N ∧ p.2 ^ 2 = p.1 ^ 3 - 25 * p.1} ⊆
        ⋃ x ∈ {q : ℚ | hgt q ≤ N}, {x} ×ˢ {y : ℚ | y ^ 2 = x ^ 3 - 25 * x} := by
      rintro ⟨a, b⟩ ⟨h1, h2⟩
      simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff,
        Set.mem_setOf_eq]
      exact ⟨a, h1, rfl, h2⟩
    refine Set.Finite.subset (Set.Finite.biUnion (theBoundedRationalsAreFinite N)
      fun x _ => Set.Finite.prod (Set.finite_singleton x) ?_) hsub
    by_cases hex : ∃ y₀ : ℚ, y₀ ^ 2 = x ^ 3 - 25 * x
    · obtain ⟨y₀, hy₀⟩ := hex
      refine Set.Finite.subset ((Set.finite_singleton (-y₀)).insert y₀) ?_
      intro w hw
      simp only [Set.mem_setOf_eq] at hw
      have h0 : (w - y₀) * (w + y₀) = 0 := by linear_combination hw - hy₀
      rcases mul_eq_zero.mp h0 with h' | h'
      · left; linarith
      · right
        simp only [Set.mem_singleton_iff]
        linarith
    · refine Set.Finite.subset (Set.finite_empty) ?_
      intro w hw
      exact absurd ⟨w, hw⟩ hex
  have himg : coords '' {X : RankOne.E5.Point | pheight X ≤ N} ⊆
      insert none (Option.some ''
        {p : ℚ × ℚ | hgt p.1 ≤ N ∧ p.2 ^ 2 = p.1 ^ 3 - 25 * p.1}) := by
    rintro w ⟨P, hP, rfl⟩
    rcases P with _ | @⟨x, y, h⟩
    · exact Set.mem_insert _ _
    · refine Set.mem_insert_of_mem _ ⟨(x, y), ⟨hP, onCurveFive h⟩, rfl⟩
  exact Set.Finite.of_finite_image
    (Set.Finite.subset ((Set.Finite.image _ hpair).insert none) himg)
    coords_injective.injOn

/-! ## 5. The generation and the finite generation -/

/-- **The bounded-height points generate**: strong descent through the step. -/
theorem theBoundedHeightsGenerate :
    AddSubgroup.closure {X : RankOne.E5.Point | pheight X ≤ 163000} = ⊤ := by
  rw [eq_top_iff]
  intro X _
  have key : ∀ n (Y : RankOne.E5.Point), pheight Y ≤ n →
      Y ∈ AddSubgroup.closure {Z : RankOne.E5.Point | pheight Z ≤ 163000} := by
    intro n
    induction n with
    | zero =>
      intro Y hY
      exact AddSubgroup.subset_closure (by simp only [Set.mem_setOf_eq]; omega)
    | succ n ih =>
      intro Y hY
      by_cases hle : pheight Y ≤ 163000
      · exact AddSubgroup.subset_closure hle
      · obtain ⟨Q, R, hR45, hEq, hlt⟩ := theDescentStep Y (by omega)
        have hQmem := ih Q (by omega)
        have hRmem : R ∈ AddSubgroup.closure
            {Z : RankOne.E5.Point | pheight Z ≤ 163000} :=
          AddSubgroup.subset_closure (by simp only [Set.mem_setOf_eq]; omega)
        rw [hEq]
        exact AddSubgroup.add_mem _ (AddSubgroup.add_mem _ hQmem hQmem) hRmem
  exact key (pheight X) X le_rfl

/-- **THE MORDELL–WEIL GROUP AT FIVE IS FINITELY GENERATED**: the bounded-height
points are a finite generating set.  A fully formal Mordell–Weil instance. -/
theorem theMordellWeilGroupIsFinitelyGenerated : AddGroup.FG (RankOne.E5.Point) := by
  rw [AddGroup.fg_iff]
  exact ⟨{X : RankOne.E5.Point | pheight X ≤ 163000}, theBoundedHeightsGenerate,
    theBoundedHeightsAreFinite 163000⟩

end Soma.Holonics.Millennium.FiveDescent
