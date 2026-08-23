import ElementaryHolonics.Millennium.FamilySupport
import ElementaryHolonics.Millennium.FamilyHom
import ElementaryHolonics.Millennium.FamilyImage
import ElementaryHolonics.Millennium.FamilyHeight
import ElementaryHolonics.Millennium.FiveDescent
import Mathlib.Tactic

/-!
# FamilyMordell: the Mordell–Weil theorem at every modulus

**The family descent assembled.**  On every congruent-number curve `y² = x³ − n²x`
with `n ≥ 1`, the group of rational points is finitely generated:

* **`theMordellWeilTheoremAtEveryModulus`** — `AddGroup.FG (E_n(ℚ))`, at every
  modulus at once.

The assembly: the face image is finite (`FamilySupport`), so choosing one
representative per realized class gives a finite set of bounded height `H₀`; the
face homomorphism (`FamilyHom`) cancels a point's class against its
representative's, the exact kernel (`FamilyKernel`) halves the difference, and the
two growth laws (`FamilyHeight`) contract the half strictly below the point once
the height clears the threshold `16n⁶·C + 4n + H₀`.  Strong descent then generates
from the bounded-height points, which are finitely many.  The five-instance
Mordell–Weil theorem is this law read at `n = 5`.  Every `theorem` is discharged
and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyMordell

open WeierstrassCurve.Affine
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.FamilyKernel
open Soma.Holonics.Millennium.FiveHeight

variable {n : ℕ}

/-! ## 1. The point height at a modulus, and plumbing -/

/-- The naive height of a point at modulus `n`. -/
def pheightAt (n : ℕ) : (FamilyFace.E ((n : ℚ))).Point → ℕ
  | .zero => 0
  | .some (x := x) _ => hgt x

private lemma onCurveAt {m x y : ℚ} (h : (FamilyFace.E m).Nonsingular x y) :
    y ^ 2 = x ^ 3 - m ^ 2 * x := by
  have h1 := ((nonsingular_iff x y).mp h).1
  rw [equation_iff] at h1
  simp only [FamilyFace.E] at h1
  linarith [h1]

private lemma negYAt (m x y : ℚ) : (FamilyFace.E m).negY x y = -y := by
  simp [negY, FamilyFace.E]

private lemma someEqAt {m x₁ y₁ x₂ y₂ : ℚ} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : (FamilyFace.E m).Nonsingular x₁ y₁} {h₂ : (FamilyFace.E m).Nonsingular x₂ y₂} :
    (Point.some h₁ : (FamilyFace.E m).Point) = Point.some h₂ := by
  subst hx; subst hy; rfl

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

private lemma slotOneAt_ne (hn : 0 < n) (P : (FamilyFace.E ((n : ℚ))).Point) :
    slotOneAt ((n : ℚ)) P ≠ 0 := by
  rcases P with _ | @⟨x, y, h⟩
  · exact one_ne_zero
  · show (if x = 0 then -((n : ℚ)) ^ 2 else x) ≠ 0
    split_ifs with hx
    · have h1 : ((n : ℚ)) ≠ 0 := by exact_mod_cast hn.ne'
      exact neg_ne_zero.mpr (pow_ne_zero 2 h1)
    · exact hx

private lemma slotTwoAt_ne (hn : 0 < n) (P : (FamilyFace.E ((n : ℚ))).Point) :
    slotTwoAt ((n : ℚ)) P ≠ 0 := by
  rcases P with _ | @⟨x, y, h⟩
  · exact one_ne_zero
  · show (if x = (n : ℚ) then 2 * ((n : ℚ)) ^ 2 else x - (n : ℚ)) ≠ 0
    split_ifs with hx
    · have h1 : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
      positivity
    · exact sub_ne_zero.mpr hx

/-! ## 2. Same class means the difference is a double -/

private lemma sameClass_diff_double (hn : 0 < n)
    (X R : (FamilyFace.E ((n : ℚ))).Point) {d₁ d₂ : ℤ}
    (hX1 : Descent.SqCls (slotOneAt ((n : ℚ)) X) (d₁ : ℚ))
    (hX2 : Descent.SqCls (slotTwoAt ((n : ℚ)) X) (d₂ : ℚ))
    (hR1 : Descent.SqCls (slotOneAt ((n : ℚ)) R) (d₁ : ℚ))
    (hR2 : Descent.SqCls (slotTwoAt ((n : ℚ)) R) (d₂ : ℚ)) :
    ∃ Q : (FamilyFace.E ((n : ℚ))).Point, Q + Q = X - R := by
  have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  have hd₁ : (d₁ : ℚ) ≠ 0 := sqcls_ne hR1 (slotOneAt_ne hn R)
  have hd₂ : (d₂ : ℚ) ≠ 0 := sqcls_ne hR2 (slotTwoAt_ne hn R)
  have hs1 : slotOneAt ((n : ℚ)) (-R) = slotOneAt ((n : ℚ)) R := by
    rcases R with _ | @⟨x, y, h⟩
    · rw [← Point.zero_def, neg_zero]
    · rw [Point.neg_some]
      rfl
  have hs2 : slotTwoAt ((n : ℚ)) (-R) = slotTwoAt ((n : ℚ)) R := by
    rcases R with _ | @⟨x, y, h⟩
    · rw [← Point.zero_def, neg_zero]
    · rw [Point.neg_some]
      rfl
  obtain ⟨hom1, hom2⟩ :=
    FamilyHom.theFaceIsAHomomorphismAtEveryModulus ((n : ℚ)) hnq X (-R)
  rw [hs1, ← sub_eq_add_neg] at hom1
  rw [hs2, ← sub_eq_add_neg] at hom2
  have h1 : Descent.SqCls (slotOneAt ((n : ℚ)) (X - R)) 1 :=
    sqcls_trans hom1 (sqcls_trans (sqcls_mul hX1 hR1) ⟨(d₁ : ℚ), hd₁, by ring⟩)
  have h2 : Descent.SqCls (slotTwoAt ((n : ℚ)) (X - R)) 1 :=
    sqcls_trans hom2 (sqcls_trans (sqcls_mul hX2 hR2) ⟨(d₂ : ℚ), hd₂, by ring⟩)
  exact FamilyKernel.theKernelIsTheDoublesAtEveryModulus ((n : ℚ)) hnq (X - R) h1 h2

/-! ## 3. The contraction core -/

set_option maxHeartbeats 1000000 in
private lemma contract_core (hn : 0 < n) {C : ℕ} (hC : 0 < C)
    (X R : (FamilyFace.E ((n : ℚ))).Point)
    (hdouble : ∃ Q, Q + Q = X - R)
    (hb : pheightAt n (X - R) ≤ C * pheightAt n X ^ 2)
    (hbig : 16 * n ^ 6 * C + 4 * n < pheightAt n X) :
    ∃ Q, X = Q + Q + R ∧ pheightAt n Q < pheightAt n X := by
  obtain ⟨Q, hQ⟩ := hdouble
  refine ⟨Q, by rw [hQ]; abel, ?_⟩
  rcases Q with _ | @⟨u, v, hQns⟩
  · have h0 : pheightAt n (Point.zero : (FamilyFace.E ((n : ℚ))).Point) = 0 := rfl
    omega
  · have hcurveQ := onCurveAt hQns
    by_cases hv : v = 0
    · rw [hv] at hcurveQ
      have h0 : u * (u - (n : ℚ)) * (u + (n : ℚ)) = 0 := by linear_combination -hcurveQ
      have h3 : u = 0 ∨ u = (n : ℚ) ∨ u = -(n : ℚ) := by
        rcases mul_eq_zero.mp h0 with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl (by linarith))
        · exact Or.inr (Or.inr (by linarith))
      have hub : hgt u ≤ 4 * n := by
        have hcast : ((n : ℚ)) = ((n : ℤ) : ℚ) / ((1 : ℤ) : ℚ) := by
          push_cast
          ring
        have hcastm : (-(n : ℚ)) = ((-(n : ℤ) : ℤ) : ℚ) / ((1 : ℤ) : ℚ) := by
          push_cast
          ring
        rcases h3 with h' | h' | h'
        · rw [h']
          have h4 : hgt (0 : ℚ) = 1 := by unfold hgt; simp
          omega
        · rw [h']
          have h4 := FiveTranslation.hgt_div_le (n : ℤ) 1 one_ne_zero
          rw [← hcast] at h4
          simp only [Int.natAbs_natCast, Int.natAbs_one] at h4
          omega
        · rw [h']
          have h4 := FiveTranslation.hgt_div_le (-(n : ℤ)) 1 one_ne_zero
          rw [← hcastm] at h4
          simp only [Int.natAbs_neg, Int.natAbs_natCast, Int.natAbs_one] at h4
          omega
      have hp : pheightAt n (Point.some hQns) = hgt u := rfl
      omega
    · have hu0 : u ≠ 0 := by
        intro hc
        rw [hc] at hcurveQ
        apply hv
        nlinarith [hcurveQ]
      have hu25 : u ^ 2 ≠ ((n : ℚ)) ^ 2 := by
        intro hc
        apply hv
        have hval : v ^ 2 = u * (u ^ 2 - ((n : ℚ)) ^ 2) := by
          linear_combination hcurveQ
        rw [hc] at hval
        simp only [sub_self, mul_zero] at hval
        exact pow_eq_zero_iff two_ne_zero |>.mp hval
      have hyne : v ≠ (FamilyFace.E ((n : ℚ))).negY u v := by
        rw [negYAt]
        intro hc
        exact hv (by linarith)
      have hQQ : (Point.some hQns : (FamilyFace.E ((n : ℚ))).Point) + Point.some hQns =
          Point.some (nonsingular_add hQns hQns fun hxy => hyne hxy.right) :=
        Point.add_self_of_Y_ne hyne
      have hs : (FamilyFace.E ((n : ℚ))).slope u u v v
          = (3 * u ^ 2 - ((n : ℚ)) ^ 2) / (2 * v) := by
        rw [slope_of_Y_ne rfl hyne, negYAt]
        simp only [FamilyFace.E]
        ring_nf
      have h2v : (2 : ℚ) * v ≠ 0 := mul_ne_zero two_ne_zero hv
      have hden : (4 : ℚ) * u * (u ^ 2 - ((n : ℚ)) ^ 2) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num) hu0) (sub_ne_zero.mpr hu25)
      have h4v : ((2 : ℚ) * v) ^ 2 = 4 * u * (u ^ 2 - ((n : ℚ)) ^ 2) := by
        linear_combination 4 * hcurveQ
      have hxdup : (FamilyFace.E ((n : ℚ))).addX u u
            ((FamilyFace.E ((n : ℚ))).slope u u v v)
          = (u ^ 2 + ((n : ℚ)) ^ 2) ^ 2 / (4 * u * (u ^ 2 - ((n : ℚ)) ^ 2)) := by
        calc (FamilyFace.E ((n : ℚ))).addX u u ((FamilyFace.E ((n : ℚ))).slope u u v v)
            = ((3 * u ^ 2 - ((n : ℚ)) ^ 2) / (2 * v)) ^ 2 - u - u := by
              rw [hs]
              simp only [addX, FamilyFace.E]
              ring
          _ = (u ^ 2 + ((n : ℚ)) ^ 2) ^ 2 / (4 * u * (u ^ 2 - ((n : ℚ)) ^ 2)) := by
              rw [div_pow, sub_sub]
              have e2 : (3 * u ^ 2 - ((n : ℚ)) ^ 2) ^ 2 / (2 * v) ^ 2 - (u + u)
                  = ((3 * u ^ 2 - ((n : ℚ)) ^ 2) ^ 2 - (u + u) * (2 * v) ^ 2)
                      / (2 * v) ^ 2 := by
                rw [sub_div, mul_div_assoc, div_self (pow_ne_zero 2 h2v), mul_one]
              rw [e2, div_eq_div_iff (pow_ne_zero 2 h2v) hden]
              linear_combination
                (-36 * u ^ 4 + 24 * ((n : ℚ)) ^ 2 * u ^ 2 - 4 * ((n : ℚ)) ^ 4)
                  * hcurveQ
      have hpQQ : pheightAt n
            ((Point.some hQns : (FamilyFace.E ((n : ℚ))).Point) + Point.some hQns)
          = hgt ((u ^ 2 + ((n : ℚ)) ^ 2) ^ 2 / (4 * u * (u ^ 2 - ((n : ℚ)) ^ 2))) := by
        rw [hQQ]
        show hgt ((FamilyFace.E ((n : ℚ))).addX u u
          ((FamilyFace.E ((n : ℚ))).slope u u v v)) = _
        rw [hxdup]
      have hdup := FamilyHeight.theDuplicationGrowsTheHeightAtEveryModulus n hn u
        hu0 hu25
      have hlink : pheightAt n
            ((Point.some hQns : (FamilyFace.E ((n : ℚ))).Point) + Point.some hQns)
          = pheightAt n (X - R) := congrArg (pheightAt n) hQ
      have hchain : hgt u ^ 4 ≤ 16 * n ^ 6 * (C * pheightAt n X ^ 2) := by
        calc hgt u ^ 4
            ≤ 16 * n ^ 6 *
              hgt ((u ^ 2 + ((n : ℚ)) ^ 2) ^ 2 / (4 * u * (u ^ 2 - ((n : ℚ)) ^ 2))) :=
              hdup
          _ = 16 * n ^ 6 * pheightAt n (X - R) := by rw [← hpQQ, hlink]
          _ ≤ 16 * n ^ 6 * (C * pheightAt n X ^ 2) :=
              Nat.mul_le_mul_left _ hb
      have hp : pheightAt n (Point.some hQns) = hgt u := rfl
      rw [hp]
      by_contra hge
      push_neg at hge
      set H : ℕ := pheightAt n X with hH
      have hH1 : 1 ≤ H := by omega
      have hHle : H ≤ H ^ 2 := Nat.le_self_pow two_ne_zero H
      have hH2 : 16 * n ^ 6 * C < H ^ 2 := by omega
      have h4 : H ^ 4 ≤ hgt u ^ 4 := Nat.pow_le_pow_left hge 4
      have h5 : 16 * n ^ 6 * C * H ^ 2 < H ^ 2 * H ^ 2 :=
        Nat.mul_lt_mul_of_lt_of_le hH2 (le_refl _) (by positivity)
      have h6 : H ^ 2 * H ^ 2 = H ^ 4 := by ring
      have h7 : 16 * n ^ 6 * (C * H ^ 2) = 16 * n ^ 6 * C * H ^ 2 := by ring
      omega

/-! ## 4. The representatives -/

private def classOf (hn : 0 < n) (P : (FamilyFace.E ((n : ℚ))).Point) : ℤ × ℤ :=
  ((FamilySupport.theSlotClassesAreSupportedAtEveryModulus n hn P).choose,
   (FamilySupport.theSlotClassesAreSupportedAtEveryModulus n hn P).choose_spec.choose)

private lemma classOf_spec (hn : 0 < n) (P : (FamilyFace.E ((n : ℚ))).Point) :
    (classOf hn P).1 ≠ 0 ∧ (classOf hn P).2 ≠ 0 ∧
    (classOf hn P).1.natAbs ∣ 2 * n ∧ (classOf hn P).2.natAbs ∣ 2 * n ∧
    Descent.SqCls (slotOneAt ((n : ℚ)) P) (((classOf hn P).1 : ℤ) : ℚ) ∧
    Descent.SqCls (slotTwoAt ((n : ℚ)) P) (((classOf hn P).2 : ℤ) : ℚ) :=
  (FamilySupport.theSlotClassesAreSupportedAtEveryModulus n hn
    P).choose_spec.choose_spec

private lemma range_classOf_finite (hn : 0 < n) :
    (Set.range (classOf hn)).Finite := by
  have h2n : 0 < 2 * n := by omega
  refine Set.Finite.subset
    (Set.Finite.prod (Set.finite_Icc (-(2 * n : ℤ)) (2 * n))
      (Set.finite_Icc (-(2 * n : ℤ)) (2 * n))) ?_
  rintro c ⟨P, rfl⟩
  obtain ⟨h10, h20, h1d, h2d, -, -⟩ := classOf_spec hn P
  have hb1 : (classOf hn P).1.natAbs ≤ 2 * n := Nat.le_of_dvd h2n h1d
  have hb2 : (classOf hn P).2.natAbs ≤ 2 * n := Nat.le_of_dvd h2n h2d
  constructor
  · simp only [Set.mem_Icc]
    omega
  · simp only [Set.mem_Icc]
    omega

open Classical in
private def repOfClass (hn : 0 < n) (c : ℤ × ℤ) : (FamilyFace.E ((n : ℚ))).Point :=
  if hc : ∃ Y, classOf hn Y = c then hc.choose else 0

private lemma repOfClass_spec (hn : 0 < n) {c : ℤ × ℤ}
    (hc : ∃ Y, classOf hn Y = c) : classOf hn (repOfClass hn c) = c := by
  classical
  rw [repOfClass, dif_pos hc]
  exact hc.choose_spec

/-- The height ceiling of the chosen representatives. -/
private def H0 (hn : 0 < n) : ℕ :=
  (range_classOf_finite hn).toFinset.sup fun c => pheightAt n (repOfClass hn c)

private lemma rep_height_le (hn : 0 < n) {c : ℤ × ℤ}
    (hc : c ∈ Set.range (classOf hn)) :
    pheightAt n (repOfClass hn c) ≤ H0 hn := by
  unfold H0
  exact Finset.le_sup (f := fun c => pheightAt n (repOfClass hn c))
    ((range_classOf_finite hn).mem_toFinset.mpr hc)

/-- The chord constant of the modulus and its representatives. -/
private def CC (hn : 0 < n) : ℕ := 2 * ((1 + n ^ 2) * (H0 hn + 1)) ^ 2

private lemma CC_pos (hn : 0 < n) : 0 < CC hn := by
  unfold CC
  positivity

/-! ## 5. The descent step -/

set_option maxHeartbeats 2000000 in
private lemma descent_step (hn : 0 < n) (X : (FamilyFace.E ((n : ℚ))).Point)
    (hbig : 16 * n ^ 6 * CC hn + 4 * n + H0 hn < pheightAt n X) :
    ∃ Q R, pheightAt n R ≤ H0 hn ∧ X = Q + Q + R ∧
      pheightAt n Q < pheightAt n X := by
  set R : (FamilyFace.E ((n : ℚ))).Point := repOfClass hn (classOf hn X) with hR
  have hcR : classOf hn R = classOf hn X := repOfClass_spec hn ⟨X, rfl⟩
  have hRh : pheightAt n R ≤ H0 hn := rep_height_le hn ⟨X, rfl⟩
  obtain ⟨hX10, hX20, -, -, hX1, hX2⟩ := classOf_spec hn X
  obtain ⟨-, -, -, -, hR1, hR2⟩ := classOf_spec hn R
  rw [hcR] at hR1 hR2
  have hdouble : ∃ Q, Q + Q = X - R := sameClass_diff_double hn X R hX1 hX2 hR1 hR2
  -- the height bound on the translate
  have hb : pheightAt n (X - R) ≤ CC hn * pheightAt n X ^ 2 := by
    rcases hXz : X with _ | @⟨x, y, hXns⟩
    · exfalso
      rw [hXz] at hbig
      have h0 : pheightAt n (Point.zero : (FamilyFace.E ((n : ℚ))).Point) = 0 := rfl
      omega
    · have hpx : pheightAt n X = hgt x := by rw [hXz]; rfl
      rcases hRz : R with _ | @⟨xR, yR, hRns⟩
      · rw [← Point.zero_def, sub_zero]
        have h1 : hgt x ≤ hgt x ^ 2 := Nat.le_self_pow two_ne_zero _
        have h2 : hgt x ^ 2 ≤ CC hn * hgt x ^ 2 :=
          Nat.le_mul_of_pos_left _ (CC_pos hn)
        have hpx' : pheightAt n (Point.some hXns) = hgt x := rfl
        rw [hpx']
        omega
      · -- the finite representative: the family chord bound
        have hpR : pheightAt n R = hgt xR := by rw [hRz]; rfl
        have hxne : x ≠ xR := by
          intro hc
          rw [hc] at hpx
          omega
        have hb0 : (0 : ℤ) < (xR.den : ℤ) := by exact_mod_cast xR.den_pos
        have hxRv : xR = ((xR.num : ℤ) : ℚ) / ((xR.den : ℤ) : ℚ) := by
          exact_mod_cast (Rat.num_div_den xR).symm
        -- the negated representative
        have hNk : (FamilyFace.E ((n : ℚ))).Nonsingular xR (-yR) := by
          have h := (nonsingular_neg (x := xR) (y := yR)).mpr hRns
          rwa [negYAt] at h
        have hNeg : -(Point.some hRns : (FamilyFace.E ((n : ℚ))).Point)
            = Point.some hNk := by
          rw [Point.neg_some]
          exact someEqAt rfl (negYAt ((n : ℚ)) xR yR)
        have hsub : (Point.some hXns : (FamilyFace.E ((n : ℚ))).Point)
            - Point.some hRns = Point.some hXns + Point.some hNk := by
          rw [sub_eq_add_neg, hNeg]
        rw [hsub, Point.add_of_X_ne hxne]
        show hgt ((FamilyFace.E ((n : ℚ))).addX x xR
          ((FamilyFace.E ((n : ℚ))).slope x xR y (-yR)))
          ≤ CC hn * pheightAt n (Point.some hXns) ^ 2
        have harg : (FamilyFace.E ((n : ℚ))).addX x xR
            ((FamilyFace.E ((n : ℚ))).slope x xR y (-yR))
            = ((y + yR) / (x - xR)) ^ 2 - x - xR := by
          rw [slope_of_X_ne hxne]
          simp only [addX, FamilyFace.E]
          ring
        rw [harg]
        have hch := FamilyHeight.theChordRootIsBoundedAtEveryModulus n hn x y xR yR
          xR.num (xR.den : ℤ) hb0 hxRv (onCurveAt hXns) (onCurveAt hRns) hxne
        have hL : xR.num.natAbs + n ^ 2 * ((xR.den : ℤ)).natAbs
            ≤ (1 + n ^ 2) * (H0 hn + 1) := by
          have h1 : xR.num.natAbs ≤ hgt xR := num_natAbs_le_hgt xR
          have h2 : ((xR.den : ℤ)).natAbs ≤ hgt xR := by
            rw [Int.natAbs_natCast]
            exact den_le_hgt xR
          have h3 : hgt xR ≤ H0 hn := by omega
          calc xR.num.natAbs + n ^ 2 * ((xR.den : ℤ)).natAbs
              ≤ hgt xR + n ^ 2 * hgt xR := by
                have := Nat.mul_le_mul (le_refl (n ^ 2)) h2
                omega
            _ = (1 + n ^ 2) * hgt xR := by ring
            _ ≤ (1 + n ^ 2) * (H0 hn + 1) :=
                Nat.mul_le_mul (le_refl _) (by omega)
        calc hgt (((y + yR) / (x - xR)) ^ 2 - x - xR)
            ≤ 2 * (xR.num.natAbs + n ^ 2 * ((xR.den : ℤ)).natAbs) ^ 2 * hgt x ^ 2 :=
              hch
          _ ≤ 2 * ((1 + n ^ 2) * (H0 hn + 1)) ^ 2 * hgt x ^ 2 :=
              Nat.mul_le_mul (Nat.mul_le_mul (le_refl 2)
                (Nat.pow_le_pow_left hL 2)) (le_refl _)
          _ = CC hn * pheightAt n (Point.some hXns) ^ 2 := by
              unfold CC
              rw [show pheightAt n (Point.some hXns) = hgt x from rfl]
  obtain ⟨Q, hQeq, hQlt⟩ := contract_core hn (CC_pos hn) X R hdouble hb (by omega)
  exact ⟨Q, R, hRh, hQeq, hQlt⟩

/-! ## 6. The bounded-height points are finite -/

private def coordsAt : (FamilyFace.E ((n : ℚ))).Point → Option (ℚ × ℚ)
  | .zero => none
  | .some (x := x) (y := y) _ => some (x, y)

private lemma coordsAt_injective : Function.Injective (coordsAt (n := n)) := by
  intro P Q h
  rcases P with _ | @⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | @⟨x₂, y₂, h₂⟩
  · rfl
  · exact absurd h (by simp [coordsAt])
  · exact absurd h (by simp [coordsAt])
  · simp only [coordsAt, Option.some.injEq, Prod.mk.injEq] at h
    exact someEqAt h.1 h.2

private lemma bounded_heights_finite (hn : 0 < n) (N : ℕ) :
    {X : (FamilyFace.E ((n : ℚ))).Point | pheightAt n X ≤ N}.Finite := by
  have hpair : {p : ℚ × ℚ | hgt p.1 ≤ N ∧
      p.2 ^ 2 = p.1 ^ 3 - ((n : ℚ)) ^ 2 * p.1}.Finite := by
    have hsub : {p : ℚ × ℚ | hgt p.1 ≤ N ∧
        p.2 ^ 2 = p.1 ^ 3 - ((n : ℚ)) ^ 2 * p.1} ⊆
        ⋃ x ∈ {q : ℚ | hgt q ≤ N},
          {x} ×ˢ {y : ℚ | y ^ 2 = x ^ 3 - ((n : ℚ)) ^ 2 * x} := by
      rintro ⟨a, b⟩ ⟨h1, h2⟩
      simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff,
        Set.mem_setOf_eq]
      exact ⟨a, h1, rfl, h2⟩
    refine Set.Finite.subset (Set.Finite.biUnion
      (FiveDescent.theBoundedRationalsAreFinite N) fun x _ =>
        Set.Finite.prod (Set.finite_singleton x) ?_) hsub
    by_cases hex : ∃ y₀ : ℚ, y₀ ^ 2 = x ^ 3 - ((n : ℚ)) ^ 2 * x
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
    · refine Set.Finite.subset Set.finite_empty ?_
      intro w hw
      exact absurd ⟨w, hw⟩ hex
  have himg : coordsAt '' {X : (FamilyFace.E ((n : ℚ))).Point | pheightAt n X ≤ N} ⊆
      insert none (Option.some ''
        {p : ℚ × ℚ | hgt p.1 ≤ N ∧ p.2 ^ 2 = p.1 ^ 3 - ((n : ℚ)) ^ 2 * p.1}) := by
    rintro w ⟨P, hP, rfl⟩
    rcases P with _ | @⟨x, y, h⟩
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨(x, y), ⟨hP, onCurveAt h⟩, rfl⟩
  exact Set.Finite.of_finite_image
    (Set.Finite.subset ((Set.Finite.image _ hpair).insert none) himg)
    coordsAt_injective.injOn

/-! ## 7. The Mordell–Weil theorem at every modulus -/

/-- **THE MORDELL–WEIL THEOREM AT EVERY MODULUS**: on every congruent-number curve
`y² = x³ − n²x` with `n ≥ 1`, the group of rational points is finitely generated.
The five-instance theorem is this law read at `n = 5`. -/
theorem theMordellWeilTheoremAtEveryModulus (n : ℕ) (hn : 0 < n) :
    AddGroup.FG ((FamilyFace.E ((n : ℚ))).Point) := by
  set N₀ : ℕ := 16 * n ^ 6 * CC hn + 4 * n + H0 hn with hN₀
  rw [AddGroup.fg_iff]
  refine ⟨{X : (FamilyFace.E ((n : ℚ))).Point | pheightAt n X ≤ N₀}, ?_,
    bounded_heights_finite hn N₀⟩
  rw [eq_top_iff]
  intro X _
  have key : ∀ m (Y : (FamilyFace.E ((n : ℚ))).Point), pheightAt n Y ≤ m →
      Y ∈ AddSubgroup.closure
        {Z : (FamilyFace.E ((n : ℚ))).Point | pheightAt n Z ≤ N₀} := by
    intro m
    induction m with
    | zero =>
      intro Y hY
      exact AddSubgroup.subset_closure (by simp only [Set.mem_setOf_eq]; omega)
    | succ m ih =>
      intro Y hY
      by_cases hle : pheightAt n Y ≤ N₀
      · exact AddSubgroup.subset_closure hle
      · obtain ⟨Q, R, hRh, hEq, hlt⟩ := descent_step hn Y (by omega)
        have hQmem := ih Q (by omega)
        have hRmem : R ∈ AddSubgroup.closure
            {Z : (FamilyFace.E ((n : ℚ))).Point | pheightAt n Z ≤ N₀} :=
          AddSubgroup.subset_closure (by simp only [Set.mem_setOf_eq]; omega)
        rw [hEq]
        exact AddSubgroup.add_mem _ (AddSubgroup.add_mem _ hQmem hQmem) hRmem
  exact key (pheightAt n X) X le_rfl

end Soma.Holonics.Millennium.FamilyMordell
