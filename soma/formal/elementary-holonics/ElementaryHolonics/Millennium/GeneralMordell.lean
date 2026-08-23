import ElementaryHolonics.Millennium.GeneralHeight
import ElementaryHolonics.Millennium.GeneralCollision
import ElementaryHolonics.Millennium.UniversalBSD

/-!
# GeneralMordell: the descent assembled on every full-2-torsion curve

Every input the descent consumes is now a theorem on the two-parameter family:

* finite coset representatives — `GeneralCollision` (weak Mordell–Weil);
* the quartic law — `GeneralHeight.theDuplicationGrowsTheAbscissaHeight`;
* the quadratic law — `GeneralHeight.theChordRootIsBoundedOnEveryFullTwoTorsionCurve`.

This file assembles them.  The contraction is the whole content: above a computable
threshold, a point is a double plus a bounded representative, with the half strictly
shorter — so strong induction on height generates from the bounded points.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.GeneralMordell

open WeierstrassCurve.Affine
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.GeneralFace
open Soma.Holonics.Millennium.GeneralHeight
open Soma.Holonics.Millennium.FiveHeight
open Soma.Holonics.Millennium.GeneralCollision

variable {a b : ℤ}

/-! ## 1. The point height -/

/-- The height of a point: the height of its abscissa, with the identity at zero. -/
def pheight (a b : ℤ) : (E ((a : ℚ)) ((b : ℚ))).Point → ℕ
  | .zero => 0
  | .some (x := x) _ => hgt x

@[simp]
lemma pheight_zero : pheight a b 0 = 0 := rfl

lemma pheight_some {x y : ℚ} (h : (E ((a : ℚ)) ((b : ℚ))).Nonsingular x y) :
    pheight a b (.some h) = hgt x := rfl

/-! ## 2. The torsion abscissae are short -/

/-- The three two-torsion abscissae have height at most the coefficient size. -/
lemma torsion_abscissa_short {x y : ℚ}
    (h : (E ((a : ℚ)) ((b : ℚ))).Nonsingular x y) (hy : y = 0) :
    hgt x ≤ GeneralHeight.sizeOf a b := by
  have hcurve := onCurve h
  rw [hy] at hcurve
  have hroots : x * (x - (a : ℚ)) * (x - (b : ℚ)) = 0 := by linear_combination -hcurve
  have hx3 : x = 0 ∨ x = (a : ℚ) ∨ x = (b : ℚ) := by
    rcases mul_eq_zero.mp hroots with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact Or.inl h''
      · exact Or.inr (Or.inl (by linarith [sub_eq_zero.mp h'']))
    · exact Or.inr (Or.inr (by linarith [sub_eq_zero.mp h']))
  have hD : 1 ≤ GeneralHeight.sizeOf a b := one_le_sizeOf a b
  rcases hx3 with h' | h' | h'
  · rw [h']
    have : hgt (0 : ℚ) = 1 := by unfold hgt; simp
    omega
  · rw [h']
    have hz : ((a : ℤ) : ℚ) = ((a : ℤ) : ℚ) / ((1 : ℤ) : ℚ) := by push_cast; ring
    have h4 := FiveTranslation.hgt_div_le (a : ℤ) 1 one_ne_zero
    rw [← hz] at h4
    simp only [Int.natAbs_one] at h4
    unfold GeneralHeight.sizeOf
    omega
  · rw [h']
    have hz : ((b : ℤ) : ℚ) = ((b : ℤ) : ℚ) / ((1 : ℤ) : ℚ) := by push_cast; ring
    have h4 := FiveTranslation.hgt_div_le (b : ℤ) 1 one_ne_zero
    rw [← hz] at h4
    simp only [Int.natAbs_one] at h4
    unfold GeneralHeight.sizeOf
    omega


/-! ## 3. The doubled point's height, read through the certified quotient -/

lemma double_height {x y : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0)
    (h : (E ((a : ℚ)) ((b : ℚ))).Nonsingular x y) (hy : y ≠ 0) :
    pheight a b ((Point.some h : (E ((a : ℚ)) ((b : ℚ))).Point) + Point.some h)
      = hgt ((x ^ 2 - (a : ℚ) * (b : ℚ)) ^ 2
          / (2 ^ 2 * (x * (x - (a : ℚ)) * (x - (b : ℚ))))) := by
  have hyne : y ≠ (E ((a : ℚ)) ((b : ℚ))).negY x y := by
    simp only [negY, E]
    intro hc
    exact hy (by linarith)
  rw [Point.add_self_of_Y_ne hyne]
  show hgt ((E ((a : ℚ)) ((b : ℚ))).addX x x
    ((E ((a : ℚ)) ((b : ℚ))).slope x x y y)) = _
  rw [GeneralCertificate.theDoubledAbscissaIsTheCertifiedQuotient h hy]
  norm_num

/-- The doubled abscissa is the certified quotient in the `numA`/`denB` shape.  Both
sides clear by `q⁴`, so the identity is the two homogenizations agreeing. -/
lemma certified_quotient_eq {u : ℚ} (hu : u ≠ 0)
    (hua : u - (a : ℚ) ≠ 0) (hub : u - (b : ℚ) ≠ 0) :
    (u ^ 2 - (a : ℚ) * (b : ℚ)) ^ 2
        / (2 ^ 2 * (u * (u - (a : ℚ)) * (u - (b : ℚ))))
      = ((numA a b u.num (u.den : ℤ) : ℤ) : ℚ)
        / ((denB a b u.num (u.den : ℤ) : ℤ) : ℚ) := by
  set p : ℤ := u.num with hp
  set q : ℤ := (u.den : ℤ) with hq
  have hq0 : ((q : ℤ) : ℚ) ≠ 0 := by
    rw [hq]
    exact_mod_cast (Nat.cast_ne_zero (R := ℚ)).mpr u.den_nz
  have hu_eq : u * ((q : ℤ) : ℚ) = ((p : ℤ) : ℚ) := by
    rw [hp, hq]
    exact_mod_cast Rat.mul_den_eq_num u
  have h1 : ((numA a b p q : ℤ) : ℚ)
      = (u ^ 2 - (a : ℚ) * (b : ℚ)) ^ 2 * ((q : ℤ) : ℚ) ^ 4 := by
    unfold numA
    push_cast
    rw [← hu_eq]
    ring
  have h2 : ((denB a b p q : ℤ) : ℚ)
      = 2 ^ 2 * (u * (u - (a : ℚ)) * (u - (b : ℚ))) * ((q : ℤ) : ℚ) ^ 4 := by
    unfold denB
    push_cast
    rw [← hu_eq]
    ring
  rw [h1, h2]
  rw [mul_div_mul_right _ _ (pow_ne_zero 4 hq0)]

/-- The denominator is nonzero exactly off the two-torsion. -/
lemma denB_ne_zero {u : ℚ} (hu : u ≠ 0) (hua : u - (a : ℚ) ≠ 0)
    (hub : u - (b : ℚ) ≠ 0) : ((denB a b u.num (u.den : ℤ) : ℤ) : ℚ) ≠ 0 := by
  set p : ℤ := u.num with hp
  set q : ℤ := (u.den : ℤ) with hq
  have hq0 : ((q : ℤ) : ℚ) ≠ 0 := by
    rw [hq]
    exact_mod_cast (Nat.cast_ne_zero (R := ℚ)).mpr u.den_nz
  have hu_eq : u * ((q : ℤ) : ℚ) = ((p : ℤ) : ℚ) := by
    rw [hp, hq]
    exact_mod_cast Rat.mul_den_eq_num u
  have h2 : ((denB a b p q : ℤ) : ℚ)
      = 2 ^ 2 * (u * (u - (a : ℚ)) * (u - (b : ℚ))) * ((q : ℤ) : ℚ) ^ 4 := by
    unfold denB
    push_cast
    rw [← hu_eq]
    ring
  rw [h2]
  exact mul_ne_zero (mul_ne_zero (by norm_num)
    (mul_ne_zero (mul_ne_zero hu hua) hub)) (pow_ne_zero 4 hq0)


/-! ## 4. The exceptional fibre `u² = ab`, bounded directly

Sol's decomposition: the assembly must retain two exceptional fibres rather than
hiding them in a totalized division.  The two-torsion fibre is bounded by
`torsion_abscissa_short`; this one — where the doubled abscissa's numerator vanishes —
is bounded as a **rational root of the integral quadratic `z² − ab = 0`**, with no
reference to the doubling law at all. -/

/-- A rational root of `z² = c` for an integer `c` is an **integer**, of height at
most `|c| + 1`.  Coprimality does it: clearing denominators gives `num² = c·den²`, so
`den²` divides `num²` while being coprime to it. -/
lemma rational_sqrt_short {c : ℤ} {u : ℚ} (hu : u ^ 2 = (c : ℚ)) :
    hgt u ≤ c.natAbs + 1 := by
  have hden0 : ((u.den : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero (R := ℚ)).mpr u.den_nz
  have hnumden : u * ((u.den : ℤ) : ℚ) = ((u.num : ℤ) : ℚ) := by
    exact_mod_cast Rat.mul_den_eq_num u
  -- clear denominators
  have hclear : u.num ^ 2 = c * (u.den : ℤ) ^ 2 := by
    have h1 : ((u.num ^ 2 : ℤ) : ℚ) = ((c * (u.den : ℤ) ^ 2 : ℤ) : ℚ) := by
      rw [show ((u.num ^ 2 : ℤ) : ℚ) = (((u.num : ℤ) : ℚ)) ^ 2 from by push_cast; ring,
        ← hnumden]
      push_cast
      rw [mul_pow, hu]
    exact_mod_cast h1
  -- the denominator squared divides the numerator squared and is coprime to it
  have hdvd : u.den ^ 2 ∣ u.num.natAbs ^ 2 := by
    refine ⟨c.natAbs, ?_⟩
    have h1 : (u.num ^ 2).natAbs = (c * (u.den : ℤ) ^ 2).natAbs := by rw [hclear]
    rw [Int.natAbs_pow] at h1
    rw [h1, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    ring
  have hcop : Nat.Coprime (u.den ^ 2) (u.num.natAbs ^ 2) :=
    (Nat.Coprime.pow _ _ (u.reduced.symm))
  have hden1 : u.den = 1 := by
    have h1 : u.den ^ 2 = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
    nlinarith [u.den_pos]
  -- with denominator one the point is its numerator
  have hval : ((u.num : ℤ) : ℚ) = u := by
    conv_rhs => rw [← Rat.num_div_den u, hden1]
    push_cast
    ring
  have hnum : u.num ^ 2 = c := by rw [hclear, hden1]; ring
  have habs : u.num.natAbs ^ 2 = c.natAbs := by
    rw [← Int.natAbs_pow, hnum]
  have hle : u.num.natAbs ≤ c.natAbs := by
    nlinarith [Nat.zero_le u.num.natAbs, habs]
  unfold hgt
  rw [hden1]
  omega


/-! ## 5. The contraction core

Every point splits into exactly three fibres, and each is bounded by its own owner:

* the **two-torsion fibre** `y = 0`, bounded by `torsion_abscissa_short`;
* the **vanishing-numerator fibre** `u² = ab`, bounded by `rational_sqrt_short`;
* the **generic fibre**, where the certified quotient and the quartic law apply.

Nothing is hidden in a totalized division. -/

set_option maxHeartbeats 2000000 in
/-- **THE CONTRACTION**: if the double of `Q` has bounded height and `Q` itself is
long, the quartic law forces a contradiction — so a long point's half is short.  The
constant is explicit: `2⁷·D¹⁰·C` against the coefficient size. -/
theorem theContraction (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0)
    (Q : (E ((a : ℚ)) ((b : ℚ))).Point) {B : ℕ}
    (hdouble : pheight a b (Q + Q) ≤ B) :
    pheight a b Q ^ 4
      ≤ 2 ^ 7 * GeneralHeight.sizeOf a b ^ 10 * B
        + (GeneralHeight.sizeOf a b + (a * b).natAbs + 1) ^ 4 := by
  rcases Q with _ | @⟨u, v, hQ⟩
  · simp [pheight]
  · by_cases hv : v = 0
    · -- the two-torsion fibre
      have hshort := torsion_abscissa_short hQ hv
      have hp : pheight a b (Point.some hQ) = hgt u := rfl
      rw [hp]
      have h1 : hgt u ≤ GeneralHeight.sizeOf a b + (a * b).natAbs + 1 := by omega
      have h2 : hgt u ^ 4 ≤ (GeneralHeight.sizeOf a b + (a * b).natAbs + 1) ^ 4 :=
        Nat.pow_le_pow_left h1 4
      omega
    · have hcurve := onCurve hQ
      have hu0 : u ≠ 0 := by
        intro hc
        refine hv ?_
        rw [hc] at hcurve
        have : v ^ 2 = 0 := by rw [hcurve]; ring
        exact pow_eq_zero_iff two_ne_zero |>.mp this
      have hua : u - (a : ℚ) ≠ 0 := by
        intro hc
        refine hv ?_
        rw [hc, mul_zero, zero_mul] at hcurve
        exact pow_eq_zero_iff two_ne_zero |>.mp hcurve
      have hub : u - (b : ℚ) ≠ 0 := by
        intro hc
        refine hv ?_
        rw [hc, mul_zero] at hcurve
        exact pow_eq_zero_iff two_ne_zero |>.mp hcurve
      by_cases hnum : u ^ 2 - (a : ℚ) * (b : ℚ) = 0
      · -- the vanishing-numerator fibre, bounded as a rational square root
        have hsq : u ^ 2 = ((a * b : ℤ) : ℚ) := by
          push_cast
          linarith [hnum]
        have hshort := rational_sqrt_short hsq
        have hp : pheight a b (Point.some hQ) = hgt u := rfl
        rw [hp]
        have h1 : hgt u ≤ GeneralHeight.sizeOf a b + (a * b).natAbs + 1 := by omega
        have h2 : hgt u ^ 4 ≤ (GeneralHeight.sizeOf a b + (a * b).natAbs + 1) ^ 4 :=
          Nat.pow_le_pow_left h1 4
        omega
      · -- the generic fibre: the quartic law applies
        have hAne : numA a b u.num (u.den : ℤ) ≠ 0 := by
          intro hc
          refine hnum ?_
          have h1 : ((numA a b u.num (u.den : ℤ) : ℤ) : ℚ)
              = (u ^ 2 - (a : ℚ) * (b : ℚ)) ^ 2 * ((u.den : ℚ)) ^ 4 := by
            unfold numA
            push_cast
            have hnd : u * ((u.den : ℤ) : ℚ) = ((u.num : ℤ) : ℚ) := by
              exact_mod_cast Rat.mul_den_eq_num u
            push_cast at hnd
            rw [← hnd]
            ring
          rw [hc] at h1
          have hden0 : ((u.den : ℚ)) ≠ 0 := by
            exact_mod_cast u.den_nz
          have h2 : (u ^ 2 - (a : ℚ) * (b : ℚ)) ^ 2 * ((u.den : ℚ)) ^ 4 = 0 := by
            rw [← h1]
            norm_num
          rcases mul_eq_zero.mp h2 with h | h
          · exact pow_eq_zero_iff two_ne_zero |>.mp h
          · exact absurd (pow_eq_zero_iff (n := 4) (by norm_num) |>.mp h) hden0
        have hBne : denB a b u.num (u.den : ℤ) ≠ 0 := by
          intro hc
          refine denB_ne_zero hu0 hua hub ?_
          rw [hc]
          push_cast
          ring
        have hdup := GeneralHeight.theDuplicationGrowsTheAbscissaHeight a b ha hb hab u
          hAne hBne
        have hlink : hgt (((numA a b u.num (u.den : ℤ) : ℤ) : ℚ)
            / ((denB a b u.num (u.den : ℤ) : ℤ) : ℚ))
            = pheight a b (Point.some hQ + Point.some hQ) := by
          rw [double_height ha hb hab hQ hv, ← certified_quotient_eq hu0 hua hub]
        rw [hlink] at hdup
        have hp : pheight a b (Point.some hQ) = hgt u := rfl
        rw [hp]
        have hchain : hgt u ^ 4
            ≤ 2 ^ 7 * GeneralHeight.sizeOf a b ^ 10 * B := by
          refine le_trans hdup ?_
          exact Nat.mul_le_mul_left _ hdouble
        omega


/-! ## 6. The translate bound: the chord law applied to `X − R`

The shared-abscissa case is **excluded by the height threshold** rather than handled:
if `X` is longer than the representative then their abscissae differ, because equal
abscissae would give equal heights. -/

lemma neg_some_point {x y : ℚ} (h : (E ((a : ℚ)) ((b : ℚ))).Nonsingular x y)
    (h' : (E ((a : ℚ)) ((b : ℚ))).Nonsingular x (-y)) :
    -(Point.some h : (E ((a : ℚ)) ((b : ℚ))).Point) = Point.some h' := by
  rw [Point.neg_some]
  congr 1
  simp only [negY, E]
  ring

set_option maxHeartbeats 1000000 in
/-- **THE TRANSLATE IS BOUNDED QUADRATICALLY**: subtracting a fixed point grows the
height at most quadratically, with a constant depending only on that point and the
curve. -/
theorem theTranslateIsBoundedQuadratically (a b : ℤ) {xR yR : ℚ}
    (hR : (E ((a : ℚ)) ((b : ℚ))).Nonsingular xR yR)
    (X : (E ((a : ℚ)) ((b : ℚ))).Point) (hbig : hgt xR < pheight a b X) :
    pheight a b (X - Point.some hR)
      ≤ 2 ^ 4 * GeneralHeight.pointSize a b xR.num (xR.den : ℤ) ^ 6
          * pheight a b X ^ 2 := by
  rcases X with _ | @⟨x, y, hX⟩
  · exfalso
    have : pheight a b (0 : (E ((a : ℚ)) ((b : ℚ))).Point) = 0 := rfl
    have hpos := hgt_pos xR
    rw [← Point.zero_def] at hbig
    omega
  · have hpx : pheight a b (Point.some hX) = hgt x := rfl
    have hxne : x ≠ xR := by
      intro hc
      rw [hpx] at hbig
      rw [hc] at hbig
      omega
    -- the negated representative
    have hNk : (E ((a : ℚ)) ((b : ℚ))).Nonsingular xR (-yR) := by
      have h := (nonsingular_neg (W' := E ((a : ℚ)) ((b : ℚ))) (x := xR) (y := yR)).mpr hR
      have he : (E ((a : ℚ)) ((b : ℚ))).negY xR yR = -yR := by
        simp only [negY, E]; ring
      rwa [he] at h
    have hsub : (Point.some hX : (E ((a : ℚ)) ((b : ℚ))).Point) - Point.some hR
        = Point.some hX + Point.some hNk := by
      rw [sub_eq_add_neg, neg_some_point hR hNk]
    rw [hsub, Point.add_of_X_ne hxne]
    show hgt ((E ((a : ℚ)) ((b : ℚ))).addX x xR
      ((E ((a : ℚ)) ((b : ℚ))).slope x xR y (-yR))) ≤ _
    have harg : (E ((a : ℚ)) ((b : ℚ))).addX x xR
        ((E ((a : ℚ)) ((b : ℚ))).slope x xR y (-yR))
        = ((y + yR) / (x - xR)) ^ 2 + ((a : ℚ) + (b : ℚ)) - x - xR := by
      rw [slope_of_X_ne hxne]
      simp only [addX, E]
      have hd : x - xR ≠ 0 := sub_ne_zero.mpr hxne
      field_simp
      ring
    rw [harg, hpx]
    have hbe : (0 : ℤ) < (xR.den : ℤ) := by exact_mod_cast xR.den_pos
    have hxRv : xR = ((xR.num : ℤ) : ℚ) / (((xR.den : ℤ)) : ℚ) := by
      exact_mod_cast (Rat.num_div_den xR).symm
    exact GeneralHeight.theChordRootIsBoundedOnEveryFullTwoTorsionCurve a b hbe hxRv
      (onCurve hX) (onCurve hR) hxne


/-! ## 7. The finite class atlas and its representatives -/

variable (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0)

lemma range_classOf_finite (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0) :
    (Set.range (classOf ha hb hab)).Finite := by
  set K : ℕ := (a * b * (a - b)).natAbs with hK
  have hK0 : 0 < K := by
    rw [hK, Int.natAbs_pos]
    exact mul_ne_zero (mul_ne_zero ha hb) hab
  refine Set.Finite.subset
    (Set.Finite.prod (Set.finite_Icc (-(K : ℤ)) (K : ℤ))
      (Set.finite_Icc (-(K : ℤ)) (K : ℤ))) ?_
  rintro c ⟨P, rfl⟩
  obtain ⟨h10, h20, h1d, h2d, -, -⟩ := classOf_spec ha hb hab P
  have hb1 : (classOf ha hb hab P).1.natAbs ≤ K := Nat.le_of_dvd hK0 h1d
  have hb2 : (classOf ha hb hab P).2.natAbs ≤ K := Nat.le_of_dvd hK0 h2d
  constructor
  · simp only [Set.mem_Icc]; omega
  · simp only [Set.mem_Icc]; omega

open Classical in
/-- One chosen representative per realized class. -/
def repOfClass (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0) (c : ℤ × ℤ) :
    (E ((a : ℚ)) ((b : ℚ))).Point :=
  if hc : ∃ Y, classOf ha hb hab Y = c then hc.choose else 0

lemma repOfClass_spec (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0) {c : ℤ × ℤ}
    (hc : ∃ Y, classOf ha hb hab Y = c) :
    classOf ha hb hab (repOfClass ha hb hab c) = c := by
  classical
  rw [repOfClass, dif_pos hc]
  exact hc.choose_spec

/-- The height ceiling of the chosen representatives. -/
def H0 (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0) : ℕ :=
  (range_classOf_finite ha hb hab).toFinset.sup
    fun c => pheight a b (repOfClass ha hb hab c)

lemma rep_height_le (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0) {c : ℤ × ℤ}
    (hc : c ∈ Set.range (classOf ha hb hab)) :
    pheight a b (repOfClass ha hb hab c) ≤ H0 ha hb hab := by
  unfold H0
  exact Finset.le_sup (f := fun c => pheight a b (repOfClass ha hb hab c))
    ((range_classOf_finite ha hb hab).mem_toFinset.mpr hc)

/-- The chord constant of the curve and its chosen representatives. -/
def chordConst (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0) : ℕ :=
  2 ^ 4 * (2 * H0 ha hb hab + GeneralHeight.sizeOf a b) ^ 6

/-- The descent threshold: above it the contraction bites. -/
def threshold (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0) : ℕ :=
  2 ^ 7 * GeneralHeight.sizeOf a b ^ 10 * chordConst ha hb hab
    + (GeneralHeight.sizeOf a b + (a * b).natAbs + 1) ^ 4 + H0 ha hb hab


/-! ## 8. The descent step -/

private lemma sqT {u v w : ℚ} (h₁ : Descent.SqCls u v) (h₂ : Descent.SqCls v w) :
    Descent.SqCls u w := by
  obtain ⟨c, hc, hv⟩ := h₁
  obtain ⟨d, hd, hw⟩ := h₂
  exact ⟨c * d, mul_ne_zero hc hd, by rw [hv, hw]; ring⟩

private lemma sqS {u v : ℚ} (h : Descent.SqCls u v) (hu : u ≠ 0) :
    Descent.SqCls v u := by
  obtain ⟨c, hc, hv⟩ := h
  refine ⟨1 / c, one_div_ne_zero hc, ?_⟩
  rw [hv]
  field_simp


set_option maxHeartbeats 2000000 in
/-- **THE DESCENT STEP**: above the threshold, a point is twice a strictly shorter
point plus a bounded representative.  This is where quartic beats quadratic. -/
theorem theDescentStep (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0)
    (X : (E ((a : ℚ)) ((b : ℚ))).Point)
    (hbig : threshold ha hb hab < pheight a b X) :
    ∃ Q R, pheight a b R ≤ H0 ha hb hab ∧ X = Q + Q + R ∧
      pheight a b Q < pheight a b X := by
  have haq : ((a : ℚ)) ≠ 0 := by exact_mod_cast ha
  have hbq : ((b : ℚ)) ≠ 0 := by exact_mod_cast hb
  have habq : ((a : ℚ)) - ((b : ℚ)) ≠ 0 := by
    intro hc
    refine hab ?_
    have h1 : ((a : ℚ)) = ((b : ℚ)) := by linarith
    have h2 : (a : ℤ) = b := by exact_mod_cast h1
    exact sub_eq_zero_of_eq h2
  set R : (E ((a : ℚ)) ((b : ℚ))).Point :=
    repOfClass ha hb hab (classOf ha hb hab X) with hRdef
  have hcR : classOf ha hb hab R = classOf ha hb hab X :=
    repOfClass_spec ha hb hab ⟨X, rfl⟩
  have hRh : pheight a b R ≤ H0 ha hb hab := rep_height_le ha hb hab ⟨X, rfl⟩
  obtain ⟨-, -, -, -, hX1, hX2⟩ := classOf_spec ha hb hab X
  obtain ⟨-, -, -, -, hR1, hR2⟩ := classOf_spec ha hb hab R
  rw [hcR] at hR1 hR2
  -- the difference is a double
  have hs1 : Descent.SqCls (slotOne ((a : ℚ)) ((b : ℚ)) X)
      (slotOne ((a : ℚ)) ((b : ℚ)) R) := by
    exact sqT hX1 (sqS hR1 (GeneralHom.slotOne_ne haq hbq R))
  have hs2 : Descent.SqCls (slotTwo ((a : ℚ)) ((b : ℚ)) X)
      (slotTwo ((a : ℚ)) ((b : ℚ)) R) := by
    exact sqT hX2 (sqS hR2 (GeneralHom.slotTwo_ne haq habq R))
  obtain ⟨Q, hQ⟩ := sameClassDouble haq hbq habq X R hs1 hs2
  refine ⟨Q, R, hRh, by rw [← hQ]; abel, ?_⟩
  -- the translate is bounded quadratically, in both fibres of `R`
  have hchord1 : 1 ≤ chordConst ha hb hab := by
    unfold chordConst
    have h1 : 1 ≤ (2 * H0 ha hb hab + GeneralHeight.sizeOf a b) ^ 6 := by
      refine Nat.one_le_pow _ _ ?_
      have := GeneralHeight.one_le_sizeOf a b
      omega
    have h2 : 1 ≤ (2 : ℕ) ^ 4 := by norm_num
    nlinarith
  have hX1 : 1 ≤ pheight a b X := by
    unfold threshold at hbig
    omega
  have htrans : pheight a b (X - R)
      ≤ chordConst ha hb hab * pheight a b X ^ 2 := by
    rcases hRz : R with _ | @⟨xR, yR, hRns⟩
    · -- the identity representative: the translate is `X` itself
      rw [← Point.zero_def, sub_zero]
      have h1 : pheight a b X ≤ pheight a b X ^ 2 :=
        Nat.le_self_pow two_ne_zero _
      have h2 : pheight a b X ^ 2 ≤ chordConst ha hb hab * pheight a b X ^ 2 :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    · have hRval : pheight a b R = hgt xR := by rw [hRz]; rfl
      have hbigR : hgt xR < pheight a b X := by
        unfold threshold at hbig
        omega
      refine le_trans (theTranslateIsBoundedQuadratically a b hRns X hbigR) ?_
      refine Nat.mul_le_mul_right _ ?_
      unfold chordConst
      refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 6)
      unfold GeneralHeight.pointSize
      have h1 : xR.num.natAbs ≤ hgt xR := num_natAbs_le_hgt xR
      have h2 : ((xR.den : ℤ)).natAbs ≤ hgt xR := by
        rw [Int.natAbs_natCast]
        exact den_le_hgt xR
      have h3 : hgt xR ≤ H0 ha hb hab := by omega
      unfold GeneralHeight.sizeOf
      omega
  -- the contraction
  have hdouble : pheight a b (Q + Q) ≤ chordConst ha hb hab * pheight a b X ^ 2 := by
    rw [← hQ]
    exact htrans
  have hcon := theContraction ha hb hab Q hdouble
  -- quartic beats quadratic above the threshold
  set H : ℕ := pheight a b X with hH
  set D : ℕ := GeneralHeight.sizeOf a b with hD
  set T : ℕ := 2 ^ 7 * D ^ 10 * chordConst ha hb hab with hT
  set S : ℕ := (D + (a * b).natAbs + 1) ^ 4 with hS
  have hHbig : T + S + H0 ha hb hab < H := by
    unfold threshold at hbig
    exact hbig
  have hH1 : 1 ≤ H := by omega
  have hH2 : 1 ≤ H ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hstep : pheight a b Q ^ 4 ≤ T * H ^ 2 + S := by
    rw [hT, hS]
    calc pheight a b Q ^ 4
        ≤ 2 ^ 7 * D ^ 10 * (chordConst ha hb hab * H ^ 2)
          + (D + (a * b).natAbs + 1) ^ 4 := hcon
      _ = 2 ^ 7 * D ^ 10 * chordConst ha hb hab * H ^ 2
          + (D + (a * b).natAbs + 1) ^ 4 := by ring
  have hlt : T * H ^ 2 + S < H ^ 4 := by
    have h1 : S ≤ S * H ^ 2 := Nat.le_mul_of_pos_right _ (by omega)
    have h2 : T * H ^ 2 + S * H ^ 2 = (T + S) * H ^ 2 := by ring
    have h3 : (T + S) * H ^ 2 < H * H ^ 2 :=
      Nat.mul_lt_mul_of_lt_of_le (by omega) (le_refl _) (by omega)
    have h4 : H * H ^ 2 ≤ H ^ 4 := by
      have : H ^ 3 ≤ H ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
      calc H * H ^ 2 = H ^ 3 := by ring
        _ ≤ H ^ 4 := this
    omega
  have hfour : pheight a b Q ^ 4 < H ^ 4 := by omega
  by_contra hge
  push_neg at hge
  have : H ^ 4 ≤ pheight a b Q ^ 4 := Nat.pow_le_pow_left hge 4
  omega


/-! ## 9. The bounded-height points are finite -/

private def coords : (E ((a : ℚ)) ((b : ℚ))).Point → Option (ℚ × ℚ)
  | .zero => none
  | .some (x := x) (y := y) _ => some (x, y)

private lemma someEqPt {x₁ y₁ x₂ y₂ : ℚ} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : (E ((a : ℚ)) ((b : ℚ))).Nonsingular x₁ y₁}
    {h₂ : (E ((a : ℚ)) ((b : ℚ))).Nonsingular x₂ y₂} :
    (Point.some h₁ : (E ((a : ℚ)) ((b : ℚ))).Point) = Point.some h₂ := by
  subst hx; subst hy; rfl

private lemma coords_injective : Function.Injective (coords (a := a) (b := b)) := by
  intro P Q h
  rcases P with _ | @⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | @⟨x₂, y₂, h₂⟩
  · rfl
  · exact absurd h (by simp [coords])
  · exact absurd h (by simp [coords])
  · simp only [coords, Option.some.injEq, Prod.mk.injEq] at h
    exact someEqPt h.1 h.2

lemma bounded_heights_finite (a b : ℤ) (N : ℕ) :
    {X : (E ((a : ℚ)) ((b : ℚ))).Point | pheight a b X ≤ N}.Finite := by
  have hpair : {p : ℚ × ℚ | hgt p.1 ≤ N ∧
      p.2 ^ 2 = p.1 * (p.1 - (a : ℚ)) * (p.1 - (b : ℚ))}.Finite := by
    have hsub : {p : ℚ × ℚ | hgt p.1 ≤ N ∧
        p.2 ^ 2 = p.1 * (p.1 - (a : ℚ)) * (p.1 - (b : ℚ))} ⊆
        ⋃ x ∈ {q : ℚ | hgt q ≤ N},
          {x} ×ˢ {y : ℚ | y ^ 2 = x * (x - (a : ℚ)) * (x - (b : ℚ))} := by
      rintro ⟨u, v⟩ ⟨h1, h2⟩
      simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff, Set.mem_setOf_eq]
      exact ⟨u, h1, rfl, h2⟩
    refine Set.Finite.subset (Set.Finite.biUnion
      (FiveDescent.theBoundedRationalsAreFinite N) fun x _ =>
        Set.Finite.prod (Set.finite_singleton x) ?_) hsub
    by_cases hex : ∃ y₀ : ℚ, y₀ ^ 2 = x * (x - (a : ℚ)) * (x - (b : ℚ))
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
  have himg : coords '' {X : (E ((a : ℚ)) ((b : ℚ))).Point | pheight a b X ≤ N} ⊆
      insert none (Option.some ''
        {p : ℚ × ℚ | hgt p.1 ≤ N ∧
          p.2 ^ 2 = p.1 * (p.1 - (a : ℚ)) * (p.1 - (b : ℚ))}) := by
    rintro w ⟨P, hP, rfl⟩
    rcases P with _ | @⟨x, y, h⟩
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨(x, y), ⟨hP, onCurve h⟩, rfl⟩
  exact Set.Finite.of_finite_image
    (Set.Finite.subset ((Set.Finite.image _ hpair).insert none) himg)
    coords_injective.injOn

/-! ## 10. The Mordell–Weil theorem on every full-2-torsion curve -/

/-- **THE MORDELL–WEIL THEOREM ON EVERY FULL-TWO-TORSION CURVE**: for every elliptic
curve over `ℚ` whose two-torsion is entirely rational, the group of rational points is
**finitely generated**.

Mathlib carries no Mordell–Weil theorem of any kind.  This is the strong form on a
two-parameter family of unbounded rank, assembled from the exact two-descent, the
quartic duplication law, and the quadratic chord law. -/
theorem theMordellWeilTheoremOnEveryFullTwoTorsionCurve
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0) :
    AddGroup.FG ((E ((a : ℚ)) ((b : ℚ))).Point) := by
  set N₀ : ℕ := threshold ha hb hab with hN₀
  rw [AddGroup.fg_iff]
  refine ⟨{X : (E ((a : ℚ)) ((b : ℚ))).Point | pheight a b X ≤ N₀}, ?_,
    bounded_heights_finite a b N₀⟩
  rw [eq_top_iff]
  intro X _
  have key : ∀ m (Y : (E ((a : ℚ)) ((b : ℚ))).Point), pheight a b Y ≤ m →
      Y ∈ AddSubgroup.closure
        {Z : (E ((a : ℚ)) ((b : ℚ))).Point | pheight a b Z ≤ N₀} := by
    intro m
    induction m with
    | zero =>
      intro Y hY
      exact AddSubgroup.subset_closure (by simp only [Set.mem_setOf_eq]; omega)
    | succ m ih =>
      intro Y hY
      by_cases hle : pheight a b Y ≤ N₀
      · exact AddSubgroup.subset_closure hle
      · obtain ⟨Q, R, hRh, hEq, hlt⟩ := theDescentStep ha hb hab Y (by omega)
        have hQmem := ih Q (by omega)
        have hRmem : R ∈ AddSubgroup.closure
            {Z : (E ((a : ℚ)) ((b : ℚ))).Point | pheight a b Z ≤ N₀} := by
          refine AddSubgroup.subset_closure ?_
          simp only [Set.mem_setOf_eq]
          unfold threshold at hN₀
          omega
        rw [hEq]
        exact AddSubgroup.add_mem _ (AddSubgroup.add_mem _ hQmem hQmem) hRmem
  exact key (pheight a b X) X le_rfl


/-! ## 11. The rank is bounded by the divisor count -/

open DirectSum

set_option maxHeartbeats 2000000 in
/-- **THE RANK IS BOUNDED ON EVERY FULL-TWO-TORSION CURVE**: with Mordell–Weil in
hand the rank is a finite invariant, and the descent bounds it — whenever
`4·τ(|ab(a−b)|)² < 2^r`, no `r` points are independent modulo torsion.

The `2^r` sign vectors built from the free basis are pairwise incongruent modulo
doubles, because at a coordinate where two sign vectors differ their difference is
odd while a double is even everywhere.  They must therefore collide in the finite
class atlas, which bounds `2^r`.

The congruent slice gets a further factor of three from its two-torsion trio; that
factor does **not** survive to two parameters, because `(0,0)` can itself be a double
when `ab` and `−a` are both squares.  The bound here is stated without it. -/
theorem theRankIsBoundedOnEveryFullTwoTorsionCurve (r : ℕ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0)
    (hr : 4 * (a * b * (a - b)).natAbs.divisors.card
      * (a * b * (a - b)).natAbs.divisors.card < 2 ^ r) :
    ¬ Soma.Holonics.Millennium.UniversalBSD.RankAtLeastOn
        (E ((a : ℚ)) ((b : ℚ))) r := by
  intro hR
  unfold Soma.Holonics.Millennium.UniversalBSD.RankAtLeastOn
    Soma.Holonics.Millennium.UniversalBSD.IndependentModTorsionOn
    Soma.Holonics.Millennium.UniversalBSD.IsTorsionOn at hR
  obtain ⟨Pts, hind⟩ := hR
  haveI : AddGroup.FG ((E ((a : ℚ)) ((b : ℚ))).Point) :=
    theMordellWeilTheoremOnEveryFullTwoTorsionCurve ha hb hab
  obtain ⟨m, ι, hι, qq, hqq, e, ⟨F⟩⟩ :=
    AddCommGroup.equiv_free_prod_directSum_zmod ((E ((a : ℚ)) ((b : ℚ))).Point)
  haveI := hι
  haveI : ∀ i, NeZero (qq i ^ e i) := fun i => ⟨pow_ne_zero _ (hqq i).pos.ne'⟩
  haveI : Finite (⨁ i, ZMod (qq i ^ e i)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  have htor : ∀ X : (E ((a : ℚ)) ((b : ℚ))).Point, (F X).1 = 0 →
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
    · by_cases hbb : ε i
      · rw [if_pos hbb, if_pos hbb, Finsupp.single_eq_same]
      · rw [if_neg hbb, if_neg hbb, Finsupp.coe_zero, Pi.zero_apply]
    · intro j _ hji
      by_cases hbb : ε j
      · rw [if_pos hbb]
        exact Finsupp.single_eq_of_ne
          (fun hc => hji (Fin.castLE_injective hrm hc).symm)
      · rw [if_neg hbb, Finsupp.coe_zero, Pi.zero_apply]
    · intro habs
      exact absurd (Finset.mem_univ i) habs
  -- the colliding family of `2^r` points
  obtain ⟨ε, δ, hne, Q, hQ⟩ :=
    theClassesCollideOnEveryFullTwoTorsionCurve ha hb hab
      (α := Fin r → Bool)
      (by
        simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
        omega)
      (fun ε => F.symm (wv ε, 0))
  -- the difference of two sign vectors is even at every coordinate
  have hfree : wv ε - wv δ = (2 : ℤ) • (F Q).1 := by
    have h1 : F (F.symm (wv ε, 0) - F.symm (wv δ, 0)) = F (Q + Q) := by rw [hQ]
    rw [map_sub, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, map_add] at h1
    have h2 := congrArg Prod.fst h1
    simp only [Prod.fst_sub, Prod.fst_add] at h2
    rw [h2]
    module
  -- but it is odd at a coordinate where the signs differ
  obtain ⟨i, hi⟩ : ∃ i : Fin r, ε i ≠ δ i := by
    by_contra hall
    push_neg at hall
    exact hne (funext hall)
  have hodd := congrArg (fun g => g (Fin.castLE hrm i)) hfree
  simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_smul, Pi.smul_apply,
    smul_eq_mul] at hodd
  rw [hwv_apply, hwv_apply] at hodd
  rcases Bool.eq_false_or_eq_true (ε i) with hε | hε <;>
    rcases Bool.eq_false_or_eq_true (δ i) with hδ | hδ <;>
      rw [hε, hδ] at hodd hi <;> simp at hodd hi <;> omega

end Soma.Holonics.Millennium.GeneralMordell
