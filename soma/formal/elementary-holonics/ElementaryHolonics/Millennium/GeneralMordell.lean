import ElementaryHolonics.Millennium.GeneralHeight
import ElementaryHolonics.Millennium.GeneralCollision

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
    {C : ℕ} (Q : (E ((a : ℚ)) ((b : ℚ))).Point) {B : ℕ}
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

end Soma.Holonics.Millennium.GeneralMordell
