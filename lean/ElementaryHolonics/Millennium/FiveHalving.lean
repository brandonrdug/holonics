import ElementaryHolonics.Millennium.FaceImageFive
import Mathlib.Tactic

/-!
# FiveHalving: the kernel of the descent face is the doubles

**The halving converse at five** — the named-open of `FaceHomomorphism.lean` (*"the
converse — a point with trivial face is a double — remains open"*), closed.  A point of
`y² = x³ − 25x` whose two slots are rational squares is a double: the three slot
square-roots `r, s, t` (with `rst = −y` sign-coherent) assemble the half-point

```text
u = (r + s)(r − t),   v = u·(s − t),
```

and the tangent case of the group law doubles `(u, v)` back to the point exactly —
verified by three certified polynomial identities modulo `s² = r² − 5`, `t² = r² + 5`.
With `theDoublesLandInTheKernelOnTheFiveCurve` this makes the two-descent **exact** at
five: `ker(face) = 2·E₅(ℚ)`, so `E₅(ℚ)/2E₅(ℚ)` injects into the realized eight.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FiveHalving

open WeierstrassCurve.Affine
open Soma.Holonics.Millennium

/-! ## 1. Point-level plumbing on the five-curve -/

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
    (Point.some x₁ y₁ h₁ : RankOne.E5.Point) = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

private lemma slotOne5_some {x y : ℚ} (h : RankOne.E5.Nonsingular x y) :
    RankOne.slotOne (.some x y h) = if x = 0 then -25 else x := rfl

private lemma slotTwo5_some {x y : ℚ} (h : RankOne.E5.Nonsingular x y) :
    RankOne.slotTwo (.some x y h) = if x = 5 then 50 else x - 5 := rfl

/-! ## 2. The halving at coordinates -/

/-- **The half-point construction.**  Given the sign-coherent slot square-roots, the
point `(u, v) = ((r+s)(r−t), (r+s)(r−t)(s−t))` lies on the curve and doubles to
`(r², −rst)`. -/
private lemma halving {x₀ y₀ r s t : ℚ} (hr0 : r ≠ 0) (hs0 : s ≠ 0)
    (hs2 : s ^ 2 = r ^ 2 - 5) (ht2 : t ^ 2 = r ^ 2 + 5) (hx : x₀ = r ^ 2)
    (hy : y₀ = -(r * s * t)) (hP : RankOne.E5.Nonsingular x₀ y₀) :
    ∃ Q : RankOne.E5.Point, Q + Q = Point.some x₀ y₀ hP := by
  have ht0 : t ≠ 0 := by
    intro hc
    rw [hc] at ht2
    nlinarith [sq_nonneg r]
  -- the nonvanishing of the assembling factors
  have hne_rs : r + s ≠ 0 := by
    intro hc
    have : s = -r := by linarith
    rw [this] at hs2
    nlinarith
  have hne_rt : r - t ≠ 0 := by
    intro hc
    have : t = r := by linarith
    rw [this] at ht2
    nlinarith
  have hne_st : s - t ≠ 0 := by
    intro hc
    have : t = s := by linarith
    rw [this] at ht2
    nlinarith [hs2]
  set u : ℚ := (r + s) * (r - t) with hu_def
  set v : ℚ := (r + s) * (r - t) * (s - t) with hv_def
  have hu0 : u ≠ 0 := mul_ne_zero hne_rs hne_rt
  have hv0 : v ≠ 0 := mul_ne_zero hu0 hne_st
  -- the half-point is on the curve
  have hcurveQ : v ^ 2 = u ^ 3 - 25 * u := by
    rw [hu_def, hv_def]
    linear_combination
      (-5*t^2 + t^4 - s*t^3 + s^2*t^2 + 10*r*t - 3*r*t^3 + 3*r*s*t^2 - 2*r*s^2*t
        - 5*r^2 + 2*r^2*t^2 - 3*r^2*s*t + r^2*s^2 + r^3*t + r^3*s - r^4) * hs2
      + (-5*t^2 + 5*s*t + 15*r*t - 5*r*s + 2*r*s*t^2 - 10*r^2 + 2*r^2*t^2
        - 4*r^2*s*t - 4*r^3*t + 2*r^3*s + 2*r^4) * ht2
  have hQns : RankOne.E5.Nonsingular u v := by
    rw [nonsingular_iff, equation_iff]
    constructor
    · simp only [RankOne.E5]
      linear_combination hcurveQ
    · right
      simp only [RankOne.E5]
      intro hc
      apply hv0
      linarith
  refine ⟨Point.some u v hQns, ?_⟩
  have hyne : v ≠ RankOne.E5.negY u v := by
    rw [negYFive]
    intro hc
    exact hv0 (by linarith)
  rw [Point.add_self_of_Y_ne hyne]
  have hslope : RankOne.E5.slope u u v v = (3 * u ^ 2 - 25) / (2 * v) := by
    rw [slope_of_Y_ne rfl hyne, negYFive]
    simp only [RankOne.E5]
    ring_nf
  have h2v : (2 : ℚ) * v ≠ 0 := mul_ne_zero two_ne_zero hv0
  have keyX : (3 * u ^ 2 - 25) ^ 2 = (r ^ 2 + u + u) * (2 * v) ^ 2 := by
    rw [hu_def, hv_def]
    linear_combination
      ((-150)*t^2 + 35*t^4 + (-40)*s*t^3 + 8*s*t^5 + (-7)*s^2*t^4 + 8*s^3*t^3
        + 300*r*t + (-180)*r*t^3 + 24*r*t^5 + 120*r*s*t^2 + (-36)*r*s*t^4
        + 36*r*s^2*t^3 + (-24)*r*s^3*t^2 + (-150)*r^2 + 350*r^2*t^2 + (-77)*r^2*t^4
        + (-120)*r^2*s*t + 64*r^2*s*t^3 + (-70)*r^2*s^2*t^2 + 24*r^2*s^3*t
        + (-300)*r^3*t + 68*r^3*t^3 + 40*r^3*s + (-56)*r^3*s*t^2 + 60*r^3*s^2*t
        + (-8)*r^3*s^3 + 95*r^4 + 22*r^4*t^2 + 24*r^4*s*t + (-19)*r^4*s^2
        + (-60)*r^5*t + (-4)*r^5*s + 23*r^6) * hs2
      + ((-125) + (-175)*t^2 + (-40)*s*t^3 + 300*r*t + (-120)*r*t^3 + 180*r*s*t^2
        + (-125)*r^2 + 420*r^2*t^2 + (-240)*r^2*s*t + 32*r^2*s*t^3 + (-480)*r^3*t
        + 32*r^3*t^3 + 100*r^3*s + (-96)*r^3*s*t^2 + 180*r^4 + (-96)*r^4*t^2
        + 96*r^4*s*t + 96*r^5*t + (-32)*r^5*s + (-32)*r^6) * ht2
  have keyY : (3 * u ^ 2 - 25) * (r ^ 2 - u) + 2 * v ^ 2 = 2 * (r * s * t) * v := by
    rw [hu_def, hv_def]
    linear_combination
      ((-10)*t^2 + 2*t^4 + (-1)*s*t^3 + 2*s^2*t^2 + 20*r*t + (-5)*r*t^3 + 5*r*s*t^2
        + (-4)*r*s^2*t + (-10)*r^2 + 2*r^2*t^2 + (-5)*r^2*s*t + 2*r^2*s^2 + 3*r^3*t
        + r^3*s + (-2)*r^4) * hs2
      + ((-10)*t^2 + 5*s*t + 25*r*t + (-5)*r*s + 4*r*s*t^2 + (-10)*r^2 + 4*r^2*t^2
        + (-6)*r^2*s*t + (-6)*r^3*t + 2*r^3*s + 2*r^4) * ht2
  have haddX : RankOne.E5.addX u u (RankOne.E5.slope u u v v)
      = ((3 * u ^ 2 - 25) / (2 * v)) ^ 2 - u - u := by
    rw [hslope]
    simp only [addX, RankOne.E5]
    ring
  have hL2 : ((3 * u ^ 2 - 25) / (2 * v)) ^ 2 = r ^ 2 + u + u := by
    rw [div_pow, keyX]
    exact mul_div_cancel_right₀ _ (pow_ne_zero 2 h2v)
  refine someEqFive ?_ ?_
  · -- the abscissa doubles back to `r²`
    rw [haddX, hx, hL2]
    ring
  · -- the ordinate doubles back to `−rst`
    have haddY : RankOne.E5.addY u u v (RankOne.E5.slope u u v v)
        = -(((3 * u ^ 2 - 25) / (2 * v)) *
            (((3 * u ^ 2 - 25) / (2 * v)) ^ 2 - u - u - u) + v) := by
      rw [addY, negAddY, haddX, hslope, negYFive]
    have hLru : ((3 * u ^ 2 - 25) / (2 * v)) * (r ^ 2 - u) = r * s * t - v := by
      rw [div_mul_eq_mul_div, div_eq_iff h2v]
      linear_combination keyY
    rw [haddY, hy, hL2,
      show r ^ 2 + u + u - u - u - u = r ^ 2 - u from by ring, hLru]
    ring

/-! ## 3. The kernel is the doubles -/

/-- **THE KERNEL OF THE FACE IS THE DOUBLES AT FIVE**: a point of `y² = x³ − 25x` with
both slots trivial is a double.  With `theDoublesLandInTheKernelOnTheFiveCurve` this is
the exactness of the two-descent: `ker(face) = 2·E₅(ℚ)`. -/
theorem theKernelIsTheDoublesAtFive (P : RankOne.E5.Point)
    (h1 : Descent.SqCls (RankOne.slotOne P) 1)
    (h2 : Descent.SqCls (RankOne.slotTwo P) 1) :
    ∃ Q : RankOne.E5.Point, Q + Q = P := by
  rcases P with _ | @⟨x₀, y₀, hP⟩
  · exact ⟨0, rfl⟩
  · by_cases hy0 : y₀ = 0
    · -- the half-turns have nontrivial faces: three refutations
      exfalso
      subst hy0
      have hcurve := onCurveFive hP
      have hroots : x₀ * (x₀ - 5) * (x₀ + 5) = 0 := by linear_combination -hcurve
      have hx3 : x₀ = 0 ∨ x₀ = 5 ∨ x₀ = -5 := by
        rcases mul_eq_zero.mp hroots with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl (by linarith))
        · exact Or.inr (Or.inr (by linarith))
      rcases hx3 with rfl | rfl | rfl
      · obtain ⟨c, hc0, hc⟩ := h1
        rw [slotOne5_some, if_pos rfl] at hc
        nlinarith [sq_nonneg c]
      · obtain ⟨c, hc0, hc⟩ := h2
        rw [slotTwo5_some, if_pos rfl] at hc
        apply Descent.notSquareTwo
        refine ⟨c / 5, ?_⟩
        rw [div_mul_div_comm, show c * c = 50 from by linear_combination -hc]
        norm_num
      · obtain ⟨c, hc0, hc⟩ := h1
        rw [slotOne5_some, if_neg (by norm_num)] at hc
        nlinarith [sq_nonneg c]
    · -- the sighted case: assemble the slot square-roots and halve
      have hcurve := onCurveFive hP
      have hx0 : x₀ ≠ 0 := by
        intro hc
        rw [hc] at hcurve
        apply hy0
        nlinarith [hcurve]
      have hx5 : x₀ - 5 ≠ 0 := by
        intro hc
        have : x₀ = 5 := by linarith
        rw [this] at hcurve
        apply hy0
        nlinarith [hcurve]
      obtain ⟨r, hr0, hr⟩ := h1
      rw [slotOne5_some, if_neg hx0] at hr
      obtain ⟨s, hs0, hs⟩ := h2
      rw [slotTwo5_some, if_neg (fun hc => hx5 (by rw [hc]; ring))] at hs
      -- `hr : x₀ = r²·1`, `hs : x₀ − 5 = s²·1`
      have hx : x₀ = r ^ 2 := by linarith [hr]
      have hs2 : s ^ 2 = r ^ 2 - 5 := by linarith [hs]
      set t : ℚ := -y₀ / (r * s) with ht_def
      have hrs : r * s ≠ 0 := mul_ne_zero hr0 hs0
      have hy : y₀ = -(r * s * t) := by
        rw [ht_def]
        field_simp
      have ht2 : t ^ 2 = r ^ 2 + 5 := by
        have hcancel : (x₀ * (x₀ - 5)) * t ^ 2 = (x₀ * (x₀ - 5)) * (x₀ + 5) := by
          have hyt : (r * s * t) ^ 2 = y₀ ^ 2 := by
            rw [hy]
            ring
          calc (x₀ * (x₀ - 5)) * t ^ 2 = (r ^ 2 * s ^ 2) * t ^ 2 := by
                rw [hx, hs2]
            _ = (r * s * t) ^ 2 := by ring
            _ = y₀ ^ 2 := hyt
            _ = x₀ ^ 3 - 25 * x₀ := hcurve
            _ = (x₀ * (x₀ - 5)) * (x₀ + 5) := by ring
        have hne : x₀ * (x₀ - 5) ≠ 0 := mul_ne_zero hx0 hx5
        have := mul_left_cancel₀ hne hcancel
        rw [hx] at this
        linarith [this]
      exact halving hr0 hs0 hs2 ht2 hx hy hP

end Soma.Holonics.Millennium.FiveHalving
