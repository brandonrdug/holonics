import ElementaryHolonics.Millennium.FamilyHalving
import ElementaryHolonics.Millennium.FamilyFace
import ElementaryHolonics.Millennium.Descent
import Mathlib.Tactic

/-!
# FamilyKernel: the kernel of the face is the doubles at every modulus

**The point-level family exactness, one direction.**  On every congruent-number
curve `y² = x³ − n²x` with `n > 0`, a rational point whose two descent slots are
trivial square classes is a double: the slot square-roots assemble the half point
through the family halving certificates, and mathlib's group law doubles it back
exactly.

* **`slotOneAt` / `slotTwoAt`** — the descent face at every modulus, with the
  classical conventions at the vanishing coordinates
  (`(0,0) ↦ −n²`, `(n,0) ↦ 2n²`);
* **`theKernelIsTheDoublesAtEveryModulus`** — the halving converse as a family
  law: `ker(face) ⊆ 2·E_n(ℚ)` at every modulus.

The five-instance (`FiveHalving.theKernelIsTheDoublesAtFive`) is this theorem read
at `n = 5`.  Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyKernel

open WeierstrassCurve.Affine
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.FamilyHalving

/-! ## 1. The face at every modulus -/

/-- The first slot at modulus `n`: `x`, with the convention `(0−n)(0+n) = −n²` at the
vanishing coordinate. -/
def slotOneAt (n : ℚ) : (FamilyFace.E n).Point → ℚ
  | .zero => 1
  | .some x _ _ => if x = 0 then -n ^ 2 else x

/-- The second slot at modulus `n`: `x − n`, with the convention `(n−0)(n+n) = 2n²`
at its vanishing coordinate. -/
def slotTwoAt (n : ℚ) : (FamilyFace.E n).Point → ℚ
  | .zero => 1
  | .some x _ _ => if x = n then 2 * n ^ 2 else x - n

private lemma slotOneAt_some {n x y : ℚ} (h : (FamilyFace.E n).Nonsingular x y) :
    slotOneAt n (.some x y h) = if x = 0 then -n ^ 2 else x := rfl

private lemma slotTwoAt_some {n x y : ℚ} (h : (FamilyFace.E n).Nonsingular x y) :
    slotTwoAt n (.some x y h) = if x = n then 2 * n ^ 2 else x - n := rfl

/-! ## 2. Point-level plumbing at every modulus -/

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

/-! ## 3. The halving, assembled through the group law -/

set_option maxHeartbeats 1000000 in
/-- **The half-point construction at every modulus**: given the sign-coherent slot
square-roots, the point `(u, v)` lies on the curve and doubles to `(r², −rst)`. -/
private lemma halvingAt {n x₀ y₀ r s t : ℚ} (hn : 0 < n) (hr0 : r ≠ 0) (hs0 : s ≠ 0)
    (hs2 : s ^ 2 = r ^ 2 - n) (ht2 : t ^ 2 = r ^ 2 + n) (hx : x₀ = r ^ 2)
    (hy : y₀ = -(r * s * t)) (hP : (FamilyFace.E n).Nonsingular x₀ y₀) :
    ∃ Q : (FamilyFace.E n).Point, Q + Q = Point.some _ _ hP := by
  have ht0 : t ≠ 0 := by
    intro hc
    rw [hc] at ht2
    nlinarith [sq_nonneg r]
  obtain ⟨hne_rs, hne_rt, hne_st⟩ :=
    theHalfPointFactorsDoNotVanishAtEveryModulus hn.ne' hs2 ht2
  set u : ℚ := (r + s) * (r - t) with hu_def
  set v : ℚ := (r + s) * (r - t) * (s - t) with hv_def
  have hu0 : u ≠ 0 := mul_ne_zero hne_rs hne_rt
  have hv0 : v ≠ 0 := mul_ne_zero hu0 hne_st
  -- the half point is on the curve
  have hcurveQ : v ^ 2 = u ^ 3 - n ^ 2 * u := by
    rw [hu_def, hv_def]
    exact theHalfPointLiesOnTheCurveAtEveryModulus hs2 ht2
  have hQns : (FamilyFace.E n).Nonsingular u v := by
    rw [nonsingular_iff, equation_iff]
    constructor
    · simp only [FamilyFace.E]
      linear_combination hcurveQ
    · right
      simp only [FamilyFace.E]
      intro hc
      apply hv0
      linarith
  refine ⟨Point.some _ _ hQns, ?_⟩
  have hyne : v ≠ (FamilyFace.E n).negY u v := by
    rw [negYAt]
    intro hc
    exact hv0 (by linarith)
  rw [Point.add_self_of_Y_ne hyne]
  have hslope : (FamilyFace.E n).slope u u v v = (3 * u ^ 2 - n ^ 2) / (2 * v) := by
    rw [slope_of_Y_ne rfl hyne, negYAt]
    simp only [FamilyFace.E]
    ring_nf
  have h2v : (2 : ℚ) * v ≠ 0 := mul_ne_zero two_ne_zero hv0
  have keyX : (3 * u ^ 2 - n ^ 2) ^ 2 = (r ^ 2 + u + u) * (2 * v) ^ 2 := by
    rw [hu_def, hv_def]
    exact theTangentSquareLawAtEveryModulus hs2 ht2
  have keyY : (3 * u ^ 2 - n ^ 2) * (r ^ 2 - u) + 2 * v ^ 2 = 2 * (r * s * t) * v := by
    rw [hu_def, hv_def]
    exact theTangentOrdinateLawAtEveryModulus hs2 ht2
  have haddX : (FamilyFace.E n).addX u u ((FamilyFace.E n).slope u u v v)
      = ((3 * u ^ 2 - n ^ 2) / (2 * v)) ^ 2 - u - u := by
    rw [hslope]
    simp only [addX, FamilyFace.E]
    ring
  have hL2 : ((3 * u ^ 2 - n ^ 2) / (2 * v)) ^ 2 = r ^ 2 + u + u := by
    rw [div_pow, keyX]
    exact mul_div_cancel_right₀ _ (pow_ne_zero 2 h2v)
  refine someEqAt ?_ ?_
  · rw [haddX, hx, hL2]
    ring
  · have haddY : (FamilyFace.E n).addY u u v ((FamilyFace.E n).slope u u v v)
        = -(((3 * u ^ 2 - n ^ 2) / (2 * v)) *
            (((3 * u ^ 2 - n ^ 2) / (2 * v)) ^ 2 - u - u - u) + v) := by
      rw [addY, negAddY, haddX, hslope, negYAt]
    have hLru : ((3 * u ^ 2 - n ^ 2) / (2 * v)) * (r ^ 2 - u) = r * s * t - v := by
      rw [div_mul_eq_mul_div, div_eq_iff h2v]
      linear_combination keyY
    rw [haddY, hy, hL2,
      show r ^ 2 + u + u - u - u - u = r ^ 2 - u from by ring, hLru]
    ring

/-! ## 4. The kernel is the doubles, at every modulus -/

set_option maxHeartbeats 1000000 in
/-- **THE KERNEL OF THE FACE IS THE DOUBLES AT EVERY MODULUS**: on
`y² = x³ − n²x` with `n > 0`, a point with both slots in the trivial square class
is a double.  The five-instance is this theorem at `n = 5`. -/
theorem theKernelIsTheDoublesAtEveryModulus (n : ℚ) (hn : 0 < n)
    (P : (FamilyFace.E n).Point)
    (h1 : Descent.SqCls (slotOneAt n P) 1) (h2 : Descent.SqCls (slotTwoAt n P) 1) :
    ∃ Q : (FamilyFace.E n).Point, Q + Q = P := by
  rcases P with _ | @⟨x₀, y₀, hP⟩
  · exact ⟨0, rfl⟩
  · by_cases hy0 : y₀ = 0
    · -- the half-turns have nontrivial faces: three refutations
      exfalso
      subst hy0
      have hcurve := onCurveAt hP
      have hroots : x₀ * (x₀ - n) * (x₀ + n) = 0 := by linear_combination -hcurve
      have hx3 : x₀ = 0 ∨ x₀ = n ∨ x₀ = -n := by
        rcases mul_eq_zero.mp hroots with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl (by linarith))
        · exact Or.inr (Or.inr (by linarith))
      rcases hx3 with h' | h' | h'
      · obtain ⟨c, hc0, hc⟩ := h1
        rw [slotOneAt_some, if_pos h'] at hc
        nlinarith [sq_nonneg c, hn]
      · obtain ⟨c, hc0, hc⟩ := h2
        rw [slotTwoAt_some, if_pos h'] at hc
        apply Descent.notSquareTwo
        refine ⟨c / n, ?_⟩
        rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hn.ne' hn.ne')]
        linear_combination hc
      · obtain ⟨c, hc0, hc⟩ := h1
        have hx0ne : x₀ ≠ 0 := by
          intro hc'
          rw [h'] at hc'
          have : n = 0 := by linarith
          exact hn.ne' this
        rw [slotOneAt_some, if_neg hx0ne, h'] at hc
        nlinarith [sq_nonneg c, hn]
    · -- the sighted case: assemble the slot square-roots and halve
      have hcurve := onCurveAt hP
      have hx0 : x₀ ≠ 0 := by
        intro hc
        rw [hc] at hcurve
        apply hy0
        nlinarith [hcurve]
      have hxn : x₀ - n ≠ 0 := by
        intro hc
        have hxe : x₀ = n := by linarith
        rw [hxe] at hcurve
        apply hy0
        nlinarith [hcurve]
      obtain ⟨r, hr0, hr⟩ := h1
      rw [slotOneAt_some, if_neg hx0] at hr
      obtain ⟨s, hs0, hs⟩ := h2
      rw [slotTwoAt_some, if_neg (fun hc => hxn (by rw [hc]; ring))] at hs
      have hx : x₀ = r ^ 2 := by linarith [hr]
      have hs2 : s ^ 2 = r ^ 2 - n := by linarith [hs]
      set t : ℚ := -y₀ / (r * s) with ht_def
      have hrs : r * s ≠ 0 := mul_ne_zero hr0 hs0
      have hy : y₀ = -(r * s * t) := by
        rw [ht_def]
        field_simp
      have ht2 : t ^ 2 = r ^ 2 + n := by
        have hcancel : (x₀ * (x₀ - n)) * t ^ 2 = (x₀ * (x₀ - n)) * (x₀ + n) := by
          have hyt : (r * s * t) ^ 2 = y₀ ^ 2 := by
            rw [hy]
            ring
          calc (x₀ * (x₀ - n)) * t ^ 2 = (r ^ 2 * s ^ 2) * t ^ 2 := by
                rw [hx, hs2]
            _ = (r * s * t) ^ 2 := by ring
            _ = y₀ ^ 2 := hyt
            _ = x₀ ^ 3 - n ^ 2 * x₀ := hcurve
            _ = (x₀ * (x₀ - n)) * (x₀ + n) := by ring
        have hne : x₀ * (x₀ - n) ≠ 0 := mul_ne_zero hx0 hxn
        have h3 := mul_left_cancel₀ hne hcancel
        rw [hx] at h3
        linarith [h3]
      exact halvingAt hn hr0 hs0 hs2 ht2 hx hy hP

end Soma.Holonics.Millennium.FamilyKernel
