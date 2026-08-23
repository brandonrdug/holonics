import ElementaryHolonics.Millennium.FamilyKernel
import Mathlib.Tactic

/-!
# FamilyImage: the doubles land in the kernel at every modulus

**The forward half of family exactness.**  On every congruent-number curve
`y² = x³ − n²x` with `n > 0`, both descent slots of a doubled point are literal
rational squares:

```text
x(2Q) = ((x² + n²)/(2y))²,        x(2Q) − n = ((x² − 2nx − n²)/(2y))²,
```

and the doubled point is never a half-turn because `x² − 2nx − n² = 0` would make
two a rational square.  With `FamilyKernel.theKernelIsTheDoublesAtEveryModulus`
this closes the two-descent **exactly at every modulus**:
`ker(face) = 2·E_n(ℚ)`, family-wise.

* **`theDoublesLandInTheKernelAtEveryModulus`** — for every point `Q`,
  both slots of `Q + Q` are in the trivial square class.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyImage

open WeierstrassCurve.Affine
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.FamilyKernel

private lemma onCurveAt {n x y : ℚ} (h : (FamilyFace.E n).Nonsingular x y) :
    y ^ 2 = x ^ 3 - n ^ 2 * x := by
  have h1 := ((nonsingular_iff x y).mp h).1
  rw [equation_iff] at h1
  simp only [FamilyFace.E] at h1
  linarith [h1]

private lemma negYAt (n x y : ℚ) : (FamilyFace.E n).negY x y = -y := by
  simp [negY, FamilyFace.E]

private lemma slotOneAt_some' {n x y : ℚ} (h : (FamilyFace.E n).Nonsingular x y) :
    slotOneAt n (.some h) = if x = 0 then -n ^ 2 else x := rfl

private lemma slotTwoAt_some' {n x y : ℚ} (h : (FamilyFace.E n).Nonsingular x y) :
    slotTwoAt n (.some h) = if x = n then 2 * n ^ 2 else x - n := rfl

set_option maxHeartbeats 1000000 in
/-- **THE DOUBLES LAND IN THE KERNEL AT EVERY MODULUS**: both slots of a doubled
point are rational squares, at every positive modulus. -/
theorem theDoublesLandInTheKernelAtEveryModulus (n : ℚ) (hn : 0 < n)
    (Q : (FamilyFace.E n).Point) :
    Descent.SqCls (slotOneAt n (Q + Q)) 1 ∧
    Descent.SqCls (slotTwoAt n (Q + Q)) 1 := by
  rcases Q with _ | @⟨x, y, h⟩
  · rw [← Point.zero_def, add_zero]
    exact ⟨Descent.sqClsRefl 1, Descent.sqClsRefl 1⟩
  · by_cases hy : y = 0
    · have hzero : (Point.some h : (FamilyFace.E n).Point) + Point.some h = 0 :=
        Point.add_self_of_Y_eq (by rw [negYAt, hy]; norm_num)
      rw [hzero]
      exact ⟨Descent.sqClsRefl 1, Descent.sqClsRefl 1⟩
    · have hcurve := onCurveAt h
      have hyne : y ≠ (FamilyFace.E n).negY x y := by
        rw [negYAt]
        intro hc
        exact hy (by linarith)
      rw [Point.add_self_of_Y_ne hyne]
      have h2y : (2 : ℚ) * y ≠ 0 := mul_ne_zero two_ne_zero hy
      have hslope : (FamilyFace.E n).slope x x y y = (3 * x ^ 2 - n ^ 2) / (2 * y) := by
        rw [slope_of_Y_ne rfl hyne, negYAt]
        simp only [FamilyFace.E]
        ring_nf
      -- the two square laws
      have hkey1 : (3 * x ^ 2 - n ^ 2) ^ 2 - (x + x) * (2 * y) ^ 2
          = (x ^ 2 + n ^ 2) ^ 2 := by
        linear_combination (-8 * x) * hcurve
      have hkey2 : (3 * x ^ 2 - n ^ 2) ^ 2 - (x + x + n) * (2 * y) ^ 2
          = (x ^ 2 - 2 * n * x - n ^ 2) ^ 2 := by
        linear_combination (-(8 * x + 4 * n)) * hcurve
      have haddX : (FamilyFace.E n).addX x x ((FamilyFace.E n).slope x x y y)
          = ((3 * x ^ 2 - n ^ 2) / (2 * y)) ^ 2 - x - x := by
        rw [hslope]
        simp only [addX, FamilyFace.E]
        ring
      have hXval : (FamilyFace.E n).addX x x ((FamilyFace.E n).slope x x y y)
          = ((x ^ 2 + n ^ 2) / (2 * y)) ^ 2 := by
        rw [haddX, div_pow, div_pow, ← hkey1, sub_div, mul_div_assoc,
          div_self (pow_ne_zero 2 h2y), mul_one]
        ring
      have hXnval : (FamilyFace.E n).addX x x ((FamilyFace.E n).slope x x y y) - n
          = ((x ^ 2 - 2 * n * x - n ^ 2) / (2 * y)) ^ 2 := by
        rw [haddX, div_pow, div_pow, ← hkey2, sub_div, mul_div_assoc,
          div_self (pow_ne_zero 2 h2y), mul_one]
        ring
      -- the numerators do not vanish
      have hnum1 : x ^ 2 + n ^ 2 ≠ 0 := by
        intro hc
        have h1 : n = 0 := by nlinarith [sq_nonneg x, sq_nonneg n]
        exact hn.ne' h1
      have hnum2 : x ^ 2 - 2 * n * x - n ^ 2 ≠ 0 := by
        intro hc
        apply Descent.notSquareTwo
        refine ⟨(x - n) / n, ?_⟩
        rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hn.ne' hn.ne')]
        linear_combination -hc
      -- the abscissa avoids the half-turn conditions
      have hd0 : (FamilyFace.E n).addX x x ((FamilyFace.E n).slope x x y y) ≠ 0 := by
        rw [hXval]
        exact pow_ne_zero 2 (div_ne_zero hnum1 h2y)
      have hd1 : (FamilyFace.E n).addX x x ((FamilyFace.E n).slope x x y y) ≠ n := by
        intro hc
        have h1 : (FamilyFace.E n).addX x x ((FamilyFace.E n).slope x x y y) - n = 0 := by
          rw [hc]
          ring
        rw [hXnval] at h1
        exact pow_ne_zero 2 (div_ne_zero hnum2 h2y) h1
      constructor
      · rw [slotOneAt_some', if_neg hd0]
        exact ⟨(x ^ 2 + n ^ 2) / (2 * y), div_ne_zero hnum1 h2y, by rw [hXval]; ring⟩
      · rw [slotTwoAt_some', if_neg hd1]
        exact ⟨(x ^ 2 - 2 * n * x - n ^ 2) / (2 * y), div_ne_zero hnum2 h2y, by
          rw [hXnval]
          ring⟩

/-- **THE TWO-DESCENT IS EXACT AT EVERY MODULUS**: a point has both slots trivial
exactly when it is a double — `ker(face) = 2·E_n(ℚ)`, family-wise. -/
theorem theTwoDescentIsExactAtEveryModulus (n : ℚ) (hn : 0 < n)
    (P : (FamilyFace.E n).Point) :
    (Descent.SqCls (slotOneAt n P) 1 ∧ Descent.SqCls (slotTwoAt n P) 1)
      ↔ ∃ Q : (FamilyFace.E n).Point, Q + Q = P := by
  constructor
  · intro h
    exact FamilyKernel.theKernelIsTheDoublesAtEveryModulus n hn P h.1 h.2
  · rintro ⟨Q, rfl⟩
    exact theDoublesLandInTheKernelAtEveryModulus n hn Q

end Soma.Holonics.Millennium.FamilyImage
