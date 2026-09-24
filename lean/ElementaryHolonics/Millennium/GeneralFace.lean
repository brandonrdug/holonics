import ElementaryHolonics.Millennium.FamilyImage

/-!
# GeneralFace: the descent face on **every** curve with full rational 2-torsion

The congruent-number family `y² = x³ − n²x` is the one-parameter slice `b = −a` of
the two-parameter family of every elliptic curve over `ℚ` whose two-torsion is
entirely rational:

```text
E_{a,b} : y² = x(x − a)(x − b),      a ≠ 0,  b ≠ 0,  a ≠ b.
```

This family has unbounded rank and is Zariski-dense in the moduli of elliptic
curves with full level-two structure.  This file carries the descent face onto it.

* **`E a b`**, **`slotOne`, `slotTwo`** — the curve and the two slots, with the
  conventions `(0,0) ↦ ab` and `(a,0) ↦ a(a−b)` read off the factorization.  At
  `b = −a` they specialize to `−a²` and `2a²`, the congruent-number conventions.
* **`theDoublingIdentities`** — the three exact identities behind the descent,
  each a polynomial consequence of the curve equation:
  `x(2Q) = ((x²−ab)/2y)²`, `x(2Q) − a = ((x²−2ax+ab)/2y)²`,
  `x(2Q) − b = ((x²−2bx+ab)/2y)²`.
* **`theDoublesLandInTheKernelOnEveryFullTwoTorsionCurve`** — both slots of a
  doubled point are rational squares, on **every** such curve.

The degenerate branches are self-consistent here in a way the congruent slice
hides: if `x² = ab` then `2Q = (0,0)` and the convention value `ab` **is** the
square `x²`; if `(x−a)² = a(a−b)` then `2Q = (a,0)` and the convention value
`a(a−b)` **is** that square.  The conventions are not a patch — they are the
values the identities force.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.GeneralFace

open WeierstrassCurve.Affine
open Soma.Holonics.Millennium

/-! ## 1. The two-parameter family and its face -/

/-- The general curve with full rational two-torsion: `y² = x(x−a)(x−b)`. -/
def E (a b : ℚ) : WeierstrassCurve.Affine ℚ := ⟨0, -(a + b), 0, a * b, 0⟩

/-- The first slot: `x`, with the convention `(0−a)(0−b) = ab` at the vanishing
coordinate. -/
def slotOne (a b : ℚ) : (E a b).Point → ℚ
  | .zero => 1
  | .some x _ _ => if x = 0 then a * b else x

/-- The second slot: `x − a`, with the convention `(a−0)(a−b) = a(a−b)` at its
vanishing coordinate. -/
def slotTwo (a b : ℚ) : (E a b).Point → ℚ
  | .zero => 1
  | .some x _ _ => if x = a then a * (a - b) else x - a

lemma slotOne_some {a b x y : ℚ} (h : (E a b).Nonsingular x y) :
    slotOne a b (.some _ _ h) = if x = 0 then a * b else x := rfl

lemma slotTwo_some {a b x y : ℚ} (h : (E a b).Nonsingular x y) :
    slotTwo a b (.some _ _ h) = if x = a then a * (a - b) else x - a := rfl

lemma onCurve {a b x y : ℚ} (h : (E a b).Nonsingular x y) :
    y ^ 2 = x * (x - a) * (x - b) := by
  have h1 := ((nonsingular_iff x y).mp h).1
  rw [equation_iff] at h1
  simp only [E] at h1
  linarith [h1]

lemma negY_eq (a b x y : ℚ) : (E a b).negY x y = -y := by
  simp [negY, E]

/-- The congruent-number family is the slice `b = −a`. -/
lemma E_neg (a : ℚ) : E a (-a) = FamilyFace.E a := by
  unfold E FamilyFace.E
  norm_num
  ring

/-! ## 2. The three doubling identities -/

variable {a b : ℚ}

/-- **THE DOUBLING IDENTITIES**: the numerators of the doubled abscissa and of its
two translates are exact squares, as polynomial consequences of the curve equation.
`N = 3x² − 2(a+b)x + ab` is the tangent numerator. -/
theorem theDoublingIdentities {x y : ℚ} (hcurve : y ^ 2 = x * (x - a) * (x - b)) :
    (3 * x ^ 2 - 2 * (a + b) * x + a * b) ^ 2
        + ((a + b) - 2 * x) * (2 * y) ^ 2 = (x ^ 2 - a * b) ^ 2 ∧
    (3 * x ^ 2 - 2 * (a + b) * x + a * b) ^ 2
        + (b - 2 * x) * (2 * y) ^ 2 = (x ^ 2 - 2 * a * x + a * b) ^ 2 ∧
    (3 * x ^ 2 - 2 * (a + b) * x + a * b) ^ 2
        + (a - 2 * x) * (2 * y) ^ 2 = (x ^ 2 - 2 * b * x + a * b) ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (4 * ((a + b) - 2 * x)) * hcurve
  · linear_combination (4 * (b - 2 * x)) * hcurve
  · linear_combination (4 * (a - 2 * x)) * hcurve

/-! ## 3. The doubles land in the kernel -/

set_option maxHeartbeats 1000000 in
/-- **THE DOUBLES LAND IN THE KERNEL ON EVERY FULL-TWO-TORSION CURVE**: both slots
of a doubled point are rational squares, for every `a, b` with `a`, `b`, `a−b`
nonzero.  The degenerate abscissae are not exceptions: when the doubled point lands
on a two-torsion point the convention value is exactly the square the identity
produces. -/
theorem theDoublesLandInTheKernelOnEveryFullTwoTorsionCurve
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0) (Q : (E a b).Point) :
    Descent.SqCls (slotOne a b (Q + Q)) 1 ∧ Descent.SqCls (slotTwo a b (Q + Q)) 1 := by
  rcases Q with _ | @⟨x, y, h⟩
  · rw [← Point.zero_def, add_zero]
    simpa [slotOne, slotTwo] using
      (And.intro (Descent.sqClsRefl (1 : ℚ)) (Descent.sqClsRefl (1 : ℚ)))
  · by_cases hy : y = 0
    · have hzero : (Point.some _ _ h : (E a b).Point) + Point.some _ _ h = 0 :=
        Point.add_self_of_Y_eq (by rw [negY_eq, hy]; norm_num)
      rw [hzero]
      simpa [slotOne, slotTwo] using
        (And.intro (Descent.sqClsRefl (1 : ℚ)) (Descent.sqClsRefl (1 : ℚ)))
    · have hcurve := onCurve h
      have hyne : y ≠ (E a b).negY x y := by
        rw [negY_eq]
        intro hc
        exact hy (by linarith)
      rw [Point.add_self_of_Y_ne hyne]
      have h2y : (2 : ℚ) * y ≠ 0 := mul_ne_zero two_ne_zero hy
      set N : ℚ := 3 * x ^ 2 - 2 * (a + b) * x + a * b with hN
      have hslope : (E a b).slope x x y y = N / (2 * y) := by
        rw [slope_of_Y_ne rfl hyne, negY_eq]
        simp only [E, hN]
        ring_nf
      have haddX : (E a b).addX x x ((E a b).slope x x y y)
          = (N / (2 * y)) ^ 2 + (a + b) - 2 * x := by
        rw [hslope]
        simp only [addX, E]
        ring
      obtain ⟨key1, key2, -⟩ := theDoublingIdentities hcurve
      -- the doubled abscissa and its translate, as exact squares
      have hX : (E a b).addX x x ((E a b).slope x x y y)
          = ((x ^ 2 - a * b) / (2 * y)) ^ 2 := by
        rw [haddX, div_pow, div_pow, ← key1, add_div, mul_div_assoc,
          div_self (pow_ne_zero 2 h2y), mul_one]
        ring
      have hXa : (E a b).addX x x ((E a b).slope x x y y) - a
          = ((x ^ 2 - 2 * a * x + a * b) / (2 * y)) ^ 2 := by
        rw [haddX, div_pow, div_pow, ← key2, add_div, mul_div_assoc,
          div_self (pow_ne_zero 2 h2y), mul_one]
        ring
      constructor
      · by_cases hd0 : (E a b).addX x x ((E a b).slope x x y y) = 0
        · -- the double is `(0,0)`: the convention value is the square `x²`
          rw [slotOne_some, if_pos hd0]
          rw [hd0] at hX
          have hnum : x ^ 2 - a * b = 0 := by
            by_contra hne
            exact (div_ne_zero hne h2y) (pow_eq_zero_iff two_ne_zero |>.mp hX.symm)
          have hx0 : x ≠ 0 := by
            intro hc
            rw [hc] at hnum
            exact (mul_ne_zero ha hb) (by linarith)
          exact ⟨x, hx0, by linarith [hnum]⟩
        · rw [slotOne_some, if_neg hd0]
          refine ⟨(x ^ 2 - a * b) / (2 * y), ?_, by rw [hX]; ring⟩
          intro hc
          exact hd0 (by rw [hX, hc]; ring)
      · by_cases hd1 : (E a b).addX x x ((E a b).slope x x y y) = a
        · -- the double is `(a,0)`: the convention value is the square `(x−a)²`
          rw [slotTwo_some, if_pos hd1]
          have hzero : (E a b).addX x x ((E a b).slope x x y y) - a = 0 := by
            rw [hd1]; ring
          rw [hzero] at hXa
          have hnum : x ^ 2 - 2 * a * x + a * b = 0 := by
            by_contra hne
            exact (div_ne_zero hne h2y) (pow_eq_zero_iff two_ne_zero |>.mp hXa.symm)
          have hxa : x - a ≠ 0 := by
            intro hc
            have hxe : x = a := by linarith
            rw [hxe] at hnum
            exact (mul_ne_zero ha hab) (by linarith)
          exact ⟨x - a, hxa, by linarith [hnum]⟩
        · rw [slotTwo_some, if_neg hd1]
          refine ⟨(x ^ 2 - 2 * a * x + a * b) / (2 * y), ?_, by rw [hXa]; ring⟩
          intro hc
          exact hd1 (by
            have : (E a b).addX x x ((E a b).slope x x y y) - a = 0 := by
              rw [hXa, hc]; ring
            linarith)

end Soma.Holonics.Millennium.GeneralFace
