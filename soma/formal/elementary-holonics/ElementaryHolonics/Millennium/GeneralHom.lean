import ElementaryHolonics.Millennium.GeneralFace

/-!
# GeneralHom: the descent face is a homomorphism on every full-2-torsion curve

The whole descent rests on one polynomial identity, and on the two-parameter family
`y² = x(x−a)(x−b)` it can be stated without any case analysis at all.  If the line
`y = λx + ν` meets the curve at `x₁, x₂, x₃`, then

```text
f(x) − (λx + ν)²  =  (x − x₁)(x − x₂)(x − x₃)
```

is a monic cubic, so comparing constant terms at `x = 0` — where `f(0) = 0` — gives
`x₁x₂x₃ = ν²`, and evaluating at `x = a` — where `f(a) = 0` — gives
`(x₁−a)(x₂−a)(x₃−a) = (λa+ν)²`.  **Both slot products are squares**, which is exactly
the homomorphism property, and each is one `linear_combination` from the two curve
equations.

* **`theChordProductIsASquare`** — the first slot's identity.
* **`theShiftedChordProductIsASquare`** — the second slot's.
* **`theVerticalChordProducts`** — the degenerate line through the origin: when one
  abscissa is `0` the remaining two multiply to `ab`, which is why the convention
  value at `(0,0)` is `ab` and not a choice; likewise `a(a−b)` at `(a,0)`.

These are the identities the face homomorphism is assembled from, on **every** curve
over `ℚ` with full rational two-torsion.  Every `theorem` is discharged and none
depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.GeneralHom

open WeierstrassCurve.Affine
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.GeneralFace

variable {a b : ℚ}

/-! ## 1. The chord identities -/

/-- **THE CHORD PRODUCT IS A SQUARE**: the three abscissae cut by a chord multiply to
the square of the line's intercept.  This is the first slot's homomorphism law, and
it is the constant term of the cubic `f(x) − (λx+ν)²` read at `x = 0`. -/
theorem theChordProductIsASquare {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : y₁ ^ 2 = x₁ * (x₁ - a) * (x₁ - b))
    (h₂ : y₂ ^ 2 = x₂ * (x₂ - a) * (x₂ - b)) (hx : x₁ ≠ x₂) :
    x₁ * x₂ * (((y₂ - y₁) / (x₂ - x₁)) ^ 2 + (a + b) - x₁ - x₂)
      = (y₁ - ((y₂ - y₁) / (x₂ - x₁)) * x₁) ^ 2 := by
  have hd : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  field_simp
  linear_combination (-(x₂ - x₁) * x₂) * h₁ + ((x₂ - x₁) * x₁) * h₂

/-- **THE SHIFTED CHORD PRODUCT IS A SQUARE**: the same cubic read at `x = a`, where
`f(a) = 0` again.  This is the second slot's homomorphism law. -/
theorem theShiftedChordProductIsASquare {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : y₁ ^ 2 = x₁ * (x₁ - a) * (x₁ - b))
    (h₂ : y₂ ^ 2 = x₂ * (x₂ - a) * (x₂ - b)) (hx : x₁ ≠ x₂) :
    (x₁ - a) * (x₂ - a) * ((((y₂ - y₁) / (x₂ - x₁)) ^ 2 + (a + b) - x₁ - x₂) - a)
      = (((y₂ - y₁) / (x₂ - x₁)) * a + (y₁ - ((y₂ - y₁) / (x₂ - x₁)) * x₁)) ^ 2 := by
  have hd : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  field_simp
  linear_combination (-(x₂ - x₁) * (x₂ - a)) * h₁ + ((x₂ - x₁) * (x₁ - a)) * h₂

/-- **THE CHORD THROUGH THE ORIGIN**: when one abscissa is `0` the intercept vanishes
and the identity degenerates, but the remaining two abscissae multiply to `ab` — which
is exactly the convention value assigned to `(0,0)`.  The convention is forced, not
chosen. -/
theorem theVerticalChordProducts {x₂ y₂ : ℚ}
    (h₂ : y₂ ^ 2 = x₂ * (x₂ - a) * (x₂ - b)) (hx : x₂ ≠ 0) (hy : y₂ ≠ 0) :
    x₂ * ((y₂ / x₂) ^ 2 + (a + b) - 0 - x₂) = a * b := by
  field_simp
  linear_combination h₂

/-- **THE CHORD THROUGH `(a,0)`**: the same reading at the second two-torsion point.
The remaining two shifted abscissae multiply to `a(a−b)`, the convention value. -/
theorem theShiftedChordThroughTheSecondTorsion {x₂ y₂ : ℚ}
    (h₂ : y₂ ^ 2 = x₂ * (x₂ - a) * (x₂ - b)) (hxa : x₂ ≠ a) (hy : y₂ ≠ 0) :
    (x₂ - a) * (((y₂ / (x₂ - a)) ^ 2 + (a + b) - a - x₂) - a) = a * (a - b) := by
  have hd : x₂ - a ≠ 0 := sub_ne_zero.mpr hxa
  field_simp
  linear_combination h₂


/-! ## 2. The conservation law: the three faces multiply to a square

This is the angle-sum of the descent.  A chord meets the curve in three abscissae;
the three slot values it reads multiply to a **nonzero rational square**, so the three
face classes sum to zero in the square-class group `(ℤ/2)`-vector space.  The
homomorphism property is that conservation law, and the convention values at the
two-torsion points are exactly what keeps it exact there. -/

/-- Vieta's second relation for the chord cubic. -/
theorem theChordSecondSymmetric {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : y₁ ^ 2 = x₁ * (x₁ - a) * (x₁ - b))
    (h₂ : y₂ ^ 2 = x₂ * (x₂ - a) * (x₂ - b)) (hx : x₁ ≠ x₂) :
    x₁ * x₂ + (((y₂ - y₁) / (x₂ - x₁)) ^ 2 + (a + b) - x₁ - x₂) * (x₁ + x₂)
      = a * b - 2 * ((y₂ - y₁) / (x₂ - x₁)) * (y₁ - ((y₂ - y₁) / (x₂ - x₁)) * x₁) := by
  have hd : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  field_simp
  linear_combination (-(x₂ - x₁)) * h₁ + (x₂ - x₁) * h₂

/-- **THE FIRST FACE IS CONSERVED ALONG A CHORD**: the three first-slot values a chord
reads multiply to a nonzero rational square.  At most one abscissa can vanish — two
would force `ab = 0` — and when one does, the convention value `ab` is exactly the
product of the other two, so the triple product is `(ab)²`. -/
theorem theFirstFaceIsConservedAlongAChord (ha : a ≠ 0) (hb : b ≠ 0)
    {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : y₁ ^ 2 = x₁ * (x₁ - a) * (x₁ - b))
    (h₂ : y₂ ^ 2 = x₂ * (x₂ - a) * (x₂ - b)) (hx : x₁ ≠ x₂) :
    ∃ t : ℚ, t ≠ 0 ∧
      (if x₁ = 0 then a * b else x₁) * (if x₂ = 0 then a * b else x₂) *
        (if (((y₂ - y₁) / (x₂ - x₁)) ^ 2 + (a + b) - x₁ - x₂) = 0 then a * b
          else (((y₂ - y₁) / (x₂ - x₁)) ^ 2 + (a + b) - x₁ - x₂)) = t ^ 2 := by
  set L : ℚ := (y₂ - y₁) / (x₂ - x₁) with hL
  set x₃ : ℚ := L ^ 2 + (a + b) - x₁ - x₂ with hx₃
  set N : ℚ := y₁ - L * x₁ with hN
  have hprod : x₁ * x₂ * x₃ = N ^ 2 := theChordProductIsASquare h₁ h₂ hx
  have hsym : x₁ * x₂ + x₃ * (x₁ + x₂) = a * b - 2 * L * N :=
    theChordSecondSymmetric h₁ h₂ hx
  have hab0 : a * b ≠ 0 := mul_ne_zero ha hb
  -- a vanishing abscissa forces the intercept to vanish
  have hvan : ∀ {u v w : ℚ}, u * v * w = N ^ 2 → u = 0 → N = 0 := by
    intro u v w h hu
    have : N ^ 2 = 0 := by rw [← h, hu]; ring
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  by_cases h1 : x₁ = 0
  · -- the chord passes through the origin
    have hN0 : N = 0 := hvan hprod h1
    have hx₂x₃ : x₂ * x₃ = a * b := by
      rw [h1] at hsym
      rw [hN0] at hsym
      linarith [hsym]
    have hx₂0 : x₂ ≠ 0 := fun hc => hab0 (by rw [← hx₂x₃, hc]; ring)
    have hx₃0 : x₃ ≠ 0 := fun hc => hab0 (by rw [← hx₂x₃, hc]; ring)
    refine ⟨a * b, hab0, ?_⟩
    rw [if_pos h1, if_neg hx₂0, if_neg hx₃0]
    linear_combination (a * b) * hx₂x₃
  · by_cases h2 : x₂ = 0
    · have hN0 : N = 0 := hvan (by rw [← hprod]; ring : x₂ * x₁ * x₃ = N ^ 2) h2
      have hx₁x₃ : x₁ * x₃ = a * b := by
        rw [h2] at hsym
        rw [hN0] at hsym
        linarith [hsym]
      have hx₃0 : x₃ ≠ 0 := fun hc => hab0 (by rw [← hx₁x₃, hc]; ring)
      refine ⟨a * b, hab0, ?_⟩
      rw [if_neg h1, if_pos h2, if_neg hx₃0]
      linear_combination (a * b) * hx₁x₃
    · by_cases h3 : x₃ = 0
      · have hN0 : N = 0 := hvan (by rw [← hprod]; ring : x₃ * x₁ * x₂ = N ^ 2) h3
        have hx₁x₂ : x₁ * x₂ = a * b := by
          rw [h3] at hsym
          rw [hN0] at hsym
          linarith [hsym]
        refine ⟨a * b, hab0, ?_⟩
        rw [if_neg h1, if_neg h2, if_pos h3]
        linear_combination (a * b) * hx₁x₂
      · refine ⟨N, ?_, ?_⟩
        · intro hc
          rw [hc] at hprod
          have : x₁ * x₂ * x₃ = 0 := by rw [hprod]; ring
          rcases mul_eq_zero.mp this with hz | hz
          · rcases mul_eq_zero.mp hz with hz' | hz'
            · exact h1 hz'
            · exact h2 hz'
          · exact h3 hz
        · rw [if_neg h1, if_neg h2, if_neg h3]
          exact hprod


/-- Vieta's second relation for the chord cubic shifted to the second torsion point. -/
theorem theShiftedChordSecondSymmetric {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : y₁ ^ 2 = x₁ * (x₁ - a) * (x₁ - b))
    (h₂ : y₂ ^ 2 = x₂ * (x₂ - a) * (x₂ - b)) (hx : x₁ ≠ x₂) :
    (x₁ - a) * (x₂ - a)
        + ((((y₂ - y₁) / (x₂ - x₁)) ^ 2 + (a + b) - x₁ - x₂) - a)
          * ((x₁ - a) + (x₂ - a))
      = a * (a - b) - 2 * ((y₂ - y₁) / (x₂ - x₁))
          * (((y₂ - y₁) / (x₂ - x₁)) * a + (y₁ - ((y₂ - y₁) / (x₂ - x₁)) * x₁)) := by
  have hd : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  field_simp
  linear_combination (-(x₂ - x₁)) * h₁ + (x₂ - x₁) * h₂

/-- **THE SECOND FACE IS CONSERVED ALONG A CHORD**: the same law at the second
two-torsion point.  At most one shifted abscissa can vanish — two would force
`a(a−b) = 0` — and the convention value `a(a−b)` is exactly the product of the other
two when one does. -/
theorem theSecondFaceIsConservedAlongAChord (ha : a ≠ 0) (hab : a - b ≠ 0)
    {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : y₁ ^ 2 = x₁ * (x₁ - a) * (x₁ - b))
    (h₂ : y₂ ^ 2 = x₂ * (x₂ - a) * (x₂ - b)) (hx : x₁ ≠ x₂) :
    ∃ t : ℚ, t ≠ 0 ∧
      (if x₁ = a then a * (a - b) else x₁ - a) * (if x₂ = a then a * (a - b) else x₂ - a) *
        (if (((y₂ - y₁) / (x₂ - x₁)) ^ 2 + (a + b) - x₁ - x₂) = a then a * (a - b)
          else (((y₂ - y₁) / (x₂ - x₁)) ^ 2 + (a + b) - x₁ - x₂) - a) = t ^ 2 := by
  set L : ℚ := (y₂ - y₁) / (x₂ - x₁) with hL
  set x₃ : ℚ := L ^ 2 + (a + b) - x₁ - x₂ with hx₃
  set N : ℚ := L * a + (y₁ - L * x₁) with hN
  have hprod : (x₁ - a) * (x₂ - a) * (x₃ - a) = N ^ 2 :=
    theShiftedChordProductIsASquare h₁ h₂ hx
  have hsym : (x₁ - a) * (x₂ - a) + (x₃ - a) * ((x₁ - a) + (x₂ - a))
      = a * (a - b) - 2 * L * N := theShiftedChordSecondSymmetric h₁ h₂ hx
  have hab0 : a * (a - b) ≠ 0 := mul_ne_zero ha hab
  have hvan : ∀ {u v w : ℚ}, u * v * w = N ^ 2 → u = 0 → N = 0 := by
    intro u v w h hu
    have : N ^ 2 = 0 := by rw [← h, hu]; ring
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  by_cases h1 : x₁ = a
  · have he1 : x₁ - a = 0 := by rw [h1]; ring
    have hN0 : N = 0 := hvan hprod he1
    have h23 : (x₂ - a) * (x₃ - a) = a * (a - b) := by
      rw [he1] at hsym
      rw [hN0] at hsym
      linarith [hsym]
    have hx₂0 : x₂ ≠ a := by
      intro hc
      refine hab0 ?_
      rw [← h23, hc]
      ring
    have hx₃0 : x₃ ≠ a := by
      intro hc
      refine hab0 ?_
      rw [← h23, hc]
      ring
    refine ⟨a * (a - b), hab0, ?_⟩
    rw [if_pos h1, if_neg hx₂0, if_neg hx₃0]
    linear_combination (a * (a - b)) * h23
  · by_cases h2 : x₂ = a
    · have he2 : x₂ - a = 0 := by rw [h2]; ring
      have hN0 : N = 0 :=
        hvan (by rw [← hprod]; ring : (x₂ - a) * (x₁ - a) * (x₃ - a) = N ^ 2) he2
      have h13 : (x₁ - a) * (x₃ - a) = a * (a - b) := by
        rw [he2] at hsym
        rw [hN0] at hsym
        linarith [hsym]
      have hx₃0 : x₃ ≠ a := by
        intro hc
        refine hab0 ?_
        rw [← h13, hc]
        ring
      refine ⟨a * (a - b), hab0, ?_⟩
      rw [if_neg h1, if_pos h2, if_neg hx₃0]
      linear_combination (a * (a - b)) * h13
    · by_cases h3 : x₃ = a
      · have he3 : x₃ - a = 0 := by rw [h3]; ring
        have hN0 : N = 0 :=
          hvan (by rw [← hprod]; ring : (x₃ - a) * (x₁ - a) * (x₂ - a) = N ^ 2) he3
        have h12 : (x₁ - a) * (x₂ - a) = a * (a - b) := by
          rw [he3] at hsym
          rw [hN0] at hsym
          linarith [hsym]
        refine ⟨a * (a - b), hab0, ?_⟩
        rw [if_neg h1, if_neg h2, if_pos h3]
        linear_combination (a * (a - b)) * h12
      · refine ⟨N, ?_, ?_⟩
        · intro hc
          rw [hc] at hprod
          have hz0 : (x₁ - a) * (x₂ - a) * (x₃ - a) = 0 := by rw [hprod]; ring
          rcases mul_eq_zero.mp hz0 with hz | hz
          · rcases mul_eq_zero.mp hz with hz' | hz'
            · exact h1 (by linarith [sub_eq_zero.mp hz'])
            · exact h2 (by linarith [sub_eq_zero.mp hz'])
          · exact h3 (by linarith [sub_eq_zero.mp hz])
        · rw [if_neg h1, if_neg h2, if_neg h3]
          exact hprod


/-! ## 3. The face is a homomorphism -/

private lemma someEq {x₁ y₁ x₂ y₂ : ℚ} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : (E a b).Nonsingular x₁ y₁} {h₂ : (E a b).Nonsingular x₂ y₂} :
    (Point.some h₁ : (E a b).Point) = Point.some h₂ := by
  subst hx; subst hy; rfl

lemma slotOne_ne (ha : a ≠ 0) (hb : b ≠ 0) (P : (E a b).Point) :
    slotOne a b P ≠ 0 := by
  rcases P with _ | @⟨x, y, h⟩
  · exact one_ne_zero
  · rw [slotOne_some]
    split_ifs with hx
    · exact mul_ne_zero ha hb
    · exact hx

lemma slotTwo_ne (ha : a ≠ 0) (hab : a - b ≠ 0) (P : (E a b).Point) :
    slotTwo a b P ≠ 0 := by
  rcases P with _ | @⟨x, y, h⟩
  · exact one_ne_zero
  · rw [slotTwo_some]
    split_ifs with hx
    · exact mul_ne_zero ha hab
    · exact sub_ne_zero.mpr hx

private lemma sqcls_one_mul_self {s : ℚ} (hs : s ≠ 0) : Descent.SqCls 1 (s * s) := by
  refine ⟨1 / s, one_div_ne_zero hs, ?_⟩
  field_simp

private lemma sqcls_scale_sq {z s : ℚ} (h : Descent.SqCls z 1) (hs : s ≠ 0) :
    Descent.SqCls z (s * s) := by
  obtain ⟨c, hc, hval⟩ := h
  refine ⟨c / s, div_ne_zero hc hs, ?_⟩
  rw [hval]
  field_simp

/-- Extract a square class from a conserved triple. -/
private lemma sqcls_of_triple {s₁ s₂ s₃ t : ℚ} (h1 : s₁ ≠ 0) (h2 : s₂ ≠ 0)
    (ht : t ≠ 0) (h : s₁ * s₂ * s₃ = t ^ 2) : Descent.SqCls s₃ (s₁ * s₂) := by
  refine ⟨t / (s₁ * s₂), div_ne_zero ht (mul_ne_zero h1 h2), ?_⟩
  rw [div_pow, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 (mul_ne_zero h1 h2))]
  linear_combination (s₁ * s₂) * h

private lemma addX_eq (x₁ x₂ L : ℚ) :
    (E a b).addX x₁ x₂ L = L ^ 2 + (a + b) - x₁ - x₂ := by
  simp only [addX, E]
  ring

private lemma slope_eq {x₁ y₁ x₂ y₂ : ℚ} (hx : x₁ ≠ x₂) :
    (E a b).slope x₁ x₂ y₁ y₂ = (y₂ - y₁) / (x₂ - x₁) := by
  rw [slope_of_X_ne hx]
  have h : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have h' : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  rw [div_eq_div_iff h h']
  ring

set_option maxHeartbeats 1000000 in
/-- **THE DESCENT FACE IS A HOMOMORPHISM ON EVERY FULL-TWO-TORSION CURVE**: both
slots carry sums to products modulo squares, for every `a, b` with `a`, `b`, `a−b`
nonzero.  The chord case is the conservation law; the tangent case is the doubling
law; the vertical case is the reflection.  Nothing else occurs. -/
theorem theFaceIsAHomomorphismOnEveryFullTwoTorsionCurve
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0) (P Q : (E a b).Point) :
    Descent.SqCls (slotOne a b (P + Q)) (slotOne a b P * slotOne a b Q) ∧
    Descent.SqCls (slotTwo a b (P + Q)) (slotTwo a b P * slotTwo a b Q) := by
  rcases P with _ | @⟨x₁, y₁, h₁⟩
  · rw [← Point.zero_def, zero_add]
    rw [show slotOne a b 0 = 1 from rfl, show slotTwo a b 0 = 1 from rfl, one_mul, one_mul]
    exact ⟨Descent.sqClsRefl _, Descent.sqClsRefl _⟩
  rcases Q with _ | @⟨x₂, y₂, h₂⟩
  · rw [← Point.zero_def, add_zero]
    rw [show slotOne a b 0 = 1 from rfl, show slotTwo a b 0 = 1 from rfl, mul_one, mul_one]
    exact ⟨Descent.sqClsRefl _, Descent.sqClsRefl _⟩
  by_cases hx : x₁ = x₂
  · -- the two points share an abscissa: they are equal or opposite
    subst hx
    have hc₁ := onCurve h₁
    have hc₂ := onCurve h₂
    have hyy : (y₂ - y₁) * (y₂ + y₁) = 0 := by linear_combination hc₂ - hc₁
    have hsame : slotOne a b (Point.some h₂) = slotOne a b (Point.some h₁) := by
      rw [slotOne_some, slotOne_some]
    have hsame2 : slotTwo a b (Point.some h₂) = slotTwo a b (Point.some h₁) := by
      rw [slotTwo_some, slotTwo_some]
    rcases mul_eq_zero.mp hyy with hcase | hcase
    · -- equal points: the double
      have heq : (Point.some h₂ : (E a b).Point) = Point.some h₁ :=
        someEq rfl (by linarith)
      rw [hsame, hsame2, heq]
      obtain ⟨k1, k2⟩ :=
        theDoublesLandInTheKernelOnEveryFullTwoTorsionCurve ha hb hab (Point.some h₁)
      exact ⟨sqcls_scale_sq k1 (slotOne_ne ha hb _),
        sqcls_scale_sq k2 (slotTwo_ne ha hab _)⟩
    · by_cases hy0 : y₁ = 0
      · have heq : (Point.some h₂ : (E a b).Point) = Point.some h₁ :=
          someEq rfl (by linarith)
        rw [hsame, hsame2, heq]
        obtain ⟨k1, k2⟩ :=
          theDoublesLandInTheKernelOnEveryFullTwoTorsionCurve ha hb hab (Point.some h₁)
        exact ⟨sqcls_scale_sq k1 (slotOne_ne ha hb _),
          sqcls_scale_sq k2 (slotTwo_ne ha hab _)⟩
      · -- opposite points: the sum is the identity
        have hzero : (Point.some h₁ : (E a b).Point) + Point.some h₂ = 0 :=
          Point.add_of_Y_eq rfl (by rw [negY_eq]; linarith)
        rw [hsame, hsame2, hzero]
        exact ⟨sqcls_one_mul_self (slotOne_ne ha hb _),
          sqcls_one_mul_self (slotTwo_ne ha hab _)⟩
  · -- the chord case
    have hc₁ := onCurve h₁
    have hc₂ := onCurve h₂
    rw [Point.add_of_X_ne hx]
    obtain ⟨t₁, ht₁, hcons₁⟩ := theFirstFaceIsConservedAlongAChord ha hb hc₁ hc₂ hx
    obtain ⟨t₂, ht₂, hcons₂⟩ := theSecondFaceIsConservedAlongAChord ha hab hc₁ hc₂ hx
    have hX : (E a b).addX x₁ x₂ ((E a b).slope x₁ x₂ y₁ y₂)
        = ((y₂ - y₁) / (x₂ - x₁)) ^ 2 + (a + b) - x₁ - x₂ := by
      rw [addX_eq, slope_eq hx]
    constructor
    · rw [slotOne_some, hX]
      rw [slotOne_some, slotOne_some] at *
      exact sqcls_of_triple (slotOne_ne ha hb (Point.some h₁))
        (slotOne_ne ha hb (Point.some h₂)) ht₁ hcons₁
    · rw [slotTwo_some, hX]
      rw [slotTwo_some, slotTwo_some] at *
      exact sqcls_of_triple (slotTwo_ne ha hab (Point.some h₁))
        (slotTwo_ne ha hab (Point.some h₂)) ht₂ hcons₂

end Soma.Holonics.Millennium.GeneralHom
