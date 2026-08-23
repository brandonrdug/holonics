import ElementaryHolonics.Millennium.GeneralSupport

/-!
# GeneralHalving: the kernel of the face is the doubles, on every full-2-torsion curve

The halving is where the two-descent becomes exact, and on the two-parameter family
it has a closed form that the congruent slice hides.  Write the three slot values as
squares, `x = u²`, `x − a = v²`, `x − b = w²`, with `y = uvw`.  Then

```text
a = u² − v²,   b = u² − w²
```

and the half point is the **pairwise composition of the three roots**:

```text
Q = ( (u+v)(u+w),  (u+v)(u+w)(v+w) ).
```

Everything follows by cancelling `(u ± v)`, `(u ± w)`:

* `X − a = (u+v)(v+w)` and `X − b = (u+w)(v+w)`, so `Y² = X(X−a)(X−b)` on the nose;
* `X² − ab = 2u·Y`, so the tangent slope at `Q` is exactly `u`, and the doubled
  abscissa is `u² = x`;
* the doubled ordinate is `uvw = y`.

None of `u+v`, `u+w`, `v+w` can vanish, because they would force `a = 0`, `b = 0` or
`a = b`.  So the halving is **total**: no case analysis, no degenerate branch, and the
two-torsion points are covered by the same formula with one root equal to zero.

* **`theHalvingIdentities`** — the four identities above.
* **`theKernelIsTheDoublesOnEveryFullTwoTorsionCurve`** — a point whose two slots are
  trivial square classes is a double.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.GeneralHalving

open WeierstrassCurve.Affine
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.GeneralFace

/-! ## 1. The halving identities -/

/-- **THE HALVING IDENTITIES**: with `a = u²−v²` and `b = u²−w²`, the point
`Q = ((u+v)(u+w), (u+v)(u+w)(v+w))` lies on the curve, its tangent slope is `u`, and
doubling it returns `(u², uvw)`. -/
theorem theHalvingIdentities (u v w : ℚ) :
    ((u + v) * (u + w) - (u ^ 2 - v ^ 2) = (u + v) * (v + w)) ∧
    ((u + v) * (u + w) - (u ^ 2 - w ^ 2) = (u + w) * (v + w)) ∧
    (((u + v) * (u + w) * (v + w)) ^ 2
      = (u + v) * (u + w) * ((u + v) * (v + w)) * ((u + w) * (v + w))) ∧
    (((u + v) * (u + w)) ^ 2 - (u ^ 2 - v ^ 2) * (u ^ 2 - w ^ 2)
      = 2 * u * ((u + v) * (u + w) * (v + w))) := by
  refine ⟨by ring, by ring, by ring, by ring⟩

/-! ## 2. The half point -/

variable {a b : ℚ}

/-- The half point built from three chosen square roots. -/
def halfAbscissa (u v w : ℚ) : ℚ := (u + v) * (u + w)

/-- Its ordinate. -/
def halfOrdinate (u v w : ℚ) : ℚ := (u + v) * (u + w) * (v + w)

lemma half_onCurve {u v w : ℚ} (ha : a = u ^ 2 - v ^ 2) (hb : b = u ^ 2 - w ^ 2) :
    halfOrdinate u v w ^ 2
      = halfAbscissa u v w * (halfAbscissa u v w - a) * (halfAbscissa u v w - b) := by
  rw [halfAbscissa, halfOrdinate, ha, hb]
  ring

/-- The three pairwise sums are nonzero exactly because the roots are distinct. -/
lemma half_sums_ne {u v w : ℚ} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab0 : a - b ≠ 0)
    (ha : a = u ^ 2 - v ^ 2) (hb : b = u ^ 2 - w ^ 2) :
    u + v ≠ 0 ∧ u + w ≠ 0 ∧ v + w ≠ 0 := by
  refine ⟨fun hc => ha0 ?_, fun hc => hb0 ?_, fun hc => hab0 ?_⟩
  · rw [ha]
    have : v = -u := by linarith
    rw [this]
    ring
  · rw [hb]
    have : w = -u := by linarith
    rw [this]
    ring
  · rw [ha, hb]
    have : w = -v := by linarith
    rw [this]
    ring

lemma half_nonsingular {u v w : ℚ} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab0 : a - b ≠ 0)
    (ha : a = u ^ 2 - v ^ 2) (hb : b = u ^ 2 - w ^ 2) :
    (E a b).Nonsingular (halfAbscissa u v w) (halfOrdinate u v w) := by
  obtain ⟨h1, h2, h3⟩ := half_sums_ne ha0 hb0 hab0 ha hb
  have hY : halfOrdinate u v w ≠ 0 := by
    rw [halfOrdinate]
    exact mul_ne_zero (mul_ne_zero h1 h2) h3
  rw [nonsingular_iff]
  refine ⟨?_, Or.inr ?_⟩
  · rw [equation_iff]
    simp only [E]
    have := half_onCurve (a := a) (b := b) ha hb
    linarith [this]
  · simp only [negY, E]
    intro hc
    exact hY (by linarith)

set_option maxHeartbeats 1000000 in
/-- **THE HALF POINT DOUBLES BACK**: doubling `Q` returns `(u², uvw)`. -/
theorem theHalfPointDoublesBack {u v w : ℚ} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hab0 : a - b ≠ 0) (ha : a = u ^ 2 - v ^ 2) (hb : b = u ^ 2 - w ^ 2)
    (hP : (E a b).Nonsingular (u ^ 2) (u * v * w)) :
    (Point.some (half_nonsingular ha0 hb0 hab0 ha hb) : (E a b).Point)
      + Point.some (half_nonsingular ha0 hb0 hab0 ha hb) = Point.some hP := by
  obtain ⟨h1, h2, h3⟩ := half_sums_ne ha0 hb0 hab0 ha hb
  set X : ℚ := halfAbscissa u v w with hX
  set Y : ℚ := halfOrdinate u v w with hY
  have hY0 : Y ≠ 0 := by
    rw [hY, halfOrdinate]
    exact mul_ne_zero (mul_ne_zero h1 h2) h3
  have hyne : Y ≠ (E a b).negY X Y := by
    simp only [negY, E]
    intro hc
    exact hY0 (by linarith)
  rw [Point.add_self_of_Y_ne hyne]
  have hYpoly : Y = (u + v) * (u + w) * (v + w) := by rw [hY, halfOrdinate]
  have hXpoly : X = (u + v) * (u + w) := by rw [hX, halfAbscissa]
  subst ha
  subst hb
  -- the tangent at the half point passes through the negation of the doubled point,
  -- so its slope is the sum of the three roots
  have hslope : (E (u ^ 2 - v ^ 2) (u ^ 2 - w ^ 2)).slope X X Y Y = u + v + w := by
    rw [slope_of_Y_ne rfl hyne]
    simp only [negY, E]
    rw [hXpoly, hYpoly]
    rw [div_eq_iff (by
      intro hc
      exact (mul_ne_zero (mul_ne_zero h1 h2) h3) (by linarith))]
    ring
  have hX2 : (E (u ^ 2 - v ^ 2) (u ^ 2 - w ^ 2)).addX X X
      ((E (u ^ 2 - v ^ 2) (u ^ 2 - w ^ 2)).slope X X Y Y) = u ^ 2 := by
    rw [hslope]
    simp only [addX, E]
    rw [hXpoly]
    ring
  have hY2 : (E (u ^ 2 - v ^ 2) (u ^ 2 - w ^ 2)).addY X X Y
      ((E (u ^ 2 - v ^ 2) (u ^ 2 - w ^ 2)).slope X X Y Y) = u * v * w := by
    rw [addY, negAddY, hX2, hslope]
    simp only [negY, E]
    rw [hXpoly, hYpoly]
    ring
  simp only [hX2, hY2]


/-! ## 3. The kernel is the doubles -/

set_option maxHeartbeats 1000000 in
/-- **THE THREE ROOTS EXIST**: if both slots are trivial square classes then all three
slot values are squares, with the product of the roots equal to the ordinate.  The two
conventions at the two-torsion points are what make this uniform: at `(0,0)` the pair
`(ab, −a)` being square forces `−b` square, and at `(a,0)` the pair `(a, a(a−b))` being
square forces `a−b` square. -/
theorem theThreeRootsExist (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab0 : a - b ≠ 0)
    {x y : ℚ} (hns : (E a b).Nonsingular x y)
    (h1 : Descent.SqCls (slotOne a b (Point.some hns)) 1)
    (h2 : Descent.SqCls (slotTwo a b (Point.some hns)) 1) :
    ∃ u v w : ℚ, u ^ 2 = x ∧ v ^ 2 = x - a ∧ w ^ 2 = x - b ∧ u * v * w = y := by
  have hcurve := onCurve hns
  obtain ⟨c₁, hc₁, hv₁⟩ := h1
  obtain ⟨c₂, hc₂, hv₂⟩ := h2
  rw [slotOne_some, mul_one] at hv₁
  rw [slotTwo_some, mul_one] at hv₂
  by_cases hy : y = 0
  · -- the two-torsion points
    rw [hy] at hcurve
    have hroots : x * (x - a) * (x - b) = 0 := by linear_combination -hcurve
    have hx3 : x = 0 ∨ x = a ∨ x = b := by
      rcases mul_eq_zero.mp hroots with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact Or.inl h''
        · exact Or.inr (Or.inl (by linarith [sub_eq_zero.mp h'']))
      · exact Or.inr (Or.inr (by linarith [sub_eq_zero.mp h']))
    rcases hx3 with hx | hx | hx
    · -- `(0,0)`: `ab` and `−a` are squares, so `−b` is
      rw [if_pos hx] at hv₁
      rw [if_neg (by rw [hx]; intro hc; exact ha0 (by linarith)), hx] at hv₂
      have hane : a = -c₂ ^ 2 := by linarith [hv₂]
      have habe : a * b = c₁ ^ 2 := hv₁
      refine ⟨0, c₂, c₁ / c₂, by rw [hx]; ring, by rw [hx, hane]; ring, ?_, by rw [hy]; ring⟩
      rw [hx, div_pow]
      rw [div_eq_iff (pow_ne_zero 2 hc₂)]
      rw [hane] at habe
      linarith [habe]
    · -- `(a,0)`: `a` and `a(a−b)` are squares, so `a−b` is
      rw [if_neg (by rw [hx]; exact ha0), hx] at hv₁
      rw [if_pos hx] at hv₂
      refine ⟨c₁, 0, c₂ / c₁, by rw [hx]; exact hv₁.symm, by rw [hx]; ring, ?_, by rw [hy]; ring⟩
      rw [hx, div_pow]
      rw [div_eq_iff (pow_ne_zero 2 hc₁)]
      rw [← hv₁]
      linarith [hv₂]
    · -- `(b,0)`: both slots are read plainly
      have hxa : x ≠ a := by
        rw [hx]
        intro hc
        exact hab0 (by linarith)
      rw [if_neg (by rw [hx]; exact hb0)] at hv₁
      rw [if_neg hxa] at hv₂
      exact ⟨c₁, c₂, 0, hv₁.symm, hv₂.symm, by rw [hx]; ring, by rw [hy]; ring⟩
  · -- a point off the two-torsion: the third root is the quotient
    have hx0 : x ≠ 0 := by
      intro hc
      refine hy ?_
      rw [hc] at hcurve
      have : y ^ 2 = 0 := by rw [hcurve]; ring
      exact pow_eq_zero_iff two_ne_zero |>.mp this
    have hxa : x ≠ a := by
      intro hc
      refine hy ?_
      rw [hc] at hcurve
      have : y ^ 2 = 0 := by rw [hcurve]; ring
      exact pow_eq_zero_iff two_ne_zero |>.mp this
    rw [if_neg hx0] at hv₁
    rw [if_neg hxa] at hv₂
    have hc₁' : c₁ ≠ 0 := hc₁
    have hc₂' : c₂ ≠ 0 := hc₂
    refine ⟨c₁, c₂, y / (c₁ * c₂), hv₁.symm, hv₂.symm, ?_, ?_⟩
    · rw [div_pow, div_eq_iff (pow_ne_zero 2 (mul_ne_zero hc₁' hc₂'))]
      have hexp : (c₁ * c₂) ^ 2 = x * (x - a) := by
        rw [mul_pow, ← hv₁, ← hv₂]
      rw [hexp]
      linear_combination hcurve
    · field_simp

set_option maxHeartbeats 1000000 in
/-- **THE KERNEL OF THE FACE IS THE DOUBLES ON EVERY FULL-TWO-TORSION CURVE**: a point
whose two slots are trivial square classes is a double.  With `GeneralFace`'s converse
this makes the two-descent **exact** on the whole two-parameter family. -/
theorem theKernelIsTheDoublesOnEveryFullTwoTorsionCurve
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab0 : a - b ≠ 0) (P : (E a b).Point)
    (h1 : Descent.SqCls (slotOne a b P) 1) (h2 : Descent.SqCls (slotTwo a b P) 1) :
    ∃ Q : (E a b).Point, Q + Q = P := by
  rcases P with _ | @⟨x, y, hns⟩
  · exact ⟨0, by rw [← Point.zero_def, add_zero]⟩
  · obtain ⟨u, v, w, hu, hv, hw, huvw⟩ := theThreeRootsExist ha0 hb0 hab0 hns h1 h2
    subst hu
    subst huvw
    have ha' : a = u ^ 2 - v ^ 2 := by linarith [hv]
    have hb' : b = u ^ 2 - w ^ 2 := by linarith [hw]
    exact ⟨Point.some (half_nonsingular ha0 hb0 hab0 ha' hb'),
      theHalfPointDoublesBack ha0 hb0 hab0 ha' hb' hns⟩

/-- **THE TWO-DESCENT IS EXACT ON EVERY FULL-TWO-TORSION CURVE**: the kernel of the
descent face is exactly the doubles. -/
theorem theTwoDescentIsExactOnEveryFullTwoTorsionCurve
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab0 : a - b ≠ 0) (P : (E a b).Point) :
    (Descent.SqCls (slotOne a b P) 1 ∧ Descent.SqCls (slotTwo a b P) 1)
      ↔ ∃ Q : (E a b).Point, Q + Q = P := by
  constructor
  · rintro ⟨p1, p2⟩
    exact theKernelIsTheDoublesOnEveryFullTwoTorsionCurve ha0 hb0 hab0 P p1 p2
  · rintro ⟨Q, rfl⟩
    exact theDoublesLandInTheKernelOnEveryFullTwoTorsionCurve ha0 hb0 hab0 Q

end Soma.Holonics.Millennium.GeneralHalving
