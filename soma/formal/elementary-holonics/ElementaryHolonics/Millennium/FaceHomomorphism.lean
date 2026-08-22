import ElementaryHolonics.Millennium.ChordFace
import ElementaryHolonics.Millennium.FaithfulFace
import ElementaryHolonics.Millennium.DistantWindings
import Mathlib.Tactic

/-!
# FaceHomomorphism: the descent face is a homomorphism on the whole point group

**The assembly deed.**  `ChordFace.lean` proved the heart — the chord's three slot products
are literal squares, for every twist at once — and `FaithfulFace.lean` proved the doubling
and half-turn-translation families at coordinate level with their point-group lifts.  This
file assembles them, together with the three landing laws the general chord still owed,
into the total point-level theorems that have been the route's blocking named-open
propositions since `Descent.lean` was written:

* **`theDescentFaceIsAHomomorphismEverywhereHolds`** — discharges
  `Descent.TheFaceIsAHomomorphismEverywhere` on `y² = x³ − x`;
* **`theRankOneFaceIsAHomomorphismEverywhereHolds`** — discharges
  `RankOne.TheFaceIsAHomomorphismEverywhere` on `y² = x³ − 25x`;
* **`theGeneralChordClosesTheFaceHolds`** — discharges
  `FaithfulFace.TheGeneralChordClosesTheFace`, the guarded coordinate form.

The two landing laws are where the classical conventions are *derived* rather than
declared: when the chord's third abscissa lands on the vanishing slot, the constraint
algebra forces the exact values

```text
X₃ = 0  ⟹  x₁·x₂ = −n²           (the (0,0) convention −n² arrives as a theorem)
X₃ = n  ⟹  (x₁−n)(x₂−n) = 2n²    (the (n,0) convention 2n² arrives as a theorem)
```

— both verified in exact rational arithmetic over hundreds of random samples before
encoding, then kernel-checked here for every `n` at once.

**The consequence that closes the rank-one descent certificate.**  With the homomorphism
discharged and `DistantWindings` having already proved the five-curve torsion is the Klein
four-group, the certificate `RankOne.theFaceSeparatesTheNewPoint` composes into
**`theNewPointEscapesTheTorsionAndTheDoubles`**: `P = (−4, 6)` is not `T + 2Q` for any
torsion `T` and any point `Q` — the point is nonzero in `E₅(ℚ)/(torsion + 2·E₅(ℚ))`,
unconditionally.  Every ingredient is now a theorem in this tree.

Every `theorem` is discharged and none depends on `sorryAx`.  **Boundary**: the kernel's
converse — a point with trivial face is a double — remains open
(`Descent.TheKernelIsTheDoubledPopulation`); only the forward half is proved here
(`theDoublesLandInTheKernel`).  Nothing about the Birch–Swinnerton-Dyer conjecture.
-/

namespace Soma.Holonics.Millennium.FaceHomomorphism

open WeierstrassCurve.Affine

/-! ## 1. Square-class helpers -/

private lemma sqcls_of_mul_eq_sq {a b s : ℚ} (hb : b ≠ 0) (hs : s ≠ 0)
    (h : a * b = s ^ 2) : Descent.SqCls a b := by
  refine ⟨s / b, div_ne_zero hs hb, ?_⟩
  rw [div_pow, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hb)]
  linear_combination b * h

private lemma sqcls_one_mul_self {s : ℚ} (hs : s ≠ 0) : Descent.SqCls 1 (s * s) := by
  refine ⟨1 / s, one_div_ne_zero hs, ?_⟩
  field_simp

private lemma sqcls_scale_sq {a s : ℚ} (h : Descent.SqCls a 1) (hs : s ≠ 0) :
    Descent.SqCls a (s * s) := by
  obtain ⟨c, hc, hval⟩ := h
  refine ⟨c / s, div_ne_zero hc hs, ?_⟩
  rw [hval]
  field_simp

private lemma sqcls_symm {a b : ℚ} (h : Descent.SqCls a b) : Descent.SqCls b a := by
  obtain ⟨c, hc, hval⟩ := h
  refine ⟨1 / c, one_div_ne_zero hc, ?_⟩
  rw [hval]
  field_simp

private lemma sqcls_mul_sq_left {a b t : ℚ} (h : Descent.SqCls a b) (ht : t ≠ 0) :
    Descent.SqCls (t ^ 2 * a) b := by
  obtain ⟨c, hc, hval⟩ := h
  exact ⟨t * c, mul_ne_zero ht hc, by rw [hval]; ring⟩

private lemma sqcls_absorb_right {a b c : ℚ} (h : Descent.SqCls a (b * c))
    (hc : Descent.SqCls c 1) : Descent.SqCls a b := by
  obtain ⟨k, hk, hkval⟩ := h
  obtain ⟨m, hm, hmval⟩ := hc
  exact ⟨k * m, mul_ne_zero hk hm, by rw [hkval, hmval]; ring⟩

/-! ## 2. The family landing laws

On any twist `y² = x³ − n²x` with slots read at `{0, n}`: the chord through two points off
the two-torsion lands generically (both slot classes carried by the chord identities), or
on the zero half-turn (the product of abscissae is exactly `−n²`), or on the `n` half-turn
(the product of shifted abscissae is exactly `2n²`). -/

/-- **A nonzero ordinate avoids the three roots**, on every twist at once. -/
theorem theNonzeroOrdinateAvoidsTheRoots {n x y : ℚ} (h : y ^ 2 = x ^ 3 - n ^ 2 * x)
    (hy : y ≠ 0) : x ≠ 0 ∧ x ≠ n ∧ x ≠ -n := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;>
    exact hy (pow_eq_zero_iff two_ne_zero |>.mp (by rw [h]; ring))

/-- **The chord lands generically**: when the third abscissa avoids `0` and `n`, both slot
classes are carried by the chord identities, with the nonvanishing of the line values
derived from the landing rather than assumed. -/
theorem theChordLandsGenerically {n x₁ y₁ x₂ y₂ lam : ℚ}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 - n ^ 2 * x₁) (h₂ : y₂ ^ 2 = x₂ ^ 3 - n ^ 2 * x₂)
    (hlam : lam * (x₂ - x₁) = y₂ - y₁) (hx : x₁ ≠ x₂)
    (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (hX0 : lam ^ 2 - x₁ - x₂ ≠ 0) (hXn : lam ^ 2 - x₁ - x₂ ≠ n) :
    Descent.SqCls (lam ^ 2 - x₁ - x₂) (x₁ * x₂) ∧
    Descent.SqCls (lam ^ 2 - x₁ - x₂ - n) ((x₁ - n) * (x₂ - n)) := by
  obtain ⟨ha1, ha2, -⟩ := theNonzeroOrdinateAvoidsTheRoots h₁ hy₁
  obtain ⟨hb1, hb2, -⟩ := theNonzeroOrdinateAvoidsTheRoots h₂ hy₂
  obtain ⟨i1, i2, -⟩ := ChordFace.theChordClosesTheSlots h₁ h₂ hlam hx
  have hz₁ : x₁ * x₂ ≠ 0 := mul_ne_zero ha1 hb1
  have hz₂ : (x₁ - n) * (x₂ - n) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr ha2) (sub_ne_zero.mpr hb2)
  have hnu : y₁ - lam * x₁ ≠ 0 := by
    intro hc
    rw [hc] at i1
    have h0 : x₁ * x₂ * (lam ^ 2 - x₁ - x₂) = 0 := by rw [i1]; ring
    rcases mul_eq_zero.mp h0 with h | h
    · exact hz₁ h
    · exact hX0 h
  have hnun : lam * n + (y₁ - lam * x₁) ≠ 0 := by
    intro hc
    rw [hc] at i2
    have h0 : (x₁ - n) * (x₂ - n) * (lam ^ 2 - x₁ - x₂ - n) = 0 := by rw [i2]; ring
    rcases mul_eq_zero.mp h0 with h | h
    · exact hz₂ h
    · exact hXn (by linarith [h])
  exact ChordFace.theChordClosesTheFaceGenerically h₁ h₂ hlam hx hz₁ hnu hz₂ hnun

/-- **The chord lands on the zero half-turn**: `X₃ = 0` forces `x₁·x₂ = −n²` exactly — the
classical convention value `−n²` at `(0,0)` is derived, not declared.  Both slot classes
follow: the first is `−1` (equivalently `−n²`), the second is `−n`. -/
theorem theChordLandsOnTheZeroHalfTurn {n x₁ y₁ x₂ y₂ lam : ℚ} (hn : n ≠ 0)
    (h₁ : y₁ ^ 2 = x₁ ^ 3 - n ^ 2 * x₁) (h₂ : y₂ ^ 2 = x₂ ^ 3 - n ^ 2 * x₂)
    (hlam : lam * (x₂ - x₁) = y₂ - y₁) (hx : x₁ ≠ x₂)
    (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (hX0 : lam ^ 2 - x₁ - x₂ = 0) :
    x₁ * x₂ = -n ^ 2 ∧
    Descent.SqCls (-1) (x₁ * x₂) ∧ Descent.SqCls (-n) ((x₁ - n) * (x₂ - n)) := by
  obtain ⟨ha1, ha2, -⟩ := theNonzeroOrdinateAvoidsTheRoots h₁ hy₁
  obtain ⟨hb1, hb2, -⟩ := theNonzeroOrdinateAvoidsTheRoots h₂ hy₂
  obtain ⟨i1, i2, -⟩ := ChordFace.theChordClosesTheSlots h₁ h₂ hlam hx
  have hz₂ : (x₁ - n) * (x₂ - n) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr ha2) (sub_ne_zero.mpr hb2)
  -- the line passes through the origin: its constant term vanishes
  have hnu2 : (y₁ - lam * x₁) ^ 2 = 0 := by
    linear_combination -i1 + (x₁ * x₂) * hX0
  have hnu : y₁ = lam * x₁ := by
    have := pow_eq_zero_iff two_ne_zero |>.mp hnu2
    linarith
  have hy2eq : y₂ = lam * x₂ := by linarith [hlam, hnu]
  have hx2 : x₂ = lam ^ 2 - x₁ := by linarith [hX0]
  -- the landing forces the product of abscissae exactly
  have hprod0 : x₁ * (x₁ * x₂ + n ^ 2) = 0 := by
    linear_combination h₁ - (y₁ + lam * x₁) * hnu + x₁ ^ 2 * hx2
  have hprod : x₁ * x₂ = -n ^ 2 := by
    rcases mul_eq_zero.mp hprod0 with h | h
    · exact absurd h ha1
    · linarith
  refine ⟨hprod, ⟨1 / n, one_div_ne_zero hn, ?_⟩, ?_⟩
  · rw [hprod]
    field_simp
  · -- the second slot rides the chord identity: `A·(−n) = (λn)²`
    have hlamn : lam ≠ 0 := by
      intro hc
      rw [hc] at hnu
      exact hy₁ (by linarith)
    have i2' : (x₁ - n) * (x₂ - n) * (-n) = (lam * n) ^ 2 := by
      linear_combination i2 - (x₁ - n) * (x₂ - n) * hX0
        + (lam * n + (y₁ - lam * x₁) + lam * n) * hnu
    refine ⟨lam * n / ((x₁ - n) * (x₂ - n)), div_ne_zero (mul_ne_zero hlamn hn) hz₂, ?_⟩
    rw [div_pow, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hz₂)]
    linear_combination ((x₁ - n) * (x₂ - n)) * i2'

/-- **The chord lands on the `n` half-turn**: `X₃ = n` forces `(x₁−n)(x₂−n) = 2n²` exactly
— the classical convention value `2n²` at `(n,0)` is derived, not declared.  Both slot
classes follow: the first is `n`, the second is `2` (equivalently `2n²`). -/
theorem theChordLandsOnTheSecondHalfTurn {n x₁ y₁ x₂ y₂ lam : ℚ} (hn : n ≠ 0)
    (h₁ : y₁ ^ 2 = x₁ ^ 3 - n ^ 2 * x₁) (h₂ : y₂ ^ 2 = x₂ ^ 3 - n ^ 2 * x₂)
    (hlam : lam * (x₂ - x₁) = y₂ - y₁) (hx : x₁ ≠ x₂)
    (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (hXn : lam ^ 2 - x₁ - x₂ = n) :
    (x₁ - n) * (x₂ - n) = 2 * n ^ 2 ∧
    Descent.SqCls n (x₁ * x₂) ∧ Descent.SqCls 2 ((x₁ - n) * (x₂ - n)) := by
  obtain ⟨ha1, ha2, -⟩ := theNonzeroOrdinateAvoidsTheRoots h₁ hy₁
  obtain ⟨hb1, hb2, -⟩ := theNonzeroOrdinateAvoidsTheRoots h₂ hy₂
  obtain ⟨i1, i2, -⟩ := ChordFace.theChordClosesTheSlots h₁ h₂ hlam hx
  have hz₁ : x₁ * x₂ ≠ 0 := mul_ne_zero ha1 hb1
  -- the line passes through `(n, 0)`: its value there vanishes
  have hval2 : (lam * n + (y₁ - lam * x₁)) ^ 2 = 0 := by
    linear_combination -i2 + ((x₁ - n) * (x₂ - n)) * hXn
  have hval : lam * n + (y₁ - lam * x₁) = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp hval2
  have hy1eq : y₁ = lam * x₁ - lam * n := by linarith
  have hx2 : x₂ = lam ^ 2 - x₁ - n := by linarith [hXn]
  -- the landing forces the shifted product exactly
  have hprod0 : (x₁ - n) * ((x₁ - n) * (x₂ - n) - 2 * n ^ 2) = 0 := by
    linear_combination h₁ - (y₁ + lam * x₁ - lam * n) * hy1eq
      + (x₁ - n) ^ 2 * hx2
  have hprod : (x₁ - n) * (x₂ - n) = 2 * n ^ 2 := by
    rcases mul_eq_zero.mp hprod0 with h | h
    · exact absurd h (sub_ne_zero.mpr ha2)
    · linarith
  have i1' : x₁ * x₂ * n = (y₁ - lam * x₁) ^ 2 := by
    linear_combination i1 - (x₁ * x₂) * hXn
  have hnu : y₁ - lam * x₁ ≠ 0 := by
    intro hc
    rw [hc] at i1'
    rcases mul_eq_zero.mp (by rw [i1']; ring : x₁ * x₂ * n = 0) with h | h
    · exact hz₁ h
    · exact hn h
  refine ⟨hprod, ?_, ⟨1 / n, one_div_ne_zero hn, ?_⟩⟩
  · refine ⟨(y₁ - lam * x₁) / (x₁ * x₂), div_ne_zero hnu hz₁, ?_⟩
    rw [div_pow, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hz₁)]
    linear_combination (x₁ * x₂) * i1'
  · rw [hprod]
    field_simp

/-! ## 3. The one-curve assembly: point-level plumbing on `y² = x³ − x` -/

private lemma onCurveOne {x y : ℚ} (h : Descent.E.Nonsingular x y) : y ^ 2 = x ^ 3 - x := by
  have h1 := ((nonsingular_iff x y).mp h).1
  rw [equation_iff] at h1
  simp only [Descent.E] at h1
  linarith [h1]

private lemma negYOne (x y : ℚ) : Descent.E.negY x y = -y := by
  simp [negY, Descent.E]

private lemma someEqOne {x₁ y₁ x₂ y₂ : ℚ} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : Descent.E.Nonsingular x₁ y₁} {h₂ : Descent.E.Nonsingular x₂ y₂} :
    (Point.some h₁ : Descent.E.Point) = Point.some h₂ := by
  subst hx; subst hy; rfl

private lemma slotOne_some {x y : ℚ} (h : Descent.E.Nonsingular x y) :
    Descent.slotOne (.some h) = if x = 0 then -1 else x := rfl

private lemma slotTwo_some {x y : ℚ} (h : Descent.E.Nonsingular x y) :
    Descent.slotTwo (.some h) = if x = 1 then 2 else x - 1 := rfl

private lemma slotOne_ne (P : Descent.E.Point) : Descent.slotOne P ≠ 0 := by
  rcases P with _ | @⟨x, y, h⟩
  · exact one_ne_zero
  · rw [slotOne_some]
    split_ifs with hx
    · norm_num
    · exact hx

private lemma slotTwo_ne (P : Descent.E.Point) : Descent.slotTwo P ≠ 0 := by
  rcases P with _ | @⟨x, y, h⟩
  · exact one_ne_zero
  · rw [slotTwo_some]
    split_ifs with hx
    · norm_num
    · exact sub_ne_zero.mpr hx

private lemma slopeLineOne {x₁ y₁ x₂ y₂ : ℚ} (hx : x₁ ≠ x₂) :
    Descent.E.slope x₁ x₂ y₁ y₂ * (x₂ - x₁) = y₂ - y₁ := by
  rw [slope_of_X_ne hx]
  have h : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  field_simp
  ring

private lemma addXOne (x₁ x₂ L : ℚ) :
    Descent.E.addX x₁ x₂ L = L ^ 2 - x₁ - x₂ := by
  simp only [addX, Descent.E]
  ring

private lemma halfTurnAbscissaOne {x y : ℚ} (h : Descent.E.Nonsingular x y) (hy : y = 0) :
    x = 0 ∨ x = 1 ∨ x = -1 := by
  have hc := onCurveOne h
  rw [hy] at hc
  have h0 : x * (x - 1) * (x + 1) = 0 := by linear_combination -hc
  rcases mul_eq_zero.mp h0 with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact Or.inl h''
    · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (by linarith))

/-- **The doubles land in the kernel**, at point level: both slots of `Q + Q` lie in the
trivial square class, for every point of `y² = x³ − x`.  This is the forward half of
`Descent.TheKernelIsTheDoubledPopulation`; the converse remains open. -/
theorem theDoublesLandInTheKernel (Q : Descent.E.Point) :
    Descent.SqCls (Descent.slotOne (Q + Q)) 1 ∧
    Descent.SqCls (Descent.slotTwo (Q + Q)) 1 := by
  rcases Q with _ | @⟨x, y, h⟩
  · rw [← Point.zero_def, add_zero]
    exact ⟨Descent.sqClsRefl 1, Descent.sqClsRefl 1⟩
  · by_cases hy : y = 0
    · have hzero : (Point.some h : Descent.E.Point) + Point.some h = 0 :=
        Point.add_self_of_Y_eq (by rw [negYOne, hy]; norm_num)
      rw [hzero]
      exact ⟨Descent.sqClsRefl 1, Descent.sqClsRefl 1⟩
    · have hyne : y ≠ Descent.E.negY x y := by
        rw [negYOne]
        intro hc
        exact hy (by linarith)
      rw [Point.add_self_of_Y_ne hyne]
      have hbr := FaithfulFace.theTangentCoordinateIsMathlibsAddX x y hy
      obtain ⟨hd0, hd1, -⟩ :=
        FaithfulFace.theDoubledPointIsNeverAHalfTurn (onCurveOne h) hy
      obtain ⟨ht1, ht2⟩ :=
        FaithfulFace.theDoubledSlotsAreTheTrivialClass (onCurveOne h) hy
      constructor
      · rw [slotOne_some, hbr, if_neg hd0]
        exact ht1
      · rw [slotTwo_some, hbr, if_neg hd1]
        exact ht2

/-- The chord through a point off the two-torsion and a half-turn closes both slots, at
point level — `FaithfulFace`'s translation lift composed with its face-law closure. -/
private lemma chordHalfTurnRight {x₁ y₁ x₂ : ℚ} (h₁ : Descent.E.Nonsingular x₁ y₁)
    (h₂ : Descent.E.Nonsingular x₂ 0) (hy₁ : y₁ ≠ 0) (hx : x₁ ≠ x₂) :
    Descent.SqCls (Descent.slotOne (Point.some h₁ + Point.some h₂))
      (Descent.slotOne (Point.some h₁) * Descent.slotOne (Point.some h₂)) ∧
    Descent.SqCls (Descent.slotTwo (Point.some h₁ + Point.some h₂))
      (Descent.slotTwo (Point.some h₁) * Descent.slotTwo (Point.some h₂)) := by
  have hcurve := onCurveOne h₁
  obtain ⟨hx0, hx1, hxm1⟩ := FaithfulFace.theNonzeroOrdinateAvoidsTheThreeRoots hcurve hy₁
  obtain ⟨⟨e1, e2⟩, ⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ := Descent.theFourFaceValues
  obtain ⟨q0, q1, q2, q3, q4, q5⟩ :=
    FaithfulFace.theFaceLawClosesOnEveryHalfTurnTranslation hcurve hy₁
  obtain ⟨⟨t00, t01, -⟩, ⟨t10, t11, -⟩, ⟨tm0, tm1, -⟩⟩ :=
    FaithfulFace.theTranslatedPointIsNeverAHalfTurn hcurve hy₁
  rw [FaithfulFace.theTranslationIsTheGroupSum h₁ h₂ hx]
  have hs₁ : Descent.slotOne (Point.some h₁) = x₁ := by rw [slotOne_some, if_neg hx0]
  have ht₁ : Descent.slotTwo (Point.some h₁) = x₁ - 1 := by rw [slotTwo_some, if_neg hx1]
  rcases halfTurnAbscissaOne h₂ rfl with h0 | h0 | h0
  · subst h0
    have hsQ : Descent.slotOne (Point.some h₂) = Descent.slotOne Descent.P00 := rfl
    have htQ : Descent.slotTwo (Point.some h₂) = Descent.slotTwo Descent.P00 := rfl
    constructor
    · rw [slotOne_some, if_neg t00, hs₁, hsQ]
      exact q0
    · rw [slotTwo_some, if_neg t01, ht₁, htQ]
      exact q1
  · subst h0
    have hsQ : Descent.slotOne (Point.some h₂) = Descent.slotOne Descent.P10 := rfl
    have htQ : Descent.slotTwo (Point.some h₂) = Descent.slotTwo Descent.P10 := rfl
    constructor
    · rw [slotOne_some, if_neg t10, hs₁, hsQ]
      exact q2
    · rw [slotTwo_some, if_neg t11, ht₁, htQ]
      exact q3
  · subst h0
    have hsQ : Descent.slotOne (Point.some h₂) = Descent.slotOne Descent.Pm10 := rfl
    have htQ : Descent.slotTwo (Point.some h₂) = Descent.slotTwo Descent.Pm10 := rfl
    constructor
    · rw [slotOne_some, if_neg tm0, hs₁, hsQ]
      exact q4
    · rw [slotTwo_some, if_neg tm1, ht₁, htQ]
      exact q5

/-- **THE DESCENT FACE IS A HOMOMORPHISM ON THE WHOLE POINT GROUP** of `y² = x³ − x`:
the named-open proposition of `Descent.lean`, discharged.  Every pair of points, every
configuration — identity, vertical inverses, doubling, half-turn chords, and the general
chord with its three landings — closes through the machinery this route built for it. -/
theorem theDescentFaceIsAHomomorphismEverywhereHolds :
    Descent.TheFaceIsAHomomorphismEverywhere := by
  intro P Q
  obtain ⟨⟨e1, e2⟩, -, -, -⟩ := Descent.theFourFaceValues
  rcases P with _ | @⟨x₁, y₁, h₁⟩
  · rw [← Point.zero_def, zero_add, e1, e2, one_mul, one_mul]
    exact ⟨Descent.sqClsRefl _, Descent.sqClsRefl _⟩
  rcases Q with _ | @⟨x₂, y₂, h₂⟩
  · rw [← Point.zero_def, add_zero, e1, e2, mul_one, mul_one]
    exact ⟨Descent.sqClsRefl _, Descent.sqClsRefl _⟩
  by_cases hx : x₁ = x₂
  · -- equal abscissae: the same point, its vertical inverse, or a repeated half-turn
    subst hx
    have hyy : (y₂ - y₁) * (y₂ + y₁) = 0 := by
      have hA := onCurveOne h₁
      have hB := onCurveOne h₂
      linear_combination hB - hA
    rcases mul_eq_zero.mp hyy with hcase | hcase
    · -- y₂ = y₁: the two points are one point, and the sum is the double
      have heq : (Point.some h₂ : Descent.E.Point) = Point.some h₁ :=
        someEqOne rfl (by linarith)
      rw [heq]
      obtain ⟨k1, k2⟩ := theDoublesLandInTheKernel (Point.some h₁)
      exact ⟨sqcls_scale_sq k1 (slotOne_ne _), sqcls_scale_sq k2 (slotTwo_ne _)⟩
    · -- y₂ = −y₁: vertical inverse or repeated half-turn
      by_cases hy0 : y₁ = 0
      · have heq : (Point.some h₂ : Descent.E.Point) = Point.some h₁ :=
          someEqOne rfl (by linarith)
        rw [heq]
        obtain ⟨k1, k2⟩ := theDoublesLandInTheKernel (Point.some h₁)
        exact ⟨sqcls_scale_sq k1 (slotOne_ne _), sqcls_scale_sq k2 (slotTwo_ne _)⟩
      · have hzero : (Point.some h₁ : Descent.E.Point) + Point.some h₂ = 0 :=
          Point.add_of_Y_eq rfl (by rw [negYOne]; linarith)
        have hs : Descent.slotOne (Point.some h₂) = Descent.slotOne (Point.some h₁) := by
          rw [slotOne_some, slotOne_some]
        have ht : Descent.slotTwo (Point.some h₂) = Descent.slotTwo (Point.some h₁) := by
          rw [slotTwo_some, slotTwo_some]
        rw [hzero, e1, e2, hs, ht]
        exact ⟨sqcls_one_mul_self (slotOne_ne _), sqcls_one_mul_self (slotTwo_ne _)⟩
  · -- distinct abscissae: a genuine chord
    by_cases hy1 : y₁ = 0
    · by_cases hy2 : y₂ = 0
      · -- both half-turns: the Klein population, computed in `Descent.lean`
        subst hy1; subst hy2
        obtain ⟨-, -, ⟨m01a, m01b⟩, ⟨m0m1a, m0m1b⟩, ⟨m1m1a, m1m1b⟩⟩ :=
          Descent.theFaceIsMultiplicativeOnTheComputedPopulation
        rcases halfTurnAbscissaOne h₁ rfl with hA | hA | hA <;>
          rcases halfTurnAbscissaOne h₂ rfl with hB | hB | hB
        · exact absurd (hA.trans hB.symm) hx
        · subst hA; subst hB
          have hP : (Point.some h₁ : Descent.E.Point) = Descent.P00 := rfl
          have hQ : (Point.some h₂ : Descent.E.Point) = Descent.P10 := rfl
          rw [hP, hQ]
          exact ⟨m01a, m01b⟩
        · subst hA; subst hB
          have hP : (Point.some h₁ : Descent.E.Point) = Descent.P00 := rfl
          have hQ : (Point.some h₂ : Descent.E.Point) = Descent.Pm10 := rfl
          rw [hP, hQ]
          exact ⟨m0m1a, m0m1b⟩
        · subst hA; subst hB
          have hP : (Point.some h₁ : Descent.E.Point) = Descent.P10 := rfl
          have hQ : (Point.some h₂ : Descent.E.Point) = Descent.P00 := rfl
          rw [hP, hQ]
          constructor
          · rw [add_comm, mul_comm]
            exact m01a
          · rw [add_comm, mul_comm]
            exact m01b
        · exact absurd (hA.trans hB.symm) hx
        · subst hA; subst hB
          have hP : (Point.some h₁ : Descent.E.Point) = Descent.P10 := rfl
          have hQ : (Point.some h₂ : Descent.E.Point) = Descent.Pm10 := rfl
          rw [hP, hQ]
          exact ⟨m1m1a, m1m1b⟩
        · subst hA; subst hB
          have hP : (Point.some h₁ : Descent.E.Point) = Descent.Pm10 := rfl
          have hQ : (Point.some h₂ : Descent.E.Point) = Descent.P00 := rfl
          rw [hP, hQ]
          constructor
          · rw [add_comm, mul_comm]
            exact m0m1a
          · rw [add_comm, mul_comm]
            exact m0m1b
        · subst hA; subst hB
          have hP : (Point.some h₁ : Descent.E.Point) = Descent.Pm10 := rfl
          have hQ : (Point.some h₂ : Descent.E.Point) = Descent.P10 := rfl
          rw [hP, hQ]
          constructor
          · rw [add_comm, mul_comm]
            exact m1m1a
          · rw [add_comm, mul_comm]
            exact m1m1b
        · exact absurd (hA.trans hB.symm) hx
      · -- the first summand is the half-turn: commute and use the closed family
        subst hy1
        obtain ⟨c1, c2⟩ := chordHalfTurnRight h₂ h₁ hy2 (Ne.symm hx)
        constructor
        · rw [add_comm, mul_comm]
          exact c1
        · rw [add_comm, mul_comm]
          exact c2
    · by_cases hy2 : y₂ = 0
      · subst hy2
        exact chordHalfTurnRight h₁ h₂ hy1 hx
      · -- the general chord, with its three landings
        have eA := onCurveOne h₁
        have eB := onCurveOne h₂
        have eA' : y₁ ^ 2 = x₁ ^ 3 - 1 ^ 2 * x₁ := by linear_combination eA
        have eB' : y₂ ^ 2 = x₂ ^ 3 - 1 ^ 2 * x₂ := by linear_combination eB
        obtain ⟨ha1, ha2, -⟩ := theNonzeroOrdinateAvoidsTheRoots eA' hy1
        obtain ⟨hb1, hb2, -⟩ := theNonzeroOrdinateAvoidsTheRoots eB' hy2
        rw [Point.add_of_X_ne hx]
        have hlam : Descent.E.slope x₁ x₂ y₁ y₂ * (x₂ - x₁) = y₂ - y₁ := slopeLineOne hx
        have hax := addXOne x₁ x₂ (Descent.E.slope x₁ x₂ y₁ y₂)
        have hs₁ : Descent.slotOne (Point.some h₁) = x₁ := by rw [slotOne_some, if_neg ha1]
        have hs₂ : Descent.slotOne (Point.some h₂) = x₂ := by rw [slotOne_some, if_neg hb1]
        have ht₁ : Descent.slotTwo (Point.some h₁) = x₁ - 1 := by
          rw [slotTwo_some, if_neg ha2]
        have ht₂ : Descent.slotTwo (Point.some h₂) = x₂ - 1 := by
          rw [slotTwo_some, if_neg hb2]
        rw [hs₁, hs₂, ht₁, ht₂]
        by_cases hX0 : Descent.E.slope x₁ x₂ y₁ y₂ ^ 2 - x₁ - x₂ = 0
        · obtain ⟨-, c1, c2⟩ :=
            theChordLandsOnTheZeroHalfTurn one_ne_zero eA' eB' hlam hx hy1 hy2 hX0
          constructor
          · rw [slotOne_some, hax, if_pos hX0]
            exact c1
          · rw [slotTwo_some, hax, if_neg (by rw [hX0]; norm_num), hX0]
            norm_num
            exact c2
        · by_cases hX1 : Descent.E.slope x₁ x₂ y₁ y₂ ^ 2 - x₁ - x₂ = 1
          · obtain ⟨-, c1, c2⟩ :=
              theChordLandsOnTheSecondHalfTurn one_ne_zero eA' eB' hlam hx hy1 hy2 hX1
            constructor
            · rw [slotOne_some, hax, if_neg (by rw [hX1]; norm_num), hX1]
              exact c1
            · rw [slotTwo_some, hax, if_pos hX1]
              exact c2
          · obtain ⟨c1, c2⟩ :=
              theChordLandsGenerically eA' eB' hlam hx hy1 hy2 hX0 hX1
            constructor
            · rw [slotOne_some, hax, if_neg hX0]
              exact c1
            · rw [slotTwo_some, hax, if_neg hX1]
              exact c2

/-! ## 4. The five-curve assembly: point-level plumbing on `y² = x³ − 25x` -/

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
    (Point.some h₁ : RankOne.E5.Point) = Point.some h₂ := by
  subst hx; subst hy; rfl

private lemma slotOne5_some {x y : ℚ} (h : RankOne.E5.Nonsingular x y) :
    RankOne.slotOne (.some h) = if x = 0 then -25 else x := rfl

private lemma slotTwo5_some {x y : ℚ} (h : RankOne.E5.Nonsingular x y) :
    RankOne.slotTwo (.some h) = if x = 5 then 50 else x - 5 := rfl

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

private lemma slopeLineFive {x₁ y₁ x₂ y₂ : ℚ} (hx : x₁ ≠ x₂) :
    RankOne.E5.slope x₁ x₂ y₁ y₂ * (x₂ - x₁) = y₂ - y₁ := by
  rw [slope_of_X_ne hx]
  have h : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  field_simp
  ring

private lemma addXFive (x₁ x₂ L : ℚ) :
    RankOne.E5.addX x₁ x₂ L = L ^ 2 - x₁ - x₂ := by
  simp only [addX, RankOne.E5]
  ring

private lemma halfTurnAbscissaFive {x y : ℚ} (h : RankOne.E5.Nonsingular x y) (hy : y = 0) :
    x = 0 ∨ x = 5 ∨ x = -5 := by
  have hc := onCurveFive h
  rw [hy] at hc
  have h0 : x * (x - 5) * (x + 5) = 0 := by linear_combination -hc
  rcases mul_eq_zero.mp h0 with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact Or.inl h''
    · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (by linarith))

/-- **A translated point is never a half-turn**, on the five-curve — the sibling of
`FaithfulFace.theTranslatedPointIsNeverAHalfTurn`, which that file carries only for the
one-curve. -/
theorem theTranslatedPointIsNeverAHalfTurnOnTheFiveCurve {x y : ℚ}
    (h : y ^ 2 = x ^ 3 - 25 * x) (hy : y ≠ 0) :
    (FaithfulFace.translatedX x y 0 ≠ 0 ∧ FaithfulFace.translatedX x y 0 ≠ 5 ∧
      FaithfulFace.translatedX x y 0 ≠ -5) ∧
    (FaithfulFace.translatedX x y 5 ≠ 0 ∧ FaithfulFace.translatedX x y 5 ≠ 5 ∧
      FaithfulFace.translatedX x y 5 ≠ -5) ∧
    (FaithfulFace.translatedX x y (-5) ≠ 0 ∧ FaithfulFace.translatedX x y (-5) ≠ 5 ∧
      FaithfulFace.translatedX x y (-5) ≠ -5) := by
  obtain ⟨hx0, hx5, hxm5⟩ := FaithfulFace.theNonzeroOrdinateAvoidsTheThreeRootsOnTheFiveCurve h hy
  have hd1 : x - 5 ≠ 0 := sub_ne_zero.mpr hx5
  have hd2 : x + 5 ≠ 0 := fun hc => hxm5 (by linarith)
  rw [FaithfulFace.theHalfTurnAtZeroTranslatesOnTheFiveCurve h hy,
    FaithfulFace.theHalfTurnAtFiveTranslates h hy,
    FaithfulFace.theHalfTurnAtNegativeFiveTranslates h hy]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · intro hc; rw [div_eq_iff hx0] at hc; norm_num at hc
  · intro hc; rw [div_eq_iff hx0] at hc; exact hxm5 (by linarith)
  · intro hc; rw [div_eq_iff hx0] at hc; exact hx5 (by linarith)
  · intro hc; rw [div_eq_iff hd1] at hc; exact hxm5 (by linarith)
  · intro hc; rw [div_eq_iff hd1] at hc; linarith
  · intro hc; rw [div_eq_iff hd1] at hc; exact hx0 (by linarith)
  · intro hc; rw [div_eq_iff hd2] at hc; exact hx5 (by linarith)
  · intro hc; rw [div_eq_iff hd2] at hc; exact hx0 (by linarith)
  · intro hc; rw [div_eq_iff hd2] at hc; linarith

/-- **The doubles land in the kernel on the five-curve**, at point level: the forward half
of the descent kernel law, for every point of `y² = x³ − 25x`. -/
theorem theDoublesLandInTheKernelOnTheFiveCurve (Q : RankOne.E5.Point) :
    Descent.SqCls (RankOne.slotOne (Q + Q)) 1 ∧
    Descent.SqCls (RankOne.slotTwo (Q + Q)) 1 := by
  rcases Q with _ | @⟨x, y, h⟩
  · rw [← Point.zero_def, add_zero]
    exact ⟨Descent.sqClsRefl 1, Descent.sqClsRefl 1⟩
  · by_cases hy : y = 0
    · have hzero : (Point.some h : RankOne.E5.Point) + Point.some h = 0 :=
        Point.add_self_of_Y_eq (by rw [negYFive, hy]; norm_num)
      rw [hzero]
      exact ⟨Descent.sqClsRefl 1, Descent.sqClsRefl 1⟩
    · have hyne : y ≠ RankOne.E5.negY x y := by
        rw [negYFive]
        intro hc
        exact hy (by linarith)
      rw [Point.add_self_of_Y_ne hyne]
      have hbr := FaithfulFace.theTangentCoordinateIsMathlibsAddXOnTheFiveCurve x y hy
      obtain ⟨hd0, hd1, -⟩ :=
        FaithfulFace.theDoubledPointIsNeverAHalfTurnOnTheFiveCurve (onCurveFive h) hy
      obtain ⟨hq1, hq2⟩ :=
        FaithfulFace.theDoubledSlotsAreSquaresOnTheFiveCurve (onCurveFive h) hy
      obtain ⟨-, -, -, n4, n5, -⟩ := FaithfulFace.theDoublingNumeratorsNeverVanish x
      have h2y : (2 : ℚ) * y ≠ 0 := mul_ne_zero two_ne_zero hy
      constructor
      · rw [slotOne5_some, hbr, if_neg hd0]
        exact ⟨(x ^ 2 + 25) / (2 * y), div_ne_zero n4 h2y, by rw [hq1]; ring⟩
      · rw [slotTwo5_some, hbr, if_neg hd1]
        exact ⟨(x ^ 2 - 10 * x - 25) / (2 * y), div_ne_zero n5 h2y, by rw [hq2]; ring⟩

/-- The chord through a point off the two-torsion and a half-turn closes both slots on the
five-curve, at point level. -/
private lemma chordHalfTurnRightFive {x₁ y₁ x₂ : ℚ} (h₁ : RankOne.E5.Nonsingular x₁ y₁)
    (h₂ : RankOne.E5.Nonsingular x₂ 0) (hy₁ : y₁ ≠ 0) (hx : x₁ ≠ x₂) :
    RankOne.SqCls (RankOne.slotOne (Point.some h₁ + Point.some h₂))
      (RankOne.slotOne (Point.some h₁) * RankOne.slotOne (Point.some h₂)) ∧
    RankOne.SqCls (RankOne.slotTwo (Point.some h₁ + Point.some h₂))
      (RankOne.slotTwo (Point.some h₁) * RankOne.slotTwo (Point.some h₂)) := by
  have hcurve := onCurveFive h₁
  obtain ⟨hx0, hx5, hxm5⟩ :=
    FaithfulFace.theNonzeroOrdinateAvoidsTheThreeRootsOnTheFiveCurve hcurve hy₁
  obtain ⟨q0, q1, q2, q3, q4, q5⟩ :=
    FaithfulFace.theFaceLawClosesOnEveryHalfTurnTranslationOnTheFiveCurve hcurve hy₁
  obtain ⟨⟨t00, t01, -⟩, ⟨t10, t11, -⟩, ⟨tm0, tm1, -⟩⟩ :=
    theTranslatedPointIsNeverAHalfTurnOnTheFiveCurve hcurve hy₁
  -- the translation lift, transported to the five-curve through mathlib's `addX`
  have hsum : ∀ (hxe : x₁ ≠ x₂),
      (Point.some h₁ : RankOne.E5.Point) + Point.some h₂ =
        Point.some (nonsingular_add h₁ h₂ fun hc => hxe hc.1) := fun hxe =>
    Point.add_of_X_ne hxe
  rw [hsum hx]
  have haxT : RankOne.E5.addX x₁ x₂ (RankOne.E5.slope x₁ x₂ y₁ 0) =
      FaithfulFace.translatedX x₁ y₁ x₂ := by
    rw [slope_of_X_ne hx, addXFive, FaithfulFace.translatedX]
    have h : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    field_simp
    ring
  have hs₁ : RankOne.slotOne (Point.some h₁) = x₁ := by rw [slotOne5_some, if_neg hx0]
  have ht₁ : RankOne.slotTwo (Point.some h₁) = x₁ - 5 := by rw [slotTwo5_some, if_neg hx5]
  rcases halfTurnAbscissaFive h₂ rfl with h0 | h0 | h0
  · subst h0
    have hsQ : RankOne.slotOne (Point.some h₂) = RankOne.slotOne RankOne.T0 := rfl
    have htQ : RankOne.slotTwo (Point.some h₂) = RankOne.slotTwo RankOne.T0 := rfl
    constructor
    · rw [slotOne5_some, haxT, if_neg t00, hs₁, hsQ]
      exact q0
    · rw [slotTwo5_some, haxT, if_neg t01, ht₁, htQ]
      exact q1
  · subst h0
    have hsQ : RankOne.slotOne (Point.some h₂) = RankOne.slotOne RankOne.T5 := rfl
    have htQ : RankOne.slotTwo (Point.some h₂) = RankOne.slotTwo RankOne.T5 := rfl
    constructor
    · rw [slotOne5_some, haxT, if_neg t10, hs₁, hsQ]
      exact q2
    · rw [slotTwo5_some, haxT, if_neg t11, ht₁, htQ]
      exact q3
  · subst h0
    have hsQ : RankOne.slotOne (Point.some h₂) = RankOne.slotOne RankOne.Tm5 := rfl
    have htQ : RankOne.slotTwo (Point.some h₂) = RankOne.slotTwo RankOne.Tm5 := rfl
    constructor
    · rw [slotOne5_some, haxT, if_neg tm0, hs₁, hsQ]
      exact q4
    · rw [slotTwo5_some, haxT, if_neg tm1, ht₁, htQ]
      exact q5

/-- **THE FACE IS A HOMOMORPHISM ON THE WHOLE POINT GROUP** of `y² = x³ − 25x`: the
named-open proposition of `RankOne.lean`, discharged.  With the torsion classification of
`DistantWindings.lean` this completes every ingredient of the rank-one descent
certificate. -/
theorem theRankOneFaceIsAHomomorphismEverywhereHolds :
    RankOne.TheFaceIsAHomomorphismEverywhere := by
  intro P Q
  rw [← FaithfulFace.theTwoFilesDeclareOneSquareClass,
    ← FaithfulFace.theTwoFilesDeclareOneSquareClass]
  obtain ⟨⟨e1, e2⟩, -, -, -, -, -⟩ := RankOne.theFaceValues
  rcases P with _ | @⟨x₁, y₁, h₁⟩
  · rw [← Point.zero_def, zero_add, e1, e2, one_mul, one_mul]
    exact ⟨Descent.sqClsRefl _, Descent.sqClsRefl _⟩
  rcases Q with _ | @⟨x₂, y₂, h₂⟩
  · rw [← Point.zero_def, add_zero, e1, e2, mul_one, mul_one]
    exact ⟨Descent.sqClsRefl _, Descent.sqClsRefl _⟩
  by_cases hx : x₁ = x₂
  · subst hx
    have hyy : (y₂ - y₁) * (y₂ + y₁) = 0 := by
      have hA := onCurveFive h₁
      have hB := onCurveFive h₂
      linear_combination hB - hA
    rcases mul_eq_zero.mp hyy with hcase | hcase
    · have heq : (Point.some h₂ : RankOne.E5.Point) = Point.some h₁ :=
        someEqFive rfl (by linarith)
      rw [heq]
      obtain ⟨k1, k2⟩ := theDoublesLandInTheKernelOnTheFiveCurve (Point.some h₁)
      exact ⟨sqcls_scale_sq k1 (slotOne5_ne _), sqcls_scale_sq k2 (slotTwo5_ne _)⟩
    · by_cases hy0 : y₁ = 0
      · have heq : (Point.some h₂ : RankOne.E5.Point) = Point.some h₁ :=
          someEqFive rfl (by linarith)
        rw [heq]
        obtain ⟨k1, k2⟩ := theDoublesLandInTheKernelOnTheFiveCurve (Point.some h₁)
        exact ⟨sqcls_scale_sq k1 (slotOne5_ne _), sqcls_scale_sq k2 (slotTwo5_ne _)⟩
      · have hzero : (Point.some h₁ : RankOne.E5.Point) + Point.some h₂ = 0 :=
          Point.add_of_Y_eq rfl (by rw [negYFive]; linarith)
        have hs : RankOne.slotOne (Point.some h₂) = RankOne.slotOne (Point.some h₁) := by
          rw [slotOne5_some, slotOne5_some]
        have ht : RankOne.slotTwo (Point.some h₂) = RankOne.slotTwo (Point.some h₁) := by
          rw [slotTwo5_some, slotTwo5_some]
        rw [hzero, e1, e2, hs, ht]
        exact ⟨sqcls_one_mul_self (slotOne5_ne _), sqcls_one_mul_self (slotTwo5_ne _)⟩
  · by_cases hy1 : y₁ = 0
    · by_cases hy2 : y₂ = 0
      · -- both half-turns: the Klein chords, computed literally
        subst hy1; subst hy2
        rw [Point.add_of_X_ne hx]
        have hax := addXFive x₁ x₂ (RankOne.E5.slope x₁ x₂ 0 0)
        have hsl : RankOne.E5.slope x₁ x₂ 0 0 = 0 := by
          rw [slope_of_X_ne hx]
          norm_num
        rcases halfTurnAbscissaFive h₁ rfl with hA | hA | hA <;>
          rcases halfTurnAbscissaFive h₂ rfl with hB | hB | hB
        · exact absurd (hA.trans hB.symm) hx
        · -- (0,0) + (5,0) lands at −5: faces (−5, −10) against (−125, −250)
          subst hA; subst hB
          constructor
          · rw [slotOne5_some, hax, hsl, slotOne5_some, slotOne5_some]
            norm_num
            exact ⟨1 / 5, by norm_num, by norm_num⟩
          · rw [slotTwo5_some, hax, hsl, slotTwo5_some, slotTwo5_some]
            norm_num
            exact ⟨1 / 5, by norm_num, by norm_num⟩
        · -- (0,0) + (−5,0) lands at 5: faces (5, 50) against (125, 50)
          subst hA; subst hB
          constructor
          · rw [slotOne5_some, hax, hsl, slotOne5_some, slotOne5_some]
            norm_num
            exact ⟨1 / 5, by norm_num, by norm_num⟩
          · rw [slotTwo5_some, hax, hsl, slotTwo5_some, slotTwo5_some]
            norm_num
            exact ⟨1, one_ne_zero, by norm_num⟩
        · -- (5,0) + (0,0) lands at −5
          subst hA; subst hB
          constructor
          · rw [slotOne5_some, hax, hsl, slotOne5_some, slotOne5_some]
            norm_num
            exact ⟨1 / 5, by norm_num, by norm_num⟩
          · rw [slotTwo5_some, hax, hsl, slotTwo5_some, slotTwo5_some]
            norm_num
            exact ⟨1 / 5, by norm_num, by norm_num⟩
        · exact absurd (hA.trans hB.symm) hx
        · -- (5,0) + (−5,0) lands at 0: faces (−25, −5) against (−25, −500)
          subst hA; subst hB
          constructor
          · rw [slotOne5_some, hax, hsl, slotOne5_some, slotOne5_some]
            norm_num
            exact ⟨1, one_ne_zero, by norm_num⟩
          · rw [slotTwo5_some, hax, hsl, slotTwo5_some, slotTwo5_some]
            norm_num
            exact ⟨1 / 10, by norm_num, by norm_num⟩
        · -- (−5,0) + (0,0) lands at 5
          subst hA; subst hB
          constructor
          · rw [slotOne5_some, hax, hsl, slotOne5_some, slotOne5_some]
            norm_num
            exact ⟨1 / 5, by norm_num, by norm_num⟩
          · rw [slotTwo5_some, hax, hsl, slotTwo5_some, slotTwo5_some]
            norm_num
            exact ⟨1, one_ne_zero, by norm_num⟩
        · -- (−5,0) + (5,0) lands at 0
          subst hA; subst hB
          constructor
          · rw [slotOne5_some, hax, hsl, slotOne5_some, slotOne5_some]
            norm_num
            exact ⟨1, one_ne_zero, by norm_num⟩
          · rw [slotTwo5_some, hax, hsl, slotTwo5_some, slotTwo5_some]
            norm_num
            exact ⟨1 / 10, by norm_num, by norm_num⟩
        · exact absurd (hA.trans hB.symm) hx
      · subst hy1
        rw [FaithfulFace.theTwoFilesDeclareOneSquareClass,
          FaithfulFace.theTwoFilesDeclareOneSquareClass]
        obtain ⟨c1, c2⟩ := chordHalfTurnRightFive h₂ h₁ hy2 (Ne.symm hx)
        constructor
        · rw [add_comm, mul_comm]
          exact c1
        · rw [add_comm, mul_comm]
          exact c2
    · by_cases hy2 : y₂ = 0
      · subst hy2
        rw [FaithfulFace.theTwoFilesDeclareOneSquareClass,
          FaithfulFace.theTwoFilesDeclareOneSquareClass]
        exact chordHalfTurnRightFive h₁ h₂ hy1 hx
      · -- the general chord, with its three landings
        have eA := onCurveFive h₁
        have eB := onCurveFive h₂
        have eA' : y₁ ^ 2 = x₁ ^ 3 - 5 ^ 2 * x₁ := by linear_combination eA
        have eB' : y₂ ^ 2 = x₂ ^ 3 - 5 ^ 2 * x₂ := by linear_combination eB
        obtain ⟨ha1, ha2, -⟩ := theNonzeroOrdinateAvoidsTheRoots eA' hy1
        obtain ⟨hb1, hb2, -⟩ := theNonzeroOrdinateAvoidsTheRoots eB' hy2
        rw [Point.add_of_X_ne hx]
        have hlam : RankOne.E5.slope x₁ x₂ y₁ y₂ * (x₂ - x₁) = y₂ - y₁ := slopeLineFive hx
        have hax := addXFive x₁ x₂ (RankOne.E5.slope x₁ x₂ y₁ y₂)
        have hs₁ : RankOne.slotOne (Point.some h₁) = x₁ := by rw [slotOne5_some, if_neg ha1]
        have hs₂ : RankOne.slotOne (Point.some h₂) = x₂ := by rw [slotOne5_some, if_neg hb1]
        have ht₁ : RankOne.slotTwo (Point.some h₁) = x₁ - 5 := by
          rw [slotTwo5_some, if_neg ha2]
        have ht₂ : RankOne.slotTwo (Point.some h₂) = x₂ - 5 := by
          rw [slotTwo5_some, if_neg hb2]
        rw [hs₁, hs₂, ht₁, ht₂]
        by_cases hX0 : RankOne.E5.slope x₁ x₂ y₁ y₂ ^ 2 - x₁ - x₂ = 0
        · obtain ⟨-, c1, c2⟩ :=
            theChordLandsOnTheZeroHalfTurn (by norm_num : (5 : ℚ) ≠ 0)
              eA' eB' hlam hx hy1 hy2 hX0
          constructor
          · rw [slotOne5_some, hax, if_pos hX0]
            have h25 : (-25 : ℚ) = 5 ^ 2 * -1 := by norm_num
            rw [h25]
            exact sqcls_mul_sq_left c1 (by norm_num)
          · rw [slotTwo5_some, hax, if_neg (by rw [hX0]; norm_num), hX0]
            norm_num
            exact c2
        · by_cases hX5 : RankOne.E5.slope x₁ x₂ y₁ y₂ ^ 2 - x₁ - x₂ = 5
          · obtain ⟨-, c1, c2⟩ :=
              theChordLandsOnTheSecondHalfTurn (by norm_num : (5 : ℚ) ≠ 0)
                eA' eB' hlam hx hy1 hy2 hX5
            constructor
            · rw [slotOne5_some, hax, if_neg (by rw [hX5]; norm_num), hX5]
              exact c1
            · rw [slotTwo5_some, hax, if_pos hX5]
              have h50 : (50 : ℚ) = 5 ^ 2 * 2 := by norm_num
              rw [h50]
              exact sqcls_mul_sq_left c2 (by norm_num)
          · obtain ⟨c1, c2⟩ :=
              theChordLandsGenerically eA' eB' hlam hx hy1 hy2 hX0 hX5
            constructor
            · rw [slotOne5_some, hax, if_neg hX0]
              exact c1
            · rw [slotTwo5_some, hax, if_neg hX5]
              exact c2

/-! ## 5. The consequences -/

/-- **The general chord closes the face**: `FaithfulFace.TheGeneralChordClosesTheFace`,
the guarded coordinate proposition checked over 198 pairs before this file, discharged for
every pair at once. -/
theorem theGeneralChordClosesTheFaceHolds : FaithfulFace.TheGeneralChordClosesTheFace := by
  intro x₁ y₁ x₂ y₂ h₁ h₂ hy₁ hy₂ hx hc0 hc5
  have h₁' : y₁ ^ 2 = x₁ ^ 3 - 5 ^ 2 * x₁ := by linear_combination h₁
  have h₂' : y₂ ^ 2 = x₂ ^ 3 - 5 ^ 2 * x₂ := by linear_combination h₂
  have hlam : (y₂ - y₁) / (x₂ - x₁) * (x₂ - x₁) = y₂ - y₁ :=
    div_mul_cancel₀ _ (sub_ne_zero.mpr (Ne.symm hx))
  have hchord : FaithfulFace.chordX x₁ y₁ x₂ y₂ =
      ((y₂ - y₁) / (x₂ - x₁)) ^ 2 - x₁ - x₂ := rfl
  rw [← FaithfulFace.theTwoFilesDeclareOneSquareClass,
    ← FaithfulFace.theTwoFilesDeclareOneSquareClass, hchord]
  exact theChordLandsGenerically h₁' h₂' hlam hx hy₁ hy₂
    (by rw [← hchord]; exact hc0) (by rw [← hchord]; exact hc5)

/-- **THE NEW POINT ESCAPES THE TORSION AND THE DOUBLES**: `P = (−4, 6)` is not
`T + 2Q` for any half-turn-or-identity `T` and any point `Q` of `y² = x³ − 25x` — the
descent certificate that the realized population strictly exceeds
`torsion + 2·E₅(ℚ)`, with every ingredient now a theorem: the face homomorphism (this
file), the doubles-in-kernel law (this file), and the face separations
(`RankOne.theFaceSeparatesTheNewPoint`). -/
theorem theNewPointEscapesTheTorsionAndTheDoubles :
    ∀ T Q : RankOne.E5.Point,
      (T = 0 ∨ T = RankOne.T0 ∨ T = RankOne.T5 ∨ T = RankOne.Tm5) →
      RankOne.P ≠ T + (2 : ℕ) • Q := by
  intro T Q hT hEq
  rw [two_nsmul] at hEq
  obtain ⟨hom1, hom2⟩ := theRankOneFaceIsAHomomorphismEverywhereHolds T (Q + Q)
  rw [← hEq] at hom1 hom2
  obtain ⟨k1, k2⟩ := theDoublesLandInTheKernelOnTheFiveCurve Q
  obtain ⟨sep0, sepT0, sepT5, sepTm5⟩ := RankOne.theFaceSeparatesTheNewPoint
  have habs1 : RankOne.SqCls (RankOne.slotOne RankOne.P) (RankOne.slotOne T) := by
    rw [← FaithfulFace.theTwoFilesDeclareOneSquareClass] at hom1 ⊢
    exact sqcls_absorb_right hom1 k1
  have habs2 : RankOne.SqCls (RankOne.slotTwo RankOne.P) (RankOne.slotTwo T) := by
    rw [← FaithfulFace.theTwoFilesDeclareOneSquareClass] at hom2 ⊢
    exact sqcls_absorb_right hom2 k2
  rcases hT with rfl | rfl | rfl | rfl
  · exact sep0 habs1
  · exact sepT0 habs2
  · exact sepT5 habs1
  · exact sepTm5 habs1

/-- **The escape, quantified over torsion by its property**: for every point `T` of finite
order and every `Q`, `P ≠ T + 2Q`.  The torsion classification of `DistantWindings.lean`
reduces the property to the four listed points; nothing here assumes the list. -/
theorem theNewPointEscapesEveryTorsionTranslateOfADouble :
    ∀ T Q : RankOne.E5.Point,
      (∃ k : ℕ, 0 < k ∧ k • T = 0) → RankOne.P ≠ T + (2 : ℕ) • Q := by
  intro T Q hTor
  exact theNewPointEscapesTheTorsionAndTheDoubles T Q
    ((DistantWindings.theTorsionIsTheKleinGroupHolds T).mp hTor)

end Soma.Holonics.Millennium.FaceHomomorphism
