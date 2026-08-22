import ElementaryHolonics.Millennium.FaceHomomorphism
import Mathlib.Tactic

/-!
# FamilyFace: the descent face is a homomorphism on every twist at once

`FaceHomomorphism.lean` assembled the point-level face homomorphism for the two route
curves, one at a time.  This file proves it **for the whole twist family**: for every
nonzero `n`, on `y² = x³ − n²x` with the descent face

```text
P ↦ (x, x − n)  mod squares,   conventions  −n² at (0,0)  and  2n² at (n,0)
```

the face is a homomorphism on the whole mathlib point group
(`theFaceIsAHomomorphismOnEveryTwist`), and every double lands in the kernel
(`theDoublesLandInTheKernelOnEveryTwist`).  The per-curve theorems become instances; the
coordinate laws — doubling, three half-turn translations, Klein chords, and the three
chord landings — are each one family-wise identity, verified in exact rational
arithmetic over hundreds of random samples before encoding.

**The thirty-four instance: the two directions and their sum escape.**  On the rank-two
twist (`n = 34`), the three realized directions of `ChordFace.lean` — `P₁ = (−2, 48)`,
`P₂ = (−16, 120)`, and `P₁ + P₂` — are each proved **not equal to `T + 2Q`** for any
half-turn-or-identity `T` and any point `Q`
(`theFirstDirectionEscapes`, `theSecondDirectionEscapes`, `theSumDirectionEscapes`):
the descent's mod-2 independence certificate for the two directions, relative to the
listed torsion, with every ingredient kernel-checked — the family homomorphism, the
doubles-in-kernel law, and twelve square-class refusals carried by signs and by two,
seventeen, and thirty-four failing to be rational squares.

Every `theorem` is discharged and none depends on `sorryAx`.  **Boundary**: the torsion
classification at thirty-four (that the four listed points are *all* the torsion) is
owed — it upgrades the escape from list-quantified to property-quantified exactly as
`DistantWindings.lean` did at five; the kernel's converse remains open; nothing about
the Birch–Swinnerton-Dyer conjecture.
-/

namespace Soma.Holonics.Millennium.FamilyFace

open WeierstrassCurve.Affine

/-! ## 1. The twist family and its face -/

/-- The congruent-number twist: `y² = x³ − n²x`. -/
def E (n : ℚ) : WeierstrassCurve.Affine ℚ := ⟨0, 0, 0, -n ^ 2, 0⟩

/-- The first slot: `x`, with the convention `(0−n)(0+n) = −n²` at the vanishing
coordinate. -/
def slotOne (n : ℚ) : (E n).Point → ℚ
  | .zero => 1
  | .some (x := x) _ => if x = 0 then -n ^ 2 else x

/-- The second slot: `x − n`, with the convention `(n−0)(n+n) = 2n²` at the vanishing
coordinate. -/
def slotTwo (n : ℚ) : (E n).Point → ℚ
  | .zero => 1
  | .some (x := x) _ => if x = n then 2 * n ^ 2 else x - n

/-! ## 2. Coordinate plumbing, family-wise -/

private lemma sqcls_of_mul_eq_sq {a b s : ℚ} (hb : b ≠ 0) (hs : s ≠ 0)
    (h : a * b = s ^ 2) : Descent.SqCls a b := by
  refine ⟨s / b, div_ne_zero hs hb, ?_⟩
  rw [div_pow, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hb)]
  linear_combination b * h

private lemma sqcls_trans {a b c : ℚ} (h₁ : Descent.SqCls a b) (h₂ : Descent.SqCls b c) :
    Descent.SqCls a c := by
  obtain ⟨k, hk, hkv⟩ := h₁
  obtain ⟨m, hm, hmv⟩ := h₂
  exact ⟨k * m, mul_ne_zero hk hm, by rw [hkv, hmv]; ring⟩

private lemma sqcls_symm {a b : ℚ} (h : Descent.SqCls a b) : Descent.SqCls b a := by
  obtain ⟨c, hc, hval⟩ := h
  refine ⟨1 / c, one_div_ne_zero hc, ?_⟩
  rw [hval]
  field_simp

private lemma sqcls_one_mul_self {s : ℚ} (hs : s ≠ 0) : Descent.SqCls 1 (s * s) := by
  refine ⟨1 / s, one_div_ne_zero hs, ?_⟩
  field_simp

private lemma sqcls_scale_sq {a s : ℚ} (h : Descent.SqCls a 1) (hs : s ≠ 0) :
    Descent.SqCls a (s * s) := by
  obtain ⟨c, hc, hval⟩ := h
  refine ⟨c / s, div_ne_zero hc hs, ?_⟩
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

private lemma onCurve {n x y : ℚ} (h : (E n).Nonsingular x y) :
    y ^ 2 = x ^ 3 - n ^ 2 * x := by
  have h1 := ((nonsingular_iff x y).mp h).1
  rw [equation_iff] at h1
  simp only [E] at h1
  linarith [h1]

private lemma negYE (n x y : ℚ) : (E n).negY x y = -y := by
  simp [negY, E]

private lemma someEqE {n x₁ y₁ x₂ y₂ : ℚ} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : (E n).Nonsingular x₁ y₁} {h₂ : (E n).Nonsingular x₂ y₂} :
    (Point.some h₁ : (E n).Point) = Point.some h₂ := by
  subst hx; subst hy; rfl

private lemma slotOneE_some {n x y : ℚ} (h : (E n).Nonsingular x y) :
    slotOne n (.some h) = if x = 0 then -n ^ 2 else x := rfl

private lemma slotTwoE_some {n x y : ℚ} (h : (E n).Nonsingular x y) :
    slotTwo n (.some h) = if x = n then 2 * n ^ 2 else x - n := rfl

private lemma slotOneE_ne {n : ℚ} (hn : n ≠ 0) (P : (E n).Point) : slotOne n P ≠ 0 := by
  rcases P with _ | @⟨x, y, h⟩
  · exact one_ne_zero
  · rw [slotOneE_some]
    split_ifs with hx
    · exact neg_ne_zero.mpr (pow_ne_zero 2 hn)
    · exact hx

private lemma slotTwoE_ne {n : ℚ} (hn : n ≠ 0) (P : (E n).Point) : slotTwo n P ≠ 0 := by
  rcases P with _ | @⟨x, y, h⟩
  · exact one_ne_zero
  · rw [slotTwoE_some]
    split_ifs with hx
    · exact mul_ne_zero two_ne_zero (pow_ne_zero 2 hn)
    · exact sub_ne_zero.mpr hx

private lemma slopeLineE {n x₁ y₁ x₂ y₂ : ℚ} (hx : x₁ ≠ x₂) :
    (E n).slope x₁ x₂ y₁ y₂ * (x₂ - x₁) = y₂ - y₁ := by
  rw [slope_of_X_ne hx]
  have h : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  field_simp
  ring

private lemma addXE (n x₁ x₂ L : ℚ) : (E n).addX x₁ x₂ L = L ^ 2 - x₁ - x₂ := by
  simp only [addX, E]
  ring

private lemma halfTurnAbscissaE {n x y : ℚ} (h : (E n).Nonsingular x y) (hy : y = 0) :
    x = 0 ∨ x = n ∨ x = -n := by
  have hc := onCurve h
  rw [hy] at hc
  have h0 : x * (x - n) * (x + n) = 0 := by linear_combination -hc
  rcases mul_eq_zero.mp h0 with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact Or.inl h''
    · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (by linarith))

private lemma rootOfTwoScaled {u c : ℚ} (hc : c ≠ 0) (h : u ^ 2 = 2 * c ^ 2) : False := by
  refine Descent.notSquareTwo ⟨u / c, ?_⟩
  rw [div_mul_div_comm, ← pow_two, ← pow_two, h]
  field_simp

/-! ## 3. Doubling, family-wise -/

/-- **The doubling triple over the ordinate, on every twist**: the three slot values of
the doubled point clear against `4y²` to literal squares. -/
theorem theDoubledSlotsClearOnEveryTwist {n x y : ℚ} (h : y ^ 2 = x ^ 3 - n ^ 2 * x)
    (hy : y ≠ 0) :
    FaithfulFace.doubledX x y (-n ^ 2) * (4 * y ^ 2) = (x ^ 2 + n ^ 2) ^ 2 ∧
    (FaithfulFace.doubledX x y (-n ^ 2) - n) * (4 * y ^ 2)
      = (x ^ 2 - 2 * n * x - n ^ 2) ^ 2 ∧
    (FaithfulFace.doubledX x y (-n ^ 2) + n) * (4 * y ^ 2)
      = (x ^ 2 + 2 * n * x - n ^ 2) ^ 2 := by
  have key : FaithfulFace.doubledX x y (-n ^ 2) * (4 * y ^ 2)
      = (3 * x ^ 2 - n ^ 2) ^ 2 - 8 * x * y ^ 2 := by
    simp only [FaithfulFace.doubledX]
    field_simp
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [key, h]; ring
  · have hsplit : (FaithfulFace.doubledX x y (-n ^ 2) - n) * (4 * y ^ 2)
        = FaithfulFace.doubledX x y (-n ^ 2) * (4 * y ^ 2) - 4 * n * y ^ 2 := by ring
    rw [hsplit, key, h]; ring
  · have hsplit : (FaithfulFace.doubledX x y (-n ^ 2) + n) * (4 * y ^ 2)
        = FaithfulFace.doubledX x y (-n ^ 2) * (4 * y ^ 2) + 4 * n * y ^ 2 := by ring
    rw [hsplit, key, h]; ring

/-- **A doubled point is never a half-turn, on every twist**: landing on `0` needs
`x² + n² = 0`, and landing on `±n` needs a rational square root of two. -/
theorem theDoubledPointIsNeverAHalfTurnOnEveryTwist {n x y : ℚ} (hn : n ≠ 0)
    (h : y ^ 2 = x ^ 3 - n ^ 2 * x) (hy : y ≠ 0) :
    FaithfulFace.doubledX x y (-n ^ 2) ≠ 0 ∧
    FaithfulFace.doubledX x y (-n ^ 2) ≠ n ∧
    FaithfulFace.doubledX x y (-n ^ 2) ≠ -n := by
  obtain ⟨d1, d2, d3⟩ := theDoubledSlotsClearOnEveryTwist h hy
  refine ⟨fun hc => ?_, fun hc => ?_, fun hc => ?_⟩
  · rw [hc] at d1
    have hz : x ^ 2 + n ^ 2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by linarith)
    exact hn (by nlinarith [sq_nonneg x, sq_nonneg n])
  · rw [hc] at d2
    have hz : x ^ 2 - 2 * n * x - n ^ 2 = 0 :=
      pow_eq_zero_iff two_ne_zero |>.mp (by linarith)
    exact rootOfTwoScaled hn (u := x - n) (by linear_combination hz)
  · rw [hc] at d3
    have hz : x ^ 2 + 2 * n * x - n ^ 2 = 0 :=
      pow_eq_zero_iff two_ne_zero |>.mp (by linarith)
    exact rootOfTwoScaled hn (u := x + n) (by linear_combination hz)

private lemma doubledTrivialClass {n x y : ℚ} (h : y ^ 2 = x ^ 3 - n ^ 2 * x)
    (hy : y ≠ 0) :
    Descent.SqCls (FaithfulFace.doubledX x y (-n ^ 2)) 1 ∧
    Descent.SqCls (FaithfulFace.doubledX x y (-n ^ 2) - n) 1 := by
  obtain ⟨d1, d2, -⟩ := theDoubledSlotsClearOnEveryTwist h hy
  have h4 : (4 : ℚ) * y ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)
  have h2y : (2 : ℚ) * y ≠ 0 := mul_ne_zero two_ne_zero hy
  have hn1 : x ^ 2 + n ^ 2 ≠ 0 ∨ FaithfulFace.doubledX x y (-n ^ 2) = 0 := by
    by_cases hz : x ^ 2 + n ^ 2 = 0
    · right
      have : FaithfulFace.doubledX x y (-n ^ 2) * (4 * y ^ 2) = 0 := by rw [d1, hz]; ring
      rcases mul_eq_zero.mp this with h' | h'
      · exact h'
      · exact absurd h' h4
    · left; exact hz
  constructor
  · rcases hn1 with hz | hz
    · exact ⟨(x ^ 2 + n ^ 2) / (2 * y), div_ne_zero hz h2y, by
        rw [mul_one, div_pow]
        rw [eq_div_iff (by positivity)]
        linear_combination d1⟩
    · -- degenerate: the doubled abscissa is zero, so the slot is `0 = c²·1` is
      -- impossible; but this branch cannot occur, since `x² + n² = 0` forces `x = n = 0`
      -- and then `y² = 0`
      exfalso
      have hx0 : x ^ 2 + n ^ 2 = 0 := by
        have := d1
        rw [hz] at this
        exact pow_eq_zero_iff two_ne_zero |>.mp (by linarith)
      have hxz : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg n]
      rw [hxz] at h
      exact hy (pow_eq_zero_iff two_ne_zero |>.mp (by rw [h]; ring))
  · have hz2 : x ^ 2 - 2 * n * x - n ^ 2 ≠ 0 ∨ n = 0 := by
      by_cases hzz : x ^ 2 - 2 * n * x - n ^ 2 = 0
      · right
        by_contra hnn
        exact rootOfTwoScaled hnn (u := x - n) (by linear_combination hzz)
      · left; exact hzz
    rcases hz2 with hz | hz
    · exact ⟨(x ^ 2 - 2 * n * x - n ^ 2) / (2 * y), div_ne_zero hz h2y, by
        rw [mul_one, div_pow]
        rw [eq_div_iff (by positivity)]
        linear_combination d2⟩
    · -- `n = 0`: the second slot is the first slot, already handled
      subst hz
      have hxne : x ≠ 0 := by
        intro hxz
        rw [hxz] at h
        exact hy (pow_eq_zero_iff two_ne_zero |>.mp (by rw [h]; ring))
      refine ⟨(x ^ 2) / (2 * y), div_ne_zero (pow_ne_zero 2 hxne) h2y, by
        rw [mul_one, div_pow]
        rw [eq_div_iff (by positivity)]
        linear_combination d2⟩

/-! ## 4. The half-turn translations, family-wise -/

private lemma avoidRoots {n x y : ℚ} (h : y ^ 2 = x ^ 3 - n ^ 2 * x) (hy : y ≠ 0) :
    x ≠ 0 ∧ x ≠ n ∧ x ≠ -n :=
  FaceHomomorphism.theNonzeroOrdinateAvoidsTheRoots h hy

/-- **The three translations, on every twist**: `x(P + (0,0)) = −n²/x`,
`x(P + (n,0)) = n(x+n)/(x−n)`, `x(P + (−n,0)) = n(n−x)/(x+n)`. -/
theorem theTranslationsOnEveryTwist {n x y : ℚ} (h : y ^ 2 = x ^ 3 - n ^ 2 * x)
    (hy : y ≠ 0) :
    FaithfulFace.translatedX x y 0 = -n ^ 2 / x ∧
    FaithfulFace.translatedX x y n = n * (x + n) / (x - n) ∧
    FaithfulFace.translatedX x y (-n) = n * (n - x) / (x + n) := by
  obtain ⟨hx0, hxn, hxm⟩ := avoidRoots h hy
  have hd1 : x - n ≠ 0 := sub_ne_zero.mpr hxn
  have hd2 : x + n ≠ 0 := fun hc => hxm (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · have e0 : FaithfulFace.translatedX x y 0 = (y / x) ^ 2 - x := by
      simp [FaithfulFace.translatedX]
    rw [e0, div_pow, h]
    field_simp
    ring
  · simp only [FaithfulFace.translatedX, div_pow]
    rw [h]
    field_simp
    ring
  · have e0 : FaithfulFace.translatedX x y (-n) = (y / (x + n)) ^ 2 - x + n := by
      simp only [FaithfulFace.translatedX]; ring_nf
    rw [e0, div_pow, h]
    field_simp
    ring

/-- **A translated point is never a half-turn, on every twist.** -/
theorem theTranslatedPointIsNeverAHalfTurnOnEveryTwist {n x y : ℚ} (hn : n ≠ 0)
    (h : y ^ 2 = x ^ 3 - n ^ 2 * x) (hy : y ≠ 0) :
    (FaithfulFace.translatedX x y 0 ≠ 0 ∧ FaithfulFace.translatedX x y 0 ≠ n ∧
      FaithfulFace.translatedX x y 0 ≠ -n) ∧
    (FaithfulFace.translatedX x y n ≠ 0 ∧ FaithfulFace.translatedX x y n ≠ n ∧
      FaithfulFace.translatedX x y n ≠ -n) ∧
    (FaithfulFace.translatedX x y (-n) ≠ 0 ∧ FaithfulFace.translatedX x y (-n) ≠ n ∧
      FaithfulFace.translatedX x y (-n) ≠ -n) := by
  obtain ⟨hx0, hxn, hxm⟩ := avoidRoots h hy
  have hd1 : x - n ≠ 0 := sub_ne_zero.mpr hxn
  have hd2 : x + n ≠ 0 := fun hc => hxm (by linarith)
  obtain ⟨t0, tn, tm⟩ := theTranslationsOnEveryTwist h hy
  rw [t0, tn, tm]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · intro hc; rw [div_eq_iff hx0] at hc
    exact hn (pow_eq_zero_iff two_ne_zero |>.mp (by linarith))
  · intro hc; rw [div_eq_iff hx0] at hc
    have h0 : n * (x + n) = 0 := by linear_combination -hc
    rcases mul_eq_zero.mp h0 with h' | h'
    · exact hn h'
    · exact hxm (by linarith)
  · intro hc; rw [div_eq_iff hx0] at hc
    have h0 : n * (x - n) = 0 := by linear_combination hc
    rcases mul_eq_zero.mp h0 with h' | h'
    · exact hn h'
    · exact hxn (by linarith)
  · intro hc; rw [div_eq_iff hd1] at hc
    rcases mul_eq_zero.mp (by linarith : n * (x + n) = 0) with h' | h'
    · exact hn h'
    · exact hd2 h'
  · intro hc; rw [div_eq_iff hd1] at hc
    have : n * (2 * n) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact hn h'
    · exact hn (by linarith)
  · intro hc; rw [div_eq_iff hd1] at hc
    have : n * (2 * x) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact hn h'
    · exact hx0 (by linarith)
  · intro hc; rw [div_eq_iff hd2] at hc
    rcases mul_eq_zero.mp (by linarith : n * (n - x) = 0) with h' | h'
    · exact hn h'
    · exact hxn (by linarith)
  · intro hc; rw [div_eq_iff hd2] at hc
    have : n * (2 * x) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact hn h'
    · exact hx0 (by linarith)
  · intro hc; rw [div_eq_iff hd2] at hc
    have : n * (2 * n) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact hn h'
    · exact hn (by linarith)

/-- **The face law closes on every half-turn translation, on every twist**: the six
square-class memberships, with the convention values `−n²`, `−n`, `n`, `2n²`, `−n`,
`−2n` entering as the products the face predicts. -/
theorem theTranslationClosesTheFaceOnEveryTwist {n x y : ℚ} (hn : n ≠ 0)
    (h : y ^ 2 = x ^ 3 - n ^ 2 * x) (hy : y ≠ 0) :
    Descent.SqCls (FaithfulFace.translatedX x y 0) (x * (-n ^ 2)) ∧
    Descent.SqCls (FaithfulFace.translatedX x y 0 - n) ((x - n) * (-n)) ∧
    Descent.SqCls (FaithfulFace.translatedX x y n) (x * n) ∧
    Descent.SqCls (FaithfulFace.translatedX x y n - n) ((x - n) * (2 * n ^ 2)) ∧
    Descent.SqCls (FaithfulFace.translatedX x y (-n)) (x * (-n)) ∧
    Descent.SqCls (FaithfulFace.translatedX x y (-n) - n) ((x - n) * (-2 * n)) := by
  obtain ⟨hx0, hxn, hxm⟩ := avoidRoots h hy
  have hd1 : x - n ≠ 0 := sub_ne_zero.mpr hxn
  have hd2 : x + n ≠ 0 := fun hc => hxm (by linarith)
  obtain ⟨t0, tn, tm⟩ := theTranslationsOnEveryTwist h hy
  have hxn2 : x * (-n ^ 2) ≠ 0 :=
    mul_ne_zero hx0 (neg_ne_zero.mpr (pow_ne_zero 2 hn))
  have h2n2 : (2 : ℚ) * n ^ 2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hn)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine sqcls_of_mul_eq_sq hxn2 (pow_ne_zero 2 hn) ?_
    rw [t0]
    field_simp
  · refine sqcls_of_mul_eq_sq (mul_ne_zero hd1 (neg_ne_zero.mpr hn))
      (div_ne_zero (mul_ne_zero hn hy) hx0) ?_
    rw [t0]
    field_simp
    linear_combination -h
  · refine sqcls_of_mul_eq_sq (mul_ne_zero hx0 hn)
      (div_ne_zero (mul_ne_zero hn hy) hd1) ?_
    rw [tn]
    field_simp
    linear_combination -h
  · refine sqcls_of_mul_eq_sq (mul_ne_zero hd1 h2n2) h2n2 ?_
    rw [tn]
    field_simp
    ring
  · refine sqcls_of_mul_eq_sq (mul_ne_zero hx0 (neg_ne_zero.mpr hn))
      (div_ne_zero (mul_ne_zero hn hy) hd2) ?_
    rw [tm]
    field_simp
    linear_combination -h
  · refine sqcls_of_mul_eq_sq
      (mul_ne_zero hd1 (mul_ne_zero (by norm_num : (-2 : ℚ) ≠ 0) hn))
      (div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hn) hy) hd2) ?_
    rw [tm]
    field_simp
    linear_combination -2 * h

/-! ## 5. The half-turn chord, lifted to the point group -/

private lemma chordHalfTurnRightE {n x₁ y₁ x₂ : ℚ} (hn : n ≠ 0)
    (h₁ : (E n).Nonsingular x₁ y₁) (h₂ : (E n).Nonsingular x₂ 0)
    (hy₁ : y₁ ≠ 0) (hx : x₁ ≠ x₂) :
    Descent.SqCls (slotOne n (Point.some h₁ + Point.some h₂))
      (slotOne n (Point.some h₁) * slotOne n (Point.some h₂)) ∧
    Descent.SqCls (slotTwo n (Point.some h₁ + Point.some h₂))
      (slotTwo n (Point.some h₁) * slotTwo n (Point.some h₂)) := by
  have hcurve := onCurve h₁
  obtain ⟨hx0, hxn, hxm⟩ := avoidRoots hcurve hy₁
  obtain ⟨q0, q1, q2, q3, q4, q5⟩ := theTranslationClosesTheFaceOnEveryTwist hn hcurve hy₁
  obtain ⟨⟨t00, t01, -⟩, ⟨t10, t11, -⟩, ⟨tm0, tm1, -⟩⟩ :=
    theTranslatedPointIsNeverAHalfTurnOnEveryTwist hn hcurve hy₁
  rw [Point.add_of_X_ne hx]
  have haxT : (E n).addX x₁ x₂ ((E n).slope x₁ x₂ y₁ 0) =
      FaithfulFace.translatedX x₁ y₁ x₂ := by
    rw [slope_of_X_ne hx, addXE, FaithfulFace.translatedX]
    have h : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    field_simp
    ring
  have hs₁ : slotOne n (Point.some h₁) = x₁ := by rw [slotOneE_some, if_neg hx0]
  have ht₁ : slotTwo n (Point.some h₁) = x₁ - n := by rw [slotTwoE_some, if_neg hxn]
  rcases halfTurnAbscissaE h₂ rfl with h0 | h0 | h0
  · subst h0
    have hsQ : slotOne n (Point.some h₂) = -n ^ 2 := by
      rw [slotOneE_some, if_pos rfl]
    have htQ : slotTwo n (Point.some h₂) = -n := by
      rw [slotTwoE_some, if_neg (fun hc => hn hc.symm), zero_sub]
    constructor
    · rw [slotOneE_some, haxT, if_neg t00, hs₁, hsQ]
      exact q0
    · rw [slotTwoE_some, haxT, if_neg t01, ht₁, htQ]
      exact q1
  · replace h0 := h0.symm; subst h0
    have hsQ : slotOne n (Point.some h₂) = n := by
      rw [slotOneE_some, if_neg hn]
    have htQ : slotTwo n (Point.some h₂) = 2 * n ^ 2 := by
      rw [slotTwoE_some, if_pos rfl]
    constructor
    · rw [slotOneE_some, haxT, if_neg t10, hs₁, hsQ]
      exact q2
    · rw [slotTwoE_some, haxT, if_neg t11, ht₁, htQ]
      exact q3
  · subst h0
    have hsQ : slotOne n (Point.some h₂) = -n := by
      rw [slotOneE_some, if_neg (neg_ne_zero.mpr hn)]
    have htQ : slotTwo n (Point.some h₂) = -2 * n := by
      rw [slotTwoE_some, if_neg (fun hc => hn (by linarith))]
      ring
    constructor
    · rw [slotOneE_some, haxT, if_neg tm0, hs₁, hsQ]
      exact q4
    · rw [slotTwoE_some, haxT, if_neg tm1, ht₁, htQ]
      exact q5

/-! ## 6. Doubles land in the kernel, on every twist -/

/-- **The doubles land in the kernel, on every twist**: both slots of `Q + Q` lie in the
trivial square class, for every point of `y² = x³ − n²x`. -/
theorem theDoublesLandInTheKernelOnEveryTwist {n : ℚ} (hn : n ≠ 0) (Q : (E n).Point) :
    Descent.SqCls (slotOne n (Q + Q)) 1 ∧ Descent.SqCls (slotTwo n (Q + Q)) 1 := by
  rcases Q with _ | @⟨x, y, h⟩
  · rw [← Point.zero_def, add_zero]
    exact ⟨Descent.sqClsRefl 1, Descent.sqClsRefl 1⟩
  · by_cases hy : y = 0
    · have hzero : (Point.some h : (E n).Point) + Point.some h = 0 :=
        Point.add_self_of_Y_eq (by rw [negYE, hy]; norm_num)
      rw [hzero]
      exact ⟨Descent.sqClsRefl 1, Descent.sqClsRefl 1⟩
    · have hyne : y ≠ (E n).negY x y := by
        rw [negYE]
        intro hc
        exact hy (by linarith)
      rw [Point.add_self_of_Y_ne hyne]
      have hbr : (E n).addX x x ((E n).slope x x y y) =
          FaithfulFace.doubledX x y (-n ^ 2) := by
        have hs : (E n).slope x x y y = (3 * x ^ 2 + -n ^ 2) / (2 * y) := by
          rw [slope_of_Y_ne rfl hyne]
          simp only [negY, E]
          congr 1 <;> ring
        rw [hs, addXE]
        simp only [FaithfulFace.doubledX]
        ring
      obtain ⟨hd0, hd1, -⟩ :=
        theDoubledPointIsNeverAHalfTurnOnEveryTwist hn (onCurve h) hy
      obtain ⟨k1, k2⟩ := doubledTrivialClass (onCurve h) hy
      constructor
      · rw [slotOneE_some, hbr, if_neg hd0]
        exact k1
      · rw [slotTwoE_some, hbr, if_neg hd1]
        exact k2

/-! ## 7. The homomorphism, on every twist -/

/-- **THE FACE IS A HOMOMORPHISM ON EVERY TWIST**: for every nonzero `n` and every pair
of points of `y² = x³ − n²x`, both slots of the sum lie in the square class of the
product of slots.  The per-curve theorems of `FaceHomomorphism.lean` are instances. -/
theorem theFaceIsAHomomorphismOnEveryTwist {n : ℚ} (hn : n ≠ 0) (P Q : (E n).Point) :
    Descent.SqCls (slotOne n (P + Q)) (slotOne n P * slotOne n Q) ∧
    Descent.SqCls (slotTwo n (P + Q)) (slotTwo n P * slotTwo n Q) := by
  rcases P with _ | @⟨x₁, y₁, h₁⟩
  · rw [← Point.zero_def, zero_add,
      show slotOne n (0 : (E n).Point) = 1 from rfl,
      show slotTwo n (0 : (E n).Point) = 1 from rfl, one_mul, one_mul]
    exact ⟨Descent.sqClsRefl _, Descent.sqClsRefl _⟩
  rcases Q with _ | @⟨x₂, y₂, h₂⟩
  · rw [← Point.zero_def, add_zero,
      show slotOne n (0 : (E n).Point) = 1 from rfl,
      show slotTwo n (0 : (E n).Point) = 1 from rfl, mul_one, mul_one]
    exact ⟨Descent.sqClsRefl _, Descent.sqClsRefl _⟩
  by_cases hx : x₁ = x₂
  · subst hx
    have hyy : (y₂ - y₁) * (y₂ + y₁) = 0 := by
      have hA := onCurve h₁
      have hB := onCurve h₂
      linear_combination hB - hA
    rcases mul_eq_zero.mp hyy with hcase | hcase
    · have heq : (Point.some h₂ : (E n).Point) = Point.some h₁ :=
        someEqE rfl (by linarith)
      rw [heq]
      obtain ⟨k1, k2⟩ := theDoublesLandInTheKernelOnEveryTwist hn (Point.some h₁)
      exact ⟨sqcls_scale_sq k1 (slotOneE_ne hn _), sqcls_scale_sq k2 (slotTwoE_ne hn _)⟩
    · by_cases hy0 : y₁ = 0
      · have heq : (Point.some h₂ : (E n).Point) = Point.some h₁ :=
          someEqE rfl (by linarith)
        rw [heq]
        obtain ⟨k1, k2⟩ := theDoublesLandInTheKernelOnEveryTwist hn (Point.some h₁)
        exact ⟨sqcls_scale_sq k1 (slotOneE_ne hn _), sqcls_scale_sq k2 (slotTwoE_ne hn _)⟩
      · have hzero : (Point.some h₁ : (E n).Point) + Point.some h₂ = 0 :=
          Point.add_of_Y_eq rfl (by rw [negYE]; linarith)
        have hs : slotOne n (Point.some h₂) = slotOne n (Point.some h₁) := by
          rw [slotOneE_some, slotOneE_some]
        have ht : slotTwo n (Point.some h₂) = slotTwo n (Point.some h₁) := by
          rw [slotTwoE_some, slotTwoE_some]
        rw [hzero, show slotOne n (0 : (E n).Point) = 1 from rfl,
          show slotTwo n (0 : (E n).Point) = 1 from rfl, hs, ht]
        exact ⟨sqcls_one_mul_self (slotOneE_ne hn _), sqcls_one_mul_self (slotTwoE_ne hn _)⟩
  · by_cases hy1 : y₁ = 0
    · by_cases hy2 : y₂ = 0
      · -- both half-turns: the Klein chords, family-wise
        subst hy1; subst hy2
        rw [Point.add_of_X_ne hx]
        have hax := addXE n x₁ x₂ ((E n).slope x₁ x₂ 0 0)
        have hsl : (E n).slope x₁ x₂ 0 0 = 0 := by
          rw [slope_of_X_ne hx]
          simp
        rcases halfTurnAbscissaE h₁ rfl with hA | hA | hA <;>
          rcases halfTurnAbscissaE h₂ rfl with hB | hB | hB
        · exact absurd (hA.trans hB.symm) hx
        · -- (0,0) + (n,0) lands at −n
          subst hA; replace hB := hB.symm; subst hB
          have hv : (0 : ℚ) ^ 2 - 0 - n = -n := by ring
          constructor
          · rw [slotOneE_some, hax, hsl, hv, if_neg (neg_ne_zero.mpr hn),
              slotOneE_some, if_pos rfl, slotOneE_some, if_neg hn]
            exact ⟨1 / n, one_div_ne_zero hn, by field_simp⟩
          · rw [slotTwoE_some, hax, hsl, hv,
              if_neg (fun hc => hn (by linarith)),
              slotTwoE_some, if_neg (fun hc => hn hc.symm),
              slotTwoE_some, if_pos rfl]
            exact ⟨1 / n, one_div_ne_zero hn, by field_simp; ring⟩
        · -- (0,0) + (−n,0) lands at n
          subst hA; subst hB
          have hv : (0 : ℚ) ^ 2 - 0 - -n = n := by ring
          constructor
          · rw [slotOneE_some, hax, hsl, hv, if_neg hn,
              slotOneE_some, if_pos rfl, slotOneE_some, if_neg (neg_ne_zero.mpr hn)]
            exact ⟨1 / n, one_div_ne_zero hn, by field_simp⟩
          · rw [slotTwoE_some, hax, hsl, hv, if_pos rfl,
              slotTwoE_some, if_neg (fun hc => hn hc.symm),
              slotTwoE_some, if_neg (fun hc => hn (by linarith))]
            exact ⟨1, one_ne_zero, by ring⟩
        · -- (n,0) + (0,0) lands at −n
          replace hA := hA.symm; subst hA; subst hB
          have hv : (0 : ℚ) ^ 2 - n - 0 = -n := by ring
          constructor
          · rw [slotOneE_some, hax, hsl, hv, if_neg (neg_ne_zero.mpr hn),
              slotOneE_some, if_neg hn, slotOneE_some, if_pos rfl]
            exact ⟨1 / n, one_div_ne_zero hn, by field_simp⟩
          · rw [slotTwoE_some, hax, hsl, hv,
              if_neg (fun hc => hn (by linarith)),
              slotTwoE_some, if_pos rfl,
              slotTwoE_some, if_neg (fun hc => hn hc.symm)]
            exact ⟨1 / n, one_div_ne_zero hn, by field_simp; ring⟩
        · exact absurd (hA.trans hB.symm) hx
        · -- (n,0) + (−n,0) lands at 0
          replace hA := hA.symm; subst hA; subst hB
          have hv : (0 : ℚ) ^ 2 - n - -n = 0 := by ring
          constructor
          · rw [slotOneE_some, hax, hsl, hv, if_pos rfl,
              slotOneE_some, if_neg hn, slotOneE_some, if_neg (neg_ne_zero.mpr hn)]
            exact ⟨1, one_ne_zero, by ring⟩
          · rw [slotTwoE_some, hax, hsl, hv,
              if_neg (fun hc => hn hc.symm),
              slotTwoE_some, if_pos rfl,
              slotTwoE_some, if_neg (fun hc => hn (by linarith))]
            exact ⟨1 / (2 * n), one_div_ne_zero (mul_ne_zero two_ne_zero hn), by
              rw [zero_sub]
              field_simp
              ring⟩
        · -- (−n,0) + (0,0) lands at n
          subst hA; subst hB
          have hv : (0 : ℚ) ^ 2 - -n - 0 = n := by ring
          constructor
          · rw [slotOneE_some, hax, hsl, hv, if_neg hn,
              slotOneE_some, if_neg (neg_ne_zero.mpr hn), slotOneE_some, if_pos rfl]
            exact ⟨1 / n, one_div_ne_zero hn, by field_simp⟩
          · rw [slotTwoE_some, hax, hsl, hv, if_pos rfl,
              slotTwoE_some, if_neg (fun hc => hn (by linarith)),
              slotTwoE_some, if_neg (fun hc => hn hc.symm)]
            exact ⟨1, one_ne_zero, by ring⟩
        · -- (−n,0) + (n,0) lands at 0
          subst hA; replace hB := hB.symm; subst hB
          have hv : (0 : ℚ) ^ 2 - -n - n = 0 := by ring
          constructor
          · rw [slotOneE_some, hax, hsl, hv, if_pos rfl,
              slotOneE_some, if_neg (neg_ne_zero.mpr hn), slotOneE_some, if_neg hn]
            exact ⟨1, one_ne_zero, by ring⟩
          · rw [slotTwoE_some, hax, hsl, hv,
              if_neg (fun hc => hn hc.symm),
              slotTwoE_some, if_neg (fun hc => hn (by linarith)),
              slotTwoE_some, if_pos rfl]
            exact ⟨1 / (2 * n), one_div_ne_zero (mul_ne_zero two_ne_zero hn), by
              rw [zero_sub]
              field_simp
              ring⟩
        · exact absurd (hA.trans hB.symm) hx
      · -- the first summand is the half-turn: commute
        subst hy1
        obtain ⟨c1, c2⟩ := chordHalfTurnRightE hn h₂ h₁ hy2 (Ne.symm hx)
        constructor
        · rw [add_comm, mul_comm]
          exact c1
        · rw [add_comm, mul_comm]
          exact c2
    · by_cases hy2 : y₂ = 0
      · subst hy2
        exact chordHalfTurnRightE hn h₁ h₂ hy1 hx
      · -- the general chord, with its three landings
        have eA := onCurve h₁
        have eB := onCurve h₂
        obtain ⟨ha1, ha2, -⟩ := FaceHomomorphism.theNonzeroOrdinateAvoidsTheRoots eA hy1
        obtain ⟨hb1, hb2, -⟩ := FaceHomomorphism.theNonzeroOrdinateAvoidsTheRoots eB hy2
        rw [Point.add_of_X_ne hx]
        have hlam : (E n).slope x₁ x₂ y₁ y₂ * (x₂ - x₁) = y₂ - y₁ := slopeLineE hx
        have hax := addXE n x₁ x₂ ((E n).slope x₁ x₂ y₁ y₂)
        have hs₁ : slotOne n (Point.some h₁) = x₁ := by rw [slotOneE_some, if_neg ha1]
        have hs₂ : slotOne n (Point.some h₂) = x₂ := by rw [slotOneE_some, if_neg hb1]
        have ht₁ : slotTwo n (Point.some h₁) = x₁ - n := by
          rw [slotTwoE_some, if_neg ha2]
        have ht₂ : slotTwo n (Point.some h₂) = x₂ - n := by
          rw [slotTwoE_some, if_neg hb2]
        rw [hs₁, hs₂, ht₁, ht₂]
        by_cases hX0 : (E n).slope x₁ x₂ y₁ y₂ ^ 2 - x₁ - x₂ = 0
        · obtain ⟨-, c1, c2⟩ :=
            FaceHomomorphism.theChordLandsOnTheZeroHalfTurn hn eA eB hlam hx hy1 hy2 hX0
          constructor
          · rw [slotOneE_some, hax, if_pos hX0,
              show -n ^ 2 = n ^ 2 * -1 by ring]
            exact sqcls_mul_sq_left c1 hn
          · rw [slotTwoE_some, hax,
              if_neg (fun hc => hn (by rw [hX0] at hc; linarith)), hX0, zero_sub]
            exact c2
        · by_cases hXn : (E n).slope x₁ x₂ y₁ y₂ ^ 2 - x₁ - x₂ = n
          · obtain ⟨-, c1, c2⟩ :=
              FaceHomomorphism.theChordLandsOnTheSecondHalfTurn hn eA eB hlam hx hy1 hy2 hXn
            constructor
            · rw [slotOneE_some, hax,
                if_neg (fun hc => hn (by rw [← hXn]; exact hc)), hXn]
              exact c1
            · rw [slotTwoE_some, hax, if_pos hXn,
                show 2 * n ^ 2 = n ^ 2 * 2 by ring]
              exact sqcls_mul_sq_left c2 hn
          · obtain ⟨c1, c2⟩ :=
              FaceHomomorphism.theChordLandsGenerically eA eB hlam hx hy1 hy2 hX0 hXn
            constructor
            · rw [slotOneE_some, hax, if_neg hX0]
              exact c1
            · rw [slotTwoE_some, hax, if_neg hXn]
              exact c2

/-! ## 8. The thirty-four instance: the two directions and their sum escape -/

theorem nonsingular00 : (E 34).Nonsingular 0 0 := by
  rw [nonsingular_iff, equation_iff]
  norm_num [E]

theorem nonsingular340 : (E 34).Nonsingular 34 0 := by
  rw [nonsingular_iff, equation_iff]
  norm_num [E]

theorem nonsingularNeg340 : (E 34).Nonsingular (-34) 0 := by
  rw [nonsingular_iff, equation_iff]
  norm_num [E]

theorem nonsingularP1 : (E 34).Nonsingular (-2) 48 := by
  rw [nonsingular_iff, equation_iff]
  norm_num [E]

theorem nonsingularP2 : (E 34).Nonsingular (-16) 120 := by
  rw [nonsingular_iff, equation_iff]
  norm_num [E]

/-- The half-turn at zero on the thirty-four twist. -/
def torsionZero : (E 34).Point := .some nonsingular00

/-- The half-turn at thirty-four. -/
def torsionRight : (E 34).Point := .some nonsingular340

/-- The half-turn at minus thirty-four. -/
def torsionLeft : (E 34).Point := .some nonsingularNeg340

/-- The first realized direction, `P₁ = (−2, 48)`. -/
def firstDirection : (E 34).Point := .some nonsingularP1

/-- The second realized direction, `P₂ = (−16, 120)`. -/
def secondDirection : (E 34).Point := .some nonsingularP2

private lemma h34ne : (34 : ℚ) ≠ 0 := by norm_num

private lemma slotP1_one : slotOne 34 firstDirection = -2 := by
  rw [firstDirection, slotOneE_some]
  norm_num

private lemma slotP1_two : slotTwo 34 firstDirection = -36 := by
  rw [firstDirection, slotTwoE_some]
  norm_num

private lemma slotP2_one : slotOne 34 secondDirection = -16 := by
  rw [secondDirection, slotOneE_some]
  norm_num

private lemma slotP2_two : slotTwo 34 secondDirection = -50 := by
  rw [secondDirection, slotTwoE_some]
  norm_num

private lemma slotT0_two : slotTwo 34 torsionZero = -34 := by
  rw [torsionZero, slotTwoE_some]
  norm_num

private lemma slotT34_one : slotOne 34 torsionRight = 34 := by
  rw [torsionRight, slotOneE_some]
  norm_num

private lemma slotTm34_one : slotOne 34 torsionLeft = -34 := by
  rw [torsionLeft, slotOneE_some]
  norm_num

/-- **THE FIRST DIRECTION ESCAPES**: `P₁ = (−2, 48)` is not `T + 2Q` for any listed
half-turn-or-identity `T` and any point `Q` of the thirty-four twist. -/
theorem theFirstDirectionEscapes :
    ∀ T Q : (E 34).Point,
      (T = 0 ∨ T = torsionZero ∨ T = torsionRight ∨ T = torsionLeft) →
      firstDirection ≠ T + (2 : ℕ) • Q := by
  intro T Q hT hEq
  rw [two_nsmul] at hEq
  obtain ⟨hom1, hom2⟩ := theFaceIsAHomomorphismOnEveryTwist h34ne T (Q + Q)
  rw [← hEq] at hom1 hom2
  obtain ⟨k1, k2⟩ := theDoublesLandInTheKernelOnEveryTwist h34ne Q
  have habs1 := sqcls_absorb_right hom1 k1
  have habs2 := sqcls_absorb_right hom2 k2
  rw [slotP1_one] at habs1
  rw [slotP1_two] at habs2
  rcases hT with rfl | rfl | rfl | rfl
  · rw [show slotOne 34 (0 : (E 34).Point) = 1 from rfl] at habs1
    obtain ⟨c, hc, hcv⟩ := habs1
    nlinarith [sq_nonneg c]
  · rw [slotT0_two] at habs2
    obtain ⟨c, hc, hcv⟩ := habs2
    have h36 : 34 * c ^ 2 = 36 := by linarith
    refine ChordFace.theThirtyFourIsNotASquare ⟨6 / c, ?_⟩
    field_simp
    linear_combination h36
  · rw [slotT34_one] at habs1
    obtain ⟨c, hc, hcv⟩ := habs1
    nlinarith [sq_nonneg c]
  · rw [slotTm34_one] at habs1
    obtain ⟨c, hc, hcv⟩ := habs1
    have h2 : 34 * c ^ 2 = 2 := by linarith
    refine ChordFace.theSeventeenIsNotASquare ⟨1 / c, ?_⟩
    field_simp
    linear_combination h2 / 2

/-- **THE SECOND DIRECTION ESCAPES**: `P₂ = (−16, 120)` is not `T + 2Q` for any listed
`T` and any `Q`. -/
theorem theSecondDirectionEscapes :
    ∀ T Q : (E 34).Point,
      (T = 0 ∨ T = torsionZero ∨ T = torsionRight ∨ T = torsionLeft) →
      secondDirection ≠ T + (2 : ℕ) • Q := by
  intro T Q hT hEq
  rw [two_nsmul] at hEq
  obtain ⟨hom1, hom2⟩ := theFaceIsAHomomorphismOnEveryTwist h34ne T (Q + Q)
  rw [← hEq] at hom1 hom2
  obtain ⟨k1, k2⟩ := theDoublesLandInTheKernelOnEveryTwist h34ne Q
  have habs1 := sqcls_absorb_right hom1 k1
  have habs2 := sqcls_absorb_right hom2 k2
  rw [slotP2_one] at habs1
  rw [slotP2_two] at habs2
  rcases hT with rfl | rfl | rfl | rfl
  · rw [show slotOne 34 (0 : (E 34).Point) = 1 from rfl] at habs1
    obtain ⟨c, hc, hcv⟩ := habs1
    nlinarith [sq_nonneg c]
  · rw [slotT0_two] at habs2
    obtain ⟨c, hc, hcv⟩ := habs2
    have h50 : 34 * c ^ 2 = 50 := by linarith
    refine ChordFace.theSeventeenIsNotASquare ⟨5 / c, ?_⟩
    field_simp
    linear_combination h50 / 2
  · rw [slotT34_one] at habs1
    obtain ⟨c, hc, hcv⟩ := habs1
    nlinarith [sq_nonneg c]
  · rw [slotTm34_one] at habs1
    obtain ⟨c, hc, hcv⟩ := habs1
    have h16 : 34 * c ^ 2 = 16 := by linarith
    refine ChordFace.theThirtyFourIsNotASquare ⟨17 * c / 2, ?_⟩
    field_simp
    linear_combination -(17 : ℚ) / 2 * h16

/-- **THE SUM DIRECTION ESCAPES**: `P₁ + P₂` is not `T + 2Q` for any listed `T` and any
`Q` — the third odd pattern of the mod-2 independence certificate, its face read through
the homomorphism itself. -/
theorem theSumDirectionEscapes :
    ∀ T Q : (E 34).Point,
      (T = 0 ∨ T = torsionZero ∨ T = torsionRight ∨ T = torsionLeft) →
      firstDirection + secondDirection ≠ T + (2 : ℕ) • Q := by
  intro T Q hT hEq
  rw [two_nsmul] at hEq
  obtain ⟨hom1, hom2⟩ := theFaceIsAHomomorphismOnEveryTwist h34ne T (Q + Q)
  rw [← hEq] at hom1 hom2
  obtain ⟨k1, k2⟩ := theDoublesLandInTheKernelOnEveryTwist h34ne Q
  have habs1 := sqcls_absorb_right hom1 k1
  have habs2 := sqcls_absorb_right hom2 k2
  obtain ⟨g1, g2⟩ := theFaceIsAHomomorphismOnEveryTwist h34ne firstDirection secondDirection
  rw [slotP1_one, slotP2_one, show (-2 : ℚ) * -16 = 32 by norm_num] at g1
  rw [slotP1_two, slotP2_two, show (-36 : ℚ) * -50 = 1800 by norm_num] at g2
  have hcls1 := sqcls_trans (sqcls_symm g1) habs1
  have hcls2 := sqcls_trans (sqcls_symm g2) habs2
  rcases hT with rfl | rfl | rfl | rfl
  · rw [show slotOne 34 (0 : (E 34).Point) = 1 from rfl] at hcls1
    obtain ⟨c, hc, hcv⟩ := hcls1
    refine Descent.notSquareTwo ⟨c / 4, ?_⟩
    field_simp
    linear_combination hcv
  · rw [slotT0_two] at hcls2
    obtain ⟨c, hc, hcv⟩ := hcls2
    nlinarith [sq_nonneg c]
  · rw [slotT34_one] at hcls1
    obtain ⟨c, hc, hcv⟩ := hcls1
    have h32 : 34 * c ^ 2 = 32 := by linarith
    refine ChordFace.theSeventeenIsNotASquare ⟨4 / c, ?_⟩
    field_simp
    linear_combination h32 / 2
  · rw [slotTm34_one] at hcls1
    obtain ⟨c, hc, hcv⟩ := hcls1
    nlinarith [sq_nonneg c]

end Soma.Holonics.Millennium.FamilyFace
