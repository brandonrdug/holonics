import Mathlib
import Holonics.Compression.Landmark.FixedPoint

/-!
# The affine landmark, and the sign of `p + q√D` read from integers

[proved-derived] The source is `Holonics/Compression/Landmark/FixedPoint`, whose two theorems on a Möbius
navigator `z ↦ (a z + b)/(c z + d)` carry the hypothesis `c ≠ 0`: `attracting_iff_trace_ne_zero` (with two distinct
fixed points, one attracts when and only when `tr ≠ 0`) and `iterate_tendsto_fixed` (every path off the repelling
fixed point and off the pole converges to the attracting one). #410 asks for the affine case `c = 0` and for the sign
law of `p + q√D`, by which a quadratic landmark is ordered at declared widths.

What is proved.

1. **The affine navigator has one finite fixed point and one at infinity.** With `c = 0` the undivided fixed-point
   law is `(d − a) z = b` (`fixed_iff`); for `a ≠ d` the one finite fixed point is `b/(d − a)` (`fixed_point`,
   `fixed_unique`); infinity is a fixed point of a Möbius navigator when and only when `c = 0`, read as the fixed
   point `0` of the navigator in the chart `w = 1/z` (`atInfinity`, `atInfinity_fixed_zero_iff`,
   `atInfinity_act`).
2. **Where the wording for `c ≠ 0` does not extend.** With `c = 0`, two distinct finite fixed points force `a = d`
   and `b = 0` (`two_fixed_is_identity`): the navigator is the identity (`two_fixed_act`), its trace `2d` is not zero
   and neither quotient of multipliers is below one, so the statement of `attracting_iff_trace_ne_zero` with both
   fixed points finite is false at `c = 0` (`finite_form_fails`). The hypothesis `c ≠ 0` is needed there.
3. **Where it does extend.** With the second fixed point read at infinity, the eigenvalues are `d` at `b/(d − a)`
   and `a` at infinity, the multipliers `a/d` and `d/a`, and for `a ≠ d` one of the two attracts when and only when
   `tr ≠ 0` (`attracting_iff_trace_ne_zero`), with no condition on `b` or on the determinant.
4. **Every path converges.** About a finite fixed point `z₁` the navigator is the scaling
   `act z − z₁ = (a/d)(z − z₁)` (`act_sub_fixed`), so `actⁿ z − z₁ = (a/d)ⁿ (z − z₁)` (`iterate_sub_fixed`); for
   `|a| < |d|` the iterates converge to `z₁` from every start, with no pole to avoid and no repelling point in the
   finite chart (`iterate_tendsto_fixed`, `iterate_tendsto`); for `|d| < |a|` they leave every bound from every start
   but `z₁` (`iterate_tendsto_atTop`), which is convergence to the fixed point at infinity.
5. **The neutral cases.** `tr = 0` is the half-turn about the fixed point, `act z = 2 z₁ − z`, an involution
   (`half_turn`, `half_turn_involutive`); `a = d` is the shear `actⁿ z = z + n b/d` (`shear_iterate`), with no finite
   fixed point when `b ≠ 0` (`shear_no_fixed`).
6. **The kind of an affine site.** Its discriminant is the square `(a − d)²` (`discriminant_eq`), so it is never a
   rotation (`not_rotation`), and with `a ≠ d` and a positive determinant it is a boost site (`is_boost`).
7. **The sign law.** For `D > 0` the sign of `p + q√D` is read from `p`, `q` and `p² − D q²` alone
   (`quadSign`, `sign_add_mul_sqrt`): where `p` and `q` do not oppose it is the sign of `p + q`
   (`quadSign_of_nonneg`, `quadSign_of_nonpos`); for `p > 0 > q` it is the sign of `p² − D q²`
   (`quadSign_pos_neg`); for `p < 0 < q` the sign of `D q² − p²` (`quadSign_neg_pos`). The law is the same on rational
   and on integer entries (`sign_add_mul_sqrt_rat`, `sign_add_mul_sqrt_int`), so two quadratic landmarks are ordered
   by integer arithmetic (`lt_iff_quadSign`), and for a rational `D ≥ 0` that is no square the value is zero only at
   `p = q = 0` (`add_mul_sqrt_eq_zero_iff`). Rulers: `3 − 2√2 > 0`, `−7 + 5√2 > 0`, `1 − √2 < 0`
   (`ruler_signs`), and the convergents `8/5 < (1 + √5)/2 < 13/8` of the golden landmark (`ruler_golden`).

Limits. The first-arrival sieve tower beyond Eratosthenes, which #410 names in the same box, is not here. Infinity is
read through the chart `w = 1/z`; no projective line is built as a type. The sign law is of one quadratic surd over
an ordered field's rationals or integers; sums of surds of different `D` are not treated. The integers of the law are
unbounded: the width `p² − D q²` needs (about twice the operands' places plus `D`'s) is the consumer's to declare.

The computational object is the helical pair interaction: a Möbius navigator is a pair's undivided ratio transported,
and its landmark is the face where its paths converge. Of the winding guide's six general objects this touches the
helix (the scaling `(a/d)ⁿ` about the fixed point is a clock's stride) and faces and placement (the sign law reads a
face at a declared width); the pair, cell holonomy, tube and tower thread stay attached.

Consumers: #410's box "Möbius and quadratic landmarks: the affine `c = 0` case … the sign law of `p + q√D`";
`Compression/Landmark/FixedPoint` (its `c ≠ 0` theorems); the precision law's "a number is read at a declared width".

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Compression.Landmark.AffineLandmark

open Filter Topology
open Holonics.Compression.Landmark.FixedPoint
open Holonics.Compression.Landmark.SiteKind

/-! ## 1. The fixed points of an affine navigator -/

section Field

variable {K : Type*} [Field K] (m : Mobius K)

/-- [proved-derived] With `c = 0` the undivided fixed-point law is `(d − a) z = b`. -/
theorem fixed_iff (hc : m.c = 0) (z : K) : m.Fixed z ↔ (m.d - m.a) * z = m.b := by
  unfold Mobius.Fixed
  rw [hc]
  constructor <;> intro h <;> linear_combination -h

/-- [proved-derived] For `a ≠ d` the point `b/(d − a)` is fixed. -/
theorem fixed_point (hc : m.c = 0) (had : m.a ≠ m.d) : m.Fixed (m.b / (m.d - m.a)) := by
  rw [fixed_iff m hc]
  have h : m.d - m.a ≠ 0 := sub_ne_zero.mpr (Ne.symm had)
  field_simp

/-- [proved-derived] For `a ≠ d` it is the only finite fixed point. -/
theorem fixed_unique (hc : m.c = 0) (had : m.a ≠ m.d) (z : K) : m.Fixed z ↔ z = m.b / (m.d - m.a) := by
  rw [fixed_iff m hc]
  have h : m.d - m.a ≠ 0 := sub_ne_zero.mpr (Ne.symm had)
  rw [eq_div_iff h, mul_comm]

/-- [definition] The navigator read in the chart at infinity, `w = 1/z`: the block with its diagonal and its
off-diagonal exchanged. -/
def atInfinity : Mobius K := ⟨m.d, m.c, m.b, m.a⟩

/-- [proved-derived] **Infinity is fixed when and only when `c = 0`**: the chart at infinity fixes `w = 0`. -/
theorem atInfinity_fixed_zero_iff : (atInfinity m).Fixed 0 ↔ m.c = 0 := by
  simp [Mobius.Fixed, atInfinity]

/-- [proved-derived] The chart at infinity acts as `w ↦ 1/act(1/w)`. -/
theorem atInfinity_act (w : K) (hw : w ≠ 0) : (atInfinity m).act w = (m.act w⁻¹)⁻¹ := by
  unfold Mobius.act atInfinity
  simp only
  rw [inv_div]
  have h1 : m.c * w⁻¹ + m.d = (m.d * w + m.c) / w := by
    field_simp
    ring
  have h2 : m.a * w⁻¹ + m.b = (m.b * w + m.a) / w := by
    field_simp
    ring
  rw [h1, h2, div_div_div_cancel_right₀ hw]

/-- [proved-derived] The chart at infinity keeps the trace and the determinant faces. -/
theorem atInfinity_faces : (atInfinity m).trace = m.trace ∧ (atInfinity m).det = m.det := by
  constructor
  · simp [Mobius.trace, atInfinity, add_comm]
  · simp only [Mobius.det, atInfinity]
    ring

/-- [proved-derived] **Two finite fixed points of an affine navigator make it the identity's block**: `a = d` and
`b = 0`. -/
theorem two_fixed_is_identity (hc : m.c = 0) {z₁ z₂ : K} (h₁ : m.Fixed z₁) (h₂ : m.Fixed z₂) (hne : z₁ ≠ z₂) :
    m.a = m.d ∧ m.b = 0 := by
  rw [fixed_iff m hc] at h₁ h₂
  have h : (m.d - m.a) * (z₁ - z₂) = 0 := by linear_combination h₁ - h₂
  have had : m.d - m.a = 0 := (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hne)
  refine ⟨(sub_eq_zero.mp had).symm, ?_⟩
  rw [← h₁, had, zero_mul]

/-- [proved-derived] Such a navigator fixes every point. -/
theorem two_fixed_act (hc : m.c = 0) (hd : m.d ≠ 0) {z₁ z₂ : K} (h₁ : m.Fixed z₁) (h₂ : m.Fixed z₂)
    (hne : z₁ ≠ z₂) (z : K) : m.act z = z := by
  obtain ⟨had, hb⟩ := two_fixed_is_identity m hc h₁ h₂ hne
  unfold Mobius.act
  rw [hc, hb, had, zero_mul, zero_add, add_zero, mul_div_cancel_left₀ z hd]

/-- [proved-derived] About a finite fixed point the affine navigator is the scaling by `a/d`. -/
theorem act_sub_fixed (hc : m.c = 0) (hd : m.d ≠ 0) {z₁ : K} (h₁ : m.Fixed z₁) (z : K) :
    m.act z - z₁ = m.a / m.d * (z - z₁) := by
  rw [fixed_iff m hc] at h₁
  unfold Mobius.act
  rw [hc, zero_mul, zero_add, ← h₁]
  field_simp
  ring

/-- [proved-derived] **The closed form of a path**: `actⁿ z − z₁ = (a/d)ⁿ (z − z₁)`. -/
theorem iterate_sub_fixed (hc : m.c = 0) (hd : m.d ≠ 0) {z₁ : K} (h₁ : m.Fixed z₁) (z : K) (k : ℕ) :
    m.act^[k] z - z₁ = (m.a / m.d) ^ k * (z - z₁) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', act_sub_fixed m hc hd h₁, ih, pow_succ]
    ring

/-- [proved-derived] **The half-turn**: with `tr = 0` the affine navigator is the reflection `z ↦ 2 z₁ − z` about
its fixed point. -/
theorem half_turn (hc : m.c = 0) (hd : m.d ≠ 0) (htr : m.trace = 0) {z₁ : K} (h₁ : m.Fixed z₁) (z : K) :
    m.act z = 2 * z₁ - z := by
  have ha : m.a = -m.d := by
    unfold Mobius.trace at htr
    linear_combination htr
  have h := act_sub_fixed m hc hd h₁ z
  rw [ha, neg_div, div_self hd] at h
  linear_combination h

/-- [proved-derived] The half-turn is an involution. -/
theorem half_turn_involutive (hc : m.c = 0) (hd : m.d ≠ 0) (htr : m.trace = 0) {z₁ : K} (h₁ : m.Fixed z₁)
    (z : K) : m.act (m.act z) = z := by
  rw [half_turn m hc hd htr h₁, half_turn m hc hd htr h₁]
  ring

/-- [proved-derived] **The shear**: with `a = d` the affine navigator is the translation by `b/d`, and its path is
`z + n b/d`. -/
theorem shear_iterate (hc : m.c = 0) (hd : m.d ≠ 0) (had : m.a = m.d) (z : K) (k : ℕ) :
    m.act^[k] z = z + k * (m.b / m.d) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    unfold Mobius.act
    rw [hc, had]
    push_cast
    field_simp
    ring

/-- [proved-derived] A shear with `b ≠ 0` has no finite fixed point. -/
theorem shear_no_fixed (hc : m.c = 0) (had : m.a = m.d) (hb : m.b ≠ 0) (z : K) : ¬ m.Fixed z := by
  rw [fixed_iff m hc, had, sub_self, zero_mul]
  exact fun h => hb h.symm

end Field

/-! ## 2. Attraction -/

section Ordered

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (m : Mobius K)

/-- [counterexample] **The wording for `c ≠ 0` fails at `c = 0`**: with two distinct finite fixed points the
navigator is the identity, its trace is not zero, and neither quotient of the multipliers `c z_i + d` is below
one. -/
theorem finite_form_fails (hc : m.c = 0) (hd : m.d ≠ 0) {z₁ z₂ : K} (h₁ : m.Fixed z₁) (h₂ : m.Fixed z₂)
    (hne : z₁ ≠ z₂) :
    m.trace ≠ 0 ∧
      ¬ (|(m.c * z₂ + m.d) / (m.c * z₁ + m.d)| < 1 ∨ |(m.c * z₁ + m.d) / (m.c * z₂ + m.d)| < 1) := by
  obtain ⟨had, -⟩ := two_fixed_is_identity m hc h₁ h₂ hne
  constructor
  · unfold Mobius.trace
    rw [had]
    intro h
    have h2 : (2 : K) * m.d = 0 := by linear_combination h
    exact hd ((mul_eq_zero.mp h2).resolve_left two_ne_zero)
  · rw [hc]
    simp [div_self hd]

/-- [proved-derived] **One fixed point attracts when and only when `tr ≠ 0`**, the second fixed point read at
infinity: for an affine navigator with `a ≠ d` the multiplier `a/d` at the finite fixed point or `d/a` at infinity
is below one in size when and only when the trace is not zero. -/
theorem attracting_iff_trace_ne_zero (had : m.a ≠ m.d) :
    (|m.a / m.d| < 1 ∨ |m.d / m.a| < 1) ↔ m.trace ≠ 0 := by
  unfold Mobius.trace
  constructor
  · rintro h htr
    have ha : m.a = -m.d := by linear_combination htr
    have hd : m.d ≠ 0 := by
      intro h0
      apply had
      rw [ha, h0, neg_zero]
    rw [ha, neg_div, div_self hd, div_neg, div_self hd, abs_neg, abs_one] at h
    simp at h
  · intro htr
    have habs : |m.a| ≠ |m.d| := by
      intro h
      rcases abs_eq_abs.mp h with h | h
      · exact had h
      · exact htr (by rw [h]; ring)
    rcases lt_or_gt_of_ne habs with h | h
    · left
      have hd : m.d ≠ 0 := by
        intro h0
        rw [h0, abs_zero] at h
        exact absurd h (not_lt.mpr (abs_nonneg _))
      rw [abs_div, div_lt_one (abs_pos.mpr hd)]
      exact h
    · right
      have ha : m.a ≠ 0 := by
        intro h0
        rw [h0, abs_zero] at h
        exact absurd h (not_lt.mpr (abs_nonneg _))
      rw [abs_div, div_lt_one (abs_pos.mpr ha)]
      exact h

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-derived] The discriminant face of an affine site is the square `(a − d)²`. -/
theorem discriminant_eq (hc : m.c = 0) : m.trace ^ 2 - 4 * m.det = (m.a - m.d) ^ 2 := by
  unfold Mobius.trace Mobius.det
  rw [hc]
  ring

/-- [proved-derived] An affine site is never a rotation. -/
theorem not_rotation (hc : m.c = 0) : siteKind m.trace m.det ≠ .rotation := by
  rw [Ne, siteKind_eq_rotation_iff]
  have h := discriminant_eq m hc
  nlinarith [sq_nonneg (m.a - m.d)]

/-- [proved-derived] An affine site with `a ≠ d` and a positive determinant is a boost site. -/
theorem is_boost (hc : m.c = 0) (had : m.a ≠ m.d) (hdet : 0 < m.det) : siteKind m.trace m.det = .boost := by
  rw [siteKind_eq_boost_iff]
  refine ⟨hdet, ?_⟩
  have h := discriminant_eq m hc
  have hpos : 0 < (m.a - m.d) ^ 2 := by
    have : m.a - m.d ≠ 0 := sub_ne_zero.mpr had
    positivity
  linarith

end Ordered

section Converge

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Archimedean K]
  [TopologicalSpace K] [OrderTopology K] (m : Mobius K)

/-- [proved-derived] **Every path converges to the finite fixed point** when `|a| < |d|`: no start is excluded and
there is no pole. -/
theorem iterate_tendsto_fixed (hc : m.c = 0) (hlt : |m.a| < |m.d|) {z₁ : K} (h₁ : m.Fixed z₁) (z : K) :
    Tendsto (fun k => m.act^[k] z) atTop (𝓝 z₁) := by
  have hd : m.d ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hlt
    exact absurd hlt (not_lt.mpr (abs_nonneg _))
  have hr : |m.a / m.d| < 1 := by
    rw [abs_div, div_lt_one (abs_pos.mpr hd)]
    exact hlt
  have h0 : Tendsto (fun k : ℕ => (m.a / m.d) ^ k * (z - z₁) + z₁) atTop (𝓝 (0 * (z - z₁) + z₁)) :=
    ((tendsto_pow_atTop_nhds_zero_iff.mpr hr).mul_const (z - z₁)).add_const z₁
  rw [zero_mul, zero_add] at h0
  refine h0.congr fun k => ?_
  rw [← iterate_sub_fixed m hc hd h₁ z k]
  ring

/-- [proved-derived] The same with the landmark written out: for `|a| < |d|` every path converges to
`b/(d − a)`. -/
theorem iterate_tendsto (hc : m.c = 0) (hlt : |m.a| < |m.d|) (z : K) :
    Tendsto (fun k => m.act^[k] z) atTop (𝓝 (m.b / (m.d - m.a))) := by
  have had : m.a ≠ m.d := by
    intro h
    rw [h] at hlt
    exact lt_irrefl _ hlt
  exact iterate_tendsto_fixed m hc hlt (fixed_point m hc had) z

omit [TopologicalSpace K] [OrderTopology K] in
/-- [proved-derived] **For `|d| < |a|` every path but the fixed one leaves every bound**: the fixed point at
infinity attracts. -/
theorem iterate_tendsto_atTop (hc : m.c = 0) (hd : m.d ≠ 0) (hlt : |m.d| < |m.a|) {z₁ : K} (h₁ : m.Fixed z₁)
    {z : K} (hz : z ≠ z₁) : Tendsto (fun k => |m.act^[k] z|) atTop atTop := by
  have hr : 1 < |m.a / m.d| := by
    rw [abs_div, one_lt_div (abs_pos.mpr hd)]
    exact hlt
  have hpos : 0 < |z - z₁| := abs_pos.mpr (sub_ne_zero.mpr hz)
  have h1 : Tendsto (fun k : ℕ => |m.a / m.d| ^ k * |z - z₁| + -|z₁|) atTop atTop :=
    tendsto_atTop_add_const_right _ _ ((tendsto_pow_atTop_atTop_of_one_lt hr).atTop_mul_const hpos)
  refine tendsto_atTop_mono (fun k => ?_) h1
  have h := iterate_sub_fixed m hc hd h₁ z k
  have h2 : |m.act^[k] z - z₁| = |m.a / m.d| ^ k * |z - z₁| := by
    rw [h, abs_mul, abs_pow]
  have h3 : |m.act^[k] z - z₁| ≤ |m.act^[k] z| + |z₁| := abs_sub _ _
  linarith

end Converge

/-! ## 3. The sign of `p + q√D` -/

section Sign

/-- [definition] **The sign of `p + q√D` read from `p`, `q` and `p² − D q²`**: where `p` and `q` do not oppose, the
sign of `p + q`; where they oppose, the sign of `p` times the sign of the norm `p² − D q²`. -/
def quadSign {K : Type*} [Ring K] [LinearOrder K] (p q D : K) : SignType :=
  if 0 ≤ p * q then SignType.sign (p + q) else SignType.sign p * SignType.sign (p ^ 2 - D * q ^ 2)

section Table

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- [proved-derived] Both parts nonnegative: the sign of `p + q`. -/
theorem quadSign_of_nonneg {p q : K} (D : K) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    quadSign p q D = SignType.sign (p + q) := by
  unfold quadSign
  rw [if_pos (mul_nonneg hp hq)]

/-- [proved-derived] Both parts nonpositive: the sign of `p + q`. -/
theorem quadSign_of_nonpos {p q : K} (D : K) (hp : p ≤ 0) (hq : q ≤ 0) :
    quadSign p q D = SignType.sign (p + q) := by
  unfold quadSign
  rw [if_pos (mul_nonneg_of_nonpos_of_nonpos hp hq)]

/-- [proved-derived] `p > 0 > q`: the sign of the norm `p² − D q²`. -/
theorem quadSign_pos_neg {p q : K} (D : K) (hp : 0 < p) (hq : q < 0) :
    quadSign p q D = SignType.sign (p ^ 2 - D * q ^ 2) := by
  unfold quadSign
  rw [if_neg (not_le.mpr (mul_neg_of_pos_of_neg hp hq)), sign_pos hp, one_mul]

/-- [proved-derived] `p < 0 < q`: the sign of `D q² − p²`. -/
theorem quadSign_neg_pos {p q : K} (D : K) (hp : p < 0) (hq : 0 < q) :
    quadSign p q D = SignType.sign (D * q ^ 2 - p ^ 2) := by
  unfold quadSign
  rw [if_neg (not_le.mpr (mul_neg_of_neg_of_pos hp hq)), sign_neg hp, ← neg_sub (p ^ 2), Left.sign_neg]
  simp

end Table

/-- [proved-derived] **The sign law**: for `D > 0` the sign of `p + q√D` is `quadSign p q D`. -/
theorem sign_add_mul_sqrt (p q D : ℝ) (hD : 0 < D) : SignType.sign (p + q * √D) = quadSign p q D := by
  have hs : 0 < √D := Real.sqrt_pos.mpr hD
  have hss : √D * √D = D := Real.mul_self_sqrt hD.le
  have hfac : p ^ 2 - D * q ^ 2 = (p - q * √D) * (p + q * √D) := by
    have h : (p - q * √D) * (p + q * √D) = p ^ 2 - √D * √D * q ^ 2 := by ring
    rw [h, hss]
  rcases lt_trichotomy p 0 with hp | hp | hp <;> rcases lt_trichotomy q 0 with hq | hq | hq
  · have h : q * √D < 0 := mul_neg_of_neg_of_pos hq hs
    rw [quadSign_of_nonpos D hp.le hq.le, sign_neg (by linarith), sign_neg (by linarith)]
  · rw [quadSign_of_nonpos D hp.le hq.le, hq, zero_mul]
  · have h : 0 < q * √D := mul_pos hq hs
    have h3 : p - q * √D < 0 := by linarith
    unfold quadSign
    rw [if_neg (not_le.mpr (mul_neg_of_neg_of_pos hp hq)), hfac, sign_mul, sign_neg hp, sign_neg h3]
    generalize SignType.sign (p + q * √D) = t
    cases t <;> rfl
  · have h : q * √D < 0 := mul_neg_of_neg_of_pos hq hs
    rw [quadSign_of_nonpos D hp.le hq.le, hp, zero_add, zero_add, sign_neg h, sign_neg hq]
  · rw [quadSign_of_nonneg D hp.ge hq.ge, hp, hq]
    simp
  · have h : 0 < q * √D := mul_pos hq hs
    rw [quadSign_of_nonneg D hp.ge hq.le, hp, zero_add, zero_add, sign_pos h, sign_pos hq]
  · have h : q * √D < 0 := mul_neg_of_neg_of_pos hq hs
    have h3 : 0 < p - q * √D := by linarith
    rw [quadSign_pos_neg D hp hq, hfac, sign_mul, sign_pos h3, one_mul]
  · rw [quadSign_of_nonneg D hp.le hq.ge, hq, zero_mul]
  · have h : 0 < q * √D := mul_pos hq hs
    rw [quadSign_of_nonneg D hp.le hq.le, sign_pos (by linarith), sign_pos (by linarith)]

private theorem sign_ratCast (x : ℚ) : SignType.sign (x : ℝ) = SignType.sign x := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [sign_neg h, sign_neg (by exact_mod_cast h)]
  · rw [h]
    simp
  · rw [sign_pos h, sign_pos (by exact_mod_cast h)]

private theorem sign_intCast (x : ℤ) : SignType.sign (x : ℝ) = SignType.sign x := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [sign_neg h, sign_neg (by exact_mod_cast h)]
  · rw [h]
    simp
  · rw [sign_pos h, sign_pos (by exact_mod_cast h)]

/-- [proved-derived] The law reads the same on rational entries as on their real values. -/
theorem quadSign_ratCast (p q D : ℚ) : quadSign (p : ℝ) (q : ℝ) (D : ℝ) = quadSign p q D := by
  unfold quadSign
  have h : (0 ≤ (p : ℝ) * q) ↔ 0 ≤ p * q := by exact_mod_cast Iff.rfl
  by_cases hpq : 0 ≤ p * q
  · rw [if_pos hpq, if_pos (h.mpr hpq), ← sign_ratCast]
    push_cast
    rfl
  · rw [if_neg hpq, if_neg (mt h.mp hpq), ← sign_ratCast p, ← sign_ratCast (p ^ 2 - D * q ^ 2)]
    push_cast
    rfl

/-- [proved-derived] The law reads the same on integer entries as on their real values. -/
theorem quadSign_intCast (p q D : ℤ) : quadSign (p : ℝ) (q : ℝ) (D : ℝ) = quadSign p q D := by
  unfold quadSign
  have h : (0 ≤ (p : ℝ) * q) ↔ 0 ≤ p * q := by exact_mod_cast Iff.rfl
  by_cases hpq : 0 ≤ p * q
  · rw [if_pos hpq, if_pos (h.mpr hpq), ← sign_intCast]
    push_cast
    rfl
  · rw [if_neg hpq, if_neg (mt h.mp hpq), ← sign_intCast p, ← sign_intCast (p ^ 2 - D * q ^ 2)]
    push_cast
    rfl

/-- [proved-derived] **The sign law on rationals**: no root is taken. -/
theorem sign_add_mul_sqrt_rat (p q D : ℚ) (hD : 0 < D) :
    SignType.sign ((p : ℝ) + q * √(D : ℝ)) = quadSign p q D := by
  rw [sign_add_mul_sqrt _ _ _ (by exact_mod_cast hD), quadSign_ratCast]

/-- [proved-derived] **The sign law on integers**: the sign is read from integer sums and products alone. -/
theorem sign_add_mul_sqrt_int (p q D : ℤ) (hD : 0 < D) :
    SignType.sign ((p : ℝ) + q * √(D : ℝ)) = quadSign p q D := by
  rw [sign_add_mul_sqrt _ _ _ (by exact_mod_cast hD), quadSign_intCast]

/-- [proved-derived] **Two quadratic landmarks are ordered by the law**:
`p₁ + q₁√D < p₂ + q₂√D` when and only when `quadSign (p₂ − p₁) (q₂ − q₁) D = 1`. -/
theorem lt_iff_quadSign (p₁ q₁ p₂ q₂ D : ℚ) (hD : 0 < D) :
    (p₁ : ℝ) + q₁ * √(D : ℝ) < p₂ + q₂ * √(D : ℝ) ↔ quadSign (p₂ - p₁) (q₂ - q₁) D = 1 := by
  rw [← sign_add_mul_sqrt_rat _ _ _ hD, sign_eq_one_iff, ← sub_pos]
  push_cast
  constructor <;> intro h <;> linarith

/-- [proved-standard] For a rational `D ≥ 0` that is no square, `p + q√D` is zero only at `p = q = 0`. -/
theorem add_mul_sqrt_eq_zero_iff (p q D : ℚ) (hD : 0 ≤ D) (hsq : ¬ IsSquare D) :
    (p : ℝ) + q * √(D : ℝ) = 0 ↔ p = 0 ∧ q = 0 := by
  have hirr : Irrational (√(D : ℝ)) := (irrational_sqrt_ratCast_iff_of_nonneg hD).mpr hsq
  constructor
  · intro h
    by_cases hq : q = 0
    · refine ⟨?_, hq⟩
      rw [hq] at h
      simpa using h
    · exfalso
      have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
      apply hirr
      refine ⟨-p / q, ?_⟩
      push_cast
      field_simp
      linear_combination -h
  · rintro ⟨rfl, rfl⟩
    simp

/-- [proved-derived] Rulers on integers: `3 − 2√2 > 0` (9 against 8), `−7 + 5√2 > 0` (49 against 50) and
`1 − √2 < 0` (1 against 2). -/
theorem ruler_signs :
    quadSign (3 : ℤ) (-2) 2 = 1 ∧ quadSign (-7 : ℤ) 5 2 = 1 ∧ quadSign (1 : ℤ) (-1) 2 = -1 := by
  decide

/-- [proved-derived] A ruler on the golden landmark `(1 + √5)/2`, the attracting fixed point of `z ↦ 1 + 1/z`: the
convergents `8/5` and `13/8` stand on its two sides, read from `121·4 < 5·100` and `81·4 > 5·64`. -/
theorem ruler_golden : (8 / 5 : ℝ) < (1 + √5) / 2 ∧ (1 + √5) / 2 < (13 / 8 : ℝ) := by
  have h1 := (lt_iff_quadSign (8 / 5) 0 (1 / 2) (1 / 2) 5 (by norm_num)).mpr (by
    rw [quadSign_neg_pos 5 (by norm_num) (by norm_num)]
    exact sign_pos (by norm_num))
  have h2 := (lt_iff_quadSign (1 / 2) (1 / 2) (13 / 8) 0 5 (by norm_num)).mpr (by
    rw [quadSign_pos_neg 5 (by norm_num) (by norm_num)]
    exact sign_pos (by norm_num))
  push_cast at h1 h2
  constructor <;> linarith

end Sign

end Holonics.Compression.Landmark.AffineLandmark
