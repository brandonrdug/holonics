import Holonics.Compression.Landmark.SiteKind
import Holonics.Geometry.CrossRatio
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Rat
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Landmarks are fixed points where navigator paths converge

[definition] A **Möbius navigator** is the fractional chart `z ↦ (a z + b)/(c z + d)` of the
undivided block transport of `Geometry/CrossRatio` (`RatioPresentation.blockTransport` of
`(z, 1)`). Its trace face `a + d` and determinant face `ad − bc` are the site faces of
`Compression/Landmark/SiteKind`. A **landmark** of a navigator family is a face where its paths
converge; for a Möbius navigator it is a fixed point, and the fixed point that attracts every path
is where the navigator's words converge.

[proved-derived; formal-checked] What is proved.

1. **The undivided fixed-point law.** A fixed point `z₁` (`a z₁ + b = z₁(c z₁ + d)`) factors the
   navigator's displacement: `(a z + b) − z₁(c z + d) = (a − c z₁)(z − z₁)` (`sub_fixed`), so
   `act z − z₁ = μ₂ (z − z₁)/(c z + d)` with `μ₂ = a − c z₁` (`act_sub_fixed`).
2. **At most two fixed points.** Two distinct fixed points `z₁ ≠ z₂` force every fixed point to be
   one of them, unless the navigator is the identity (`b = c = 0`, `a = d`)
   (`fixed_points_at_most_two`). Their multipliers `μ_i = c z_i + d` are the navigator's
   eigenvalues: `μ₁ + μ₂ = tr`, `μ₁ μ₂ = det` (`multipliers_sum`, `multipliers_prod`), and
   `tr² − 4 det = (μ₁ − μ₂)²` (`discriminant_eq_sq`). With `c ≠ 0`, two distinct fixed points make
   the discriminant positive (`two_fixed_points_disc_pos`); with `det > 0` as well the navigator is
   a **boost site** (`two_fixed_points_is_boost`).
3. **One attracting, one repelling, exactly when `tr ≠ 0`.** The multiplier at `z₁` is `μ₂/μ₁` and
   at `z₂` is `μ₁/μ₂`. With `c ≠ 0` the multipliers differ, so they have equal size exactly when
   `μ₂ = −μ₁`, that is when `tr = 0`: one fixed point attracts (`|μ₂/μ₁| < 1`) or the other does
   exactly when `tr ≠ 0` (`attracting_iff_trace_ne_zero`). The sign of `det` plays no part. In the
   fixed-point chart `w = (z − z₁)/(z − z₂)` the navigator is the scaling `w ↦ (μ₂/μ₁) w`
   (`chart_conjugates`), so **every path converges to the attracting fixed point**: for
   `|μ₂| < |μ₁|` and any start `z ≠ z₂` whose orbit avoids the pole, `mⁿ z → z₁`
   (`iterate_tendsto_fixed`), over any Archimedean ordered field.
4. **Velocity addition.** `u ↦ (u + v)/(1 + uv)` is the Möbius navigator `[[1, v],[v, 1]]`
   (`velocity_act`), a boost site for `0 < |v| < 1` whose projective trace face is the Lorentz
   factor, `tr²/(4 det) = 1/(1 − v²)` (`velocity_is_boost`). It fixes `±1`
   (`vadd_fixes_one`, `vadd_fixes_neg_one`). In the Doppler chart `D(u) = (1+u)/(1−u)` it
   multiplies, `D(vadd v u) = D(u) D(v)` (`doppler_vadd`), preserves the open cone `|u| < 1`
   (`vadd_mem`), and its iterates are exactly `1 − uₙ = 2/(D(u) D(v)ⁿ + 1)`
   (`one_sub_iterate`). So for `0 < v < 1` **the iterates of one boost from `|u| < 1` converge to
   `1`** (`vadd_iterate_tendsto_one`), and for `−1 < v < 0` to `−1`
   (`vadd_iterate_tendsto_neg_one`). With a characteristic `c > 0` the navigator is velocity
   addition in units of `c` (`vaddC_fixes`, `vaddC_iterate`), fixes `±c`, and the iterates of one
   boost `0 < v < c` from `|u| < c` converge to `c` (`vaddC_iterate_tendsto_c`), and for
   `−c < v < 0` to `−c` (`vaddC_iterate_tendsto_neg_c`): `c` is the landmark of the boost family.

[counterexample; formal-checked]
- **`det > 0` is not needed for attraction.** `z ↦ (z + 2)/(2z + 1)` has `det = −3`, fixed points
  `±1` with multipliers `−1/3` at `1` and `−3` at `−1`, and every path from `z ≥ 0` converges to
  `1` (`reflection_attracts`).
- **`tr = 0` is neutral.** The Swing `z ↦ 1/z` (harmonic conjugation fixing `±1`) has `tr = 0`,
  `det = −1`, and multiplier `−1` at both fixed points: an involution whose fixed points neither
  attract nor repel (`swing_neither_attracts`).
-/

namespace Holonics.Compression.Landmark.FixedPoint

open Filter Topology
open Holonics.Compression.Landmark.SiteKind

/-! ## 1. A Möbius navigator -/

/-- [definition] A Möbius navigator step `z ↦ (a z + b)/(c z + d)`, carried by its block. -/
structure Mobius (K : Type*) where
  a : K
  b : K
  c : K
  d : K

namespace Mobius

section Field

variable {K : Type*} [Field K] (m : Mobius K)

/-- [definition] The fractional chart of the navigator. -/
def act (z : K) : K := (m.a * z + m.b) / (m.c * z + m.d)

/-- [definition] The trace face. -/
def trace : K := m.a + m.d

/-- [definition] The determinant face. -/
def det : K := m.a * m.d - m.b * m.c

/-- [definition] `z` is an undivided fixed point: `a z + b = z (c z + d)`. -/
def Fixed (z : K) : Prop := m.a * z + m.b = z * (m.c * z + m.d)

/-- [proved-derived; formal-checked] The fractional chart reads the undivided block transport of
`(z, 1)` (`Geometry/CrossRatio`). -/
theorem act_eq_blockTransport (z : K) :
    m.act z = (Holonics.RatioPresentation.blockTransport m.a m.b m.c m.d ⟨z, 1⟩).num /
      (Holonics.RatioPresentation.blockTransport m.a m.b m.c m.d ⟨z, 1⟩).den := by
  simp [act, Holonics.RatioPresentation.blockTransport]

/-- [proved-derived; formal-checked] Off the pole, a fixed point of the chart is an undivided fixed
point. -/
theorem act_eq_self_iff (z : K) (hz : m.c * z + m.d ≠ 0) : m.act z = z ↔ m.Fixed z := by
  unfold act Fixed
  rw [div_eq_iff hz]

/-- [proved-derived; formal-checked] **The undivided fixed-point law:**
`(a z + b) − z₁(c z + d) = (a − c z₁)(z − z₁)`. -/
theorem sub_fixed {z₁ : K} (h₁ : m.Fixed z₁) (z : K) :
    (m.a * z + m.b) - z₁ * (m.c * z + m.d) = (m.a - m.c * z₁) * (z - z₁) := by
  unfold Fixed at h₁
  linear_combination h₁

/-- [proved-derived; formal-checked] `act z − z₁ = (a − c z₁)(z − z₁)/(c z + d)`. -/
theorem act_sub_fixed {z₁ : K} (h₁ : m.Fixed z₁) (z : K) (hz : m.c * z + m.d ≠ 0) :
    m.act z - z₁ = (m.a - m.c * z₁) * (z - z₁) / (m.c * z + m.d) := by
  rw [act, div_sub' hz]
  congr 1
  linear_combination sub_fixed m h₁ z

/-- [proved-derived; formal-checked] Two distinct fixed points determine the other multiplier:
`a − c z₁ = c z₂ + d`. -/
theorem other_multiplier {z₁ z₂ : K} (h₁ : m.Fixed z₁) (h₂ : m.Fixed z₂) (hne : z₁ ≠ z₂) :
    m.a - m.c * z₁ = m.c * z₂ + m.d := by
  have key := sub_fixed m h₁ z₂
  unfold Fixed at h₂
  have hsub : z₂ - z₁ ≠ 0 := sub_ne_zero.mpr hne.symm
  have : (m.a - m.c * z₁) * (z₂ - z₁) = (m.c * z₂ + m.d) * (z₂ - z₁) := by
    rw [← key, h₂]; ring
  exact mul_right_cancel₀ hsub this

/-- [proved-derived; formal-checked] **At most two fixed points.** With two distinct fixed points,
every fixed point is one of them unless the navigator is the identity. -/
theorem fixed_points_at_most_two {z₁ z₂ : K} (h₁ : m.Fixed z₁) (h₂ : m.Fixed z₂)
    (hne : z₁ ≠ z₂) :
    (∀ z, m.Fixed z → z = z₁ ∨ z = z₂) ∨ (m.b = 0 ∧ m.c = 0 ∧ m.a = m.d) := by
  have hs := other_multiplier m h₁ h₂ hne
  by_cases hc : m.c = 0
  · right
    have had : m.a = m.d := by rw [hc] at hs; simpa using hs
    refine ⟨?_, hc, had⟩
    have := h₁
    unfold Fixed at this
    rw [hc, had] at this
    linear_combination this
  · left
    intro z hz
    have key := sub_fixed m h₁ z
    unfold Fixed at hz
    have h0 : (z - z₁) * (m.c * (z₂ - z)) = 0 := by
      linear_combination (-(z - z₁)) * hs - key + hz
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hc
      · exact Or.inr (sub_eq_zero.mp h).symm

/-- [proved-derived; formal-checked] The multipliers `μ_i = c z_i + d` add to the trace. -/
theorem multipliers_sum {z₁ z₂ : K} (h₁ : m.Fixed z₁) (h₂ : m.Fixed z₂) (hne : z₁ ≠ z₂) :
    (m.c * z₁ + m.d) + (m.c * z₂ + m.d) = m.trace := by
  have hs := other_multiplier m h₁ h₂ hne
  unfold trace
  linear_combination (-1 : K) * hs

/-- [proved-derived; formal-checked] The multipliers multiply to the determinant: they are the
navigator's eigenvalues. -/
theorem multipliers_prod {z₁ z₂ : K} (h₁ : m.Fixed z₁) (h₂ : m.Fixed z₂) (hne : z₁ ≠ z₂) :
    (m.c * z₁ + m.d) * (m.c * z₂ + m.d) = m.det := by
  have hs := other_multiplier m h₁ h₂ hne
  unfold Fixed at h₁
  unfold det
  linear_combination m.c * h₁ - (m.d + m.c * z₁) * hs

/-- [proved-derived; formal-checked] `tr² − 4 det = (μ₁ − μ₂)²`. -/
theorem discriminant_eq_sq {z₁ z₂ : K} (h₁ : m.Fixed z₁) (h₂ : m.Fixed z₂) (hne : z₁ ≠ z₂) :
    m.trace ^ 2 - 4 * m.det = ((m.c * z₁ + m.d) - (m.c * z₂ + m.d)) ^ 2 := by
  rw [← multipliers_sum m h₁ h₂ hne, ← multipliers_prod m h₁ h₂ hne]
  ring

/-- [proved-derived; formal-checked] **In the fixed-point chart the navigator is a scaling:**
`w(act z) = (μ₂/μ₁) w(z)` with `w = (z − z₁)/(z − z₂)`. -/
theorem chart_conjugates {z₁ z₂ : K} (h₁ : m.Fixed z₁) (h₂ : m.Fixed z₂) (hne : z₁ ≠ z₂)
    (z : K) (hz : m.c * z + m.d ≠ 0) (hz₂ : z ≠ z₂) (hμ₁ : m.c * z₁ + m.d ≠ 0) :
    (m.act z - z₁) / (m.act z - z₂)
      = ((m.c * z₂ + m.d) / (m.c * z₁ + m.d)) * ((z - z₁) / (z - z₂)) := by
  have e₁ := act_sub_fixed m h₁ z hz
  have e₂ := act_sub_fixed m h₂ z hz
  rw [other_multiplier m h₁ h₂ hne] at e₁
  rw [other_multiplier m h₂ h₁ hne.symm] at e₂
  have hz₂' : z - z₂ ≠ 0 := sub_ne_zero.mpr hz₂
  rw [e₁, e₂]
  field_simp

end Field

section Ordered

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (m : Mobius K)

/-- [proved-derived; formal-checked] **Two distinct fixed points make the discriminant positive**
(with `c ≠ 0`): it is the positive square `(c(z₁ − z₂))²`. -/
theorem two_fixed_points_disc_pos {z₁ z₂ : K} (h₁ : m.Fixed z₁) (h₂ : m.Fixed z₂)
    (hne : z₁ ≠ z₂) (hc : m.c ≠ 0) : 4 * m.det < m.trace ^ 2 := by
  have hd := discriminant_eq_sq m h₁ h₂ hne
  have hpos : 0 < ((m.c * z₁ + m.d) - (m.c * z₂ + m.d)) ^ 2 := by
    have : (m.c * z₁ + m.d) - (m.c * z₂ + m.d) = m.c * (z₁ - z₂) := by ring
    rw [this]
    exact lt_of_le_of_ne (sq_nonneg _)
      (Ne.symm (pow_ne_zero 2 (mul_ne_zero hc (sub_ne_zero.mpr hne))))
  linarith

/-- [proved-derived; formal-checked] **Two distinct fixed points and a positive determinant make a
boost site.** -/
theorem two_fixed_points_is_boost {z₁ z₂ : K} (h₁ : m.Fixed z₁) (h₂ : m.Fixed z₂)
    (hne : z₁ ≠ z₂) (hc : m.c ≠ 0) (hdet : 0 < m.det) : siteKind m.trace m.det = .boost := by
  rw [siteKind_eq_boost_iff]
  exact ⟨hdet, two_fixed_points_disc_pos m h₁ h₂ hne hc⟩

theorem multipliers_ne {z₁ z₂ : K} (hne : z₁ ≠ z₂) (hc : m.c ≠ 0) :
    m.c * z₁ + m.d ≠ m.c * z₂ + m.d := by
  intro h
  apply hne
  have : m.c * (z₁ - z₂) = 0 := by linear_combination h
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc)

/-- [proved-derived; formal-checked] **One fixed point attracts exactly when `tr ≠ 0`.** With two
distinct fixed points and `c ≠ 0`, the multiplier `μ₂/μ₁` at `z₁` or `μ₁/μ₂` at `z₂` has size
below one exactly when the trace is not zero; the determinant's sign plays no part. -/
theorem attracting_iff_trace_ne_zero {z₁ z₂ : K} (h₁ : m.Fixed z₁) (h₂ : m.Fixed z₂)
    (hne : z₁ ≠ z₂) (hc : m.c ≠ 0) :
    (|(m.c * z₂ + m.d) / (m.c * z₁ + m.d)| < 1 ∨ |(m.c * z₁ + m.d) / (m.c * z₂ + m.d)| < 1) ↔
      m.trace ≠ 0 := by
  have hsum := multipliers_sum m h₁ h₂ hne
  have hμ := multipliers_ne m hne hc
  set μ₁ := m.c * z₁ + m.d
  set μ₂ := m.c * z₂ + m.d
  constructor
  · rintro h htr
    have hneg : μ₂ = -μ₁ := by linear_combination hsum + htr
    have h1 : μ₁ ≠ 0 := by
      intro h0
      apply hμ
      rw [hneg, h0, neg_zero]
    have hq1 : |μ₂ / μ₁| = 1 := by
      rw [hneg, neg_div, div_self h1, abs_neg, abs_one]
    have hq2 : |μ₁ / μ₂| = 1 := by
      rw [hneg, div_neg, div_self h1, abs_neg, abs_one]
    rw [hq1, hq2] at h
    simp at h
  · intro htr
    have habs : |μ₁| ≠ |μ₂| := by
      intro h
      rcases abs_eq_abs.mp h with h | h
      · exact hμ h
      · exact htr (by rw [← hsum, h]; ring)
    rcases lt_or_gt_of_ne habs with h | h
    · right
      have h2 : μ₂ ≠ 0 := by
        intro h0
        rw [h0, abs_zero] at h
        exact absurd h (not_lt.mpr (abs_nonneg _))
      rw [abs_div, div_lt_one (abs_pos.mpr h2)]
      exact h
    · left
      have h1 : μ₁ ≠ 0 := by
        intro h0
        rw [h0, abs_zero] at h
        exact absurd h (not_lt.mpr (abs_nonneg _))
      rw [abs_div, div_lt_one (abs_pos.mpr h1)]
      exact h

/-- [proved-derived; formal-checked] The iterate of a point off the repelling fixed point stays
off it: `act z − z₂ = μ₁ (z − z₂)/(c z + d)`. -/
theorem act_ne_fixed {z₁ z₂ : K} (h₁ : m.Fixed z₁) (h₂ : m.Fixed z₂) (hne : z₁ ≠ z₂)
    (hμ₁ : m.c * z₁ + m.d ≠ 0) {z : K} (hz : z ≠ z₂) (hpole : m.c * z + m.d ≠ 0) :
    m.act z ≠ z₂ := by
  intro h
  have e := act_sub_fixed m h₂ z hpole
  rw [other_multiplier m h₂ h₁ hne.symm, h, sub_self] at e
  have := e.symm
  rw [div_eq_zero_iff] at this
  rcases this with h0 | h0
  · rcases mul_eq_zero.mp h0 with h0 | h0
    · exact hμ₁ h0
    · exact hz (sub_eq_zero.mp h0)
  · exact hpole h0

end Ordered

section Converge

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Archimedean K]
  [TopologicalSpace K] [OrderTopology K] (m : Mobius K)

open Filter Topology

/-- [proved-derived; formal-checked] **Every path converges to the attracting fixed point.** With
distinct fixed points `z₁ ≠ z₂`, `|μ₂| < |μ₁|`, and a start `z ≠ z₂` whose orbit avoids the pole,
the iterates converge to `z₁`. -/
theorem iterate_tendsto_fixed {z₁ z₂ : K} (h₁ : m.Fixed z₁) (h₂ : m.Fixed z₂) (hne : z₁ ≠ z₂)
    (hlt : |m.c * z₂ + m.d| < |m.c * z₁ + m.d|) {z : K} (hz : z ≠ z₂)
    (hpole : ∀ n, m.c * (m.act^[n] z) + m.d ≠ 0) :
    Tendsto (fun n => m.act^[n] z) atTop (𝓝 z₁) := by
  have hμ₁ : m.c * z₁ + m.d ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hlt
    exact absurd hlt (not_lt.mpr (abs_nonneg _))
  have hoff : ∀ n, m.act^[n] z ≠ z₂ := by
    intro n
    induction n with
    | zero => exact hz
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact act_ne_fixed m h₁ h₂ hne hμ₁ ih (hpole n)
  set r := (m.c * z₂ + m.d) / (m.c * z₁ + m.d) with hr
  set w : ℕ → K := fun n => (m.act^[n] z - z₁) / (m.act^[n] z - z₂) with hw
  have hwn : ∀ n, w n = r ^ n * w 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [hw, Function.iterate_succ_apply']
      rw [chart_conjugates m h₁ h₂ hne _ (hpole n) (hoff n) hμ₁, ← hr]
      change r * w n = _
      rw [ih, pow_succ]
      ring
  have hrlt : |r| < 1 := by
    rw [hr, abs_div, div_lt_one (abs_pos.mpr hμ₁)]
    exact hlt
  have hwt : Tendsto w atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_iff.mpr hrlt).mul_const (w 0)
    rw [zero_mul] at this
    exact this.congr fun n => (hwn n).symm
  have hsol : ∀ n, m.act^[n] z = (z₁ - w n * z₂) / (1 - w n) := by
    intro n
    have hd : m.act^[n] z - z₂ ≠ 0 := sub_ne_zero.mpr (hoff n)
    have h1 : 1 - w n ≠ 0 := by
      intro h
      have : w n = 1 := by linear_combination -h
      simp only [hw] at this
      rw [div_eq_one_iff_eq hd] at this
      exact hne (by linear_combination -this)
    rw [eq_div_iff h1]
    simp only [hw]
    field_simp
    ring
  have hlim : Tendsto (fun n => (z₁ - w n * z₂) / (1 - w n)) atTop (𝓝 ((z₁ - 0 * z₂) / (1 - 0))) :=
    (tendsto_const_nhds.sub (hwt.mul_const z₂)).div (tendsto_const_nhds.sub hwt)
      (by simp)
  simp only [zero_mul, sub_zero, div_one] at hlim
  exact hlim.congr fun n => (hsol n).symm

end Converge

end Mobius

/-! ## 2. The Swing: two fixed points that neither attract nor repel -/

/-- [definition] The Swing `z ↦ 1/z`, harmonic conjugation fixing `±1`. -/
def swingNavigator : Mobius ℚ := ⟨0, 1, 1, 0⟩

/-- [counterexample; formal-checked] **`tr = 0` is neutral.** The Swing fixes `1` and `−1`, has
`tr = 0` and `det = −1`, is an involution off its pole, and its multiplier is `−1` at both fixed
points: neither attracts nor repels. -/
theorem swing_neither_attracts :
    swingNavigator.Fixed 1 ∧ swingNavigator.Fixed (-1) ∧ swingNavigator.trace = 0 ∧
      swingNavigator.det = -1 ∧
      (∀ z : ℚ, z ≠ 0 → swingNavigator.act (swingNavigator.act z) = z) ∧
      (swingNavigator.c * (-1) + swingNavigator.d) / (swingNavigator.c * 1 + swingNavigator.d) = -1
      ∧ (swingNavigator.c * 1 + swingNavigator.d) / (swingNavigator.c * (-1) + swingNavigator.d)
        = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [swingNavigator, Mobius.Fixed, Mobius.det, Mobius.act, Mobius.trace]

/-- [definition] The navigator `z ↦ (z + 2)/(2z + 1)`. -/
def reflectingNavigator : Mobius ℚ := ⟨1, 2, 2, 1⟩

/-- [counterexample; formal-checked] **A negative determinant still attracts.**
`z ↦ (z + 2)/(2z + 1)` has `det = −3`, fixed points `±1` with multipliers `−1/3` at `1` and `−3`
at `−1`, and every path from `z ≥ 0` converges to `1`. -/
theorem reflection_attracts :
    reflectingNavigator.det = -3 ∧ reflectingNavigator.Fixed 1 ∧ reflectingNavigator.Fixed (-1) ∧
      (reflectingNavigator.c * (-1) + reflectingNavigator.d) /
          (reflectingNavigator.c * 1 + reflectingNavigator.d) = -1 / 3 ∧
      (reflectingNavigator.c * 1 + reflectingNavigator.d) /
          (reflectingNavigator.c * (-1) + reflectingNavigator.d) = -3 ∧
      ∀ z : ℚ, 0 ≤ z → Tendsto (fun n => reflectingNavigator.act^[n] z) atTop (𝓝 1) := by
  refine ⟨by norm_num [reflectingNavigator, Mobius.det],
    by norm_num [reflectingNavigator, Mobius.Fixed], by norm_num [reflectingNavigator, Mobius.Fixed],
    by norm_num [reflectingNavigator], by norm_num [reflectingNavigator], fun z hz => ?_⟩
  have hnonneg : ∀ n, 0 ≤ reflectingNavigator.act^[n] z := by
    intro n
    induction n with
    | zero => exact hz
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      simp only [reflectingNavigator, Mobius.act]
      positivity
  apply Mobius.iterate_tendsto_fixed reflectingNavigator (z₂ := -1)
    (by norm_num [reflectingNavigator, Mobius.Fixed]) (by norm_num [reflectingNavigator,
      Mobius.Fixed]) (by norm_num) (by norm_num [reflectingNavigator])
    (by linarith)
  intro n
  have := hnonneg n
  change (2 : ℚ) * reflectingNavigator.act^[n] z + 1 ≠ 0
  linarith

/-! ## 3. Velocity addition: `c` is the landmark of the boost family -/

/-- [definition] Velocity addition with characteristic `c = 1`. -/
def vadd (v u : ℚ) : ℚ := (u + v) / (1 + u * v)

/-- [definition] The velocity-addition navigator `[[1, v],[v, 1]]`. -/
def velocityNavigator (v : ℚ) : Mobius ℚ := ⟨1, v, v, 1⟩

/-- [proved-derived; formal-checked] Velocity addition is the Möbius navigator `[[1, v],[v, 1]]`. -/
theorem velocity_act (v u : ℚ) : (velocityNavigator v).act u = vadd v u := by
  simp [velocityNavigator, Mobius.act, vadd]
  ring_nf

/-- [proved-derived; formal-checked] **Velocity addition is a boost site, and its normalized trace
face is the Lorentz factor:** for `0 < |v| < 1`, `tr = 2`, `det = 1 − v²`, the kind is `boost`
and `tr²/(4 det) = 1/(1 − v²) = γ²`. -/
theorem velocity_is_boost (v : ℚ) (hv0 : v ≠ 0) (hv : |v| < 1) :
    (velocityNavigator v).trace = 2 ∧ (velocityNavigator v).det = 1 - v ^ 2 ∧
      siteKind (velocityNavigator v).trace (velocityNavigator v).det = .boost ∧
      (velocityNavigator v).trace ^ 2 / (4 * (velocityNavigator v).det) = 1 / (1 - v ^ 2) := by
  have htr : (velocityNavigator v).trace = 2 := by
    simp [velocityNavigator, Mobius.trace]; norm_num
  have hdet : (velocityNavigator v).det = 1 - v ^ 2 := by
    simp [velocityNavigator, Mobius.det]; ring
  have hv2 : v ^ 2 < 1 := by
    have := abs_lt.mp hv
    nlinarith
  have hv2pos : 0 < v ^ 2 := by positivity
  refine ⟨htr, hdet, ?_, ?_⟩
  · rw [htr, hdet, siteKind_eq_boost_iff]; constructor <;> nlinarith
  · rw [htr, hdet]
    have : (1 : ℚ) - v ^ 2 ≠ 0 := by linarith
    field_simp
    ring

/-- [proved-derived; formal-checked] Velocity addition fixes `1` (for `v ≠ −1`). -/
theorem vadd_fixes_one (v : ℚ) (hv : v ≠ -1) : vadd v 1 = 1 := by
  have h : (1 : ℚ) + v ≠ 0 := by intro h; apply hv; linarith
  unfold vadd
  rw [one_mul, div_self h]

/-- [proved-derived; formal-checked] Velocity addition fixes `−1` (for `v ≠ 1`). -/
theorem vadd_fixes_neg_one (v : ℚ) (hv : v ≠ 1) : vadd v (-1) = -1 := by
  have h : (1 : ℚ) + -1 * v ≠ 0 := by intro h; apply hv; linarith
  unfold vadd
  rw [div_eq_iff h]
  ring

/-- [definition] The Doppler chart `D(u) = (1 + u)/(1 − u)`: the square of the Doppler ratio `k`. -/
def doppler (u : ℚ) : ℚ := (1 + u) / (1 - u)

theorem doppler_pos {u : ℚ} (hu : |u| < 1) : 0 < doppler u := by
  obtain ⟨h1, h2⟩ := abs_lt.mp hu
  exact div_pos (by linarith) (by linarith)

/-- [proved-derived; formal-checked] A velocity is read back from its Doppler chart:
`1 − u = 2/(D(u) + 1)`. -/
theorem one_sub_eq_doppler {u : ℚ} (hu : |u| < 1) : 1 - u = 2 / (doppler u + 1) := by
  obtain ⟨h1, h2⟩ := abs_lt.mp hu
  have h : (1 : ℚ) - u ≠ 0 := by linarith
  unfold doppler
  field_simp
  ring

/-- [proved-derived; formal-checked] **Velocity addition preserves the open cone.** -/
theorem vadd_mem {u v : ℚ} (hu : |u| < 1) (hv : |v| < 1) : |vadd v u| < 1 := by
  obtain ⟨hu1, hu2⟩ := abs_lt.mp hu
  obtain ⟨hv1, hv2⟩ := abs_lt.mp hv
  have hden : 0 < 1 + u * v := by nlinarith
  rw [abs_lt, vadd, lt_div_iff₀ hden, div_lt_iff₀ hden]
  constructor <;> nlinarith

/-- [proved-derived; formal-checked] **Collinear composition multiplies the Doppler chart:**
`D(vadd v u) = D(u) D(v)`. -/
theorem doppler_vadd {u v : ℚ} (hu : |u| < 1) (hv : |v| < 1) :
    doppler (vadd v u) = doppler u * doppler v := by
  obtain ⟨hu1, hu2⟩ := abs_lt.mp hu
  obtain ⟨hv1, hv2⟩ := abs_lt.mp hv
  have hden : 0 < 1 + u * v := by nlinarith
  have h1 : (1 : ℚ) - u ≠ 0 := by linarith
  have h2 : (1 : ℚ) - v ≠ 0 := by linarith
  have h3 : (1 : ℚ) - (u + v) / (1 + u * v) ≠ 0 := by
    have := abs_lt.mp (vadd_mem hu hv)
    unfold vadd at this
    linarith [this.2]
  unfold doppler vadd
  rw [div_mul_div_comm, div_eq_div_iff h3 (mul_ne_zero h1 h2)]
  field_simp
  ring

/-- [proved-derived; formal-checked] The iterates stay in the cone and multiply the Doppler chart
by `D(v)ⁿ`. -/
theorem iterate_doppler {u v : ℚ} (hu : |u| < 1) (hv : |v| < 1) (n : ℕ) :
    |(vadd v)^[n] u| < 1 ∧ doppler ((vadd v)^[n] u) = doppler u * doppler v ^ n := by
  induction n with
  | zero => simpa using hu
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨vadd_mem ih.1 hv, ?_⟩
    rw [doppler_vadd ih.1 hv, ih.2, pow_succ]
    ring

/-- [proved-derived; formal-checked] **The iterates in exact form:**
`1 − (vadd v)ⁿ u = 2/(D(u) D(v)ⁿ + 1)`. -/
theorem one_sub_iterate {u v : ℚ} (hu : |u| < 1) (hv : |v| < 1) (n : ℕ) :
    1 - (vadd v)^[n] u = 2 / (doppler u * doppler v ^ n + 1) := by
  rw [one_sub_eq_doppler (iterate_doppler hu hv n).1, (iterate_doppler hu hv n).2]

/-- [proved-derived; formal-checked] **The iterates of one boost converge to the landmark `1`.**
For `0 < v < 1` and any `|u| < 1`, the iterates of velocity addition by `v` converge to `1`. -/
theorem vadd_iterate_tendsto_one {u v : ℚ} (hu : |u| < 1) (hv0 : 0 < v) (hv1 : v < 1) :
    Tendsto (fun n => (vadd v)^[n] u) atTop (𝓝 1) := by
  have hv : |v| < 1 := abs_lt.mpr ⟨by linarith, hv1⟩
  have hD : 1 < doppler v := by
    unfold doppler
    rw [one_lt_div (by linarith)]
    linarith
  have hDu := doppler_pos hu
  have hgrow : Tendsto (fun n : ℕ => doppler u * doppler v ^ n + 1) atTop atTop := by
    apply tendsto_atTop_add_const_right
    exact (tendsto_pow_atTop_atTop_of_one_lt hD).const_mul_atTop hDu
  have hzero : Tendsto (fun n : ℕ => (2 : ℚ) / (doppler u * doppler v ^ n + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hgrow
  have heq : (fun n => (vadd v)^[n] u) =
      fun n : ℕ => 1 - (2 : ℚ) / (doppler u * doppler v ^ n + 1) := by
    funext n
    rw [← one_sub_iterate hu hv n]
    ring
  rw [heq]
  simpa using (tendsto_const_nhds (x := (1 : ℚ))).sub hzero

/-- [proved-derived; formal-checked] Velocity addition is odd in both arguments. -/
theorem vadd_neg (v u : ℚ) : vadd (-v) (-u) = -vadd v u := by
  unfold vadd
  rw [show -u + -v = -(u + v) by ring, show 1 + -u * -v = 1 + u * v by ring, neg_div]

/-- [proved-derived; formal-checked] **For `−1 < v < 0` the iterates of one boost converge to
`−1`.** -/
theorem vadd_iterate_tendsto_neg_one {u v : ℚ} (hu : |u| < 1) (hv0 : v < 0) (hv1 : -1 < v) :
    Tendsto (fun n => (vadd v)^[n] u) atTop (𝓝 (-1)) := by
  have hiter : ∀ n, (vadd v)^[n] u = -((vadd (-v))^[n] (-u)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      rw [← vadd_neg, neg_neg]
  have h := vadd_iterate_tendsto_one (u := -u) (v := -v) (by rwa [abs_neg]) (by linarith)
    (by linarith)
  have := h.neg
  simp only [← hiter] at this
  exact this

/-- [definition] Velocity addition with characteristic `c`. -/
def vaddC (c v u : ℚ) : ℚ := (u + v) / (1 + u * v / c ^ 2)

/-- [proved-derived; formal-checked] **`±c` are fixed by velocity addition with characteristic
`c`**, and the navigator is velocity addition read in units of `c`. -/
theorem vaddC_fixes (c v : ℚ) (hc : c ≠ 0) (hv₁ : v ≠ c) (hv₂ : v ≠ -c) :
    vaddC c v c = c ∧ vaddC c v (-c) = -c ∧ ∀ u, vaddC c v u = c * vadd (v / c) (u / c) := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  refine ⟨?_, ?_, ?_⟩
  · unfold vaddC
    have : (1 : ℚ) + c * v / c ^ 2 ≠ 0 := by
      intro h
      apply hv₂
      field_simp at h
      linarith
    rw [div_eq_iff this]
    field_simp
  · unfold vaddC
    have : (1 : ℚ) + -c * v / c ^ 2 ≠ 0 := by
      intro h
      apply hv₁
      field_simp at h
      linarith
    rw [div_eq_iff this]
    field_simp
    ring
  · intro u
    unfold vaddC vadd
    field_simp

/-- [proved-derived; formal-checked] The iterates with characteristic `c` are velocity addition in
units of `c`. -/
theorem vaddC_iterate (c v u : ℚ) (hc : c ≠ 0) (hv₁ : v ≠ c) (hv₂ : v ≠ -c) (n : ℕ) :
    (vaddC c v)^[n] u = c * (vadd (v / c))^[n] (u / c) := by
  induction n with
  | zero => simp [mul_div_cancel₀ _ hc]
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      (vaddC_fixes c v hc hv₁ hv₂).2.2, mul_div_cancel_left₀ _ hc]

/-- [proved-derived; formal-checked] **The iterates of one boost converge to `c`** for every
characteristic `c > 0`: `0 < v < c`, `|u| < c`. -/
theorem vaddC_iterate_tendsto_c {c v u : ℚ} (hc : 0 < c) (hv0 : 0 < v) (hv1 : v < c)
    (hu : |u| < c) : Tendsto (fun n => (vaddC c v)^[n] u) atTop (𝓝 c) := by
  have hiter := vaddC_iterate c v u hc.ne' hv1.ne (by linarith)
  have hu' : |u / c| < 1 := by rw [abs_div, abs_of_pos hc, div_lt_one hc]; exact hu
  have h := (vadd_iterate_tendsto_one hu' (div_pos hv0 hc) ((div_lt_one hc).mpr hv1)).const_mul c
  rw [mul_one] at h
  exact h.congr fun n => (hiter n).symm

/-- [proved-derived; formal-checked] **The iterates of one boost converge to `−c`** for
`−c < v < 0`, `|u| < c`. -/
theorem vaddC_iterate_tendsto_neg_c {c v u : ℚ} (hc : 0 < c) (hv0 : v < 0) (hv1 : -c < v)
    (hu : |u| < c) : Tendsto (fun n => (vaddC c v)^[n] u) atTop (𝓝 (-c)) := by
  have hiter := vaddC_iterate c v u hc.ne' (by linarith) hv1.ne'
  have hu' : |u / c| < 1 := by rw [abs_div, abs_of_pos hc, div_lt_one hc]; exact hu
  have hv' : -1 < v / c := by rw [lt_div_iff₀ hc]; linarith
  have h := (vadd_iterate_tendsto_neg_one hu' (div_neg_of_neg_of_pos hv0 hc) hv').const_mul c
  rw [mul_neg_one] at h
  exact h.congr fun n => (hiter n).symm

section Audit
#print axioms Mobius.fixed_points_at_most_two
#print axioms Mobius.multipliers_prod
#print axioms Mobius.chart_conjugates
#print axioms Mobius.two_fixed_points_disc_pos
#print axioms Mobius.two_fixed_points_is_boost
#print axioms Mobius.attracting_iff_trace_ne_zero
#print axioms Mobius.iterate_tendsto_fixed
#print axioms reflection_attracts
#print axioms swing_neither_attracts
#print axioms velocity_is_boost
#print axioms doppler_vadd
#print axioms one_sub_iterate
#print axioms vadd_iterate_tendsto_one
#print axioms vadd_iterate_tendsto_neg_one
#print axioms vaddC_fixes
#print axioms vaddC_iterate_tendsto_c
#print axioms vaddC_iterate_tendsto_neg_c
end Audit

end Holonics.Compression.Landmark.FixedPoint
