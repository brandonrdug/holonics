import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# The scalar two-region positivity squeeze

This owner isolates the real-arithmetic sign mechanism used after a geometric argument has
supplied two complementary lower bounds.  For positive `κ`, positive `ε`, nonnegative `C`, and a
positive scale `s`, it treats

* a near-region lower bound `U ≥ (κ / 2) s³ - C s⁴`; and
* an away-region lower bound `U ≥ κ ε s² - C s³`.

[proved-derived] The explicit division-safe threshold `smallScaleThreshold` makes both displayed
lower bounds strictly positive.  The pointwise theorem only needs a predicate-level near/away
cover, and the finite theorem then makes every reading in a finite population positive and gives
a positive sum when that population is nonempty.

[established-bounded] A source note around the Brendle--Hung argument writes the relevant
smallness orientation as `√(C / δ)`, while the displayed lower-bound algebra with a squared scale
requires the reciprocal orientation `√(δ / C)`.  The results below do not inherit that ambiguous
notation: they use a conservative explicit threshold proved directly from the two inequalities.
The harmless `C + 1` denominator also covers `C = 0` without a separate division branch.

[proved-derived] The final theorem checks only the exact scalar inequality for the cited
second-order coefficient.  Nothing in this file formalizes or endorses the surrounding curvature
identity.  In particular, this owner supplies no curvature tensor, Cheeger deformation, compactness
argument, sectional-curvature statement, or geometric conclusion about `S² × S²`.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.TwoRegionPositivity

/-- A conservative positive scale on which both region estimates have positive leading margin.

The factors `4` and `2` retain, respectively, one quarter of `κ` in the near region and one half
of `κ ε` in the away region after absorbing the remainder. -/
def smallScaleThreshold (κ C ε : ℝ) : ℝ :=
  min (κ / (4 * (C + 1))) (κ * ε / (2 * (C + 1)))

/-- The explicit two-region threshold is positive under the sign hypotheses. -/
theorem smallScaleThreshold_pos {κ C ε : ℝ}
    (hκ : 0 < κ) (hC : 0 ≤ C) (hε : 0 < ε) :
    0 < smallScaleThreshold κ C ε := by
  unfold smallScaleThreshold
  apply lt_min
  · exact div_pos hκ (by positivity)
  · exact div_pos (mul_pos hκ hε) (by positivity)

/-- The near-region cubic leading term dominates its quartic remainder below the explicit
threshold. -/
theorem nearRegion_positive {κ C ε s U : ℝ}
    (hκ : 0 < κ) (hC : 0 ≤ C)
    (hs0 : 0 < s) (hs : s < smallScaleThreshold κ C ε)
    (hU : κ / 2 * s ^ 3 - C * s ^ 4 ≤ U) :
    0 < U := by
  have hsNear : s < κ / (4 * (C + 1)) :=
    lt_of_lt_of_le hs (min_le_left _ _)
  have hden : 0 < 4 * (C + 1) := by positivity
  have hscaled : 4 * (C + 1) * s < κ :=
    by simpa [mul_comm] using (lt_div_iff₀ hden).mp hsNear
  have hCs : C * s < κ / 4 := by
    have hle : C * s ≤ (C + 1) * s := by nlinarith
    nlinarith
  have hcoefficient : 0 < κ / 2 - C * s := by nlinarith
  have hlower : 0 < κ / 2 * s ^ 3 - C * s ^ 4 := by
    rw [show κ / 2 * s ^ 3 - C * s ^ 4 =
      s ^ 3 * (κ / 2 - C * s) by ring]
    exact mul_pos (pow_pos hs0 3) hcoefficient
  exact lt_of_lt_of_le hlower hU

/-- The away-region quadratic leading term dominates its cubic remainder below the explicit
threshold. -/
theorem awayRegion_positive {κ C ε s U : ℝ}
    (hκ : 0 < κ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hs0 : 0 < s) (hs : s < smallScaleThreshold κ C ε)
    (hU : κ * ε * s ^ 2 - C * s ^ 3 ≤ U) :
    0 < U := by
  have hsAway : s < κ * ε / (2 * (C + 1)) :=
    lt_of_lt_of_le hs (min_le_right _ _)
  have hden : 0 < 2 * (C + 1) := by positivity
  have hscaled : 2 * (C + 1) * s < κ * ε :=
    by simpa [mul_comm] using (lt_div_iff₀ hden).mp hsAway
  have hCs : C * s < κ * ε / 2 := by
    have hle : C * s ≤ (C + 1) * s := by nlinarith
    nlinarith
  have hcoefficient : 0 < κ * ε - C * s := by nlinarith
  have hlower : 0 < κ * ε * s ^ 2 - C * s ^ 3 := by
    rw [show κ * ε * s ^ 2 - C * s ^ 3 =
      s ^ 2 * (κ * ε - C * s) by ring]
    exact mul_pos (pow_pos hs0 2) hcoefficient
  exact lt_of_lt_of_le hlower hU

/-- Both scalar readings are positive when their respective lower bounds hold at one common
small scale. -/
theorem twoRegion_scalar_positive {κ C ε s U_near U_away : ℝ}
    (hκ : 0 < κ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hs0 : 0 < s) (hs : s < smallScaleThreshold κ C ε)
    (hnear : κ / 2 * s ^ 3 - C * s ^ 4 ≤ U_near)
    (haway : κ * ε * s ^ 2 - C * s ^ 3 ≤ U_away) :
    0 < U_near ∧ 0 < U_away :=
  ⟨nearRegion_positive hκ hC hs0 hs hnear,
    awayRegion_positive hκ hC hε hs0 hs haway⟩

/-- Predicate-level two-region squeeze: a near/away cover and the corresponding local estimate
make every receiver reading strictly positive.  No topology or geometry is hidden in the cover. -/
theorem twoRegion_pointwise_positive {ι : Type*}
    (Near Away : ι → Prop) (U : ι → ℝ) {κ C ε s : ℝ}
    (hκ : 0 < κ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hs0 : 0 < s) (hs : s < smallScaleThreshold κ C ε)
    (hcover : ∀ x, Near x ∨ Away x)
    (hnear : ∀ x, Near x → κ / 2 * s ^ 3 - C * s ^ 4 ≤ U x)
    (haway : ∀ x, Away x → κ * ε * s ^ 2 - C * s ^ 3 ≤ U x) :
    ∀ x, 0 < U x := by
  intro x
  rcases hcover x with hx | hx
  · exact nearRegion_positive hκ hC hs0 hs (hnear x hx)
  · exact awayRegion_positive hκ hC hε hs0 hs (haway x hx)

/-- Every member of a finite two-region population has a strictly positive reading. -/
theorem twoRegion_finite_positive {ι : Type*}
    (S : Finset ι) (Near Away : ι → Prop) (U : ι → ℝ) {κ C ε s : ℝ}
    (hκ : 0 < κ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hs0 : 0 < s) (hs : s < smallScaleThreshold κ C ε)
    (hcover : ∀ x ∈ S, Near x ∨ Away x)
    (hnear : ∀ x ∈ S, Near x → κ / 2 * s ^ 3 - C * s ^ 4 ≤ U x)
    (haway : ∀ x ∈ S, Away x → κ * ε * s ^ 2 - C * s ^ 3 ≤ U x) :
    ∀ x ∈ S, 0 < U x := by
  intro x hxS
  rcases hcover x hxS with hx | hx
  · exact nearRegion_positive hκ hC hs0 hs (hnear x hxS hx)
  · exact awayRegion_positive hκ hC hε hs0 hs (haway x hxS hx)

/-- A nonempty finite two-region population has strictly positive total reading. -/
theorem twoRegion_finite_sum_positive {ι : Type*}
    (S : Finset ι) (Near Away : ι → Prop) (U : ι → ℝ) {κ C ε s : ℝ}
    (hS : S.Nonempty)
    (hκ : 0 < κ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hs0 : 0 < s) (hs : s < smallScaleThreshold κ C ε)
    (hcover : ∀ x ∈ S, Near x ∨ Away x)
    (hnear : ∀ x ∈ S, Near x → κ / 2 * s ^ 3 - C * s ^ 4 ≤ U x)
    (haway : ∀ x ∈ S, Away x → κ * ε * s ^ 2 - C * s ^ 3 ≤ U x) :
    0 < ∑ x ∈ S, U x := by
  exact Finset.sum_pos
    (twoRegion_finite_positive S Near Away U hκ hC hε hs0 hs hcover hnear haway) hS

/-- The isolated exact scalar check for the Brendle--Hung second-order coefficient.

This theorem proves only the displayed real inequality.  It has no curvature identity among its
hypotheses or conclusions. -/
theorem brendleHung_secondOrderCoefficient_positive :
    -(3472117 : ℝ) / 384 + (42025 : ℝ) / 6 * Real.sqrt ((5 : ℝ) / 3) > 0 := by
  let q : ℝ := (3472117 : ℝ) * 6 / (384 * 42025)
  have hq_nonnegative : 0 ≤ q := by
    dsimp [q]
    positivity
  have hsqrt_nonnegative : 0 ≤ Real.sqrt ((5 : ℝ) / 3) :=
    Real.sqrt_nonneg _
  have hsqrt_square : Real.sqrt ((5 : ℝ) / 3) ^ 2 = (5 : ℝ) / 3 :=
    Real.sq_sqrt (by norm_num)
  have hq_square : q ^ 2 < (5 : ℝ) / 3 := by
    dsimp [q]
    norm_num
  have hq_lt_sqrt : q < Real.sqrt ((5 : ℝ) / 3) := by
    nlinarith
  rw [show
    -(3472117 : ℝ) / 384 + (42025 : ℝ) / 6 * Real.sqrt ((5 : ℝ) / 3) =
      ((42025 : ℝ) / 6) * (Real.sqrt ((5 : ℝ) / 3) - q) by
        dsimp [q]
        ring]
  exact mul_pos (by norm_num) (sub_pos.mpr hq_lt_sqrt)

section Audit

#print axioms smallScaleThreshold_pos
#print axioms nearRegion_positive
#print axioms awayRegion_positive
#print axioms twoRegion_scalar_positive
#print axioms twoRegion_pointwise_positive
#print axioms twoRegion_finite_positive
#print axioms twoRegion_finite_sum_positive
#print axioms brendleHung_secondOrderCoefficient_positive

end Audit

end Soma.Holonics.Millennium.TwoRegionPositivity
