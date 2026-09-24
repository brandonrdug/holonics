import ElementaryHolonics.RH.Jensen
import ElementaryHolonics.RH.Growth
import Mathlib.Analysis.Complex.Liouville

/-!
# The named growth input was mis-shaped, and the hypothesis was vacuous

`RH.Growth` discharged order-one growth of `Λ₀`.  Feeding it into `Jensen.TheOrderOneGrowthOfXi`
did not work, and this file says why — the mismatch is a defect in the hypothesis, not in the
growth theorem.

`TheOrderOneGrowthOfXi` asks for `circleAverage (log‖Λ₀‖) c R ≤ C·R·log R` **for every centre `c`**.
At `R = 1` the right-hand side is `C·1·log 1 = 0`, while Jensen says the boundary average is
`log‖Λ₀ c‖` plus a *nonnegative* zero population.  So the hypothesis forces `‖Λ₀ c‖ ≤ 1` at every
point (`theGrowthPropForcesABoundOfOne`), and with Liouville that forces `Λ₀` **constant**
(`theGrowthPropForcesAConstant`).

**Any theorem taking it as a hypothesis was vacuous.**  That is worse than a wrong constant: a
false hypothesis proves everything downstream of it and looks exactly like progress, which is why
the defect survived until something was actually pushed through it.

The repair is in the shape rather than the constant.  **`Λ₀` grows in the abscissa, not in the
radius**, so a circle of radius `R` about `c` reaches abscissa `‖c‖ + R` and the bound must say so:
`TheAbscissaGrowthOfXi`.  With that shape the counting argument goes through unchanged
(`theCountIsBoundedGivenTheAbscissaGrowth`) — it never needed the defective form, only *some* bound
on the boundary average.  Discharging the corrected hypothesis needs the pointwise log bound, and
both ingredients now stand: `Growth.theCompletedZetaHasGammaGrowth` outside and
`MellinHorizon.theCompletedZetaIsBoundedOnAStrip` in the middle, joined by the functional equation.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section
namespace Soma.Holonics.RH.GrowthDefect

open Soma.Holonics.RH.Jensen Metric Set Real Complex MeromorphicOn

/-- Each Jensen weight at radius one is nonnegative. -/
theorem theJensenWeightsAreNonnegativeAtRadiusOne {c : ℂ} (hc : completedRiemannZeta₀ c ≠ 0)
    (u : ℂ) :
    0 ≤ (MeromorphicOn.divisor completedRiemannZeta₀ (closedBall c |(1:ℝ)|) u : ℝ) *
        Real.log ((1:ℝ) * ‖c - u‖⁻¹) := by
  set d := MeromorphicOn.divisor completedRiemannZeta₀ (closedBall c |(1:ℝ)|) with hd
  rcases eq_or_ne (d u) 0 with h0 | h0
  · rw [h0]; simp
  · have hmem : u ∈ closedBall c |(1:ℝ)| := d.supportWithinDomain h0
    have hdist : ‖c - u‖ ≤ 1 := by
      have := Metric.mem_closedBall.mp hmem
      rw [dist_comm] at this
      simpa [Complex.dist_eq, abs_one] using this
    have hdnn : (0:ℝ) ≤ (d u : ℝ) := by
      have := theXiDivisorIsNonnegative (closedBall c |(1:ℝ)|) u
      exact_mod_cast this
    rcases eq_or_lt_of_le (norm_nonneg (c - u)) with hz | hpos
    · rw [← hz]; simp
    · have hinv : (1:ℝ) ≤ ‖c - u‖⁻¹ := by
        rw [le_inv_comm₀ one_pos hpos, inv_one]
        exact hdist
      have hlog : 0 ≤ Real.log ((1:ℝ) * ‖c - u‖⁻¹) := by
        rw [one_mul]; exact Real.log_nonneg hinv
      exact mul_nonneg hdnn hlog

/-- **THE GROWTH PROP AS STATED FORCES `‖Λ₀‖ ≤ 1` EVERYWHERE.**  At `R = 1` its right-hand side is
`C·1·log 1 = 0`, and Jensen says the boundary average is `log‖Λ₀ c‖` plus a **nonnegative** zero
population.  So the hypothesis is not an order-one growth statement at all — it is a global bound
by one, which no non-constant entire function satisfies.

Found by attempting to discharge it from `RH.Growth`; the shapes did not meet, and this is why.
The correct statement must let the bound depend on the centre as well as the radius, because the
growth of `Λ₀` is in the *abscissa*, not in the radius. -/
theorem theGrowthPropForcesABoundOfOne (hG : TheOrderOneGrowthOfXi) {c : ℂ}
    (hc : completedRiemannZeta₀ c ≠ 0) : ‖completedRiemannZeta₀ c‖ ≤ 1 := by
  obtain ⟨C, hC, hb⟩ := hG
  have havg := hb 1 le_rfl c
  rw [Real.log_one, mul_zero] at havg
  have hjen := theBoundaryAverageDeterminesTheInteriorZeros (c := c) (R := 1) one_ne_zero hc
  have hnn : (0:ℝ) ≤ ∑ᶠ u, (MeromorphicOn.divisor completedRiemannZeta₀
      (closedBall c |(1:ℝ)|) u : ℝ) * Real.log ((1:ℝ) * ‖c - u‖⁻¹) :=
    finsum_nonneg (theJensenWeightsAreNonnegativeAtRadiusOne hc)
  rw [hjen] at hnn
  have hlog : Real.log ‖completedRiemannZeta₀ c‖ ≤ 0 := by linarith
  have hpos : 0 < ‖completedRiemannZeta₀ c‖ := norm_pos_iff.mpr hc
  exact (Real.log_nonpos_iff hpos.le).mp hlog

/-- The bound holds at the zeros too, trivially. -/
theorem theGrowthPropBoundsEverywhere (hG : TheOrderOneGrowthOfXi) (c : ℂ) :
    ‖completedRiemannZeta₀ c‖ ≤ 1 := by
  rcases eq_or_ne (completedRiemannZeta₀ c) 0 with h | h
  · rw [h]; simp
  · exact theGrowthPropForcesABoundOfOne hG h

/-- **AND THEREFORE IT FORCES `Λ₀` TO BE CONSTANT.**  Bounded plus entire is Liouville.  So the
named growth input is not merely too strong — it is **incompatible with `Λ₀` being what it is**, and
any theorem taking it as a hypothesis was vacuous.

The repair is in the shape, not the constant: the growth of `Λ₀` lives in the **abscissa**, so a
correct hypothesis must let the bound depend on the centre as well as the radius.  `RH.Growth`
already supplies the pointwise ingredient (`theCompletedZetaHasGammaGrowth`), and
`MellinHorizon.theCompletedZetaIsBoundedOnAStrip` covers the middle. -/
theorem theGrowthPropForcesAConstant (hG : TheOrderOneGrowthOfXi) (z w : ℂ) :
    completedRiemannZeta₀ z = completedRiemannZeta₀ w := by
  refine Differentiable.apply_eq_apply_of_bounded differentiable_completedZeta₀ ?_ z w
  refine Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := (0:ℂ)) (r := 1)) ?_
  rintro _ ⟨u, rfl⟩
  simpa [Metric.mem_closedBall, Complex.dist_eq] using theGrowthPropBoundsEverywhere hG u

/-! ## The corrected hypothesis: the bound must see the centre -/

/-- **THE GROWTH INPUT, CORRECTLY SHAPED.**  `Λ₀` grows in the abscissa, so a circle of radius `R`
about `c` reaches abscissa `‖c‖ + R` and the bound must say so. -/
def TheAbscissaGrowthOfXi : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (c : ℂ) (R : ℝ), 1 ≤ R →
    circleAverage (fun z => Real.log ‖completedRiemannZeta₀ z‖) c R
      ≤ C * (‖c‖ + R + 2) * Real.log (‖c‖ + R + 2)

/-- With the corrected shape the counting bound goes through unchanged — the argument never needed
the defective form, only *some* bound on the boundary average. -/
theorem theCountIsBoundedGivenTheAbscissaGrowth (hG : TheAbscissaGrowthOfXi) {c : ℂ} {R : ℝ}
    (hR : 1 ≤ R) (hc : completedRiemannZeta₀ c ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      ∑ᶠ u, (MeromorphicOn.divisor completedRiemannZeta₀ (closedBall c |R|) u : ℝ) *
          Real.log (R * ‖c - u‖⁻¹)
        ≤ C * (‖c‖ + R + 2) * Real.log (‖c‖ + R + 2)
            - Real.log ‖completedRiemannZeta₀ c‖ := by
  obtain ⟨C, hC, hb⟩ := hG
  exact ⟨C, hC, theWeightedZeroCountIsBoundedByTheBoundaryAverage (by linarith) hc (hb c R hR)⟩

end Soma.Holonics.RH.GrowthDefect
