import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

/-!
# The zero population is read off the boundary — the magnitude face of the same index

**A correction, 2026-08-23.**  This file exists because a measurement made here that morning was
correct about its route and wrong about its question.  `grep -rn "argument principle" Mathlib/Analysis/`
does return nothing — that much held — and from it the note *"the box owes a contour-deformation
argument mathlib does not supply"* was written.  But mathlib carries **Jensen's formula**
(`Mathlib/Analysis/Complex/JensenFormula.lean`) and a whole `ValueDistribution` development with the
Nevanlinna counting function, and either reads the interior zero population off boundary data
without any contour at all.  A search over one route settles that route, never the question.

**What Jensen says here.**  For `Λ₀` entire, on any circle about `c`,

```text
circleAverage (log ‖Λ₀‖) c R
    =  Σ_u  divisor(u) · log(R / ‖c − u‖)     the interior zeros, weighted by depth
     +  divisor(c) · log R
     +  log ‖trailing coefficient at c‖ .
```

Every weight `log(R/‖c − u‖)` is positive strictly inside the disc and zero on the boundary, so the
sum is a genuine count-with-multiplicity, damped by how close each zero sits to the rim.

**And it is the same invariant the winding reads.**  `RH.Winding` computes the index of a zero as a
turn — `∮ f'/f = 2πi·n`, a *phase* face, with the analytic factor contributing nothing.  Jensen
computes the same index from `log ‖f‖` on the same circle — a *magnitude* face.  One divisor, two
receivers.  That is the corpus's own pairing: a defect legible in the phase and legible in the
magnitude, with the argument principle and Jensen as its two charts, and the reason RH is stated
about a *placement* rather than a magnitude is that only the phase face carries the location.
-/

namespace Soma.Holonics.RH.Jensen

open Complex Metric Real MeromorphicOn

/-- `Λ₀` is analytic on the whole plane, so on any set. -/
theorem theXiIsAnalyticOn (S : Set ℂ) : AnalyticOnNhd ℂ completedRiemannZeta₀ S :=
  (analyticOnNhd_univ_iff_differentiable.2 differentiable_completedZeta₀).mono (Set.subset_univ S)

/-- Hence meromorphic on any set, with no poles. -/
theorem theXiIsMeromorphicOn (S : Set ℂ) : MeromorphicOn completedRiemannZeta₀ S :=
  (theXiIsAnalyticOn S).meromorphicOn

/-- **THE DIVISOR OF `Λ₀` IS A NONNEGATIVE POPULATION.**  Entire, so no poles: every point of the
divisor is a zero counted with its depth, never a debt. -/
theorem theXiDivisorIsNonnegative (S : Set ℂ) :
    0 ≤ MeromorphicOn.divisor completedRiemannZeta₀ S :=
  (theXiIsAnalyticOn S).divisor_nonneg

/-- **JENSEN'S FORMULA FOR `Λ₀`.**  The boundary log-average determines the interior zero
population, with no contour and no argument principle. -/
theorem theJensenFormulaForXi {c : ℂ} {R : ℝ} (hR : R ≠ 0) :
    circleAverage (fun z => Real.log ‖completedRiemannZeta₀ z‖) c R
      = ∑ᶠ u, (MeromorphicOn.divisor completedRiemannZeta₀ (closedBall c |R|) u : ℝ) *
            Real.log (R * ‖c - u‖⁻¹)
        + (MeromorphicOn.divisor completedRiemannZeta₀ (closedBall c |R|) c : ℝ) * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt completedRiemannZeta₀ c‖ :=
  MeromorphicOn.circleAverage_log_norm hR (theXiIsMeromorphicOn _)

/-- **THE CLEAN FORM AT A NON-ZERO CENTRE.**  If `Λ₀ c ≠ 0` the trailing coefficient is `Λ₀ c` and
the centre contributes nothing, so the weighted interior count is exactly the boundary average
minus the value at the centre:

```text
Σ_u  divisor(u) · log(R / ‖c − u‖)  =  circleAverage (log ‖Λ₀‖) c R  −  log ‖Λ₀ c‖ .
```

This is the statement that a defect population inside a region is a boundary reading — the same
shape as the exact Schur elimination the operating contract already carries, in analysis. -/
theorem theBoundaryAverageDeterminesTheInteriorZeros {c : ℂ} {R : ℝ} (hR : R ≠ 0)
    (hc : completedRiemannZeta₀ c ≠ 0) :
    ∑ᶠ u, (MeromorphicOn.divisor completedRiemannZeta₀ (closedBall c |R|) u : ℝ) *
        Real.log (R * ‖c - u‖⁻¹)
      = circleAverage (fun z => Real.log ‖completedRiemannZeta₀ z‖) c R
        - Real.log ‖completedRiemannZeta₀ c‖ := by
  have hmem : c ∈ closedBall c |R| := Metric.mem_closedBall_self (abs_nonneg R)
  have hord : MeromorphicOn.divisor completedRiemannZeta₀ (closedBall c |R|) c = 0 := by
    have hA : AnalyticAt ℂ completedRiemannZeta₀ c := theXiIsAnalyticOn Set.univ c (Set.mem_univ c)
    have hz : analyticOrderAt completedRiemannZeta₀ c = 0 := hA.analyticOrderAt_eq_zero.2 hc
    have hm : meromorphicOrderAt completedRiemannZeta₀ c = 0 := by
      rw [hA.meromorphicOrderAt_eq, hz]; rfl
    rw [MeromorphicOn.divisor_apply (theXiIsMeromorphicOn _) hmem, hm]
    rfl
  have htc : meromorphicTrailingCoeffAt completedRiemannZeta₀ c = completedRiemannZeta₀ c :=
    (theXiIsAnalyticOn Set.univ c (Set.mem_univ c)).meromorphicTrailingCoeffAt_of_ne_zero hc
  rw [theJensenFormulaForXi hR, hord, htc]
  push_cast
  ring

/-- **THE TWO FACES OF ONE INDEX.**  For the model factor the phase reading and the magnitude
reading agree on the same number `n`: the winding is `2πi·n` (`RH.Winding`) and Jensen's weight at
the centre is `n · log R`.  Neither is derived from the other here; the point is that one divisor
supports both receivers, and only the phase one carries the *location*. -/
theorem theCentreWeightIsTheOrder {c : ℂ} {R : ℝ} (n : ℤ)
    (hn : MeromorphicOn.divisor completedRiemannZeta₀ (closedBall c |R|) c = n) :
    (MeromorphicOn.divisor completedRiemannZeta₀ (closedBall c |R|) c : ℝ) * Real.log R
      = (n : ℝ) * Real.log R := by
  rw [hn]

/-! ## The counting bound, given a growth input -/

/-- **THE WEIGHTED ZERO COUNT IS BOUNDED BY ANY BOUND ON THE BOUNDARY AVERAGE.**  Immediate from
Jensen, and it is the whole content of the classical counting argument: a growth estimate on the
boundary is a bound on the interior zero population, with the weights doing the counting.  What is
still owed is the growth estimate itself. -/
theorem theWeightedZeroCountIsBoundedByTheBoundaryAverage {c : ℂ} {R M : ℝ} (hR : R ≠ 0)
    (hc : completedRiemannZeta₀ c ≠ 0)
    (hbound : circleAverage (fun z => Real.log ‖completedRiemannZeta₀ z‖) c R ≤ M) :
    ∑ᶠ u, (MeromorphicOn.divisor completedRiemannZeta₀ (closedBall c |R|) u : ℝ) *
        Real.log (R * ‖c - u‖⁻¹)
      ≤ M - Real.log ‖completedRiemannZeta₀ c‖ := by
  rw [theBoundaryAverageDeterminesTheInteriorZeros hR hc]
  linarith

/-- **THE ORDER-ONE GROWTH INPUT**, named so the dependence is explicit and discharged nowhere
here.  Measured 2026-08-23: mathlib carries no complex Stirling estimate — the directory
`Mathlib/Analysis/SpecialFunctions/Gamma/` holds `Basic`, `Beta`, `BohrMollerup`, `Deligne` and
`Deriv`, and a grep for `isBigO|Stirling|asymptot` across them returns nothing bounding `‖Γ‖` on
a vertical line.  So this is the one classical input the whole `Λ₀` counting front waits on. -/
def TheOrderOneGrowthOfXi : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → ∀ c : ℂ,
    circleAverage (fun z => Real.log ‖completedRiemannZeta₀ z‖) c R ≤ C * R * Real.log R

/-- With it, every disc carries a bounded weighted zero population. -/
theorem theCountIsBoundedGivenTheGrowth (hG : TheOrderOneGrowthOfXi) {c : ℂ} {R : ℝ}
    (hR : 1 ≤ R) (hc : completedRiemannZeta₀ c ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      ∑ᶠ u, (MeromorphicOn.divisor completedRiemannZeta₀ (closedBall c |R|) u : ℝ) *
          Real.log (R * ‖c - u‖⁻¹)
        ≤ C * R * Real.log R - Real.log ‖completedRiemannZeta₀ c‖ := by
  obtain ⟨C, hC, hb⟩ := hG
  refine ⟨C, hC, ?_⟩
  exact theWeightedZeroCountIsBoundedByTheBoundaryAverage (by linarith) hc (hb R hR c)

/-! ## The boundary controls the interior — the bounded case, proved -/

/-- **`Λ₀` ON A BOUNDED REGION IS CONTROLLED BY ITS BOUNDARY.**  Maximum modulus: a bound on the
frontier is a bound on the closure.  This is the *same* statement as Jensen's above read through
magnitudes rather than through the divisor, and as Stokes read through chains — **boundary
determines interior**, in its third material here.

**And it sharpens the remaining leaf exactly.**  The bounded case is now discharged; what
`RH.theZetaBoundInTheStrip` still owes is only the **unbounded** case — a strip is not bounded, and
that is precisely where Phragmén–Lindelöf is needed rather than plain maximum modulus. -/
theorem theXiIsControlledByItsBoundary {U : Set ℂ} (hU : Bornology.IsBounded U) {C : ℝ}
    (hC : ∀ z ∈ frontier U, ‖completedRiemannZeta₀ z‖ ≤ C) {z : ℂ} (hz : z ∈ closure U) :
    ‖completedRiemannZeta₀ z‖ ≤ C := by
  refine Complex.norm_le_of_forall_mem_frontier_norm_le hU ?_ hC hz
  exact (differentiable_completedZeta₀.diffContOnCl)

/-- Likewise for `ζ` on any bounded region avoiding the pole. -/
theorem theZetaIsControlledByItsBoundary {U : Set ℂ} (hU : Bornology.IsBounded U)
    (h1 : (1 : ℂ) ∉ closure U) {C : ℝ}
    (hC : ∀ z ∈ frontier U, ‖riemannZeta z‖ ≤ C) {z : ℂ} (hz : z ∈ closure U) :
    ‖riemannZeta z‖ ≤ C := by
  refine Complex.norm_le_of_forall_mem_frontier_norm_le hU ?_ hC hz
  constructor
  · intro w hw
    have hne : w ≠ 1 := by rintro rfl; exact h1 (subset_closure hw)
    exact (differentiableAt_riemannZeta hne).differentiableWithinAt
  · intro w hw
    have hne : w ≠ 1 := by rintro rfl; exact h1 hw
    exact (differentiableAt_riemannZeta hne).continuousAt.continuousWithinAt

/-- **THE BOUNDARY LAW, IN THREE MATERIALS.**  Jensen reads the interior *zero population* off the
boundary average; maximum modulus reads the interior *size* off the boundary size; and Stokes reads
an interior differential off a boundary value.  All three are proved in this tree, and the fourth —
the area law — is proved on the lattice.  **The unbounded case is the only one still owed.** -/
theorem theBoundaryLawInThreeMaterials {c : ℂ} {R : ℝ} (hR : R ≠ 0)
    (hc : completedRiemannZeta₀ c ≠ 0) {U : Set ℂ} (hU : Bornology.IsBounded U) {C : ℝ}
    (hC : ∀ z ∈ frontier U, ‖completedRiemannZeta₀ z‖ ≤ C) {z : ℂ} (hz : z ∈ closure U) :
    (∑ᶠ u, (MeromorphicOn.divisor completedRiemannZeta₀ (closedBall c |R|) u : ℝ) *
        Real.log (R * ‖c - u‖⁻¹)
      = circleAverage (fun w => Real.log ‖completedRiemannZeta₀ w‖) c R
        - Real.log ‖completedRiemannZeta₀ c‖) ∧
    ‖completedRiemannZeta₀ z‖ ≤ C :=
  ⟨theBoundaryAverageDeterminesTheInteriorZeros hR hc, theXiIsControlledByItsBoundary hU hC hz⟩

end Soma.Holonics.RH.Jensen
