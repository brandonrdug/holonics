import ElementaryHolonics.Millennium.NavierStokesDirectionBalancedScale
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionKernelScaleLimit

/-!
# The balanced direction current factors the spatial scale receiver

**[proved-derived; formal-checked]**  The canonical distance-modulus construction already inhabits
the strict-interior spatial cross-coherence receiver.  This file supplies a distinct quantitative
factorization of the same receiver through the canonical balanced direction current, whose
summability was proved independently.

The positive-moment branch is the exact threshold balance.  The zero-moment faces are not erased:
the same threshold estimate is tested against arbitrarily small or large positive thresholds, so
their cross-coherence mass is forced to zero.  The result is spatial and pointwise in time; it does
not assert terminal-time integrability.
-/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesDirectionBalancedScaleClosure

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate
open Soma.Holonics.Millennium.NavierStokesDirectionBalancedScale
open Soma.Holonics.Millennium.NavierStokesDirectionThresholdBalance
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityCanonicalModulus
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelScaleLimit
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

private theorem openPeriodicDyadicSpatialCrossCoherenceMass_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (scale : ℕ) :
    0 ≤ openPeriodicDyadicSpatialCrossCoherenceMass solution t q scale := by
  unfold openPeriodicDyadicSpatialCrossCoherenceMass
  exact integral_nonneg fun y ↦
    mul_nonneg (dyadicHodgeJacobianKernelPointMass_nonneg scale y)
      (complexVectorL1_nonneg _)

private theorem nonnegative_eq_zero_of_le_small_threshold
    {x b : ℝ} (hx : 0 ≤ x) (hb : 0 ≤ b)
    (hthreshold : ∀ m : ℝ, 0 < m → x ≤ 9 * (m * b)) :
    x = 0 := by
  apply le_antisymm ?_ hx
  refine le_of_forall_pos_le_add fun epsilon hepsilon ↦ ?_
  let m : ℝ := epsilon / (9 * (b + 1))
  have hdenom : 0 < 9 * (b + 1) := by positivity
  have hm : 0 < m := div_pos hepsilon hdenom
  have hcost : 9 * (m * b) ≤ epsilon := by
    dsimp [m]
    rw [show 9 * (epsilon / (9 * (b + 1)) * b) =
        epsilon * (b / (b + 1)) by field_simp]
    have hratio : b / (b + 1) ≤ 1 := by
      exact (div_le_one (by positivity : 0 < b + 1)).2 (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hratio hepsilon.le]
  have hxeps := (hthreshold m hm).trans hcost
  simpa using hxeps

private theorem nonnegative_eq_zero_of_le_large_threshold
    {x a : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a)
    (hthreshold : ∀ m : ℝ, 0 < m → x ≤ 9 * (a * m⁻¹)) :
    x = 0 := by
  apply le_antisymm ?_ hx
  refine le_of_forall_pos_le_add fun epsilon hepsilon ↦ ?_
  let m : ℝ := 9 * (a + 1) / epsilon
  have hm : 0 < m := div_pos (by positivity) hepsilon
  have hcost : 9 * (a * m⁻¹) ≤ epsilon := by
    dsimp [m]
    rw [show 9 * (a * (9 * (a + 1) / epsilon)⁻¹) =
        epsilon * (a / (a + 1)) by field_simp]
    have hratio : a / (a + 1) ≤ 1 := by
      exact (div_le_one (by positivity : 0 < a + 1)).2 (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hratio hepsilon.le]
  have hxeps := (hthreshold m hm).trans hcost
  simpa using hxeps

/-- Every actual dyadic spatial cross-coherence mass is bounded by the exact canonical balanced
current, including the degenerate zero-moment faces. -/
theorem openPeriodicDyadicSpatialCrossCoherenceMass_le_canonicalBalancedScaleCurrent
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (scale : ℕ) :
    openPeriodicDyadicSpatialCrossCoherenceMass solution t q scale ≤
      18 * canonicalBalancedScaleCurrent solution t q scale := by
  let L : ℝ := openPeriodicCanonicalVorticityLipschitzConstant solution t
  let high : ℝ := highDirectionKernelMoment solution t q scale
  let low : ℝ := lowAmplitudeKernelMoment solution t q scale
  have hL : 0 ≤ L :=
    (openPeriodicCanonicalVorticityLipschitzConstant solution t).coe_nonneg
  have hhigh : 0 ≤ high :=
    highDirectionKernelMoment_nonneg solution t q scale
  have hlow : 0 ≤ low :=
    lowAmplitudeKernelMoment_nonneg solution t q scale
  by_cases hLzero : L = 0
  · have hcrossZero :
        openPeriodicDyadicSpatialCrossCoherenceMass solution t q scale = 0 := by
      apply nonnegative_eq_zero_of_le_small_threshold
        (openPeriodicDyadicSpatialCrossCoherenceMass_nonneg solution t q scale) hlow
      intro m hm
      have hbound := openPeriodicDyadicSpatialCrossCoherenceMass_le_canonicalThresholdCost
        solution t q hm scale
      change openPeriodicDyadicSpatialCrossCoherenceMass solution t q scale ≤
        9 * thresholdCost L high low m at hbound
      simpa [thresholdCost, hLzero] using hbound
    rw [hcrossZero]
    unfold canonicalBalancedScaleCurrent
    exact mul_nonneg (by norm_num)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  · by_cases hhighZero : high = 0
    · have hcrossZero :
          openPeriodicDyadicSpatialCrossCoherenceMass solution t q scale = 0 := by
        apply nonnegative_eq_zero_of_le_small_threshold
          (openPeriodicDyadicSpatialCrossCoherenceMass_nonneg solution t q scale) hlow
        intro m hm
        have hbound := openPeriodicDyadicSpatialCrossCoherenceMass_le_canonicalThresholdCost
          solution t q hm scale
        change openPeriodicDyadicSpatialCrossCoherenceMass solution t q scale ≤
          9 * thresholdCost L high low m at hbound
        simpa [thresholdCost, hhighZero] using hbound
      rw [hcrossZero]
      unfold canonicalBalancedScaleCurrent
      exact mul_nonneg (by norm_num)
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    · by_cases hlowZero : low = 0
      · have hcrossZero :
            openPeriodicDyadicSpatialCrossCoherenceMass solution t q scale = 0 := by
          apply nonnegative_eq_zero_of_le_large_threshold
            (openPeriodicDyadicSpatialCrossCoherenceMass_nonneg solution t q scale)
            (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hL) hhigh)
          intro m hm
          have hbound := openPeriodicDyadicSpatialCrossCoherenceMass_le_canonicalThresholdCost
            solution t q hm scale
          change openPeriodicDyadicSpatialCrossCoherenceMass solution t q scale ≤
            9 * thresholdCost L high low m at hbound
          calc
            openPeriodicDyadicSpatialCrossCoherenceMass solution t q scale ≤
                9 * thresholdCost L high low m := hbound
            _ = 9 * ((2 * L * high) * m⁻¹) := by
              simp [thresholdCost, hlowZero]
              ring
        rw [hcrossZero]
        unfold canonicalBalancedScaleCurrent
        exact mul_nonneg (by norm_num)
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      · have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hLzero)
        have hhighPos : 0 < high := lt_of_le_of_ne hhigh (Ne.symm hhighZero)
        have hlowPos : 0 < low := lt_of_le_of_ne hlow (Ne.symm hlowZero)
        have hbound := openPeriodicDyadicSpatialCrossCoherenceMass_le_canonicalBalanced
          solution t q scale hLpos hhighPos hlowPos
        simpa [canonicalBalancedScaleCurrent, L, high, low] using hbound

/-- An alternative unconditional inhabitant of the strict-interior spatial receiver, obtained by
factoring every actual cross-coherence mass through the canonical balanced direction current. -/
theorem openPeriodicDyadicSpatialCrossCoherenceSummable_canonical
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    OpenPeriodicDyadicSpatialCrossCoherenceSummable solution t q := by
  exact Summable.of_nonneg_of_le
    (fun scale ↦ openPeriodicDyadicSpatialCrossCoherenceMass_nonneg solution t q scale)
    (openPeriodicDyadicSpatialCrossCoherenceMass_le_canonicalBalancedScaleCurrent
      solution t q)
    ((summable_canonicalBalancedScaleCurrent solution t q).mul_left 18)

/-- The complete infinite-depth spatial cross mass is quantitatively paid by the complete
canonical balanced-current word. -/
theorem openPeriodicFullSpatialCrossCoherenceMass_le_canonicalBalancedScaleCurrent
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    openPeriodicFullSpatialCrossCoherenceMass solution t q ≤
      18 * ∑' scale : ℕ, canonicalBalancedScaleCurrent solution t q scale := by
  unfold openPeriodicFullSpatialCrossCoherenceMass
  calc
    (∑' scale : ℕ,
        openPeriodicDyadicSpatialCrossCoherenceMass solution t q scale) ≤
        ∑' scale : ℕ, 18 * canonicalBalancedScaleCurrent solution t q scale :=
      (openPeriodicDyadicSpatialCrossCoherenceSummable_canonical solution t q).tsum_le_tsum
        (openPeriodicDyadicSpatialCrossCoherenceMass_le_canonicalBalancedScaleCurrent
          solution t q)
        ((summable_canonicalBalancedScaleCurrent solution t q).mul_left 18)
    _ = 18 * ∑' scale : ℕ,
        canonicalBalancedScaleCurrent solution t q scale := by
      rw [tsum_mul_left]

/-- The literal physical vortex-stretching occurrence consumes the balanced-current factorization
of the already inhabited spatial receiver rather than a separately supplied scale-summability
hypothesis. -/
theorem abs_openPeriodicPhysicalVortexStretchingAt_le_canonicalBalancedScaleCurrent
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    |openPeriodicPhysicalVortexStretchingAt solution t q| ≤
      (81 * criticalVorticityRate solution t.1) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 +
        (‖(complexDot (openPeriodicComplexVorticityAt solution t q)
            (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
            (18 * ∑' scale : ℕ,
              canonicalBalancedScaleCurrent solution t q scale)) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 := by
  calc
    |openPeriodicPhysicalVortexStretchingAt solution t q| ≤
        (81 * criticalVorticityRate solution t.1) *
            complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 +
          (‖(complexDot (openPeriodicComplexVorticityAt solution t q)
              (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
            complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
              openPeriodicFullSpatialCrossCoherenceMass solution t q) *
            complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 :=
      abs_openPeriodicPhysicalVortexStretchingAt_le_fullSpatialCrossCoherence
        solution t q
          (openPeriodicDyadicSpatialCrossCoherenceSummable_canonical solution t q)
    _ ≤ _ := by
      have hfull :=
        openPeriodicFullSpatialCrossCoherenceMass_le_canonicalBalancedScaleCurrent
          solution t q
      have hfactor :
          0 ≤ ‖(complexDot (openPeriodicComplexVorticityAt solution t q)
              (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
            complexVectorL1 (openPeriodicComplexVorticityAt solution t q) :=
        mul_nonneg (norm_nonneg _) (complexVectorL1_nonneg _)
      have hnonlinear :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfull hfactor)
          (sq_nonneg (complexVectorL1
            (openPeriodicComplexVorticityAt solution t q)))
      exact add_le_add le_rfl hnonlinear

section Audit

#print axioms openPeriodicDyadicSpatialCrossCoherenceMass_le_canonicalBalancedScaleCurrent
#print axioms openPeriodicDyadicSpatialCrossCoherenceSummable_canonical
#print axioms openPeriodicFullSpatialCrossCoherenceMass_le_canonicalBalancedScaleCurrent
#print axioms abs_openPeriodicPhysicalVortexStretchingAt_le_canonicalBalancedScaleCurrent

end Audit

end Soma.Holonics.Millennium.NavierStokesDirectionBalancedScaleClosure
