import ElementaryHolonics.Millennium.NavierStokesHighVorticityDirection
import ElementaryHolonics.Millennium.NavierStokesVorticityCanonicalModulus

/-!
# Exact threshold balancing for the direction-depleted Hodge current

**[proved-derived]** The high/low partition is not assigned a heuristic cutoff.  At each dyadic
Hodge scale its symmetric modulus decomposes exactly into two addressed populations:

* a distance-bearing high/high direction moment, multiplied by `2L/m`;
* a low-amplitude moment, multiplied by `m`.

Their scalar receiver has the exact square-completion law
`a/m + m*b - 2*sqrt(a)*sqrt(b) = (sqrt(a)-m*sqrt(b))²/m`.
Consequently the positive threshold `sqrt(a)/sqrt(b)` is the exact balanced chart whenever the two
moment populations are positive.  This is a partition theorem, not an estimate chosen by rounding.
It does not prove that the PDE supplies one common variation coefficient `L` at the balanced
threshold or that the balanced spacetime current is terminally integrable.
-/

noncomputable section

open MeasureTheory Real Set

namespace Soma.Holonics.Millennium.NavierStokesDirectionThresholdBalance

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelMoment
open Soma.Holonics.Millennium.NavierStokesHighVorticityDirection
open Soma.Holonics.Millennium.NavierStokesVorticityCanonicalModulus

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The source-magnitude distance moment used by the high/high direction branch. -/
def highDirectionKernelMoment
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (scale : ℕ) : ℝ :=
  ∫ y : SpatialTorus,
    dyadicHodgeJacobianKernelPointMass scale y *
      (‖torusVorticityEvolution solution t q‖ *
        ‖torusVorticityEvolution solution t (q - y)‖ * dist y 0)

/-- The two endpoint-amplitude population used when either endpoint is below threshold. -/
def lowAmplitudeKernelMoment
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (scale : ℕ) : ℝ :=
  ∫ y : SpatialTorus,
    dyadicHodgeJacobianKernelPointMass scale y *
      (‖torusVorticityEvolution solution t q‖ +
        ‖torusVorticityEvolution solution t (q - y)‖)

theorem highDirectionKernelMoment_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (scale : ℕ) :
    0 ≤ highDirectionKernelMoment solution t q scale := by
  unfold highDirectionKernelMoment
  exact integral_nonneg fun y ↦
    mul_nonneg (dyadicHodgeJacobianKernelPointMass_nonneg scale y)
      (mul_nonneg
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) dist_nonneg)

theorem lowAmplitudeKernelMoment_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (scale : ℕ) :
    0 ≤ lowAmplitudeKernelMoment solution t q scale := by
  unfold lowAmplitudeKernelMoment
  exact integral_nonneg fun y ↦
    mul_nonneg (dyadicHodgeJacobianKernelPointMass_nonneg scale y)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The continuous symmetric modulus decomposes exactly into its high/high and low-endpoint
moments. -/
theorem dyadicHodgeJacobianKernel_symmetricHighLow_eq
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (K m : ℝ) (scale : ℕ) :
    dyadicHodgeJacobianKernelModulusMoment
        (symmetricHighLowVorticityModulus solution t q K m) scale =
      K * highDirectionKernelMoment solution t q scale +
        m * lowAmplitudeKernelMoment solution t q scale := by
  unfold dyadicHodgeJacobianKernelModulusMoment symmetricHighLowVorticityModulus
    highDirectionKernelMoment lowAmplitudeKernelMoment
  let highIntegrand : SpatialTorus → ℝ := fun y ↦
    dyadicHodgeJacobianKernelPointMass scale y *
      (‖torusVorticityEvolution solution t q‖ *
        ‖torusVorticityEvolution solution t (q - y)‖ * dist y 0)
  let lowIntegrand : SpatialTorus → ℝ := fun y ↦
    dyadicHodgeJacobianKernelPointMass scale y *
      (‖torusVorticityEvolution solution t q‖ +
        ‖torusVorticityEvolution solution t (q - y)‖)
  have hhigh : Integrable highIntegrand :=
    continuousMap_integrable_on_compact
      { toFun := highIntegrand
        continuous_toFun := by
          dsimp [highIntegrand]
          unfold dyadicHodgeJacobianKernelPointMass
          fun_prop }
  have hlow : Integrable lowIntegrand :=
    continuousMap_integrable_on_compact
      { toFun := lowIntegrand
        continuous_toFun := by
          dsimp [lowIntegrand]
          unfold dyadicHodgeJacobianKernelPointMass
          fun_prop }
  have hpoint :
      (fun y : SpatialTorus ↦
        dyadicHodgeJacobianKernelPointMass scale y *
          (K * ‖torusVorticityEvolution solution t q‖ *
              ‖torusVorticityEvolution solution t (q - y)‖ * dist y 0 +
            m * (‖torusVorticityEvolution solution t q‖ +
              ‖torusVorticityEvolution solution t (q - y)‖))) =
        fun y ↦ K * highIntegrand y + m * lowIntegrand y := by
    funext y
    dsimp [highIntegrand, lowIntegrand]
    ring
  simp only [ContinuousMap.coe_mk]
  rw [hpoint]
  change
    (∫ y : SpatialTorus, K * highIntegrand y + m * lowIntegrand y) =
      K * (∫ y : SpatialTorus, highIntegrand y) +
        m * (∫ y : SpatialTorus, lowIntegrand y)
  calc
    (∫ y : SpatialTorus, K * highIntegrand y + m * lowIntegrand y) =
        (∫ y : SpatialTorus, K * highIntegrand y) +
          ∫ y : SpatialTorus, m * lowIntegrand y :=
      integral_add (hhigh.const_mul K) (hlow.const_mul m)
    _ = K * (∫ y : SpatialTorus, highIntegrand y) +
        m * (∫ y : SpatialTorus, lowIntegrand y) := by
      rw [integral_const_mul, integral_const_mul]

/-- The exact scalar receiver returned by a threshold `m`. -/
def thresholdCost (L highMoment lowMoment m : ℝ) : ℝ :=
  (2 * L * m⁻¹) * highMoment + m * lowMoment

/-- Exact square completion.  The right side retains the complete imbalance rather than merely
reporting that the chosen cost is above its balanced face. -/
theorem thresholdCost_sub_balanced_eq
    {a b m : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hm : 0 < m) :
    (a * m⁻¹ + m * b) - 2 * (Real.sqrt a * Real.sqrt b) =
      (Real.sqrt a - m * Real.sqrt b) ^ 2 * m⁻¹ := by
  have hsqa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hsqb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  field_simp [hm.ne']
  nlinarith

theorem balanced_lower_le_thresholdCost
    {L highMoment lowMoment m : ℝ}
    (hL : 0 ≤ L) (hhigh : 0 ≤ highMoment) (hlow : 0 ≤ lowMoment)
    (hm : 0 < m) :
    2 * (Real.sqrt (2 * L * highMoment) * Real.sqrt lowMoment) ≤
      thresholdCost L highMoment lowMoment m := by
  have ha : 0 ≤ 2 * L * highMoment :=
    mul_nonneg (mul_nonneg (by norm_num) hL) hhigh
  have hgap := thresholdCost_sub_balanced_eq ha hlow hm
  unfold thresholdCost
  have hright :
      0 ≤ (Real.sqrt (2 * L * highMoment) - m * Real.sqrt lowMoment) ^ 2 * m⁻¹ :=
    mul_nonneg (sq_nonneg _) (inv_nonneg.mpr hm.le)
  nlinarith

/-- The exact positive threshold which equalizes the two square-root faces. -/
def balancedThreshold (L highMoment lowMoment : ℝ) : ℝ :=
  Real.sqrt (2 * L * highMoment) / Real.sqrt lowMoment

theorem balancedThreshold_pos
    {L highMoment lowMoment : ℝ}
    (hL : 0 < L) (hhigh : 0 < highMoment) (hlow : 0 < lowMoment) :
    0 < balancedThreshold L highMoment lowMoment := by
  exact div_pos
    (Real.sqrt_pos.2 (mul_pos (mul_pos (by norm_num) hL) hhigh))
    (Real.sqrt_pos.2 hlow)

/-- At the balanced threshold the upper receiver is exactly twice the geometric mean of the two
addressed moment faces. -/
theorem thresholdCost_balancedThreshold
    {L highMoment lowMoment : ℝ}
    (hL : 0 < L) (hhigh : 0 < highMoment) (hlow : 0 < lowMoment) :
    thresholdCost L highMoment lowMoment
        (balancedThreshold L highMoment lowMoment) =
      2 * (Real.sqrt (2 * L * highMoment) * Real.sqrt lowMoment) := by
  have ha : 0 < 2 * L * highMoment := mul_pos (mul_pos (by norm_num) hL) hhigh
  have hsqa : Real.sqrt (2 * L * highMoment) ^ 2 = 2 * L * highMoment :=
    Real.sq_sqrt ha.le
  have hsqb : Real.sqrt lowMoment ^ 2 = lowMoment := Real.sq_sqrt hlow.le
  have hsa : Real.sqrt (2 * L * highMoment) ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hsb : Real.sqrt lowMoment ≠ 0 := (Real.sqrt_pos.2 hlow).ne'
  unfold thresholdCost balancedThreshold
  field_simp [hsa, hsb]
  nlinarith

/-- The Hodge receiver at one scale is bounded by the exact threshold cost. -/
theorem openPeriodicDyadicSpatialCrossCoherenceMass_le_thresholdCost
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) {m L : ℝ}
    (hm : 0 < m) (hL : 0 ≤ L)
    (hvariation : HasLinearVariationOn
      (fun x ↦ vorticityField velocity x t.1)
      (HighAmplitudeRegion (fun x ↦ vorticityField velocity x t.1) m ∩
        Metric.closedBall 0 3) L)
    (scale : ℕ) :
    openPeriodicDyadicSpatialCrossCoherenceMass solution t q scale ≤
      9 * thresholdCost L
        (highDirectionKernelMoment solution t q scale)
        (lowAmplitudeKernelMoment solution t q scale) m := by
  calc
    openPeriodicDyadicSpatialCrossCoherenceMass solution t q scale ≤
        9 * dyadicHodgeJacobianKernelModulusMoment
          (symmetricHighLowVorticityModulus solution t q (2 * m⁻¹ * L) m) scale :=
      openPeriodicDyadicSpatialCrossCoherenceMass_le_symmetricHighLowMoment
        solution t q hm hL hvariation scale
    _ = 9 * thresholdCost L
        (highDirectionKernelMoment solution t q scale)
        (lowAmplitudeKernelMoment solution t q scale) m := by
      rw [dyadicHodgeJacobianKernel_symmetricHighLow_eq]
      unfold thresholdCost
      ring

/-- The actual compact-chart vorticity derivative supplies the required variation law on every
thresholded high region.  No new direction regularity hypothesis is introduced. -/
theorem canonical_hasLinearVariationOn_highRegion
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (m : ℝ) :
    HasLinearVariationOn
      (fun x ↦ vorticityField velocity x t.1)
      (HighAmplitudeRegion (fun x ↦ vorticityField velocity x t.1) m ∩
        Metric.closedBall 0 3)
      (openPeriodicCanonicalVorticityLipschitzConstant solution t : ℝ) := by
  intro x hx y hy
  have hlipschitz :=
    (openPeriodicCanonicalVorticityLipschitzOn_closedBall solution t).dist_le_mul
      x hx.2 y hy.2
  simpa [dist_eq_norm] using hlipschitz

/-- The physical solution therefore inhabits the exact threshold-cost receiver with its canonical
spatial derivative coefficient. -/
theorem openPeriodicDyadicSpatialCrossCoherenceMass_le_canonicalThresholdCost
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) {m : ℝ} (hm : 0 < m) (scale : ℕ) :
    openPeriodicDyadicSpatialCrossCoherenceMass solution t q scale ≤
      9 * thresholdCost
        (openPeriodicCanonicalVorticityLipschitzConstant solution t : ℝ)
        (highDirectionKernelMoment solution t q scale)
        (lowAmplitudeKernelMoment solution t q scale) m := by
  exact openPeriodicDyadicSpatialCrossCoherenceMass_le_thresholdCost
    solution t q hm (openPeriodicCanonicalVorticityLipschitzConstant solution t).coe_nonneg
      (canonical_hasLinearVariationOn_highRegion solution t m) scale

/-- When the two moment populations and the canonical derivative face are positive, the exact
balanced threshold constructs the geometric-mean Hodge bound with no selected cutoff. -/
theorem openPeriodicDyadicSpatialCrossCoherenceMass_le_canonicalBalanced
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (scale : ℕ)
    (hL : 0 < (openPeriodicCanonicalVorticityLipschitzConstant solution t : ℝ))
    (hhigh : 0 < highDirectionKernelMoment solution t q scale)
    (hlow : 0 < lowAmplitudeKernelMoment solution t q scale) :
    openPeriodicDyadicSpatialCrossCoherenceMass solution t q scale ≤
      18 *
        (Real.sqrt
            (2 * (openPeriodicCanonicalVorticityLipschitzConstant solution t : ℝ) *
              highDirectionKernelMoment solution t q scale) *
          Real.sqrt (lowAmplitudeKernelMoment solution t q scale)) := by
  let L : ℝ := openPeriodicCanonicalVorticityLipschitzConstant solution t
  let high : ℝ := highDirectionKernelMoment solution t q scale
  let low : ℝ := lowAmplitudeKernelMoment solution t q scale
  let m : ℝ := balancedThreshold L high low
  have hm : 0 < m := balancedThreshold_pos hL hhigh hlow
  have hbound := openPeriodicDyadicSpatialCrossCoherenceMass_le_canonicalThresholdCost
    solution t q hm scale
  have hbalance := thresholdCost_balancedThreshold hL hhigh hlow
  change openPeriodicDyadicSpatialCrossCoherenceMass solution t q scale ≤
    18 * (Real.sqrt (2 * L * high) * Real.sqrt low)
  change openPeriodicDyadicSpatialCrossCoherenceMass solution t q scale ≤
    9 * thresholdCost L high low m at hbound
  rw [hbalance] at hbound
  nlinarith

section Audit

#print axioms highDirectionKernelMoment_nonneg
#print axioms lowAmplitudeKernelMoment_nonneg
#print axioms dyadicHodgeJacobianKernel_symmetricHighLow_eq
#print axioms thresholdCost_sub_balanced_eq
#print axioms balanced_lower_le_thresholdCost
#print axioms balancedThreshold_pos
#print axioms thresholdCost_balancedThreshold
#print axioms openPeriodicDyadicSpatialCrossCoherenceMass_le_thresholdCost
#print axioms canonical_hasLinearVariationOn_highRegion
#print axioms openPeriodicDyadicSpatialCrossCoherenceMass_le_canonicalThresholdCost
#print axioms openPeriodicDyadicSpatialCrossCoherenceMass_le_canonicalBalanced

end Audit

end Soma.Holonics.Millennium.NavierStokesDirectionThresholdBalance
