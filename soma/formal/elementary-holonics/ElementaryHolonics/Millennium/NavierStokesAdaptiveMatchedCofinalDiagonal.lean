import ElementaryHolonics.Millennium.NavierStokesAdaptiveClockMatchedPacking
import ElementaryHolonics.Millennium.NavierStokesCompleteLinearWorkCompactL1

/-!
# Infinite adaptive matched diagonal through the cofinal linear-work receiver

**[proved-derived; formal-checked]**  Strong compact-time `L¹` convergence of the actual
finite-depth linear work passes the finite adaptive matched-prefix inequality to its complete
scale diagonal.  The nonlinear receiver is the real part of the interval integral of
`completeCofinalLinearMultiplierWork`; consequently the retained scale-zero stretching and
Hermitian transport boundaries are not discarded or replaced by an envelope.

Only the adaptive matched diagonal is closed.  No off-diagonal history or terminal statement is
made.
-/

noncomputable section

open Filter MeasureTheory Real Set Topology
open scoped BigOperators Interval

namespace Soma.Holonics.Millennium.NavierStokesAdaptiveMatchedCofinalDiagonal

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAdaptiveClockMatchedPacking
open Soma.Holonics.Millennium.NavierStokesClockWeightedCompactTimePacking
open Soma.Holonics.Millennium.NavierStokesCompleteLinearWorkCofinalLimit
open Soma.Holonics.Millennium.NavierStokesCompleteLinearWorkCompactL1
open Soma.Holonics.Millennium.NavierStokesFiniteLinearRadiusTailPassage
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearScaleBoundary
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability

/-! ## The retained cofinal interval receiver -/

/-- The complex cofinal work integrated on the addressed compact interval. -/
def compactCofinalLinearMultiplierWorkIntegral
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) : ℂ :=
  ∫ time in a..b,
    compactCofinalLinearMultiplierWork solution ha hab hbT time

/-- The real receiver used by the signed adaptive packing inequality.  Its source is still the
complete complex cofinal work, including both retained scale-zero boundaries. -/
def compactCofinalLinearMultiplierWorkRealIntegral
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) : ℝ :=
  (compactCofinalLinearMultiplierWorkIntegral solution ha hab hbT).re

theorem intervalIntegrable_compactCofinalLinearMultiplierWork
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    IntervalIntegrable
      (compactCofinalLinearMultiplierWork solution ha hab hbT) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  apply volume.integrableOn_of_bounded
  · exact (measure_Ioc_lt_top.ne)
  · exact (measurable_compactCofinalLinearMultiplierWork
      solution ha hab hbT).aestronglyMeasurable
  · exact ae_restrict_of_forall_mem measurableSet_Ioc fun time _htime ↦
      norm_compactCofinalLinearMultiplierWork_le_halfBound
        solution ha hab hbT time

theorem intervalIntegrable_compactActualLinearMultiplierCoefficientWork
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    IntervalIntegrable
      (compactActualLinearMultiplierCoefficientWork solution ha hab hbT depth)
      volume a b :=
  (continuous_compactActualLinearMultiplierCoefficientWork
    solution ha hab hbT depth).intervalIntegrable _ _

theorem compactOpenSmoothDyadicLinearBoundarySignedWorkRate_eq_actual_re
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth : ℕ) (time : ℝ) :
    compactOpenSmoothDyadicLinearBoundarySignedWorkRate
        solution ha hab hbT depth time =
      (compactActualLinearMultiplierCoefficientWork
        solution ha hab hbT depth time).re := by
  rfl

/-- Strong `L¹` convergence controls the distance between the complex interval integrals. -/
theorem tendsto_compactActualLinearMultiplierCoefficientWorkIntegral
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    Tendsto
      (fun depth ↦ ∫ time in a..b,
        compactActualLinearMultiplierCoefficientWork
          solution ha hab hbT depth time)
      atTop
      (nhds (compactCofinalLinearMultiplierWorkIntegral
        solution ha hab hbT)) := by
  apply tendsto_iff_dist_tendsto_zero.2
  apply squeeze_zero (fun _depth ↦ dist_nonneg) _
    (tendsto_integral_norm_compactLinearWorkError_zero
      solution ha hab hbT)
  intro depth
  rw [dist_eq_norm]
  unfold compactCofinalLinearMultiplierWorkIntegral
  rw [← intervalIntegral.integral_sub
    (intervalIntegrable_compactActualLinearMultiplierCoefficientWork
      solution ha hab hbT depth)
    (intervalIntegrable_compactCofinalLinearMultiplierWork
      solution ha hab hbT)]
  exact intervalIntegral.norm_integral_le_integral_norm hab

/-- Taking the real receiver and then absolute value preserves the cofinal passage. -/
theorem tendsto_abs_integral_compactLinearBoundaryWork
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    Tendsto
      (fun depth ↦
        |∫ time in a..b,
          compactOpenSmoothDyadicLinearBoundarySignedWorkRate
            solution ha hab hbT depth time|)
      atTop
      (nhds |compactCofinalLinearMultiplierWorkRealIntegral
        solution ha hab hbT|) := by
  have hintegral := tendsto_compactActualLinearMultiplierCoefficientWorkIntegral
    solution ha hab hbT
  have hreal := Complex.continuous_re.tendsto
      (compactCofinalLinearMultiplierWorkIntegral solution ha hab hbT) |>.comp hintegral
  have habs := continuous_abs.tendsto
      (compactCofinalLinearMultiplierWorkRealIntegral solution ha hab hbT) |>.comp hreal
  apply Tendsto.congr' _ habs
  exact Filter.Eventually.of_forall fun depth ↦ by
    dsimp only [Function.comp_apply]
    congr 1
    rw [intervalIntegral.integral_congr (fun time _htime ↦
      compactOpenSmoothDyadicLinearBoundarySignedWorkRate_eq_actual_re
        solution ha hab hbT depth time)]
    exact
      (Complex.reCLM.intervalIntegral_comp_comm
        (intervalIntegrable_compactActualLinearMultiplierCoefficientWork
          solution ha hab hbT depth)).symm

/-! ## Uniform finite-prefix payment and summability -/

theorem compactOpenSmoothDyadicAdaptiveMatchedBandL1_nonneg
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) :
    0 ≤ compactOpenSmoothDyadicAdaptiveMatchedBandL1
      solution ha hab hbT scale := by
  unfold compactOpenSmoothDyadicAdaptiveMatchedBandL1
  exact intervalIntegral.integral_nonneg
    (adaptiveSmoothDyadicTerminalWindowStart_le hab scale)
    (fun time _htime ↦
      compactOpenSmoothDyadicVorticityBandSpatialSup_nonneg
        solution ha hab hbT scale time)

/-- The finite-depth signed boundary integral is uniformly controlled by the compact native
`H³` work service, independently of depth. -/
theorem abs_integral_compactLinearBoundaryWork_le_uniform
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    |∫ time in a..b,
      compactOpenSmoothDyadicLinearBoundarySignedWorkRate
        solution ha hab hbT depth time| ≤
      (b - a) * ((2519424 * periodicH3EmbeddingConstant) *
        ‖compactOpenVelocityWeightedH3StateChart solution ha hab hbT‖ ^ 3) := by
  have hpoint (time : ℝ) :
      ‖compactOpenSmoothDyadicLinearBoundarySignedWorkRate
          solution ha hab hbT depth time‖ ≤
        (2519424 * periodicH3EmbeddingConstant) *
          ‖compactOpenVelocityWeightedH3StateChart solution ha hab hbT‖ ^ 3 := by
    rw [compactOpenSmoothDyadicLinearBoundarySignedWorkRate_eq_actual_re]
    exact (Complex.abs_re_le_norm _).trans
      (norm_compactActualLinearMultiplierCoefficientWork_le_halfBound
        solution ha hab hbT depth time)
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b)
    (f := compactOpenSmoothDyadicLinearBoundarySignedWorkRate
      solution ha hab hbT depth)
    (fun time _htime ↦ hpoint time)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hbound
  simpa only [mul_comm] using hbound

/-- An explicit finite constant bounding every adaptive matched prefix after dividing by the
positive viscosity. -/
def compactAdaptiveMatchedUniformPrefixSquareService
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) : ℝ :=
  nu⁻¹ * (1024 * (b - a) *
    ((1 / 2 : ℝ) *
        openPeriodicFullVorticityCoefficientMass solution
          ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
      (b - a) * ((2519424 * periodicH3EmbeddingConstant) *
        ‖compactOpenVelocityWeightedH3StateChart solution ha hab hbT‖ ^ 3)))

theorem compactAdaptiveMatchedUniformPrefixSquareService_nonneg
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    0 ≤ compactAdaptiveMatchedUniformPrefixSquareService
      solution ha hab hbT := by
  unfold compactAdaptiveMatchedUniformPrefixSquareService
  exact mul_nonneg (inv_nonneg.mpr hnu.le)
    (mul_nonneg
      (mul_nonneg (by norm_num) (sub_nonneg.mpr hab))
      (add_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg _))
        (mul_nonneg (sub_nonneg.mpr hab)
          (mul_nonneg
            (mul_nonneg (by norm_num) periodicH3EmbeddingConstant_nonneg)
            (pow_nonneg (norm_nonneg _) 3)))))

theorem compactOpenSmoothDyadicAdaptiveMatchedL1Prefix_sq_le_uniformService
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth : ℕ) :
    compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
        solution ha hab hbT depth ^ 2 ≤
      compactAdaptiveMatchedUniformPrefixSquareService
        solution ha hab hbT := by
  have hfinite := openPeriodicSolutionOn_adaptiveMatchedL1Prefix_sq_le_linearBoundaryWork
    solution ha hab hbT hnu depth
  have hwork := abs_integral_compactLinearBoundaryWork_le_uniform
    solution ha hab hbT depth
  have hlength : 0 ≤ b - a := sub_nonneg.mpr hab
  have hright :
      1024 * (b - a) * ((1 / 2 : ℝ) *
          openPeriodicFullVorticityCoefficientMass solution
            ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
        |∫ time in a..b,
          compactOpenSmoothDyadicLinearBoundarySignedWorkRate
            solution ha hab hbT depth time|) ≤
      1024 * (b - a) * ((1 / 2 : ℝ) *
          openPeriodicFullVorticityCoefficientMass solution
            ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
        (b - a) * ((2519424 * periodicH3EmbeddingConstant) *
          ‖compactOpenVelocityWeightedH3StateChart solution ha hab hbT‖ ^ 3)) := by
    gcongr
  have hscaled := mul_le_mul_of_nonneg_left (hfinite.trans hright)
    (inv_nonneg.mpr hnu.le)
  unfold compactAdaptiveMatchedUniformPrefixSquareService
  calc
    compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
        solution ha hab hbT depth ^ 2 =
      nu⁻¹ * (nu * compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
        solution ha hab hbT depth ^ 2) := by field_simp [hnu.ne']
    _ ≤ nu⁻¹ * (1024 * (b - a) *
      ((1 / 2 : ℝ) *
          openPeriodicFullVorticityCoefficientMass solution
            ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
        (b - a) * ((2519424 * periodicH3EmbeddingConstant) *
          ‖compactOpenVelocityWeightedH3StateChart solution ha hab hbT‖ ^ 3))) := hscaled

theorem compactOpenSmoothDyadicAdaptiveMatchedL1Prefix_le_uniformServiceSqrt
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth : ℕ) :
    compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
        solution ha hab hbT depth ≤
      Real.sqrt (compactAdaptiveMatchedUniformPrefixSquareService
        solution ha hab hbT) := by
  have hprefix : 0 ≤ compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
      solution ha hab hbT depth := by
    unfold compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
    exact Finset.sum_nonneg fun scale _hscale ↦
      compactOpenSmoothDyadicAdaptiveMatchedBandL1_nonneg
        solution ha hab hbT scale
  have hservice := compactAdaptiveMatchedUniformPrefixSquareService_nonneg
    solution hnu ha hab hbT
  apply (sq_le_sq₀ hprefix (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hservice]
  exact compactOpenSmoothDyadicAdaptiveMatchedL1Prefix_sq_le_uniformService
    solution hnu ha hab hbT depth

/-- The complete adaptive matched diagonal is summable in scale. -/
theorem summable_compactOpenSmoothDyadicAdaptiveMatchedBandL1
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    Summable fun scale ↦
      compactOpenSmoothDyadicAdaptiveMatchedBandL1
        solution ha hab hbT scale := by
  apply summable_of_sum_range_le
    (fun scale ↦ compactOpenSmoothDyadicAdaptiveMatchedBandL1_nonneg
      solution ha hab hbT scale)
  intro depth
  change compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
    solution ha hab hbT depth ≤ _
  exact compactOpenSmoothDyadicAdaptiveMatchedL1Prefix_le_uniformServiceSqrt
    solution hnu ha hab hbT depth

/-! ## Cofinal square bound for the infinite diagonal -/

/-- **Infinite adaptive matched diagonal bound.**  The complete scale sum is paid by the
interval length, inverse viscosity, the initial vorticity coefficient mass, and the real
interval receiver of the exact cofinal linear work. -/
theorem tsum_compactOpenSmoothDyadicAdaptiveMatchedBandL1_sq_le_cofinalWork
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    (∑' scale : ℕ,
      compactOpenSmoothDyadicAdaptiveMatchedBandL1
        solution ha hab hbT scale) ^ 2 ≤
      nu⁻¹ * (1024 * (b - a) *
          ((1 / 2 : ℝ) *
            openPeriodicFullVorticityCoefficientMass solution
              ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
          abs (compactCofinalLinearMultiplierWorkRealIntegral
            solution ha hab hbT))) := by
  have hsummable :=
    summable_compactOpenSmoothDyadicAdaptiveMatchedBandL1
      solution hnu ha hab hbT
  have hprefix : Tendsto
      (fun depth ↦ compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
        solution ha hab hbT depth) atTop
      (nhds (∑' scale : ℕ,
        compactOpenSmoothDyadicAdaptiveMatchedBandL1
          solution ha hab hbT scale)) := by
    simpa only [compactOpenSmoothDyadicAdaptiveMatchedL1Prefix] using
      hsummable.hasSum.tendsto_sum_nat
  have hleft : Tendsto
      (fun depth ↦ nu *
        compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
          solution ha hab hbT depth ^ 2) atTop
      (nhds (nu * (∑' scale : ℕ,
        compactOpenSmoothDyadicAdaptiveMatchedBandL1
          solution ha hab hbT scale) ^ 2)) :=
    tendsto_const_nhds.mul (hprefix.pow 2)
  have hwork : Tendsto
      (fun depth ↦
        |∫ time in a..b,
          compactOpenSmoothDyadicLinearBoundarySignedWorkRate
            solution ha hab hbT depth time|)
      atTop (nhds (abs
        (compactCofinalLinearMultiplierWorkRealIntegral
          solution ha hab hbT))) :=
    tendsto_abs_integral_compactLinearBoundaryWork solution ha hab hbT
  have hright : Tendsto
      (fun depth ↦ 1024 * (b - a) *
        ((1 / 2 : ℝ) *
            openPeriodicFullVorticityCoefficientMass solution
              ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
          |∫ time in a..b,
            compactOpenSmoothDyadicLinearBoundarySignedWorkRate
              solution ha hab hbT depth time|))
      atTop
      (nhds (1024 * (b - a) *
        ((1 / 2 : ℝ) *
            openPeriodicFullVorticityCoefficientMass solution
              ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
          abs (compactCofinalLinearMultiplierWorkRealIntegral
            solution ha hab hbT)))) := by
    exact tendsto_const_nhds.mul (tendsto_const_nhds.add hwork)
  have hfinite : ∀ depth,
      nu * compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
          solution ha hab hbT depth ^ 2 ≤
        1024 * (b - a) *
          ((1 / 2 : ℝ) *
              openPeriodicFullVorticityCoefficientMass solution
                ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
            |∫ time in a..b,
              compactOpenSmoothDyadicLinearBoundarySignedWorkRate
                solution ha hab hbT depth time|) := by
    intro depth
    exact openPeriodicSolutionOn_adaptiveMatchedL1Prefix_sq_le_linearBoundaryWork
      solution ha hab hbT hnu depth
  have hviscous : nu * (∑' scale : ℕ,
      compactOpenSmoothDyadicAdaptiveMatchedBandL1
        solution ha hab hbT scale) ^ 2 ≤
      1024 * (b - a) *
        ((1 / 2 : ℝ) *
            openPeriodicFullVorticityCoefficientMass solution
              ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
          abs (compactCofinalLinearMultiplierWorkRealIntegral
            solution ha hab hbT)) :=
    le_of_tendsto_of_tendsto hleft hright
      (Filter.Eventually.of_forall hfinite)
  calc
    (∑' scale : ℕ,
        compactOpenSmoothDyadicAdaptiveMatchedBandL1
          solution ha hab hbT scale) ^ 2 =
        nu⁻¹ * (nu * (∑' scale : ℕ,
          compactOpenSmoothDyadicAdaptiveMatchedBandL1
            solution ha hab hbT scale) ^ 2) := by
      field_simp [hnu.ne']
    _ ≤ nu⁻¹ * (1024 * (b - a) *
        ((1 / 2 : ℝ) *
            openPeriodicFullVorticityCoefficientMass solution
              ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
          abs (compactCofinalLinearMultiplierWorkRealIntegral
            solution ha hab hbT))) :=
      mul_le_mul_of_nonneg_left hviscous (inv_nonneg.mpr hnu.le)

section Audit

#print axioms tendsto_compactActualLinearMultiplierCoefficientWorkIntegral
#print axioms summable_compactOpenSmoothDyadicAdaptiveMatchedBandL1
#print axioms tsum_compactOpenSmoothDyadicAdaptiveMatchedBandL1_sq_le_cofinalWork

end Audit

end Soma.Holonics.Millennium.NavierStokesAdaptiveMatchedCofinalDiagonal
