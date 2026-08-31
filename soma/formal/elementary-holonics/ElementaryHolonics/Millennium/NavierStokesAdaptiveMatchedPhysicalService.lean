import ElementaryHolonics.Millennium.NavierStokesAdaptiveMatchedCofinalDiagonal
import ElementaryHolonics.Millennium.NavierStokesCofinalWorkEnstrophyJoin

/-!
# The adaptive matched diagonal paid by its cofinal physical receiver

**[proved-derived; formal-checked]** The earlier finite-prefix service bounded the signed linear
boundary work pointwise by a compact-time `H3` supremum cubed.  That estimate is lawful on each
compact interval, but it discards the cofinal cancellation and is unsuitable for terminal
exhaustion.  The standing infinite matched-diagonal theorem is stronger: it pays the complete
nonnegative scale sum by the absolute value of the exact cofinal signed-work integral.

This file descends that infinite receipt to every finite prefix.  The resulting service has no
compact `H3` supremum.  Its cofinal work can then be read exactly as endpoint enstrophy, accumulated
vorticity dissipation, and the retained scale-zero reconstruction fibre.  No bound on those
physical populations, and hence no terminal regularity claim, is asserted here.
-/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators Interval

namespace Soma.Holonics.Millennium.NavierStokesAdaptiveMatchedPhysicalService

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAdaptiveClockMatchedPacking
open Soma.Holonics.Millennium.NavierStokesAdaptiveMatchedCofinalDiagonal
open Soma.Holonics.Millennium.NavierStokesCofinalWorkEnstrophyJoin
open Soma.Holonics.Millennium.NavierStokesEnstrophyTerminalCurrent
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability
open Soma.Holonics.Millennium.NavierStokesVorticityThreeStrands

/-- The cancellation-preserving square service for the complete matched diagonal. -/
def compactAdaptiveMatchedCofinalSquareService
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) : ℝ :=
  nu⁻¹ * (1024 * (b - a) *
    ((1 / 2 : ℝ) *
        openPeriodicFullVorticityCoefficientMass solution
          ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
      abs (compactCofinalLinearMultiplierWorkRealIntegral
        solution ha hab hbT)))

theorem compactAdaptiveMatchedCofinalSquareService_nonneg
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    0 ≤ compactAdaptiveMatchedCofinalSquareService solution ha hab hbT := by
  unfold compactAdaptiveMatchedCofinalSquareService
  exact mul_nonneg (inv_nonneg.mpr hnu.le)
    (mul_nonneg
      (mul_nonneg (by norm_num) (sub_nonneg.mpr hab))
      (add_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg _)) (abs_nonneg _)))

/-- Every finite matched prefix is below the complete nonnegative scale population. -/
theorem compactOpenSmoothDyadicAdaptiveMatchedL1Prefix_le_tsum
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth : ℕ) :
    compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
        solution ha hab hbT depth ≤
      ∑' scale : ℕ,
        compactOpenSmoothDyadicAdaptiveMatchedBandL1
          solution ha hab hbT scale := by
  have hsummable :=
    summable_compactOpenSmoothDyadicAdaptiveMatchedBandL1
      solution hnu ha hab hbT
  unfold compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
  exact hsummable.sum_le_tsum (Finset.range depth)
    (fun scale _hscale ↦
      compactOpenSmoothDyadicAdaptiveMatchedBandL1_nonneg
        solution ha hab hbT scale)

/-- The cofinal square receipt therefore pays every finite matched prefix, with no compact-time
supremum inserted. -/
theorem compactOpenSmoothDyadicAdaptiveMatchedL1Prefix_sq_le_cofinalService
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth : ℕ) :
    compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
        solution ha hab hbT depth ^ 2 ≤
      compactAdaptiveMatchedCofinalSquareService solution ha hab hbT := by
  have hprefixNonneg : 0 ≤ compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
      solution ha hab hbT depth := by
    unfold compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
    exact Finset.sum_nonneg fun scale _hscale ↦
      compactOpenSmoothDyadicAdaptiveMatchedBandL1_nonneg
        solution ha hab hbT scale
  have htotalNonneg : 0 ≤ ∑' scale : ℕ,
      compactOpenSmoothDyadicAdaptiveMatchedBandL1
        solution ha hab hbT scale := by
    exact tsum_nonneg fun scale ↦
      compactOpenSmoothDyadicAdaptiveMatchedBandL1_nonneg
        solution ha hab hbT scale
  have hprefix := compactOpenSmoothDyadicAdaptiveMatchedL1Prefix_le_tsum
    solution hnu ha hab hbT depth
  have hsquare :
      compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
          solution ha hab hbT depth ^ 2 ≤
        (∑' scale : ℕ,
          compactOpenSmoothDyadicAdaptiveMatchedBandL1
            solution ha hab hbT scale) ^ 2 :=
    (sq_le_sq₀ hprefixNonneg htotalNonneg).2 hprefix
  exact hsquare.trans
    (tsum_compactOpenSmoothDyadicAdaptiveMatchedBandL1_sq_le_cofinalWork
      solution hnu ha hab hbT)

/-- Square-root form used by the complete adaptive rectangle. -/
theorem compactOpenSmoothDyadicAdaptiveMatchedL1Prefix_le_cofinalServiceSqrt
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth : ℕ) :
    compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
        solution ha hab hbT depth ≤
      Real.sqrt (compactAdaptiveMatchedCofinalSquareService
        solution ha hab hbT) := by
  have hprefix : 0 ≤ compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
      solution ha hab hbT depth := by
    unfold compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
    exact Finset.sum_nonneg fun scale _hscale ↦
      compactOpenSmoothDyadicAdaptiveMatchedBandL1_nonneg
        solution ha hab hbT scale
  have hservice := compactAdaptiveMatchedCofinalSquareService_nonneg
    solution hnu ha hab hbT
  apply (sq_le_sq₀ hprefix (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hservice]
  exact compactOpenSmoothDyadicAdaptiveMatchedL1Prefix_sq_le_cofinalService
    solution hnu ha hab hbT depth

/-- The cofinal service retains the exact physical endpoint/dissipation/low-pass fibre reading. -/
theorem compactAdaptiveMatchedCofinalSquareService_eq_endpointEnstrophy
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (receipt : EnstrophyStrandIntervalReceipt (0 : VelocityField) velocity a b) :
    compactAdaptiveMatchedCofinalSquareService solution ha hab hbT =
      nu⁻¹ * (1024 * (b - a) *
        ((1 / 2 : ℝ) *
            openPeriodicFullVorticityCoefficientMass solution
              ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
          abs (periodicEnstrophy velocity b - periodicEnstrophy velocity a +
            nu * (∫ time in a..b,
              periodicVorticityDissipation velocity time) -
            compactScaleZeroLinearWorkBoundaryRealIntegral
              solution ha hab hbT))) := by
  unfold compactAdaptiveMatchedCofinalSquareService
  rw [compactCofinalLinearMultiplierWorkRealIntegral_eq_endpointEnstrophy
    solution ha hab hbT receipt]

section Audit

#print axioms compactOpenSmoothDyadicAdaptiveMatchedL1Prefix_le_tsum
#print axioms compactOpenSmoothDyadicAdaptiveMatchedL1Prefix_sq_le_cofinalService
#print axioms compactOpenSmoothDyadicAdaptiveMatchedL1Prefix_le_cofinalServiceSqrt
#print axioms compactAdaptiveMatchedCofinalSquareService_eq_endpointEnstrophy

end Audit

end Soma.Holonics.Millennium.NavierStokesAdaptiveMatchedPhysicalService
