import HolonicsResearch.Fluid.NavierStokesAdaptiveMatchedPhysicalService
import HolonicsResearch.Fluid.NavierStokesAdaptiveNonlinearSourceSquareOwner
import HolonicsResearch.Fluid.NavierStokesTerminalCompactEndpointExhaustion

/-!
# The depth-free adaptive rectangle with its physical matched receiver

**[proved-derived; formal-checked]** This is the cancellation-preserving successor of the first
adaptive rectangle service.  The off-diagonal history is still paid by the exact restart
population and the summable reciprocal-clock density times the native weighted `H3` square
current.  The matched diagonal is now paid by its cofinal signed physical-work receiver, rather
than a compact-time `H3` supremum cubed.

Thus finite dyadic depth disappears without introducing a supercritical supremum.  Terminal
exhaustion still requires a single endpoint-uniform bound for the displayed physical service;
this file does not manufacture that bound.
-/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators Interval

namespace Holonics.Fluid.NavierStokesAdaptiveRectanglePhysicalService

open Holonics.Fluid.NavierStokes
open Holonics.Fluid.NavierStokesAdaptiveClockMatchedPacking
open Holonics.Fluid.NavierStokesAdaptiveMatchedPhysicalService
open Holonics.Fluid.NavierStokesAdaptiveNonlinearSourceSquareOwner
open Holonics.Fluid.NavierStokesClockWeightedCompactTimePacking
open Holonics.Fluid.NavierStokesH3BilinearNorm
open Holonics.Fluid.NavierStokesOpenLifespan
open Holonics.Fluid.NavierStokesSmoothDyadicMildPackingEquivalence
open Holonics.Fluid.NavierStokesSmoothMildSourceClockBound
open Holonics.Fluid.NavierStokesTerminalCompactEndpointExhaustion
open Holonics.Fluid.NavierStokesTerminalSmoothDyadicVorticityPacking

/-- The complete depth-free service retaining the actual cofinal signed-work receiver. -/
def compactAdaptiveRectanglePhysicalH3Service
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) : ℝ :=
  nu⁻¹ * smoothRestartCoefficientPayment solution ha (hab.trans_lt hbT) +
    adaptiveNonlinearSourceSquareDensityMass nu *
      (23328 * periodicH3EmbeddingConstant) *
        (∫ sourceTime in a..b,
          compactOpenVelocityWeightedH3SquareCurrent
            solution ha hab hbT sourceTime) +
    Real.sqrt
      (compactAdaptiveMatchedCofinalSquareService
        solution ha hab hbT)

/-- Every finite scale-time rectangle is paid by the same cancellation-preserving service. -/
theorem compactOpenSmoothDyadicFiniteScaleTimeRectangleL1_le_physicalH3Service
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth : ℕ) :
    compactOpenSmoothDyadicFiniteScaleTimeRectangleL1
        solution ha hab hbT depth ≤
      compactAdaptiveRectanglePhysicalH3Service solution ha hab hbT := by
  rw [compactOpenSmoothDyadicFiniteScaleTimeRectangleL1_eq_adaptiveOffDiagonal_add_matched]
  exact add_le_add
    (compactOpenSmoothDyadicAdaptiveOffDiagonalFiber_le_restart_add_H3SquareCurrent
      solution hnu ha hab hbT depth)
    (compactOpenSmoothDyadicAdaptiveMatchedL1Prefix_le_cofinalServiceSqrt
      solution hnu ha hab hbT depth)

/-- The exact physical service feeds the literal terminal exhaustion.  The sole premise is now
uniformity of that displayed service along the concrete endpoint exhaustion. -/
theorem openPeriodicVorticityTerminalSmoothDyadicPacking_le_of_uniformPhysicalH3Service
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (bound : ℝ)
    (uniformService : ∀ n : ℕ,
      compactAdaptiveRectanglePhysicalH3Service solution
        (smoothTerminalExhaustionLeft_pos solution.terminal_pos n)
        (smoothTerminalExhaustionLeft_le_right solution.terminal_pos n)
        (smoothTerminalExhaustionRight_lt solution.terminal_pos n) ≤ bound) :
    openPeriodicVorticityTerminalSmoothDyadicPacking solution ≤
      ENNReal.ofReal bound := by
  apply openPeriodicVorticityTerminalSmoothDyadicPacking_le_of_uniformExhaustionRectangle
    solution hnu bound
  intro n depth
  exact (compactOpenSmoothDyadicFiniteScaleTimeRectangleL1_le_physicalH3Service
    solution hnu
      (smoothTerminalExhaustionLeft_pos solution.terminal_pos n)
      (smoothTerminalExhaustionLeft_le_right solution.terminal_pos n)
      (smoothTerminalExhaustionRight_lt solution.terminal_pos n)
      depth).trans (uniformService n)

section Audit

#print axioms compactOpenSmoothDyadicFiniteScaleTimeRectangleL1_le_physicalH3Service
#print axioms openPeriodicVorticityTerminalSmoothDyadicPacking_le_of_uniformPhysicalH3Service

end Audit

end Holonics.Fluid.NavierStokesAdaptiveRectanglePhysicalService
