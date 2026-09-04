import ElementaryHolonics.Millennium.NavierStokesAdaptiveMatchedCofinalDiagonal
import ElementaryHolonics.Millennium.NavierStokesAdaptiveNonlinearSourceSquareOwner
import ElementaryHolonics.Millennium.NavierStokesTerminalCompactEndpointExhaustion

/-!
# Depth-free adaptive rectangle service from the actual H3 square current

**[proved-derived; formal-checked]** The adaptive pantographic time split separates the complete
finite scale--time rectangle into its matched diagonal and earlier-history reconstruction fibre.
The cofinal linear-work estimate pays the former uniformly in finite depth.  The reciprocal heat
clock, finite-shell square owner, and native sharp-source estimate pay the latter by a summable
scale density times the actual compact-time weighted `H3` square current.

Their exact composition below removes finite dyadic depth from the right-hand side on every fixed
compact interval inside the open lifespan.  It does not assert endpoint uniformity as `a -> 0` or
`b -> T`: the restart population, matched cofinal service, and `H3` square current remain visible.
-/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators Interval

namespace Soma.Holonics.Millennium.NavierStokesAdaptiveRectangleH3Service

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAdaptiveClockMatchedPacking
open Soma.Holonics.Millennium.NavierStokesAdaptiveMatchedCofinalDiagonal
open Soma.Holonics.Millennium.NavierStokesAdaptiveNonlinearSourceSquareOwner
open Soma.Holonics.Millennium.NavierStokesClockWeightedCompactTimePacking
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicMildPackingEquivalence
open Soma.Holonics.Millennium.NavierStokesSmoothMildSourceClockBound
open Soma.Holonics.Millennium.NavierStokesTerminalCompactEndpointExhaustion
open Soma.Holonics.Millennium.NavierStokesTerminalSmoothDyadicVorticityPacking

/-- The complete source-specific compact service.  Every term is an existing PDE population:
the restart coefficients, the native weighted-`H3` square current, and the matched cofinal
linear-work service. -/
def compactAdaptiveRectangleH3Service
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
      (compactAdaptiveMatchedUniformPrefixSquareService
        solution ha hab hbT)

/-- **Depth-free complete compact rectangle estimate.**  No finite-depth factor survives: the
same source-specific service pays every finite dyadic prefix on the addressed compact interval. -/
theorem compactOpenSmoothDyadicFiniteScaleTimeRectangleL1_le_H3Service
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth : ℕ) :
    compactOpenSmoothDyadicFiniteScaleTimeRectangleL1
        solution ha hab hbT depth ≤
      compactAdaptiveRectangleH3Service solution ha hab hbT := by
  rw [compactOpenSmoothDyadicFiniteScaleTimeRectangleL1_eq_adaptiveOffDiagonal_add_matched]
  exact add_le_add
    (compactOpenSmoothDyadicAdaptiveOffDiagonalFiber_le_restart_add_H3SquareCurrent
      solution hnu ha hab hbT depth)
    (compactOpenSmoothDyadicAdaptiveMatchedL1Prefix_le_uniformServiceSqrt
      solution hnu ha hab hbT depth)

/-- Every fixed compact interior interval therefore has an unconditional bound uniform over all
finite scale depths.  The witness is the displayed PDE service above, not a choice-defined or
assumption-supplied majorant. -/
theorem exists_compact_depth_uniform_rectangle_bound
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    ∃ bound : ℝ, ∀ depth : ℕ,
      compactOpenSmoothDyadicFiniteScaleTimeRectangleL1
        solution ha hab hbT depth ≤ bound := by
  exact ⟨compactAdaptiveRectangleH3Service solution ha hab hbT,
    compactOpenSmoothDyadicFiniteScaleTimeRectangleL1_le_H3Service
      solution hnu ha hab hbT⟩

/-- The explicit PDE service feeds the literal terminal exhaustion with no remaining finite-depth
premise.  What remains is exactly endpoint uniformity of that displayed service along the concrete
compact exhaustion; this theorem does not assert that endpoint bound. -/
theorem openPeriodicVorticityTerminalSmoothDyadicPacking_le_of_uniformH3Service
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (bound : ℝ)
    (uniformService : ∀ n : ℕ,
      compactAdaptiveRectangleH3Service solution
        (smoothTerminalExhaustionLeft_pos solution.terminal_pos n)
        (smoothTerminalExhaustionLeft_le_right solution.terminal_pos n)
        (smoothTerminalExhaustionRight_lt solution.terminal_pos n) ≤ bound) :
    openPeriodicVorticityTerminalSmoothDyadicPacking solution ≤
      ENNReal.ofReal bound := by
  apply openPeriodicVorticityTerminalSmoothDyadicPacking_le_of_uniformExhaustionRectangle
    solution hnu bound
  intro n depth
  exact (compactOpenSmoothDyadicFiniteScaleTimeRectangleL1_le_H3Service
    solution hnu
      (smoothTerminalExhaustionLeft_pos solution.terminal_pos n)
      (smoothTerminalExhaustionLeft_le_right solution.terminal_pos n)
      (smoothTerminalExhaustionRight_lt solution.terminal_pos n)
      depth).trans (uniformService n)

section Audit

#print axioms compactOpenSmoothDyadicFiniteScaleTimeRectangleL1_le_H3Service
#print axioms exists_compact_depth_uniform_rectangle_bound
#print axioms openPeriodicVorticityTerminalSmoothDyadicPacking_le_of_uniformH3Service

end Audit

end Soma.Holonics.Millennium.NavierStokesAdaptiveRectangleH3Service
