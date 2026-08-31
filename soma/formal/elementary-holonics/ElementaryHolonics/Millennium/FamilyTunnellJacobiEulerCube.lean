import ElementaryHolonics.Mathematics.JacobiFiniteDiagonalBridge
import ElementaryHolonics.Millennium.FamilyTunnellJacobiProductReceiver

/-!
# The completed Jacobi diagonal is the completed Euler cube

This closes the complete-series passage between the newly constructed finite
Jacobi diagonal bridge and the Tunnell orientation stream.  The equality is
coefficientwise exact and every coefficient factors through an explicitly
finite occurrence population.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellJacobiEulerCube

open PowerSeries
open Soma.Holonics.Mathematics.JacobiFiniteDiagonalBridge
open Soma.Holonics.Mathematics.JacobiEulerCubeStabilization
open Soma.Holonics.Millennium.FamilyTunnellJacobiProductReceiver
open Soma.Holonics.Millennium.FamilyTunnellHeckeThetaFactor
open Soma.Holonics.Millennium.FamilyTunnellHopfThetaLift

/-- **JACOBI CUBE IDENTITY IN THE TUNNELL DIAGONAL CHART.** -/
theorem jacobiProductDiagonalTheta_eq_infiniteEvenEulerCube :
    jacobiProductDiagonalTheta = infiniteEvenEulerCube := by
  apply PowerSeries.ext
  intro d
  rw [coeff_jacobiProductDiagonalTheta,
    complete_receiver_eq_infiniteEvenEulerCube]

/-- Regrading the completed Euler cube by `n = 1 + 4d` returns the existing
weighted quarter-square orientation current. -/
theorem affineFourRegrade_infiniteEvenEulerCube_eq_weightedQuarterSquareTheta :
    affineFourRegrade infiniteEvenEulerCube =
      weightedQuarterSquareTheta 1 := by
  rw [← jacobiProductDiagonalTheta_eq_infiniteEvenEulerCube,
    affineFourRegrade_jacobiProduct_eq_weightedQuarterSquareTheta]

/-- The regraded Euler cube, multiplied by the even residue difference,
returns the complete weight-two Hecke coefficient stream. -/
theorem affineFourRegrade_eulerCube_mul_evenDifference_eq_heckeCoefficientSeries :
    affineFourRegrade infiniteEvenEulerCube *
        (quarterSquareTheta 0 - quarterSquareTheta 2) =
      heckeCoefficientSeries := by
  rw [affineFourRegrade_infiniteEvenEulerCube_eq_weightedQuarterSquareTheta,
    weighted_mul_evenDifference_eq_heckeCoefficientSeries]

#print axioms jacobiProductDiagonalTheta_eq_infiniteEvenEulerCube
#print axioms affineFourRegrade_infiniteEvenEulerCube_eq_weightedQuarterSquareTheta
#print axioms affineFourRegrade_eulerCube_mul_evenDifference_eq_heckeCoefficientSeries

end Soma.Holonics.Millennium.FamilyTunnellJacobiEulerCube
