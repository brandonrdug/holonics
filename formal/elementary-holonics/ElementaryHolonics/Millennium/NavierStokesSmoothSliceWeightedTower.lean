import ElementaryHolonics.Millennium.NavierStokesSmoothSliceWeightedAllOrders
import ElementaryHolonics.Millennium.NavierStokesWeightedFiniteOrderFourierReconstruction

/-!
# One smooth periodic slice supplies one coherent native Sobolev tower

**[proved-derived]** Every finite native state constructed from one smooth periodic velocity has
the same raw Fourier coefficient population.  Exact high-to-low restriction therefore makes
those states one coherent tower over the order-three face, rather than an unrelated family of
Sobolev witnesses.  The finite-order reconstruction owner then returns the original common
receiver as a spatially smooth field.

This owner supplies coherent high-order initial material.  It does not construct a high-order
path, a uniform lifespan, or persistence of the nonlinear mild return.
-/

noncomputable section

open ContDiff

namespace Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedTower

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedAllOrders
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesWeightedFiniteOrderFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderTame
open Soma.Holonics.Millennium.NavierStokesWeightedOrderRestriction
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-- Every finite native realization of one smooth slice restricts exactly to its order-three
realization. -/
theorem restrict_smoothSliceVectorWeighted_to_three
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (m : ℕ) :
    periodicVectorWeightedSobolevRestrictCLM 3 (m + 3) (by omega)
        (smoothSliceVectorWeighted u hu hperiodic (m + 3)) =
      smoothSliceVectorWeighted u hu hperiodic 3 := by
  change periodicVectorWeightedRestrictToThree (m + 3) (by omega)
      (smoothSliceVectorWeighted u hu hperiodic (m + 3)) =
    smoothSliceVectorWeighted u hu hperiodic 3
  funext component
  rw [periodicVectorWeightedRestrictToThree_apply]
  rw [← coefficientWeightedRealization_weightedSobolevCoefficients 3
    (periodicWeightedSobolevRestrict 3 (m + 3) (by omega)
      (smoothSliceVectorWeighted u hu hperiodic (m + 3) component))]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rw [weightedSobolevCoefficients_restrict_apply,
    unweighted_smoothSliceVectorWeighted_apply]
  exact (smoothSliceFourierL2_apply u hu hperiodic component k).symm

/-- The arbitrary-order constructor at order three is exactly the established `H³` slice used by
the restart line. -/
theorem smoothSliceVectorWeighted_three_eq_smoothSliceVectorWeightedH3
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u) :
    smoothSliceVectorWeighted u hu hperiodic 3 =
      smoothSliceVectorWeightedH3 u hu hperiodic := by
  funext component
  unfold smoothSliceVectorWeighted smoothSliceWeightedComponent
    smoothSliceVectorWeightedH3 smoothSliceWeightedH3Component
  congr 1

/-- The complete all-orders native population belonging to one smooth periodic source slice. -/
def smoothSliceCompatibleNativeWeightedSobolevTower
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u) :
    CompatibleNativeWeightedSobolevTower where
  base := smoothSliceVectorWeightedH3 u hu hperiodic
  lift m := smoothSliceVectorWeighted u hu hperiodic (m + 3)
  restrict_lift m := (restrict_smoothSliceVectorWeighted_to_three
    u hu hperiodic m).trans
      (smoothSliceVectorWeighted_three_eq_smoothSliceVectorWeightedH3
        u hu hperiodic)

/-- The reconstructed smooth receiver of the coherent tower is definitionally the established
order-three inverse Fourier reconstruction of the same slice. -/
theorem reconstructedSmoothVelocity_smoothSliceTower
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u) :
    reconstructedSmoothVelocity
        (smoothSliceCompatibleNativeWeightedSobolevTower u hu hperiodic) =
      reconstructedVelocity (smoothSliceVectorWeightedH3 u hu hperiodic) :=
  rfl

/-- The coherent native tower supplies an actual spatial `C∞` receiver without a separately
assumed smoothness interface. -/
theorem contDiff_infty_reconstructedSmoothVelocity_smoothSliceTower
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u) :
    ContDiff ℝ ∞
      (reconstructedSmoothVelocity
        (smoothSliceCompatibleNativeWeightedSobolevTower u hu hperiodic)) :=
  contDiff_infty_reconstructedSmoothVelocity
    (smoothSliceCompatibleNativeWeightedSobolevTower u hu hperiodic)

section Audit

#print axioms restrict_smoothSliceVectorWeighted_to_three
#print axioms smoothSliceVectorWeighted_three_eq_smoothSliceVectorWeightedH3
#print axioms smoothSliceCompatibleNativeWeightedSobolevTower
#print axioms contDiff_infty_reconstructedSmoothVelocity_smoothSliceTower

end Audit

end Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedTower
