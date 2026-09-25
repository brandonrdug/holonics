import Holonics.Fluid.NavierStokesSmoothSliceWeightedTower
import Holonics.Fluid.NavierStokesWeightedReality

/-!
# Exact inverse-Fourier return of a smooth periodic slice

**[proved-derived]** The native weighted state of an actual smooth periodic slice was defined
from that slice's complete genuine-torus Fourier population.  The bounded native reconstruction
has exactly the same coefficients.  Completeness of the torus Fourier Hilbert basis and
injectivity of the continuous-to-`L²` passage therefore identify the two continuous torus fields,
and Fourier reality returns the original real Euclidean velocity exactly.
-/

noncomputable section

open MeasureTheory

namespace Holonics.Fluid.NavierStokesWeightedSmoothSliceReconstruction

open Holonics.Fluid.NavierStokes
open Holonics.Fluid.NavierStokesSmoothSliceWeightedH3
open Holonics.Fluid.NavierStokesTorusFourier
open Holonics.Fluid.NavierStokesTorusVorticity
open Holonics.Fluid.NavierStokesWeightedFourierReconstruction
open Holonics.Fluid.NavierStokesWeightedReality
open Holonics.Fluid.NavierStokesWeightedSobolevHilbert

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The complete complex torus reconstruction of the native smooth-slice state is the literal
complex component of the original slice. -/
theorem reconstructedTorusComplexComponent_smoothSliceVectorWeightedH3
    (u : InitialVelocity)
    (hu : ContDiff ℝ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞) u)
    (hperiodic : IsOnePeriodic u)
    (component : Fin 3) :
    reconstructedTorusComplexComponent
        (smoothSliceVectorWeightedH3 u hu hperiodic) component =
      smoothSliceComponentLift u hu hperiodic component := by
  apply ContinuousMap.toLp_injective
    (𝕜 := ℂ) (E := ℂ) (p := 2) volume
  apply UnitAddTorus.mFourierBasis.repr.injective
  ext k
  rw [UnitAddTorus.mFourierBasis_repr, UnitAddTorus.mFourierBasis_repr,
    UnitAddTorus.mFourierCoeff_toLp, UnitAddTorus.mFourierCoeff_toLp]
  change
    torusSpatialFourierCoeff
        (reconstructedTorusComplexComponent
          (smoothSliceVectorWeightedH3 u hu hperiodic) component) k =
      torusSpatialFourierCoeff (smoothSliceComponentLift u hu hperiodic component) k
  rw [torusSpatialFourierCoeff_reconstructedTorusComplexComponent]
  change
    (weightedSobolevCoefficients 3
      (smoothSliceVectorWeightedH3 u hu hperiodic component)).1 k = _
  rw [unweighted_smoothSliceVectorWeightedH3_apply]
  rw [vectorSpatialFourierCoeff_apply]
  rfl

/-- Reconstructing the native weighted `H³` state of a smooth periodic slice returns that
actual real slice pointwise, with no quotient or almost-everywhere remainder. -/
theorem reconstructedVelocity_smoothSliceVectorWeightedH3
    (u : InitialVelocity)
    (hu : ContDiff ℝ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞) u)
    (hperiodic : IsOnePeriodic u) :
    reconstructedVelocity (smoothSliceVectorWeightedH3 u hu hperiodic) = u := by
  let state := smoothSliceVectorWeightedH3 u hu hperiodic
  have hreal : IsWeightedFourierReal 3 state :=
    isWeightedFourierReal_smoothSliceVectorWeightedH3 u hu hperiodic
  funext x
  ext component
  have hcomplex := congrArg (fun field : C(SpatialTorus, ℂ) ↦
      field (euclideanToSpatialTorus x))
    (reconstructedTorusComplexComponent_smoothSliceVectorWeightedH3
      u hu hperiodic component)
  have hsource :
      smoothSliceComponentLift u hu hperiodic component
          (euclideanToSpatialTorus x) = (u x component : ℂ) := by
    exact periodicTorusLift_projection _ _ _ x
  have hreconstructed := congrFun
    (complexifySpace_reconstructedTorusReal hreal
      (euclideanToSpatialTorus x)) component
  change reconstructedTorusReal state (euclideanToSpatialTorus x) component =
    u x component
  have :
      (reconstructedTorusReal state (euclideanToSpatialTorus x) component : ℂ) =
        (u x component : ℂ) := by
    calc
      (reconstructedTorusReal state (euclideanToSpatialTorus x) component : ℂ) =
          reconstructedTorusComplexComponent state component
            (euclideanToSpatialTorus x) := hreconstructed
      _ = smoothSliceComponentLift u hu hperiodic component
            (euclideanToSpatialTorus x) := hcomplex
      _ = (u x component : ℂ) := hsource
  exact_mod_cast this

section Audit

#print axioms reconstructedTorusComplexComponent_smoothSliceVectorWeightedH3
#print axioms reconstructedVelocity_smoothSliceVectorWeightedH3

end Audit

end Holonics.Fluid.NavierStokesWeightedSmoothSliceReconstruction
