import ElementaryHolonics.Millennium.NavierStokesWeightedMildSpacetimeMomentum
import ElementaryHolonics.Millennium.NavierStokesWeightedProductReconstruction

/-!
# The mild quadratic source is an actual physical divergence and advection field

**[proved-derived]** The mild spacetime owner returns the unprojected quadratic source in native
`H²` and the product-reconstruction owner proves the coefficient/physical intertwiner.  This
owner joins those two existing ports.  At every native `H³` state, the source coefficient used by
the mild equation is exactly the Fourier population of the physical product-rule divergence.  In
the modewise incompressible fibre the retained second Leibniz face vanishes, so the same occurrence
is the actual advective derivative.

No second velocity derivative or strong time derivative is asserted here.  Those remain the
separate regularity needed to promote the mild modal law to a classical spacetime equation.
-/

noncomputable section

open scoped BigOperators
open Set

namespace Soma.Holonics.Millennium.NavierStokesWeightedMildPhysicalSource

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesWeightedMildSpacetimeMomentum
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedProductReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-- The physical complex divergence source reconstructed from one native state. -/
def physicalUnprojectedQuadraticComponent
    (state : PeriodicVectorWeightedSobolev 3) (output : Fin 3)
    (x : Space) : ℂ :=
  reconstructedUnprojectedDivergenceComponent
    (unweightedVectorThree state) (unweightedVectorThree state) output x

/-- Reweighting the exact unweighted coefficient receiver restores the identical native state. -/
theorem vectorCoefficientsAsWeighted_unweightedVectorThree
    (state : PeriodicVectorWeightedSobolev 3) :
    vectorCoefficientsAsWeighted (unweightedVectorThree state) = state := by
  funext component
  exact coefficientWeightedRealization_weightedSobolevCoefficients
    3 (state component)

/-- The physical divergence is the actual product-rule field of the two reconstructed vector
components. -/
theorem physicalUnprojectedQuadraticComponent_eq_productRule
    (state : PeriodicVectorWeightedSobolev 3) (output : Fin 3)
    (x : Space) :
    physicalUnprojectedQuadraticComponent state output x =
      ∑ coordinate : Fin 3,
        (reconstructedTorusComplexScalar
            (weightedSobolevCoefficients 3 (state coordinate))
            (euclideanToSpatialTorus x) *
              reconstructedTorusComplexScalarFDeriv
                (weightedSobolevCoefficients 3 (state output)) x
                (EuclideanSpace.single coordinate 1) +
          reconstructedTorusComplexScalar
            (weightedSobolevCoefficients 3 (state output))
            (euclideanToSpatialTorus x) *
              reconstructedTorusComplexScalarFDeriv
                (weightedSobolevCoefficients 3 (state coordinate)) x
                (EuclideanSpace.single coordinate 1)) := by
  exact reconstructedUnprojectedDivergenceComponent_eq_productRule
    (unweightedVectorThree state) (unweightedVectorThree state) output x

/-- The field is exactly the inverse Fourier population of the native `H²` source used by the
mild and pressure equations. -/
theorem physicalUnprojectedQuadraticComponent_eq_nativeSourceFourierSeries
    (state : PeriodicVectorWeightedSobolev 3) (output : Fin 3)
    (x : Space) :
    physicalUnprojectedQuadraticComponent state output x =
      ∑' k : SpatialFrequency,
        (weightedSobolevCoefficients 2
          (weightedUnprojectedQuadratic state output)).1 k *
            euclideanFourierCharacter k x := by
  rw [physicalUnprojectedQuadraticComponent,
    reconstructedUnprojectedDivergenceComponent_eq_fourierSeries]
  apply tsum_congr
  intro k
  rw [weightedUnprojectedQuadratic,
    weightedUnprojectedDivergenceConvolutionContinuous_apply,
    weightedUnprojectedDivergenceConvolution_coefficient]

/-- Incompressibility turns the same physical source into the advective derivative; the
divergence face is proved zero through the exact modewise fibre. -/
theorem physicalUnprojectedQuadraticComponent_eq_advection
    {state : PeriodicVectorWeightedSobolev 3}
    (hstate : IsModewiseDivergenceFree state)
    (output : Fin 3) (x : Space) :
    physicalUnprojectedQuadraticComponent state output x =
      ∑ coordinate : Fin 3,
        reconstructedTorusComplexScalar
            (weightedSobolevCoefficients 3 (state coordinate))
            (euclideanToSpatialTorus x) *
          reconstructedTorusComplexScalarFDeriv
            (weightedSobolevCoefficients 3 (state output)) x
            (EuclideanSpace.single coordinate 1) := by
  apply reconstructedUnprojectedDivergenceComponent_eq_advection
  rw [vectorCoefficientsAsWeighted_unweightedVectorThree]
  exact hstate

/-- Along an actual native path, the continuous quadratic-source path has this exact physical
receiver at every addressed time. -/
theorem physicalUnprojectedQuadraticComponent_eq_pathSourceFourierSeries
    {T : ℝ} (path : WeightedH3Path T) (t : Icc (0 : ℝ) T)
    (output : Fin 3) (x : Space) :
    physicalUnprojectedQuadraticComponent (path t) output x =
      ∑' k : SpatialFrequency,
        (weightedSobolevCoefficients 2
          (weightedUnprojectedQuadraticPath path t output)).1 k *
            euclideanFourierCharacter k x := by
  exact physicalUnprojectedQuadraticComponent_eq_nativeSourceFourierSeries
    (path t) output x

section Audit

#print axioms vectorCoefficientsAsWeighted_unweightedVectorThree
#print axioms physicalUnprojectedQuadraticComponent_eq_productRule
#print axioms physicalUnprojectedQuadraticComponent_eq_nativeSourceFourierSeries
#print axioms physicalUnprojectedQuadraticComponent_eq_advection
#print axioms physicalUnprojectedQuadraticComponent_eq_pathSourceFourierSeries

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedMildPhysicalSource
