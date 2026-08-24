import ElementaryHolonics.Millennium.NavierStokesCoordinateNativeMildRestart
import ElementaryHolonics.Millennium.NavierStokesSmoothSliceWeightedTower
import ElementaryHolonics.Millennium.NavierStokesWeightedClassicalRestartCarrier
import ElementaryHolonics.Millennium.NavierStokesWeightedFiniteApertureHigherOrderPersistence
import ElementaryHolonics.Millennium.NavierStokesWeightedSmoothSliceReconstruction

/-!
# Native cap restarts returned as classical restart carriers

**[proved-derived]** A uniform coordinate receiver first selects the common native `H³` cap and
its invariant mild fixed point.  The actual smooth source slice supplies a coherent all-order
initial Sobolev tower; finite-aperture higher-order persistence then supplies one coherent path
tower over that same mild occurrence.  The existing physical momentum owner packages the result
as a real classical restart carrier.  Exact inverse-Fourier reconstruction identifies its initial
field with the addressed source trace.

Joint spacetime Fourier reconstruction is composed below once its independent bounded evaluation
owner is available; no smoothness receipt is postulated here.
-/

noncomputable section

open Function Set

namespace Soma.Holonics.Millennium.NavierStokesWeightedClassicalRestartSupply

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCoordinateH3FrequencyComb
open Soma.Holonics.Millennium.NavierStokesCoordinateNativeMildRestart
open Soma.Holonics.Millennium.NavierStokesCoordinateWeightedRestartCap
open Soma.Holonics.Millennium.NavierStokesCriticalContinuation
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedTower
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesUniformRestart
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesWeightedClassicalRestartCarrier
open Soma.Holonics.Millennium.NavierStokesWeightedFiniteApertureHigherOrderPersistence
open Soma.Holonics.Millennium.NavierStokesWeightedFiniteOrderFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedRestartAperture
open Soma.Holonics.Millennium.NavierStokesWeightedSmoothSliceReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-- Every controlled interior source face returns the complete weighted classical carrier on the
common cap-selected aperture. -/
noncomputable def weightedClassicalRestartCarrierOfUniformCoordinateBound
    {T a nu bound : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (haT : a < T)
    (uniform : UniformOpenHighOrderBound T a
      (coordinateLogH3Receiver velocity) bound)
    (t : ℝ) (ht : t ∈ Ico a T) :
    WeightedClassicalRestartCarrier nu (coordinateWeightedRestartCap bound) hnu
      (coordinateWeightedRestartCap_nonneg solution ha haT uniform)
      (interiorSliceWeightedH3 solution ⟨ha.trans_le ht.1, ht.2⟩) := by
  let hinterior : t ∈ Ioo (0 : ℝ) T := ⟨ha.trans_le ht.1, ht.2⟩
  let u : InitialVelocity := fun x ↦ velocity x t
  let hu := openPeriodicSolutionOn_velocitySlice_contDiff solution hinterior
  let hperiodic : IsOnePeriodic u :=
    solution.velocityPeriodic t ⟨hinterior.1.le, hinterior.2⟩
  let initialTower : CompatibleNativeWeightedSobolevTower :=
    smoothSliceCompatibleNativeWeightedSobolevTower u hu hperiodic
  let native := nativeMildRestartOfUniformCoordinateBound
    solution hnu ha haT uniform t ht
  have hbase : initialTower.base =
      interiorSliceWeightedH3 solution hinterior := by
    rfl
  have hnativeFixed : IsFixedPt
      (weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu)
        (weightedRestartTimeFromCap_pos hnu
          (coordinateWeightedRestartCap_nonneg solution ha haT uniform)).le
        initialTower.base) native.path := by
    rw [hbase]
    simpa only [weightedMildRestartMap] using native.fixed
  let towerWitness := exists_coherentWeightedSmoothPathTower_of_nativeFixed
      hnu
      (weightedRestartTimeFromCap_pos hnu
        (coordinateWeightedRestartCap_nonneg solution ha haT uniform)).le
      initialTower native.path hnativeFixed
  let tower := Classical.choose towerWitness
  exact weightedClassicalRestartCarrierOfNative
    hnu (coordinateWeightedRestartCap_nonneg solution ha haT uniform)
    (interiorSliceWeightedH3 solution hinterior) native tower

/-- The physical initial field carried by the selected restart is exactly the original solution
trace at its addressed source time. -/
theorem weightedClassicalRestartInitial_interiorSliceWeightedH3
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    weightedClassicalRestartInitial (interiorSliceWeightedH3 solution ht) =
      velocityTrace velocity t := by
  unfold weightedClassicalRestartInitial interiorSliceWeightedH3 velocityTrace
  exact reconstructedVelocity_smoothSliceVectorWeightedH3
    (fun x ↦ velocity x t)
    (openPeriodicSolutionOn_velocitySlice_contDiff solution ht)
    (solution.velocityPeriodic t ⟨ht.1.le, ht.2⟩)

section Audit

#print axioms weightedClassicalRestartCarrierOfUniformCoordinateBound
#print axioms weightedClassicalRestartInitial_interiorSliceWeightedH3

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedClassicalRestartSupply
