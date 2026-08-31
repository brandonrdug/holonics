import ElementaryHolonics.Millennium.NavierStokesOfficialBridge
import ElementaryHolonics.Millennium.NavierStokesWeightedClassicalRestartSupply

/-!
# Unconditional periodic local existence

**[proved-derived; formal-checked]** Every smooth, divergence-free, one-periodic initial velocity
at positive viscosity supplies an actual unforced `OpenPeriodicSolutionOn` on a strictly positive
half-open lifespan.  The construction uses the existing weighted H³ realization of the initial
slice, its compatible all-order Sobolev tower, the invariant native mild fixed point at cap
`‖base‖`, finite-aperture higher-order persistence, the real classical carrier, and the proved
joint spacetime smoothness upgrade.  Exact inverse-Fourier reconstruction rebases the carrier's
physical initial field to the given initial velocity.

This module discharges only `HasPeriodicLocalExistence`.  It asserts neither terminal control nor
a cofinal or global periodic solution.
-/

noncomputable section

open Function Set
open scoped NNReal

namespace Soma.Holonics.Millennium.NavierStokesPeriodicLocalExistence

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCoordinateNativeMildRestart
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesOfficialBridge
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedTower
open Soma.Holonics.Millennium.NavierStokesWeightedClassicalRestartCarrier
open Soma.Holonics.Millennium.NavierStokesWeightedClassicalRestartSupply
open Soma.Holonics.Millennium.NavierStokesWeightedDivergenceFree
open Soma.Holonics.Millennium.NavierStokesWeightedFiniteApertureHigherOrderPersistence
open Soma.Holonics.Millennium.NavierStokesWeightedFiniteOrderFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedPathInvariants
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedRestartAperture
open Soma.Holonics.Millennium.NavierStokesWeightedSmoothSliceReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-- **[proved-derived; formal-checked]** Positive-viscosity local existence in the exact official
open-lifespan carrier, for every datum satisfying `InitialVelocityConditionPeriodic`. -/
theorem periodicLocalExistence : HasPeriodicLocalExistence := by
  intro nu hnu initial hinitial
  let base : PeriodicVectorWeightedSobolev 3 :=
    smoothSliceVectorWeightedH3 initial hinitial.smooth hinitial.periodic
  let cap : ℝ := ‖base‖
  have hcap : 0 ≤ cap := norm_nonneg base
  have hbaseReal : IsWeightedFourierReal 3 base := by
    dsimp only [base]
    exact isWeightedFourierReal_smoothSliceVectorWeightedH3
      initial hinitial.smooth hinitial.periodic
  have hbaseDivergenceFree : IsModewiseDivergenceFree base := by
    dsimp only [base]
    exact isModewiseDivergenceFree_smoothSliceVectorWeightedH3
      initial hinitial.smooth hinitial.periodic hinitial.divergenceFree
  let restart : NativeMildRestartAtCap nu cap hnu hcap base :=
    nativeMildRestartAtCap hnu hcap base le_rfl hbaseReal hbaseDivergenceFree
  let initialTower : CompatibleNativeWeightedSobolevTower :=
    smoothSliceCompatibleNativeWeightedSobolevTower
      initial hinitial.smooth hinitial.periodic
  have hbase : initialTower.base = base := by
    rfl
  have hrestartFixed : IsFixedPt
      (weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu)
        (weightedRestartTimeFromCap_pos hnu hcap).le initialTower.base) restart.path := by
    rw [hbase]
    simpa only [weightedMildRestartMap] using restart.fixed
  let towerWitness := exists_coherentWeightedSmoothPathTower_of_nativeFixed
    hnu (weightedRestartTimeFromCap_pos hnu hcap).le
    initialTower restart.path hrestartFixed
  let tower := Classical.choose towerWitness
  let carrier := weightedClassicalRestartCarrierOfNative
    hnu hcap base restart tower
  let solution := carrier.toOpenPeriodicSolutionOn
    (jointSpacetimeSmoothnessUpgradeOfWeightedClassicalRestartCarrier carrier)
  have hreconstruct : weightedClassicalRestartInitial base = initial := by
    unfold weightedClassicalRestartInitial
    dsimp only [base]
    exact reconstructedVelocity_smoothSliceVectorWeightedH3
      initial hinitial.smooth hinitial.periodic
  refine ⟨weightedRestartTimeFromCap nu cap,
    weightedClassicalRestartVelocity
      (weightedRestartTimeFromCap_pos hnu hcap).le carrier.path,
    weightedClassicalRestartPressure
      (weightedRestartTimeFromCap_pos hnu hcap).le carrier.path,
    weightedRestartTimeFromCap_pos hnu hcap, ?_⟩
  simpa only [hreconstruct] using solution

section Audit

#print axioms periodicLocalExistence

end Audit

end Soma.Holonics.Millennium.NavierStokesPeriodicLocalExistence
