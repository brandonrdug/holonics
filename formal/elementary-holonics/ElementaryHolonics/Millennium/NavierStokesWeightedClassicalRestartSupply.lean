import ElementaryHolonics.Millennium.NavierStokesCoordinateNativeMildRestart
import ElementaryHolonics.Millennium.NavierStokesSmoothSliceWeightedTower
import ElementaryHolonics.Millennium.NavierStokesWeightedClassicalRestartCarrier
import ElementaryHolonics.Millennium.NavierStokesWeightedFiniteApertureHigherOrderPersistence
import ElementaryHolonics.Millennium.NavierStokesWeightedJointFourierFiniteSmoothness
import ElementaryHolonics.Millennium.NavierStokesWeightedPressureSmoothTower
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
open scoped NNReal

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
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedJointFourierFiniteSmoothness
open Soma.Holonics.Millennium.NavierStokesWeightedJointSmoothnessScale
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedOrderRestriction
open Soma.Holonics.Millennium.NavierStokesWeightedPathInvariants
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedPressureReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedPressureSmoothTower
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedRestartAperture
open Soma.Holonics.Millennium.NavierStokesWeightedSmoothPathTower
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

/-! ## Joint smoothness of the exact reconstructed carrier -/

/-- The existing all-order pressure path and parameterized Fourier evaluation passage reconstruct
the actual zero-gauge pressure jointly `C∞`.  No new summability estimate occurs here: each finite
receiver uses the already proved high-order evaluation theorem and the matching diagonal pressure
lift, then returns to the original pressure by exact order restriction. -/
theorem contDiffOn_joint_weightedReconstructedPressure_order
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base) (r : ℕ) :
    ContDiffOn ℝ r
      (fun z : Space × ℝ ↦
        weightedReconstructedPressure hT base z.2 z.1)
      (openSpaceTimeSlab T) := by
  let pressureTower := pressureDiagonalSmoothPathTower tower
  have hpath : ContDiffOn ℝ r
      (fun t : ℝ ↦ smoothTowerLiftExtension hT pressureTower (r + 3) t)
      (Ico (0 : ℝ) T) := by
    have hinfty := contDiffOn_infty_pressureDiagonalLiftExtension_Ico
      hT tower nu hnu initial hfixed hreal (r + 3)
    rw [contDiffOn_infty] at hinfty
    exact hinfty r
  have hhigh := contDiffOn_joint_reconstructedHigherOrderVelocity r
    (fun t : ℝ ↦ smoothTowerLiftExtension hT pressureTower (r + 3) t)
    hpath
  have hcomponent : ContDiffOn ℝ r
      (fun z : Space × ℝ ↦
        reconstructedHigherOrderVelocity (r + 3)
          (smoothTowerLiftExtension hT pressureTower (r + 3) z.2) z.1 0)
      (Set.univ ×ˢ Ico (0 : ℝ) T) := by
    rw [contDiffOn_piLp] at hhigh
    exact hhigh 0
  rw [openSpaceTimeSlab, openTimeSlab]
  apply hcomponent.congr
  rintro z hz
  have htIcc : z.2 ∈ Icc (0 : ℝ) T := ⟨hz.2.1, hz.2.2.le⟩
  have hlift :
      smoothTowerLiftExtension hT pressureTower (r + 3) z.2 =
        pressureTower.lift (r + 3) ⟨z.2, htIcc⟩ := by
    change pressureTower.lift (r + 3) (Set.projIcc 0 T hT z.2) = _
    congr 1
    apply Subtype.ext
    simp [Set.projIcc, htIcc.1, htIcc.2]
  let highState := smoothTowerLiftExtension hT pressureTower (r + 3) z.2
  let lowState := periodicVectorWeightedSobolevRestrictCLM
    3 (r + 3 + 3) (by omega) highState
  have hreconstruct :
      reconstructedHigherOrderVelocity (r + 3) highState =
        reconstructedVelocity lowState :=
    reconstructedHigherOrderVelocity_eq_reconstructedVelocity_restrict
      (r + 3) highState
  have hrestrict : lowState = pressureDiagonalBasePath tower ⟨z.2, htIcc⟩ := by
    dsimp only [lowState, highState]
    rw [hlift]
    exact pressureTower.restrict_lift (r + 3) ⟨z.2, htIcc⟩
  symm
  calc
    (reconstructedHigherOrderVelocity (r + 3) highState z.1) 0 =
        (reconstructedVelocity lowState z.1) 0 :=
      congrArg (fun v : Space ↦ v 0) (congrFun hreconstruct z.1)
    _ = (reconstructedVelocity
          (pressureDiagonalBasePath tower ⟨z.2, htIcc⟩) z.1) 0 := by
      rw [hrestrict]
    _ = pressureTower.reconstructedVelocity ⟨z.2, htIcc⟩ z.1 0 := by
      rw [pressureTower.reconstructedVelocity_eq_base]
    _ = weightedReconstructedPressure hT base z.2 z.1 :=
      reconstructedVelocity_pressureDiagonal_eq_pressure
        hT tower ⟨z.2, htIcc⟩ z.1

/-- All finite pressure receivers are compatible, hence the exact reconstructed pressure is
jointly `C∞` on the native half-open aperture. -/
theorem contDiffOn_infty_joint_weightedReconstructedPressure
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base) :
    ContDiffOn ℝ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞)
      (fun z : Space × ℝ ↦
        weightedReconstructedPressure hT base z.2 z.1)
      (openSpaceTimeSlab T) := by
  rw [contDiffOn_infty]
  exact contDiffOn_joint_weightedReconstructedPressure_order
    hT tower nu hnu initial hfixed hreal

/-- The coherent cap-selected weighted carrier supplies both fields of the official joint
spacetime smoothness upgrade. -/
noncomputable def jointSpacetimeSmoothnessUpgradeOfWeightedClassicalRestartCarrier
    {nu cap : ℝ} {hnu : 0 < nu} {hcap : 0 ≤ cap}
    {initial : PeriodicVectorWeightedSobolev 3}
    (carrier : WeightedClassicalRestartCarrier nu cap hnu hcap initial) :
    JointSpacetimeSmoothnessUpgrade carrier.classical := by
  let hT : 0 ≤ weightedRestartTimeFromCap nu cap :=
    (weightedRestartTimeFromCap_pos hnu hcap).le
  have hfixed : IsFixedPt
      (weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu) hT initial)
      carrier.path := by
    simpa only [weightedMildRestartMap] using carrier.fixed
  refine
    { velocitySmooth := ?_
      pressureSmooth := ?_ }
  · change ContDiffOn ℝ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞)
      (fun z : Space × ℝ ↦
        NavierStokesWeightedMildSpacetimeMomentum.weightedReconstructedVelocity
          hT carrier.path z.2 z.1)
      (openSpaceTimeSlab (weightedRestartTimeFromCap nu cap))
    exact contDiffOn_infty_joint_weightedReconstructedVelocity
      hT carrier.tower (Real.toNNReal nu) (real_toNNReal_pos hnu)
      initial hfixed carrier.fourierReal
  · change ContDiffOn ℝ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞)
      (fun z : Space × ℝ ↦
        weightedReconstructedPressure hT carrier.path z.2 z.1)
      (openSpaceTimeSlab (weightedRestartTimeFromCap nu cap))
    exact contDiffOn_infty_joint_weightedReconstructedPressure
      hT carrier.tower (Real.toNNReal nu) (real_toNNReal_pos hnu)
      initial hfixed carrier.fourierReal

/-! ## The official one-face restart adapter -/

/-- The cap-selected classical carrier returns the corresponding official interior restart.
This adapter changes neither the selected native path nor its pressure gauge: it only transports
the proved joint smoothness, exact source-trace equality, and the definitional identity
`shiftVelocityField 0 = 0` across the official restart interface. -/
noncomputable def interiorPeriodicRestartOfUniformCoordinateBound
    {T a nu bound : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (haT : a < T)
    (uniform : UniformOpenHighOrderBound T a
      (coordinateLogH3Receiver velocity) bound)
    (t : ℝ) (ht : t ∈ Ico a T) :
    InteriorPeriodicRestart solution t
      (weightedRestartTimeFromCap nu (coordinateWeightedRestartCap bound)) := by
  let hinterior : t ∈ Ioo (0 : ℝ) T :=
    ⟨ha.trans_le ht.1, ht.2⟩
  let carrier := weightedClassicalRestartCarrierOfUniformCoordinateBound
    solution hnu ha haT uniform t ht
  have hlocal := carrier.toOpenPeriodicSolutionOn
    (jointSpacetimeSmoothnessUpgradeOfWeightedClassicalRestartCarrier carrier)
  refine
    { interior := ⟨hinterior.1.le, hinterior.2⟩
      radius_pos := weightedRestartTimeFromCap_pos hnu
        (coordinateWeightedRestartCap_nonneg solution ha haT uniform)
      restartVelocity := weightedClassicalRestartVelocity
        (weightedRestartTimeFromCap_pos hnu
          (coordinateWeightedRestartCap_nonneg solution ha haT uniform)).le
        carrier.path
      restartPressure := weightedClassicalRestartPressure
        (weightedRestartTimeFromCap_pos hnu
          (coordinateWeightedRestartCap_nonneg solution ha haT uniform)).le
        carrier.path
      restartSolution := ?_ }
  have hinitial := weightedClassicalRestartInitial_interiorSliceWeightedH3
    solution hinterior
  have hforce : shiftVelocityField (0 : VelocityField) t = 0 := by
    funext x τ
    rfl
  rw [hforce]
  simpa only [hinitial] using hlocal

/-- A single uniform coordinate bound therefore supplies one common cap-selected restart radius
at every controlled tail face. -/
noncomputable def tailUniformInteriorRestartSupplyOfUniformCoordinateBound
    {T a nu bound : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (haT : a < T)
    (uniform : UniformOpenHighOrderBound T a
      (coordinateLogH3Receiver velocity) bound) :
    TailUniformInteriorRestartSupply solution a where
  radius := weightedRestartTimeFromCap nu (coordinateWeightedRestartCap bound)
  radius_pos := weightedRestartTimeFromCap_pos hnu
    (coordinateWeightedRestartCap_nonneg solution ha haT uniform)
  restart := fun t ht ↦
    interiorPeriodicRestartOfUniformCoordinateBound
      solution hnu ha haT uniform t ht

/-- Uniform coordinate high-order control supplies the official common-radius restart family on
the whole addressed tail. -/
noncomputable def restartSupplyFromUniformCoordinateBound
    {T a nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (haT : a < T) :
    RestartSupplyFromUniformHighOrderBound solution a
      (coordinateLogH3Receiver velocity) where
  supply := fun {_bound} uniform ↦
    tailUniformInteriorRestartSupplyOfUniformCoordinateBound
      solution hnu ha haT uniform

section Audit

#print axioms weightedClassicalRestartCarrierOfUniformCoordinateBound
#print axioms weightedClassicalRestartInitial_interiorSliceWeightedH3
#print axioms contDiffOn_infty_joint_weightedReconstructedPressure
#print axioms jointSpacetimeSmoothnessUpgradeOfWeightedClassicalRestartCarrier
#print axioms interiorPeriodicRestartOfUniformCoordinateBound
#print axioms tailUniformInteriorRestartSupplyOfUniformCoordinateBound
#print axioms restartSupplyFromUniformCoordinateBound

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedClassicalRestartSupply
