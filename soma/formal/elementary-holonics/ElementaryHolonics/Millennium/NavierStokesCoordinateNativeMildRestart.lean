import ElementaryHolonics.Millennium.NavierStokesCoordinateWeightedRestartCap
import ElementaryHolonics.Millennium.NavierStokesWeightedMildInvariantRestart

/-!
# The coordinate receiver returns a family of native physical-fibre mild restarts

**[proved-derived]** The differentiated coordinate receiver already supplies one native `H³` cap
and one common positive viscous aperture for every controlled interior slice.  This owner attaches
the actual invariant mild fixed-point return to each such slice.  The resulting path retains its
source occurrence, cap-ball receipt, exact fixed equation, Fourier reality, and modewise
incompressibility.

This is the native coefficient restart family required before spatial reconstruction.  It is not
an `InteriorPeriodicRestart`: smooth inverse-Fourier reconstruction, pressure, and the classical
PDE carrier remain separate open returns.
-/

noncomputable section

open Function Set

namespace Soma.Holonics.Millennium.NavierStokesCoordinateNativeMildRestart

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCoordinateH3FrequencyComb
open Soma.Holonics.Millennium.NavierStokesCoordinateWeightedRestartCap
open Soma.Holonics.Millennium.NavierStokesCriticalContinuation
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedDivergenceFree
open Soma.Holonics.Millennium.NavierStokesWeightedMildInvariantRestart
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedPathInvariants
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedRestartAperture
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-- One native mild restart occurrence at the common cap-selected aperture. -/
structure NativeMildRestartAtCap
    (nu cap : ℝ) (hnu : 0 < nu) (hcap : 0 ≤ cap)
    (initial : PeriodicVectorWeightedSobolev 3) where
  path : WeightedH3Path (weightedRestartTimeFromCap nu cap)
  pathNorm : ‖path‖ ≤ weightedRestartRadiusFromCap cap
  fixed : IsFixedPt (weightedMildRestartMap nu cap hnu hcap initial) path
  initialFace :
    path ⟨0, ⟨le_rfl, (weightedRestartTimeFromCap_pos hnu hcap).le⟩⟩ = initial
  fourierReal : IsWeightedFourierRealPath path
  divergenceFree : IsWeightedDivergenceFreePath path

/-- The already constructed invariant fixed point packages as one addressed native restart. -/
noncomputable def nativeMildRestartAtCap
    {nu cap : ℝ} (hnu : 0 < nu) (hcap : 0 ≤ cap)
    (initial : PeriodicVectorWeightedSobolev 3) (hinitialNorm : ‖initial‖ ≤ cap)
    (hinitialReal : IsWeightedFourierReal 3 initial)
    (hinitialDivergenceFree : IsModewiseDivergenceFree initial) :
    NativeMildRestartAtCap nu cap hnu hcap initial :=
  let witness :=
    exists_weightedMildInvariantRestart_fixedPoint hnu hcap initial hinitialNorm
      hinitialReal hinitialDivergenceFree
  let path := Classical.choose witness
  let receipt := Classical.choose_spec witness
  { path := path
    pathNorm := receipt.1
    fixed := receipt.2.1
    initialFace := receipt.2.2.1
    fourierReal := receipt.2.2.2.1
    divergenceFree := receipt.2.2.2.2 }

/-! ## Actual interior-slice incidences -/

/-- Every actual incompressible interior slice enters the native carrier in the exact modewise
divergence-free fibre. -/
theorem interiorSliceWeightedH3_divergenceFree
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    IsModewiseDivergenceFree (interiorSliceWeightedH3 solution ht) := by
  exact isModewiseDivergenceFree_smoothSliceVectorWeightedH3
    (fun x ↦ velocity x t)
    (openPeriodicSolutionOn_velocitySlice_contDiff solution ht)
    (solution.velocityPeriodic t ⟨ht.1.le, ht.2⟩)
    (fun x ↦ solution.incompressible x t ⟨ht.1.le, ht.2⟩)

/-- Every actual interior slice also enters the exact Fourier-real fibre. -/
theorem interiorSliceWeightedH3_fourierReal
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    IsWeightedFourierReal 3 (interiorSliceWeightedH3 solution ht) := by
  exact openPeriodicSolutionOn_isWeightedFourierReal_slice solution ht

/-! ## The familywise coordinate-to-mild return -/

/-- A uniform coordinate receiver bound returns an actual native physical-fibre mild restart at
every controlled tail occurrence, all with the same cap-selected time aperture. -/
noncomputable def nativeMildRestartOfUniformCoordinateBound
    {T a nu bound : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (haT : a < T)
    (uniform : UniformOpenHighOrderBound T a
      (coordinateLogH3Receiver velocity) bound)
    (t : ℝ) (ht : t ∈ Ico a T) :
    NativeMildRestartAtCap nu (coordinateWeightedRestartCap bound) hnu
      (coordinateWeightedRestartCap_nonneg solution ha haT uniform)
      (interiorSliceWeightedH3 solution ⟨ha.trans_le ht.1, ht.2⟩) := by
  let hinterior : t ∈ Ioo 0 T := ⟨ha.trans_le ht.1, ht.2⟩
  exact nativeMildRestartAtCap hnu
    (coordinateWeightedRestartCap_nonneg solution ha haT uniform)
    (interiorSliceWeightedH3 solution hinterior)
    (norm_interiorSliceWeightedH3_le_cap solution ha uniform ht)
    (interiorSliceWeightedH3_fourierReal solution hinterior)
    (interiorSliceWeightedH3_divergenceFree solution hinterior)

/-- The preceding family has one strictly positive common local aperture, independent of the
chosen interior time face. -/
theorem nativeMildRestartOfUniformCoordinateBound_commonTime_pos
    {T a nu bound : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (haT : a < T)
    (uniform : UniformOpenHighOrderBound T a
      (coordinateLogH3Receiver velocity) bound) :
    0 < weightedRestartTimeFromCap nu (coordinateWeightedRestartCap bound) :=
  coordinateWeightedRestartTime_pos solution hnu ha haT uniform

section Audit

#print axioms nativeMildRestartAtCap
#print axioms interiorSliceWeightedH3_divergenceFree
#print axioms interiorSliceWeightedH3_fourierReal
#print axioms nativeMildRestartOfUniformCoordinateBound
#print axioms nativeMildRestartOfUniformCoordinateBound_commonTime_pos

end Audit

end Soma.Holonics.Millennium.NavierStokesCoordinateNativeMildRestart
