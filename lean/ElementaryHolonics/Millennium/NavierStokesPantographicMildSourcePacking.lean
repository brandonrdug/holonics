import ElementaryHolonics.Millennium.NavierStokesPantographicTerminalShellReduction

/-!
# The terminal pantographic packing is the nonlinear mild-source packing

**[proved-derived; formal-checked]**  The finite swing chain, its retained residual, and the
frozen source boundary are not three estimates.  Their combined signed torus band is exactly the
negative of the actual nonlinear mild Duhamel band.  Consequently its shell norm, shell
population, and extended-real terminal packing are independent of the chosen finite swing depth.

This identifies the one source-specific estimate still missing from terminal control: finiteness
of the `L¹`-in-time, `ℓ¹`-in-shell population of the signed nonlinear mild bands.  It does not
assert that this packing is finite.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology

namespace Soma.Holonics.Millennium.NavierStokesPantographicMildSourcePacking

set_option maxHeartbeats 1200000

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPantographicPhaseLocalShell
open Soma.Holonics.Millennium.NavierStokesPantographicTerminalShellReduction
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTransportedPantographicSwingBand

/-! ## Exact source identification -/

/-- Before any norm is taken, the complete finite-depth pantographic population is the negative
actual nonlinear mild-source band. -/
theorem compactPantographicIntegratedPopulationBand_eq_neg_mildSource
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (depth : ℕ) (modes : Finset SpatialFrequency) :
    compactPantographicIntegratedPopulationBand solution hs hst ht depth modes =
      -compactMildSourceIntegratedBand solution hs hst ht modes := by
  rw [compactMildSourceIntegratedBand_eq_neg_chain_add_residual_add_boundary
    solution hnu hs hst ht depth modes]
  simp only [neg_neg]
  rfl

/-- The norm of one combined pantographic shell is exactly the norm of the actual signed
nonlinear mild-source shell.  No componentwise triangle inequality occurs. -/
theorem norm_compactPantographicIntegratedPopulationBand_eq_mildSource
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (depth : ℕ) (modes : Finset SpatialFrequency) :
    ‖compactPantographicIntegratedPopulationBand solution hs hst ht depth modes‖ =
      ‖compactMildSourceIntegratedBand solution hs hst ht modes‖ := by
  rw [compactPantographicIntegratedPopulationBand_eq_neg_mildSource
    solution hnu hs hst ht depth modes, norm_neg]

/-! ## Shell and spacetime populations -/

/-- One shell of the actual signed nonlinear mild Duhamel population. -/
def compactMildSourceDyadicShellSpatialSup
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T) (level : ℕ) : ℝ :=
  ‖compactMildSourceIntegratedBand solution hs hst ht
    (dyadicFrequencyShell level)‖

theorem compactPantographicDyadicShellSpatialSup_eq_mildSource
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (depth level : ℕ) :
    compactPantographicDyadicShellSpatialSup solution hs hst ht depth level =
      compactMildSourceDyadicShellSpatialSup solution hs hst ht level := by
  exact norm_compactPantographicIntegratedPopulationBand_eq_mildSource
    solution hnu hs hst ht depth (dyadicFrequencyShell level)

/-- Complete shell population of the actual nonlinear mild source at one terminal-tail time. -/
def compactMildSourceDyadicShellPopulationOn
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (t : Ioo s T) : ℝ :=
  ∑' level : ℕ,
    compactMildSourceDyadicShellSpatialSup solution hs t.2.1.le t.2.2 level

/-- At each strict terminal-tail time the complete pantographic shell population is exactly the
nonlinear mild-source shell population, independently of finite swing depth. -/
theorem compactPantographicDyadicShellPopulationOn_eq_mildSource
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (depth : ℕ) (t : Ioo s T) :
    compactPantographicDyadicShellPopulationOn solution hs depth t =
      compactMildSourceDyadicShellPopulationOn solution hs t := by
  apply tsum_congr
  intro level
  exact compactPantographicDyadicShellSpatialSup_eq_mildSource
    solution hnu hs t.2.1.le t.2.2 depth level

/-- Real-time totalization of the nonlinear mild-source shell population. -/
def compactMildSourceDyadicShellPopulation
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (t : ℝ) : ℝ :=
  if ht : t ∈ Ioo s T then
    compactMildSourceDyadicShellPopulationOn solution hs ⟨t, ht⟩
  else 0

theorem compactPantographicDyadicShellPopulation_eq_mildSource
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (depth : ℕ) (t : ℝ) :
    compactPantographicDyadicShellPopulation solution hs depth t =
      compactMildSourceDyadicShellPopulation solution hs t := by
  by_cases ht : t ∈ Ioo s T
  · simp only [compactPantographicDyadicShellPopulation,
      compactMildSourceDyadicShellPopulation, ht, dite_true]
    exact compactPantographicDyadicShellPopulationOn_eq_mildSource
      solution hnu hs depth ⟨t, ht⟩
  · simp [compactPantographicDyadicShellPopulation,
      compactMildSourceDyadicShellPopulation, ht]

/-- Divergence-safe terminal-tail packing of the actual signed nonlinear mild Duhamel bands. -/
def compactMildSourceTerminalShellPacking
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) : ℝ≥0∞ :=
  ∫⁻ t in Ioo s T,
    ENNReal.ofReal (compactMildSourceDyadicShellPopulation solution hs t) ∂volume

/-- The pantographic terminal packing is exactly the nonlinear mild-source packing and hence is
independent of finite swing depth.  Possible divergence remains visible as `∞`. -/
theorem compactPantographicTerminalShellPacking_eq_mildSource
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (depth : ℕ) :
    compactPantographicTerminalShellPacking solution hs depth =
      compactMildSourceTerminalShellPacking solution hs := by
  unfold compactPantographicTerminalShellPacking compactMildSourceTerminalShellPacking
  apply lintegral_congr
  intro t
  rw [compactPantographicDyadicShellPopulation_eq_mildSource
    solution hnu hs depth t]

theorem compactPantographicTerminalShellPacking_depth_independent
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (firstDepth secondDepth : ℕ) :
    compactPantographicTerminalShellPacking solution hs firstDepth =
      compactPantographicTerminalShellPacking solution hs secondDepth := by
  rw [compactPantographicTerminalShellPacking_eq_mildSource
      solution hnu hs firstDepth,
    compactPantographicTerminalShellPacking_eq_mildSource
      solution hnu hs secondDepth]

section Audit

#print axioms compactPantographicIntegratedPopulationBand_eq_neg_mildSource
#print axioms compactPantographicDyadicShellPopulationOn_eq_mildSource
#print axioms compactPantographicTerminalShellPacking_eq_mildSource
#print axioms compactPantographicTerminalShellPacking_depth_independent

end Audit

end Soma.Holonics.Millennium.NavierStokesPantographicMildSourcePacking
