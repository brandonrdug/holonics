import ElementaryHolonics.Millennium.NavierStokesTransportedPantographicSwingChain
import ElementaryHolonics.Millennium.NavierStokesDyadicShellProjectors

/-!
# Phase-bearing torus bands of the transported pantographic source swing

**[proved-derived; formal-checked]**  The transported source-swing owner reconstructs each
Fourier coefficient before a norm is taken.  This module lifts that exact identity through an
arbitrary finite frequency aperture and reconstructs the complete signed band on the genuine
spatial torus.

The nonlinear mild band is exactly the negative of three separately retained band populations:
the finite pantographic swing chain, its finite-depth residual, and the frozen target-source
boundary action.  Characters, phases, frequency addresses, and the spatial receiver all remain
present.  Thus a later phase-local Dini or Carleson estimate can act on the actual transported
PDE band rather than on detached coefficient masses.

No band norm, cross-scale summability, terminal-uniform estimate, or terminal control is asserted.
-/

noncomputable section

open MeasureTheory Set
open scoped Interval Topology

namespace Soma.Holonics.Millennium.NavierStokesTransportedPantographicSwingBand

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCriticalMildReceiver
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFrozenSharpSourceBoundary
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesTransportedPantographicSwingChain
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity

/-! ## The four signed coefficient populations -/

/-- Source-time Duhamel coefficient of the actual nonlinear vorticity history. -/
def compactMildSourceIntegratedCoefficient
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (k : SpatialFrequency) : ComplexVector :=
  ∫ sourceTime in s..t,
    compactStokesTransportedVorticityNonlinearMode
      solution hs hst ht k sourceTime

/-- Elapsed integral of the finite signed pantographic swing chain. -/
def compactPantographicPartialChainIntegratedCoefficient
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (depth : ℕ) (k : SpatialFrequency) : ComplexVector :=
  ∫ elapsed in 0..(t - s),
    transportedCompactElapsedSharpPantographicPartialChainCoefficient
      solution (by simpa only [sub_sub_cancel] using hs) ht
        (sub_nonneg.mpr hst) depth k elapsed

/-- Elapsed integral of the explicitly retained finite-depth residual. -/
def compactPantographicResidualIntegratedCoefficient
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (depth : ℕ) (k : SpatialFrequency) : ComplexVector :=
  ∫ elapsed in 0..(t - s),
    transportedCompactElapsedSharpPantographicResidualCoefficient
      solution (by simpa only [sub_sub_cancel] using hs) ht
        (sub_nonneg.mpr hst) depth k elapsed

/-- Frozen target-source boundary coefficient after exact heat/curl elapsed integration. -/
def compactPantographicFrozenBoundaryCoefficient
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (k : SpatialFrequency) : ComplexVector :=
  frozenH2SourceCurlBoundaryAction nu (t - s)
    (compactElapsedOpenSharpTargetSource solution
      (by simpa only [sub_sub_cancel] using hs) ht
      (sub_nonneg.mpr hst)) k

/-! ## Genuine-torus finite band synthesis -/

/-- Heat-transported actual vorticity coefficient on the earlier face of the compact interval. -/
def compactInitialVorticityHeatCoefficient
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (k : SpatialFrequency) : ComplexVector :=
  heatStokesMultiplier nu (t - s) k •
    openPeriodicVorticityFourierMode solution
      ⟨s, hs, hst.trans_lt ht⟩ k

/-- Phase-bearing synthesis of the heat-transported earlier vorticity face. -/
def compactInitialVorticityHeatBand
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (modes : Finset SpatialFrequency) : C(SpatialTorus, ComplexVector) :=
  finiteFourierSynthesis
    (compactInitialVorticityHeatCoefficient solution hs hst ht) modes

/-- Actual source-time mild band on one declared lattice aperture. -/
def compactMildSourceIntegratedBand
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (modes : Finset SpatialFrequency) : C(SpatialTorus, ComplexVector) :=
  finiteFourierSynthesis
    (compactMildSourceIntegratedCoefficient solution hs hst ht) modes

/-- Phase-bearing synthesis of the integrated finite swing chain. -/
def compactPantographicPartialChainIntegratedBand
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (depth : ℕ) (modes : Finset SpatialFrequency) :
    C(SpatialTorus, ComplexVector) :=
  finiteFourierSynthesis
    (compactPantographicPartialChainIntegratedCoefficient
      solution hs hst ht depth) modes

/-- Phase-bearing synthesis of the finite-depth reconstruction residual. -/
def compactPantographicResidualIntegratedBand
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (depth : ℕ) (modes : Finset SpatialFrequency) :
    C(SpatialTorus, ComplexVector) :=
  finiteFourierSynthesis
    (compactPantographicResidualIntegratedCoefficient
      solution hs hst ht depth) modes

/-- Phase-bearing synthesis of the frozen target-source boundary action. -/
def compactPantographicFrozenBoundaryBand
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (modes : Finset SpatialFrequency) : C(SpatialTorus, ComplexVector) :=
  finiteFourierSynthesis
    (compactPantographicFrozenBoundaryCoefficient solution hs hst ht) modes

/-! ## Exact phase-bearing transported return -/

/-- Every coefficient of the actual nonlinear history is the negative transported swing chain,
residual, and frozen boundary population. -/
theorem compactMildSourceIntegratedCoefficient_eq_neg_chain_add_residual_add_boundary
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (depth : ℕ) (k : SpatialFrequency) :
    compactMildSourceIntegratedCoefficient solution hs hst ht k =
      -(compactPantographicPartialChainIntegratedCoefficient
          solution hs hst ht depth k +
        compactPantographicResidualIntegratedCoefficient
          solution hs hst ht depth k +
        compactPantographicFrozenBoundaryCoefficient solution hs hst ht k) := by
  exact
    intervalIntegral_compactStokesTransportedVorticityNonlinearMode_eq_neg_chain_add_residual_add_boundary
      solution hnu hs hst ht depth k

/-- The actual final vorticity coefficient is the retained earlier heat face plus the exact
source-time mild coefficient. -/
theorem openPeriodicVorticityFourierMode_eq_initialHeat_add_mildSource
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (k : SpatialFrequency) :
    openPeriodicVorticityFourierMode solution
        ⟨t, hs.trans_le hst, ht⟩ k =
      compactInitialVorticityHeatCoefficient solution hs hst ht k +
        compactMildSourceIntegratedCoefficient solution hs hst ht k := by
  rw [← frequencyCurlMultiplier_velocityMode_eq_openPeriodicVorticityFourierMode
    solution ⟨t, hs.trans_le hst, ht⟩ k]
  rw [openPeriodicSolutionOn_vorticityMode_mild_identity solution hs hst ht k]
  rw [frequencyCurlMultiplier_velocityMode_eq_openPeriodicVorticityFourierMode
    solution ⟨s, hs, hst.trans_lt ht⟩ k]
  rfl

/-- Finite synthesis carries the exact mild identity to the actual phase-bearing vorticity band. -/
theorem openPeriodicVorticityBandProjector_eq_initialHeat_add_mildSource
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (modes : Finset SpatialFrequency) :
    openPeriodicVorticityBandProjector solution
        ⟨t, hs.trans_le hst, ht⟩ modes =
      compactInitialVorticityHeatBand solution hs hst ht modes +
        compactMildSourceIntegratedBand solution hs hst ht modes := by
  apply ContinuousMap.ext
  intro q
  unfold openPeriodicVorticityBandProjector compactInitialVorticityHeatBand
    compactMildSourceIntegratedBand finiteFourierSynthesis
  simp_rw [openPeriodicVorticityFourierMode_eq_initialHeat_add_mildSource
    solution hs hst ht]
  simp only [smul_add, Finset.sum_add_distrib, ContinuousMap.add_apply]
  rfl

/-- **Exact transported pantographic swing band.**  Finite torus synthesis preserves the entire
signed coefficient identity.  Phase interaction occurs only after the chain, residual, and
boundary incidences have been transported to the same spatial receiver. -/
theorem compactMildSourceIntegratedBand_eq_neg_chain_add_residual_add_boundary
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (depth : ℕ) (modes : Finset SpatialFrequency) :
    compactMildSourceIntegratedBand solution hs hst ht modes =
      -(compactPantographicPartialChainIntegratedBand
          solution hs hst ht depth modes +
        compactPantographicResidualIntegratedBand
          solution hs hst ht depth modes +
        compactPantographicFrozenBoundaryBand solution hs hst ht modes) := by
  apply ContinuousMap.ext
  intro q
  unfold compactMildSourceIntegratedBand
    compactPantographicPartialChainIntegratedBand
    compactPantographicResidualIntegratedBand
    compactPantographicFrozenBoundaryBand
    finiteFourierSynthesis
  simp only [ContinuousMap.coe_mk, ContinuousMap.neg_apply,
    ContinuousMap.add_apply]
  simp_rw [compactMildSourceIntegratedCoefficient_eq_neg_chain_add_residual_add_boundary
    solution hnu hs hst ht depth]
  simp only [smul_neg, smul_add, Finset.sum_neg_distrib,
    Finset.sum_add_distrib]

/-- **Actual dyadic pantographic swing band.**  On every finite aperture—and therefore on each
declared dyadic shell—the actual vorticity band is its earlier heat face minus the transported
finite swing chain, retained residual, and frozen boundary population.  This is the exact PDE
identity to which a phase-local coherence or Carleson estimate must be applied. -/
theorem openPeriodicVorticityBandProjector_eq_initialHeat_sub_pantographicPopulation
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (depth : ℕ) (modes : Finset SpatialFrequency) :
    openPeriodicVorticityBandProjector solution
        ⟨t, hs.trans_le hst, ht⟩ modes =
      compactInitialVorticityHeatBand solution hs hst ht modes -
        (compactPantographicPartialChainIntegratedBand
            solution hs hst ht depth modes +
          compactPantographicResidualIntegratedBand
            solution hs hst ht depth modes +
          compactPantographicFrozenBoundaryBand solution hs hst ht modes) := by
  rw [openPeriodicVorticityBandProjector_eq_initialHeat_add_mildSource
    solution hs hst ht modes]
  rw [compactMildSourceIntegratedBand_eq_neg_chain_add_residual_add_boundary
    solution hnu hs hst ht depth modes]
  rfl

section Audit

#print axioms compactMildSourceIntegratedCoefficient_eq_neg_chain_add_residual_add_boundary
#print axioms openPeriodicVorticityFourierMode_eq_initialHeat_add_mildSource
#print axioms openPeriodicVorticityBandProjector_eq_initialHeat_add_mildSource
#print axioms compactMildSourceIntegratedBand_eq_neg_chain_add_residual_add_boundary
#print axioms openPeriodicVorticityBandProjector_eq_initialHeat_sub_pantographicPopulation

end Audit

end Soma.Holonics.Millennium.NavierStokesTransportedPantographicSwingBand
