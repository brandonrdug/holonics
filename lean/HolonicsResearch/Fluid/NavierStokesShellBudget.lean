import HolonicsResearch.Fluid.NavierStokesRelevanceBudget

/-!
# The shell budget: nested bands and the difference of frontier currents

For nested bands `F ⊆ G` the shell `G \ F` carries mass `E_G − E_F`, and its budget is the
difference of the two band budgets: it dissipates at `−2ν(D_G − D_F)` and exchanges through the
two frontiers, `2 Σ'_{k ∉ G} transfer − 2 Σ'_{k ∉ F} transfer`.  Its cumulative current is the
difference of the two cumulative currents.
-/

noncomputable section

open Set Filter Topology MeasureTheory intervalIntegral
open scoped Finset

namespace Holonics.Fluid.NavierStokesShellBudget

open Holonics.Fluid.NavierStokes
open Holonics.Fluid.NavierStokesOpenLifespan
open Holonics.Fluid.NavierStokesPeriodicEnergy
open Holonics.Fluid.NavierStokesPeriodicEnstrophy
open Holonics.Fluid.NavierStokesTorusVorticity
open Holonics.Fluid.NavierStokesTorusFourier
open Holonics.Fluid.NavierStokesDyadicShellProjectors
open Holonics.Fluid.NavierStokesVorticityDirectionCancellation
open Holonics.Fluid.NavierStokesVorticityDirectionRemainderBound
open Holonics.Fluid.NavierStokesVorticityDirectionFullStrain
open Holonics.Fluid.NavierStokesVorticityDirectionFiniteBandBridge
open Holonics.Fluid.NavierStokesVorticityDirectionPhysicalBridge
open Holonics.Fluid.NavierStokesVorticityDirectionBaseEnergy
open Holonics.Fluid.NavierStokesVorticityDirectionSourceModulus
open Holonics.Fluid.NavierStokesCoordinateJacobianFourierReconstruction
open Holonics.Fluid.NavierStokesH2StorageDissipationPayment
open Holonics.Fluid.NavierStokesAlignedStrainBudget
open Holonics.Fluid.NavierStokesModalRiccati
open Holonics.Fluid.NavierStokesHalfRadiusReach
open Holonics.Fluid.NavierStokesShellStepCost
open Holonics.Fluid.NavierStokesMomentSwap
open Holonics.Fluid.NavierStokesMomentGap
open Holonics.Fluid.NavierStokesYoungFeed
open Holonics.Fluid.NavierStokesYoungTsum
open Holonics.Fluid.NavierStokesWeightedTailEnergy
open Holonics.Fluid.NavierStokesIncoherentBandMass
open Holonics.Fluid.NavierStokesOpenAdvectionCarrierIntegration
open Holonics.Fluid.NavierStokesH3Production
open Holonics.Fluid.NavierStokesOpenAdvectionConvolutionBridge
open Holonics.Fluid.NavierStokesFourthMomentRiccati
open Holonics.Fluid.NavierStokesWeightedYoung
open Holonics.Fluid.NavierStokesMomentInterpolation
open Holonics.Fluid.NavierStokesSixthYoung
open Holonics.Fluid.NavierStokesYoungRiccati
open Holonics.Fluid.NavierStokesOpenFourierModeEvolution
open Holonics.Fluid.NavierStokesModeLagrange
open Holonics.Fluid.NavierStokesTailRelevance
open Holonics.Fluid.NavierStokesTailBoundedControl
open Holonics.Fluid.NavierStokesDyadicVorticityFluxConvolutionBridge
open Holonics.Fluid.NavierStokesOpenFourierMildIdentity
open Holonics.Fluid.NavierStokesFiniteFourierHeat
open Holonics.Fluid.NavierStokesModalGronwall
open Holonics.Fluid.NavierStokesTailGronwall
open Holonics.Fluid.NavierStokesFrequencyReach
open Holonics.Fluid.NavierStokesH2VorticityShellDissipationBridge
open Holonics.Fluid.NavierStokesYoungClosure
open Holonics.Fluid.NavierStokesMomentClosure
open Holonics.Fluid.NavierStokesIncoherentSource
open Holonics.Fluid.NavierStokesIncoherentClosure
open Holonics.Fluid.NavierStokesOpenEnergySpacetime
open Holonics.Fluid.NavierStokesCoordinateLowerEnergyEstimate
open Holonics.Fluid.NavierStokesSmoothSliceWeightedH3
open Holonics.Fluid.NavierStokesVelocityMassEnergy
open Holonics.Fluid.NavierStokesBandCoherence
open Holonics.Fluid.NavierStokesBandBarycenter
open Holonics.Fluid.NavierStokesCombBarycenterDefect
open Holonics.Fluid.NavierStokesTorusCubeIntegral
open Holonics.Fluid.NavierStokesInfiniteFourierHeat
open Holonics.Fluid.NavierStokesFourierKirchhoff
open Holonics.Fluid.NavierStokesOpenFourierSpatialSymbols
open Holonics.Fluid.NavierStokesBandEnergyBudget
open Holonics.Fluid.NavierStokesRelevanceBudget

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)

/-- The mass of the shell between nested bands. -/
def shellMass (F G : Finset SpatialFrequency) (τ : ℝ) : ℝ :=
  NavierStokesBandEnergyBudget.bandMass (velocity := velocity) G τ -
    NavierStokesBandEnergyBudget.bandMass (velocity := velocity) F τ

theorem shellMass_eq_sum {F G : Finset SpatialFrequency} (hFG : F ⊆ G) (τ : ℝ) :
    shellMass (velocity := velocity) F G τ = ∑ k ∈ G \ F, modeMass (velocity := velocity) k τ := by
  unfold shellMass NavierStokesBandEnergyBudget.bandMass
  rw [← Finset.sum_sdiff hFG]
  ring

theorem shellMass_nonneg {F G : Finset SpatialFrequency} (hFG : F ⊆ G) (τ : ℝ) :
    0 ≤ shellMass (velocity := velocity) F G τ := by
  rw [shellMass_eq_sum hFG]
  exact Finset.sum_nonneg fun k _ ↦ modeMass_nonneg k τ

/-- **The shell budget**: dissipation on the shell and the transfer out of the shell. -/
theorem hasDerivAt_shellMass (t : Ioo 0 T) {F G : Finset SpatialFrequency} (hFG : F ⊆ G) :
    HasDerivAt (shellMass (velocity := velocity) F G)
      (-2 * nu * ∑ k ∈ G \ F, torusStokesEigenvalue k * modeMass (velocity := velocity) k t.1 -
        2 * ∑ k ∈ G \ F, transfer solution t k) t.1 := by
  have hG := hasDerivAt_bandMass solution t G
  have hF := hasDerivAt_bandMass solution t F
  refine (hG.sub hF).congr_deriv ?_
  unfold bandDissipation
  rw [← Finset.sum_sdiff hFG, ← Finset.sum_sdiff hFG]
  ring

/-- **The shell budget through the two frontiers.** -/
theorem hasDerivAt_shellMass_kirchhoff (t : Ioo 0 T) {F G : Finset SpatialFrequency} (_hFG : F ⊆ G) :
    HasDerivAt (shellMass (velocity := velocity) F G)
      (-2 * nu * (bandDissipation (velocity := velocity) G t.1 -
          bandDissipation (velocity := velocity) F t.1) +
        2 * ∑' k : ↑((↑G : Set SpatialFrequency)ᶜ), transfer solution t k -
        2 * ∑' k : ↑((↑F : Set SpatialFrequency)ᶜ), transfer solution t k) t.1 := by
  have hG := hasDerivAt_bandMass_kirchhoff solution t G
  have hF := hasDerivAt_bandMass_kirchhoff solution t F
  refine (hG.sub hF).congr_deriv ?_
  ring

include solution in
/-- The cumulative current of the shell is the difference of the cumulative currents. -/
theorem cumulativeCurrent_sub {F G : Finset SpatialFrequency} (hFG : F ⊆ G) {s τ : ℝ}
    (hs : s ∈ Ioo 0 T) (hτ : τ ∈ Ioo 0 T) :
    cumulativeCurrent (velocity := velocity) (nu := nu) G s τ -
        cumulativeCurrent (velocity := velocity) (nu := nu) F s τ =
      (shellMass (velocity := velocity) F G τ - shellMass (velocity := velocity) F G s) / 2 +
        nu * ∫ σ in s..τ, ∑ k ∈ G \ F, torusStokesEigenvalue k * modeMass (velocity := velocity) k σ := by
  unfold cumulativeCurrent shellMass
  have hint : ∫ σ in s..τ, ∑ k ∈ G \ F, torusStokesEigenvalue k * modeMass (velocity := velocity) k σ =
      (∫ σ in s..τ, bandDissipation (velocity := velocity) G σ) -
        ∫ σ in s..τ, bandDissipation (velocity := velocity) F σ := by
    rw [← intervalIntegral.integral_sub (intervalIntegrable_bandDissipation solution G hs hτ)
      (intervalIntegrable_bandDissipation solution F hs hτ)]
    refine intervalIntegral.integral_congr fun σ _ ↦ ?_
    unfold bandDissipation
    rw [← Finset.sum_sdiff hFG]
    ring
  rw [hint]
  ring

section Audit

#print axioms hasDerivAt_shellMass_kirchhoff
#print axioms cumulativeCurrent_sub

end Audit

end Holonics.Fluid.NavierStokesShellBudget
