import ElementaryHolonics.Millennium.NavierStokesRelevanceBudget

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

namespace Soma.Holonics.Millennium.NavierStokesShellBudget

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFullStrain
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFiniteBandBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionSourceModulus
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesH2StorageDissipationPayment
open Soma.Holonics.Millennium.NavierStokesAlignedStrainBudget
open Soma.Holonics.Millennium.NavierStokesModalRiccati
open Soma.Holonics.Millennium.NavierStokesHalfRadiusReach
open Soma.Holonics.Millennium.NavierStokesShellStepCost
open Soma.Holonics.Millennium.NavierStokesMomentSwap
open Soma.Holonics.Millennium.NavierStokesMomentGap
open Soma.Holonics.Millennium.NavierStokesYoungFeed
open Soma.Holonics.Millennium.NavierStokesYoungTsum
open Soma.Holonics.Millennium.NavierStokesWeightedTailEnergy
open Soma.Holonics.Millennium.NavierStokesIncoherentBandMass
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration
open Soma.Holonics.Millennium.NavierStokesH3Production
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesFourthMomentRiccati
open Soma.Holonics.Millennium.NavierStokesWeightedYoung
open Soma.Holonics.Millennium.NavierStokesMomentInterpolation
open Soma.Holonics.Millennium.NavierStokesSixthYoung
open Soma.Holonics.Millennium.NavierStokesYoungRiccati
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesModeLagrange
open Soma.Holonics.Millennium.NavierStokesTailRelevance
open Soma.Holonics.Millennium.NavierStokesTailBoundedControl
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesModalGronwall
open Soma.Holonics.Millennium.NavierStokesTailGronwall
open Soma.Holonics.Millennium.NavierStokesFrequencyReach
open Soma.Holonics.Millennium.NavierStokesH2VorticityShellDissipationBridge
open Soma.Holonics.Millennium.NavierStokesYoungClosure
open Soma.Holonics.Millennium.NavierStokesMomentClosure
open Soma.Holonics.Millennium.NavierStokesIncoherentSource
open Soma.Holonics.Millennium.NavierStokesIncoherentClosure
open Soma.Holonics.Millennium.NavierStokesOpenEnergySpacetime
open Soma.Holonics.Millennium.NavierStokesCoordinateLowerEnergyEstimate
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesVelocityMassEnergy
open Soma.Holonics.Millennium.NavierStokesBandCoherence
open Soma.Holonics.Millennium.NavierStokesBandBarycenter
open Soma.Holonics.Millennium.NavierStokesCombBarycenterDefect
open Soma.Holonics.Millennium.NavierStokesTorusCubeIntegral
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFourierKirchhoff
open Soma.Holonics.Millennium.NavierStokesOpenFourierSpatialSymbols
open Soma.Holonics.Millennium.NavierStokesBandEnergyBudget
open Soma.Holonics.Millennium.NavierStokesRelevanceBudget

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

end Soma.Holonics.Millennium.NavierStokesShellBudget
