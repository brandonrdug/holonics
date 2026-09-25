import HolonicsResearch.Fluid.NavierStokesBandEnergyBudget

/-!
# The relevance budget: the cumulative current out of a band is paid by the band's initial mass

The cumulative current into the complement of a finite band since time `s`,

```text
C_F(τ) = (E_F(τ) − E_F(s)) / 2 + ν ∫_s^τ D_F,
```

is the antiderivative of the frontier current `Σ'_{k ∉ F} transfer k` (the band budget), and its
negative, the mass the band has given to its complement, is at most `E_F(s)/2 ≤ 3 E_kin(s)`:
the tail is fed only by the band, and the band has finite mass to give.  No integrability of the
transfer current is needed; only the continuity of the mode masses on the open lifespan.
-/

noncomputable section

open Set Filter Topology MeasureTheory intervalIntegral
open scoped Finset

namespace Holonics.Fluid.NavierStokesRelevanceBudget

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

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)

/-! ## Continuity on the open lifespan -/

theorem modeMass_nonneg (k : SpatialFrequency) (τ : ℝ) :
    0 ≤ modeMass (velocity := velocity) k τ :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem bandMass_nonneg (F : Finset SpatialFrequency) (τ : ℝ) :
    0 ≤ bandMass (velocity := velocity) F τ :=
  Finset.sum_nonneg fun k _ ↦ modeMass_nonneg k τ

theorem bandDissipation_nonneg (F : Finset SpatialFrequency) (τ : ℝ) :
    0 ≤ bandDissipation (velocity := velocity) F τ :=
  Finset.sum_nonneg fun k _ ↦ mul_nonneg (torusStokesEigenvalue_nonneg k) (modeMass_nonneg k τ)

include solution in
theorem continuousOn_modeMass (k : SpatialFrequency) :
    ContinuousOn (modeMass (velocity := velocity) k) (Ioo 0 T) := fun t ht ↦
  (hasDerivAt_modeMass solution ⟨t, ht⟩ k).continuousAt.continuousWithinAt

include solution in
theorem continuousOn_bandDissipation (F : Finset SpatialFrequency) :
    ContinuousOn (bandDissipation (velocity := velocity) F) (Ioo 0 T) := by
  unfold bandDissipation
  exact continuousOn_finsetSum F fun k _ ↦ continuousOn_const.mul (continuousOn_modeMass solution k)

theorem uIcc_subset_Ioo {s τ : ℝ} (hs : s ∈ Ioo 0 T) (hτ : τ ∈ Ioo 0 T) :
    uIcc s τ ⊆ Ioo 0 T := by
  intro x hx
  obtain ⟨h1, h2⟩ := Set.mem_Icc.mp hx
  exact ⟨lt_of_lt_of_le (lt_min hs.1 hτ.1) h1, lt_of_le_of_lt h2 (max_lt hs.2 hτ.2)⟩

include solution in
theorem intervalIntegrable_bandDissipation (F : Finset SpatialFrequency) {s τ : ℝ}
    (hs : s ∈ Ioo 0 T) (hτ : τ ∈ Ioo 0 T) :
    IntervalIntegrable (bandDissipation (velocity := velocity) F) volume s τ :=
  ((continuousOn_bandDissipation solution F).mono (uIcc_subset_Ioo hs hτ)).intervalIntegrable

/-! ## The cumulative current -/

/-- The cumulative current into the complement of the band since `s`. -/
def cumulativeCurrent (F : Finset SpatialFrequency) (s τ : ℝ) : ℝ :=
  (bandMass (velocity := velocity) F τ - bandMass (velocity := velocity) F s) / 2 +
    nu * ∫ σ in s..τ, bandDissipation (velocity := velocity) F σ

theorem cumulativeCurrent_self (F : Finset SpatialFrequency) (s : ℝ) :
    cumulativeCurrent (velocity := velocity) (nu := nu) F s s = 0 := by
  unfold cumulativeCurrent
  simp

/-- **The cumulative current is the antiderivative of the frontier current.** -/
theorem hasDerivAt_cumulativeCurrent (F : Finset SpatialFrequency) {s : ℝ} (hs : s ∈ Ioo 0 T)
    (τ : Ioo 0 T) :
    HasDerivAt (cumulativeCurrent (velocity := velocity) (nu := nu) F s)
      (∑' k : ↑((↑F : Set SpatialFrequency)ᶜ), transfer solution τ k) τ.1 := by
  unfold cumulativeCurrent
  have h1 := hasDerivAt_bandMass_kirchhoff solution τ F
  have h2 : HasDerivAt (fun u ↦ ∫ σ in s..u, bandDissipation (velocity := velocity) F σ)
      (bandDissipation (velocity := velocity) F τ.1) τ.1 := by
    apply intervalIntegral.integral_hasDerivAt_right
      (intervalIntegrable_bandDissipation solution F hs τ.2)
    · exact (continuousOn_bandDissipation solution F).stronglyMeasurableAtFilter isOpen_Ioo τ.1 τ.2
    · exact (continuousOn_bandDissipation solution F).continuousAt (isOpen_Ioo.mem_nhds τ.2)
  have := ((h1.sub_const (bandMass (velocity := velocity) F s)).div_const 2).add (h2.const_mul nu)
  refine this.congr_deriv ?_
  ring

/-- **The relevance budget**: the mass the band has given to its complement since `s` is at
most half the band's mass at `s`. -/
theorem neg_cumulativeCurrent_le (hnu : 0 ≤ nu) (F : Finset SpatialFrequency) {s τ : ℝ}
    (hsτ : s ≤ τ) :
    -cumulativeCurrent (velocity := velocity) (nu := nu) F s τ ≤
      bandMass (velocity := velocity) F s / 2 := by
  unfold cumulativeCurrent
  have hE := bandMass_nonneg (velocity := velocity) F τ
  have hD : 0 ≤ ∫ σ in s..τ, bandDissipation (velocity := velocity) F σ :=
    intervalIntegral.integral_nonneg hsτ fun σ _ ↦ bandDissipation_nonneg F σ
  nlinarith [mul_nonneg hnu hD]

include solution in
/-- The band mass is at most three times twice the kinetic energy. -/
theorem bandMass_le_kineticEnergy (t : Ioo 0 T) (F : Finset SpatialFrequency) :
    bandMass (velocity := velocity) F t.1 ≤ 3 * (2 * periodicKineticEnergy velocity t.1) := by
  calc bandMass (velocity := velocity) F t.1
      = ∑ k ∈ F, velPop solution t k := Finset.sum_congr rfl fun k _ ↦ modeMass_eq_velPop solution t k
    _ ≤ velocityMass solution t :=
        (summable_velPop solution t).sum_le_tsum F fun k _ ↦ velPop_nonneg solution t k
    _ ≤ _ := velocityMass_le_kineticEnergy solution t

include solution in
/-- **The relevance budget in the kinetic energy**: the complement of any band receives at most
`3 E_kin(s)` from the band over any interval starting at `s`. -/
theorem neg_cumulativeCurrent_le_kineticEnergy (hnu : 0 ≤ nu) (F : Finset SpatialFrequency)
    (s : Ioo 0 T) {τ : ℝ} (hsτ : s.1 ≤ τ) :
    -cumulativeCurrent (velocity := velocity) (nu := nu) F s.1 τ ≤
      3 * periodicKineticEnergy velocity s.1 := by
  have h := neg_cumulativeCurrent_le (velocity := velocity) hnu F hsτ
  have h2 := bandMass_le_kineticEnergy solution s F
  linarith

section Audit

#print axioms hasDerivAt_cumulativeCurrent
#print axioms neg_cumulativeCurrent_le_kineticEnergy

end Audit

end Holonics.Fluid.NavierStokesRelevanceBudget
