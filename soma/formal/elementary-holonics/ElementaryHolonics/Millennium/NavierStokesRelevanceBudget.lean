import ElementaryHolonics.Millennium.NavierStokesBandEnergyBudget

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

namespace Soma.Holonics.Millennium.NavierStokesRelevanceBudget

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

end Soma.Holonics.Millennium.NavierStokesRelevanceBudget
