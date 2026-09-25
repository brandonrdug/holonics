import HolonicsResearch.Fluid.NavierStokesCombBarycenterDefect

/-!
# The coherence defect is bounded by the participation number of the feed comb

For any comb `z` with summable norms, `‖Σ' z‖² ≤ (Σ' ‖z‖)²`, so the coherence defect at a
receiver is at most the participation number minus one,

```text
1 + κ_k ≤ P_k := (Σ'_p ‖feed_{k,p}‖)² / Σ'_p ‖feed_{k,p}‖²,
```

the effective number of teeth carrying the feed.  A uniform bound on the participation number of
the feed combs along a terminal tail therefore returns the coherence defect, and with it
`StatementB`: a blow-up needs feed combs whose effective tooth count diverges.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Finset

namespace Holonics.Fluid.NavierStokesCombParticipation

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

/-! ## Any summable comb -/

/-- **The comb power is at most the square of the total tooth length.** -/
theorem norm_tsum_sq_le_tsum_norm_sq {ι : Type*} (z : ι → ℂ) (hz : Summable fun p ↦ ‖z p‖) :
    ‖∑' p, z p‖ ^ 2 ≤ (∑' p, ‖z p‖) ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg _) (norm_tsum_le_tsum_norm hz) 2

/-- **The comb power is at most the participation bound.**  If
`(Σ' ‖z‖)² ≤ (1 + κ) Σ' ‖z‖²` then `‖Σ' z‖² ≤ (1 + κ) Σ' ‖z‖²`. -/
theorem norm_tsum_sq_le_of_participation {ι : Type*} (z : ι → ℂ)
    (hz : Summable fun p ↦ ‖z p‖) {κ : ℝ}
    (h : (∑' p, ‖z p‖) ^ 2 ≤ (1 + κ) * ∑' p, ‖z p‖ ^ 2) :
    ‖∑' p, z p‖ ^ 2 ≤ (1 + κ) * ∑' p, ‖z p‖ ^ 2 :=
  (norm_tsum_sq_le_tsum_norm_sq z hz).trans h

/-! ## The feed comb at a receiver -/

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
  (t : Ioo 0 T)

theorem summable_norm_feedTerm (hsum : Summable (eleventhMoment (velocity := velocity) t.1))
    (k : SpatialFrequency) (output : Fin 3) :
    Summable fun p ↦ ‖feedTerm solution t k p output‖ :=
  Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun p ↦ norm_feedTerm_le_sqrt solution t k p output)
    (summable_conv (l1Pop_nonneg solution t) (rootEnergy_nonneg t) (summable_l1Pop solution t)
      (summable_rootEnergy_sq solution t hsum) k)

/-- **Participation control at a receiver**: the square of the total tooth length of the feed
comb is at most `1 + κ` times its diagonal. -/
def ParticipationAt (κ : ℝ) (k : SpatialFrequency) : Prop :=
  ∀ output : Fin 3,
    (∑' p, ‖feedTerm solution t k p output‖) ^ 2 ≤
      (1 + κ) * ∑' p, ‖feedTerm solution t k p output‖ ^ 2

/-- **Participation control returns the coherence defect.** -/
theorem coherenceDefectAt_of_participation
    (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) {κ : ℝ}
    (k : SpatialFrequency) (h : ParticipationAt solution t κ k) :
    CoherenceDefectAt solution t κ k := by
  intro output
  rw [openActualAdvectionMode_eq_tsum_feedTerm]
  exact norm_tsum_sq_le_of_participation _ (summable_norm_feedTerm solution t hsum k output)
    (h output)

/-! ## The closure statement -/

/-- **Participation tail control.**  Along a terminal tail every nonzero receiver's feed comb
has participation number at most `1 + κ`, and the eleventh moment is finite with interior
bounds. -/
def ParticipationTailControl : Prop :=
  ∀ {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField},
    0 < nu →
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) →
      ∃ (s κ : ℝ), 0 < s ∧ s < T ∧ 0 ≤ κ ∧
        (∀ σ (hσ : σ ∈ Ioo 0 T), s ≤ σ →
          Summable (eleventhMoment (velocity := velocity) σ) ∧
            ∀ k : SpatialFrequency, k ≠ 0 → ParticipationAt solution ⟨σ, hσ⟩ κ k) ∧
        (∀ τ ∈ Ioo s T, ∃ B : ℝ, ∀ σ ∈ Icc s τ, moment (velocity := velocity) 11 σ ≤ B)

theorem coherenceDefectTail_of_participation (h : ParticipationTailControl) :
    CoherenceDefectTailControl := by
  intro T nu initial velocity pressure hnu solution
  obtain ⟨s, κ, hs0, hsT, hκ, htail, hcompact⟩ := h hnu solution
  refine ⟨s, κ, hs0, hsT, hκ, fun σ hσ hsσ ↦ ⟨(htail σ hσ hsσ).1, fun k hk ↦ ?_⟩, hcompact⟩
  exact coherenceDefectAt_of_participation solution ⟨σ, hσ⟩ (htail σ hσ hsσ).1 k
    ((htail σ hσ hsσ).2 k hk)

/-- **Participation tail control returns Statement B.** -/
theorem statementB_of_participation (h : ParticipationTailControl) : StatementB :=
  statementB_of_coherenceDefectTail (coherenceDefectTail_of_participation h)

theorem officialProblem_of_participation (h : ParticipationTailControl) :
    TheOfficialNavierStokesProblem :=
  officialProblem_of_coherenceDefectTail (coherenceDefectTail_of_participation h)

section Audit

#print axioms coherenceDefectAt_of_participation
#print axioms statementB_of_participation

end Audit

end Holonics.Fluid.NavierStokesCombParticipation
