import HolonicsResearch.Millennium.NavierStokesCombBarycenterDefect

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

namespace Holonics.Millennium.NavierStokesCombParticipation

open Holonics.Millennium.NavierStokes
open Holonics.Millennium.NavierStokesOpenLifespan
open Holonics.Millennium.NavierStokesPeriodicEnergy
open Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Holonics.Millennium.NavierStokesTorusVorticity
open Holonics.Millennium.NavierStokesTorusFourier
open Holonics.Millennium.NavierStokesDyadicShellProjectors
open Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Holonics.Millennium.NavierStokesVorticityDirectionFullStrain
open Holonics.Millennium.NavierStokesVorticityDirectionFiniteBandBridge
open Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge
open Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Holonics.Millennium.NavierStokesVorticityDirectionSourceModulus
open Holonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction
open Holonics.Millennium.NavierStokesH2StorageDissipationPayment
open Holonics.Millennium.NavierStokesAlignedStrainBudget
open Holonics.Millennium.NavierStokesModalRiccati
open Holonics.Millennium.NavierStokesHalfRadiusReach
open Holonics.Millennium.NavierStokesShellStepCost
open Holonics.Millennium.NavierStokesMomentSwap
open Holonics.Millennium.NavierStokesMomentGap
open Holonics.Millennium.NavierStokesYoungFeed
open Holonics.Millennium.NavierStokesYoungTsum
open Holonics.Millennium.NavierStokesWeightedTailEnergy
open Holonics.Millennium.NavierStokesIncoherentBandMass
open Holonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration
open Holonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
open Holonics.Millennium.NavierStokesFourthMomentRiccati
open Holonics.Millennium.NavierStokesWeightedYoung
open Holonics.Millennium.NavierStokesMomentInterpolation
open Holonics.Millennium.NavierStokesSixthYoung
open Holonics.Millennium.NavierStokesYoungRiccati
open Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Holonics.Millennium.NavierStokesModeLagrange
open Holonics.Millennium.NavierStokesTailRelevance
open Holonics.Millennium.NavierStokesTailBoundedControl
open Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge
open Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Holonics.Millennium.NavierStokesFiniteFourierHeat
open Holonics.Millennium.NavierStokesModalGronwall
open Holonics.Millennium.NavierStokesTailGronwall
open Holonics.Millennium.NavierStokesFrequencyReach
open Holonics.Millennium.NavierStokesH2VorticityShellDissipationBridge
open Holonics.Millennium.NavierStokesYoungClosure
open Holonics.Millennium.NavierStokesMomentClosure
open Holonics.Millennium.NavierStokesIncoherentSource
open Holonics.Millennium.NavierStokesIncoherentClosure
open Holonics.Millennium.NavierStokesOpenEnergySpacetime
open Holonics.Millennium.NavierStokesCoordinateLowerEnergyEstimate
open Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Holonics.Millennium.NavierStokesVelocityMassEnergy
open Holonics.Millennium.NavierStokesBandCoherence
open Holonics.Millennium.NavierStokesBandBarycenter
open Holonics.Millennium.NavierStokesCombBarycenterDefect

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

end Holonics.Millennium.NavierStokesCombParticipation
