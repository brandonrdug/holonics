import ElementaryHolonics.Millennium.NavierStokesCombBarycenterDefect

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

namespace Soma.Holonics.Millennium.NavierStokesCombParticipation

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

end Soma.Holonics.Millennium.NavierStokesCombParticipation
