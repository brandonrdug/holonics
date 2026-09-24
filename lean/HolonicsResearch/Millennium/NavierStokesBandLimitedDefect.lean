import HolonicsResearch.Millennium.NavierStokesBandLimitedRelevance
import HolonicsResearch.Millennium.NavierStokesCombParticipation

/-!
# The coherence defect of a band-limited feed comb is at most the cube count minus one

A slice supported in the cube of radius `N` has, at every receiver, a feed comb with at most
`(2N+1)³` nonzero teeth, so by Cauchy--Schwarz its participation number is at most `(2N+1)³`
and its coherence defect at most `(2N+1)³ − 1`.  A band-limited terminal tail therefore
satisfies the coherence-defect closure outright: the defect can only diverge if the effective
band diverges.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Finset

namespace Holonics.Millennium.NavierStokesBandLimitedDefect

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
open Holonics.Millennium.NavierStokesH3Production
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
open Holonics.Millennium.NavierStokesTorusCubeIntegral
open Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Holonics.Millennium.NavierStokesFourierKirchhoff
open Holonics.Millennium.NavierStokesOpenFourierSpatialSymbols
open Holonics.Millennium.NavierStokesBandEnergyBudget
open Holonics.Millennium.NavierStokesRelevanceBudget
open Holonics.Millennium.NavierStokesShellBudget
open Holonics.Millennium.NavierStokesBandLimitedRelevance
open Holonics.Millennium.NavierStokesCombParticipation

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
  (t : Ioo 0 T)

theorem feedTerm_eq_zero_of_not_mem {N : ℕ} (h : BandLimited solution t N) (k : SpatialFrequency)
    {p : SpatialFrequency} (hp : p ∉ frequencyCube N) (output : Fin 3) :
    feedTerm solution t k p output = 0 := by
  unfold feedTerm
  rw [h p hp]
  simp

/-- **The participation number of a band-limited comb is at most the cube count.** -/
theorem participationAt_of_bandLimited {N : ℕ} (h : BandLimited solution t N)
    (k : SpatialFrequency) :
    ParticipationAt solution t (((2 * N + 1) ^ 3 : ℝ) - 1) k := by
  intro output
  have hz : ∀ p ∉ frequencyCube N, ‖feedTerm solution t k p output‖ = 0 := fun p hp ↦ by
    rw [feedTerm_eq_zero_of_not_mem solution t h k hp output, norm_zero]
  have hz2 : ∀ p ∉ frequencyCube N, ‖feedTerm solution t k p output‖ ^ 2 = 0 := fun p hp ↦ by
    rw [hz p hp]
    norm_num
  rw [tsum_eq_sum (s := frequencyCube N) hz, tsum_eq_sum (s := frequencyCube N) hz2]
  have hcs := sq_sum_le_card_mul_sum_sq (s := frequencyCube N)
    (f := fun p ↦ ‖feedTerm solution t k p output‖)
  rw [card_frequencyCube] at hcs
  have hcast : (1 : ℝ) + (((2 * N + 1) ^ 3 : ℝ) - 1) = (((2 * N + 1) ^ 3 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hcast]
  exact hcs

theorem bandLimitedDefect_nonneg (N : ℕ) : (0 : ℝ) ≤ ((2 * N + 1) ^ 3 : ℝ) - 1 := by
  have : (1 : ℝ) ≤ (2 * N + 1) ^ 3 := one_le_pow₀ (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
  linarith

/-- **The coherence defect of a band-limited comb is at most the cube count minus one.** -/
theorem coherenceDefectAt_of_bandLimited (hsum : Summable (eleventhMoment (velocity := velocity) t.1))
    {N : ℕ} (h : BandLimited solution t N) (k : SpatialFrequency) :
    CoherenceDefectAt solution t (((2 * N + 1) ^ 3 : ℝ) - 1) k :=
  coherenceDefectAt_of_participation solution t hsum k (participationAt_of_bandLimited solution t h k)

/-- **Band-limited tail control**: along a terminal tail the slice is supported in one cube and the
eleventh moment is finite with interior bounds. -/
def BandLimitedTailControl : Prop :=
  ∀ {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField},
    0 < nu →
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) →
      ∃ (s : ℝ) (N : ℕ), 0 < s ∧ s < T ∧
        (∀ σ (hσ : σ ∈ Ioo 0 T), s ≤ σ →
          Summable (eleventhMoment (velocity := velocity) σ) ∧ BandLimited solution ⟨σ, hσ⟩ N) ∧
        (∀ τ ∈ Ioo s T, ∃ B : ℝ, ∀ σ ∈ Icc s τ, moment (velocity := velocity) 11 σ ≤ B)

theorem coherenceDefectTail_of_bandLimited (h : BandLimitedTailControl) :
    CoherenceDefectTailControl := by
  intro T nu initial velocity pressure hnu solution
  obtain ⟨s, N, hs0, hsT, htail, hcompact⟩ := h hnu solution
  refine ⟨s, ((2 * N + 1) ^ 3 : ℝ) - 1, hs0, hsT, bandLimitedDefect_nonneg N,
    fun σ hσ hsσ ↦ ⟨(htail σ hσ hsσ).1, fun k _ ↦ ?_⟩, hcompact⟩
  exact coherenceDefectAt_of_bandLimited solution ⟨σ, hσ⟩ (htail σ hσ hsσ).1 (htail σ hσ hsσ).2 k

/-- **A band-limited terminal tail returns Statement B.** -/
theorem statementB_of_bandLimitedTail (h : BandLimitedTailControl) : StatementB :=
  statementB_of_coherenceDefectTail (coherenceDefectTail_of_bandLimited h)

section Audit

#print axioms participationAt_of_bandLimited
#print axioms coherenceDefectAt_of_bandLimited
#print axioms statementB_of_bandLimitedTail

end Audit

end Holonics.Millennium.NavierStokesBandLimitedDefect
