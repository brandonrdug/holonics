import ElementaryHolonics.Millennium.NavierStokesBandLimitedRelevance
import ElementaryHolonics.Millennium.NavierStokesCombParticipation

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

namespace Soma.Holonics.Millennium.NavierStokesBandLimitedDefect

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
open Soma.Holonics.Millennium.NavierStokesShellBudget
open Soma.Holonics.Millennium.NavierStokesBandLimitedRelevance
open Soma.Holonics.Millennium.NavierStokesCombParticipation

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

end Soma.Holonics.Millennium.NavierStokesBandLimitedDefect
