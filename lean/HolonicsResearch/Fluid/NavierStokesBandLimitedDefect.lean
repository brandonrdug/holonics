import HolonicsResearch.Fluid.NavierStokesBandLimitedRelevance
import HolonicsResearch.Fluid.NavierStokesCombParticipation

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

namespace Holonics.Fluid.NavierStokesBandLimitedDefect

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
open Holonics.Fluid.NavierStokesShellBudget
open Holonics.Fluid.NavierStokesBandLimitedRelevance
open Holonics.Fluid.NavierStokesCombParticipation

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

end Holonics.Fluid.NavierStokesBandLimitedDefect
