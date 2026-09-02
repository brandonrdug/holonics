import ElementaryHolonics.Millennium.NavierStokesShellStepCost
import ElementaryHolonics.Millennium.NavierStokesFrequencyReach

/-!
# The frontier feed: a receiver beyond twice the band is fed only through the exterior

For `k ∉ C_{2N}` every feed term `feed k p` has a participant outside `C_N`: either `p ∉ C_N` or
`k − p ∉ C_N`.  Splitting the advection coefficient into its band and exterior feeds then bounds
the exterior current by two frontier products: the band's `ℓ¹` velocity mass times the Jacobian
mass beyond the band, plus the exterior `ℓ¹` velocity mass times the total Jacobian mass.
-/

noncomputable section

namespace Soma.Holonics.Millennium.NavierStokesFrontierFeed

open Soma.Holonics.Millennium.NavierStokesShellStepCost
open Soma.Holonics.Millennium.NavierStokesFrequencyReach
open Set Filter Topology MeasureTheory
open scoped Finset
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
open Soma.Holonics.Millennium.NavierStokesFrequencyReach
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesH2VorticityShellDissipationBridge
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
  (t : Ioo 0 T)

/-- **Frontier participation.**  Beyond twice the band, every feed has an exterior participant. -/
theorem feed_participant_exterior {N : ℕ} {k p : SpatialFrequency}
    (hk : k ∉ frequencyCube (2 * N)) :
    p ∉ frequencyCube N ∨ k - p ∉ frequencyCube N := by
  by_contra h
  push Not at h
  apply hk
  have hclosed : p + (k - p) + (-k) = 0 := by abel
  have hneg := receiver_mem_frequencyCube_of_closed hclosed h.1 h.2
  rw [← two_mul] at hneg
  have := neg_mem_frequencyCube hneg
  simpa using this

/-- The advection coefficient splits into band feeds and exterior feeds. -/
theorem advectionMode_eq_band_add_exterior (N : ℕ) (k : SpatialFrequency) (output : Fin 3) :
    openActualAdvectionMode solution t k output =
      ∑ p ∈ frequencyCube N, feedTerm solution t k p output +
        ∑' p : ↑((↑(frequencyCube N) : Set SpatialFrequency)ᶜ),
          feedTerm solution t k p output := by
  rw [openActualAdvectionMode_eq_tsum_feedTerm]
  exact ((summable_feedTerm solution t k output).sum_add_tsum_compl).symm

/-- **The frontier bound.**  Beyond twice the band, the advection coefficient is bounded by the
band's `ℓ¹` velocity mass times the Jacobian mass beyond the band, plus the exterior `ℓ¹`
velocity mass times the total Jacobian mass. -/
theorem norm_advectionMode_le_frontier {N : ℕ} {k : SpatialFrequency}
    (hk : k ∉ frequencyCube (2 * N)) (output : Fin 3) :
    ‖openActualAdvectionMode solution t k output‖ ≤
      (∑ p ∈ frequencyCube N, complexVectorL1 (openPeriodicVelocityFourierMode solution t p)) *
          openPeriodicJacobianCoefficientTailMass solution t (frequencyCube N) +
        (∑' p : ↑((↑(frequencyCube N) : Set SpatialFrequency)ᶜ),
            complexVectorL1 (openPeriodicVelocityFourierMode solution t p)) *
          openPeriodicJacobianCoefficientTailMass solution t ∅ := by
  rw [advectionMode_eq_band_add_exterior solution t N k output]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro p hp
    have hkp : k - p ∉ frequencyCube N := by
      rcases feed_participant_exterior (p := p) hk with h | h
      · exact absurd hp h
      · exact h
    exact norm_feedTerm_le solution t hkp output
  · have hsumm := (summable_feedTerm solution t k output).norm.subtype
      ((↑(frequencyCube N) : Set SpatialFrequency)ᶜ)
    refine (norm_tsum_le_tsum_norm hsumm).trans ?_
    rw [← tsum_mul_right]
    refine Summable.tsum_le_tsum (fun p ↦ ?_) hsumm ?_
    · exact norm_feedTerm_le solution t (by simp) output
    · exact ((summable_complexVectorL1_velocityMode solution t).mul_right _).subtype _

end Soma.Holonics.Millennium.NavierStokesFrontierFeed
