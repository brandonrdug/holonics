import HolonicsResearch.Fluid.NavierStokesShellStepCost
import HolonicsResearch.Fluid.NavierStokesFrequencyReach

/-!
# The frontier feed: a receiver beyond twice the band is fed only through the exterior

For `k ∉ C_{2N}` every feed term `feed k p` has a participant outside `C_N`: either `p ∉ C_N` or
`k − p ∉ C_N`.  Splitting the advection coefficient into its band and exterior feeds then bounds
the exterior current by two frontier products: the band's `ℓ¹` velocity mass times the Jacobian
mass beyond the band, plus the exterior `ℓ¹` velocity mass times the total Jacobian mass.
-/

noncomputable section

namespace Holonics.Fluid.NavierStokesFrontierFeed

open Holonics.Fluid.NavierStokesShellStepCost
open Holonics.Fluid.NavierStokesFrequencyReach
open Set Filter Topology MeasureTheory
open scoped Finset
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
open Holonics.Fluid.NavierStokesFrequencyReach
open Holonics.Fluid.NavierStokesOpenAdvectionConvolutionBridge
open Holonics.Fluid.NavierStokesOpenAdvectionCarrierIntegration
open Holonics.Fluid.NavierStokesSmoothSliceWeightedH3
open Holonics.Fluid.NavierStokesH3Bilinear
open Holonics.Fluid.NavierStokesInfiniteFourierHeatH3
open Holonics.Fluid.NavierStokesMildFourierNonlinearity
open Holonics.Fluid.NavierStokesOpenFourierMildIdentity
open Holonics.Fluid.NavierStokesH2VorticityShellDissipationBridge
open Holonics.Fluid.NavierStokesFiniteFourierHeat
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

end Holonics.Fluid.NavierStokesFrontierFeed
