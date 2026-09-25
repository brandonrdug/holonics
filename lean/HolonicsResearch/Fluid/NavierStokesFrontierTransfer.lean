import HolonicsResearch.Fluid.NavierStokesFrontierFeed
import HolonicsResearch.Fluid.NavierStokesBandEnergyBudget

/-!
# The frontier transfer: the band's net current is bounded by the frontier product

Beyond twice the band the advection coefficient obeys the frontier bound, so each exterior
transfer is bounded by the frontier product times the receiver's `ℓ¹` velocity mass.  Summing
over the exterior and using the Kirchhoff law, the net current into the cube of radius `2N` is
bounded by the frontier product times the exterior `ℓ¹` velocity mass; hence the band energy
obeys `|dE/dt + 2νD| ≤ 2 · frontier · exterior mass`.
-/

noncomputable section

namespace Holonics.Fluid.NavierStokesFrontierTransfer

open Set Filter Topology MeasureTheory Complex
open scoped Finset ComplexConjugate ContDiff
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
open Holonics.Fluid.NavierStokesTorusCubeIntegral
open Holonics.Fluid.NavierStokesInfiniteFourierHeat
open scoped ComplexConjugate
open Holonics.Fluid.NavierStokesShellStepCost
open Holonics.Fluid.NavierStokesFrontierFeed
open Holonics.Fluid.NavierStokesFourierKirchhoff
open Holonics.Fluid.NavierStokesBandEnergyBudget

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
  (t : Ioo 0 T)

/-- The frontier product of radius `N`. -/
def frontierBound (N : ℕ) : ℝ :=
  (∑ p ∈ frequencyCube N, complexVectorL1 (openPeriodicVelocityFourierMode solution t p)) *
      openPeriodicJacobianCoefficientTailMass solution t (frequencyCube N) +
    (∑' p : ↑((↑(frequencyCube N) : Set SpatialFrequency)ᶜ),
        complexVectorL1 (openPeriodicVelocityFourierMode solution t p)) *
      openPeriodicJacobianCoefficientTailMass solution t ∅

/-- The exterior `ℓ¹` velocity mass beyond the cube of radius `M`. -/
def exteriorMass (M : ℕ) : ℝ :=
  ∑' k : ↑((↑(frequencyCube M) : Set SpatialFrequency)ᶜ),
    complexVectorL1 (openPeriodicVelocityFourierMode solution t k)

/-- **Each exterior transfer is bounded by the frontier product.** -/
theorem abs_transfer_le_frontier {N : ℕ} {k : SpatialFrequency}
    (hk : k ∉ frequencyCube (2 * N)) :
    |transfer solution t k| ≤
      frontierBound solution t N * complexVectorL1 (openPeriodicVelocityFourierMode solution t k) := by
  unfold transfer
  rw [complexVectorL1_eq_sum, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  calc |(conj (openActualAdvectionMode solution t k c) *
          openPeriodicVelocityFourierMode solution t k c).re|
      ≤ ‖conj (openActualAdvectionMode solution t k c) *
          openPeriodicVelocityFourierMode solution t k c‖ := Complex.abs_re_le_norm _
    _ = ‖openActualAdvectionMode solution t k c‖ *
          ‖openPeriodicVelocityFourierMode solution t k c‖ := by
        rw [norm_mul, Complex.norm_conj]
    _ ≤ frontierBound solution t N * ‖openPeriodicVelocityFourierMode solution t k c‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        unfold frontierBound
        exact norm_advectionMode_le_frontier solution t hk c

/-- **The exterior transfer mass is bounded by the frontier product times the exterior mass.** -/
theorem tsum_compl_abs_transfer_le (N : ℕ) :
    ∑' k : ↑((↑(frequencyCube (2 * N)) : Set SpatialFrequency)ᶜ), |transfer solution t k| ≤
      frontierBound solution t N * exteriorMass solution t (2 * N) := by
  unfold exteriorMass
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun k => ?_) ?_ ?_
  · exact abs_transfer_le_frontier solution t k.2
  · exact ((summable_transfer solution t).abs).subtype _
  · exact ((summable_complexVectorL1_velocityMode solution t).mul_left _).subtype _

/-- **The band's net current is bounded by the frontier product times the exterior mass.** -/
theorem abs_sum_transfer_cube_le (N : ℕ) :
    |∑ k ∈ frequencyCube (2 * N), transfer solution t k| ≤
      frontierBound solution t N * exteriorMass solution t (2 * N) := by
  have hsum : ∑ k ∈ frequencyCube (2 * N), transfer solution t k =
      -∑' k : ↑((↑(frequencyCube (2 * N)) : Set SpatialFrequency)ᶜ), transfer solution t k :=
    eq_neg_of_add_eq_zero_left (sum_transfer_add_tsum_compl solution t _)
  rw [hsum, abs_neg]
  calc |∑' k : ↑((↑(frequencyCube (2 * N)) : Set SpatialFrequency)ᶜ), transfer solution t k|
      = ‖∑' k : ↑((↑(frequencyCube (2 * N)) : Set SpatialFrequency)ᶜ), transfer solution t k‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∑' k : ↑((↑(frequencyCube (2 * N)) : Set SpatialFrequency)ᶜ), ‖transfer solution t k‖ :=
        norm_tsum_le_tsum_norm ((summable_transfer solution t).norm.subtype _)
    _ = ∑' k : ↑((↑(frequencyCube (2 * N)) : Set SpatialFrequency)ᶜ), |transfer solution t k| := by
        simp only [Real.norm_eq_abs]
    _ ≤ _ := tsum_compl_abs_transfer_le solution t N

/-- **The band energy budget beyond the frontier.** -/
theorem abs_deriv_bandMass_add_dissipation_le (N : ℕ) :
    |deriv (NavierStokesBandEnergyBudget.bandMass (velocity := velocity) (frequencyCube (2 * N)))
        t.1 +
      2 * nu * NavierStokesBandEnergyBudget.bandDissipation (velocity := velocity)
        (frequencyCube (2 * N)) t.1| ≤
      2 * (frontierBound solution t N * exteriorMass solution t (2 * N)) := by
  rw [(hasDerivAt_bandMass solution t (frequencyCube (2 * N))).deriv]
  have h := abs_sum_transfer_cube_le solution t N
  have h2 : -2 * nu * NavierStokesBandEnergyBudget.bandDissipation (velocity := velocity)
        (frequencyCube (2 * N)) t.1 - 2 * ∑ k ∈ frequencyCube (2 * N), transfer solution t k +
      2 * nu * NavierStokesBandEnergyBudget.bandDissipation (velocity := velocity)
        (frequencyCube (2 * N)) t.1 =
      -2 * ∑ k ∈ frequencyCube (2 * N), transfer solution t k := by ring
  rw [h2, abs_mul]
  norm_num
  linarith

end Holonics.Fluid.NavierStokesFrontierTransfer
