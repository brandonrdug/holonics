import HolonicsResearch.Millennium.NavierStokesFrontierFeed
import HolonicsResearch.Millennium.NavierStokesBandEnergyBudget

/-!
# The frontier transfer: the band's net current is bounded by the frontier product

Beyond twice the band the advection coefficient obeys the frontier bound, so each exterior
transfer is bounded by the frontier product times the receiver's `ℓ¹` velocity mass.  Summing
over the exterior and using the Kirchhoff law, the net current into the cube of radius `2N` is
bounded by the frontier product times the exterior `ℓ¹` velocity mass; hence the band energy
obeys `|dE/dt + 2νD| ≤ 2 · frontier · exterior mass`.
-/

noncomputable section

namespace Holonics.Millennium.NavierStokesFrontierTransfer

open Set Filter Topology MeasureTheory Complex
open scoped Finset ComplexConjugate ContDiff
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
open Holonics.Millennium.NavierStokesTorusCubeIntegral
open Holonics.Millennium.NavierStokesInfiniteFourierHeat
open scoped ComplexConjugate
open Holonics.Millennium.NavierStokesShellStepCost
open Holonics.Millennium.NavierStokesFrontierFeed
open Holonics.Millennium.NavierStokesFourierKirchhoff
open Holonics.Millennium.NavierStokesBandEnergyBudget

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

end Holonics.Millennium.NavierStokesFrontierTransfer
