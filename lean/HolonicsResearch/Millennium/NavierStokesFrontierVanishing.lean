import HolonicsResearch.Millennium.NavierStokesFrontierTransfer
import HolonicsResearch.Millennium.NavierStokesTailRelevance

/-!
# The frontier defect vanishes as the band grows

The exterior `ℓ¹` velocity mass and the Jacobian tail mass are tails of summable series over
the cubes, so both tend to zero as the radius grows; the frontier product is bounded by a
constant times the Jacobian tail plus the exterior mass times a constant, so it tends to zero
too.  Hence the band energy budgets `dE_{C_{2N}}/dt + 2ν D_{C_{2N}}` converge to zero: in the
limit of the whole lattice the energy law is exact dissipation.
-/

noncomputable section

namespace Holonics.Millennium.NavierStokesFrontierVanishing

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
open Holonics.Millennium.NavierStokesFrontierTransfer
open Holonics.Millennium.NavierStokesTailRelevance

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
  (t : Ioo 0 T)

theorem tendsto_two_mul_atTop : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
  Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩

/-- **The exterior mass vanishes as the radius grows.** -/
theorem tendsto_exteriorMass :
    Tendsto (fun M => exteriorMass solution t M) atTop (𝓝 0) := by
  have h := (tendsto_tsum_compl_atTop_zero
    (fun p => complexVectorL1 (openPeriodicVelocityFourierMode solution t p))).comp
    tendsto_frequencyCube_atTop
  exact h

/-- **The Jacobian tail mass vanishes as the radius grows.** -/
theorem tendsto_jacobianTailMass :
    Tendsto (fun N => openPeriodicJacobianCoefficientTailMass solution t (frequencyCube N))
      atTop (𝓝 0) := by
  unfold openPeriodicJacobianCoefficientTailMass
  rw [← tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_pi_nhds.mpr fun component => tendsto_pi_nhds.mpr fun coordinate => ?_
  exact (tendsto_tsum_compl_atTop_zero
    (fun frequency => ‖openPeriodicJacobianFourierMode solution t frequency component
      coordinate‖)).comp tendsto_frequencyCube_atTop

theorem complexVectorL1_nonneg (v : ComplexVector) : 0 ≤ complexVectorL1 v := by
  rw [complexVectorL1_eq_sum]
  exact Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem jacobianTailMass_nonneg (modes : Finset SpatialFrequency) :
    0 ≤ openPeriodicJacobianCoefficientTailMass solution t modes := by
  unfold openPeriodicJacobianCoefficientTailMass
  exact norm_nonneg _

/-- **The frontier product vanishes as the radius grows.** -/
theorem tendsto_frontierBound :
    Tendsto (fun N => frontierBound solution t N) atTop (𝓝 0) := by
  have hsum := summable_complexVectorL1_velocityMode solution t
  set S := ∑' p, complexVectorL1 (openPeriodicVelocityFourierMode solution t p) with hS
  have h1 : Tendsto (fun N =>
      (∑ p ∈ frequencyCube N, complexVectorL1 (openPeriodicVelocityFourierMode solution t p)) *
        openPeriodicJacobianCoefficientTailMass solution t (frequencyCube N)) atTop (𝓝 0) := by
    refine squeeze_zero (fun N => mul_nonneg (Finset.sum_nonneg fun _ _ => complexVectorL1_nonneg _)
      (jacobianTailMass_nonneg solution t _)) (fun N => ?_)
      (by simpa using (tendsto_jacobianTailMass solution t).const_mul S)
    apply mul_le_mul_of_nonneg_right _ (jacobianTailMass_nonneg solution t _)
    exact hsum.sum_le_tsum _ (fun _ _ => complexVectorL1_nonneg _)
  have h2 : Tendsto (fun N => exteriorMass solution t N *
      openPeriodicJacobianCoefficientTailMass solution t ∅) atTop (𝓝 0) := by
    simpa using (tendsto_exteriorMass solution t).mul_const
      (openPeriodicJacobianCoefficientTailMass solution t ∅)
  have h := h1.add h2
  simp only [add_zero] at h
  exact h

/-- **The frontier defect vanishes.** -/
theorem tendsto_frontier_defect :
    Tendsto (fun N => frontierBound solution t N * exteriorMass solution t (2 * N)) atTop
      (𝓝 0) := by
  have h := (tendsto_frontierBound solution t).mul
    ((tendsto_exteriorMass solution t).comp tendsto_two_mul_atTop)
  simpa using h

include solution in
/-- **The band budgets converge to the exact dissipation law.** -/
theorem tendsto_bandBudget :
    Tendsto (fun N =>
      deriv (NavierStokesBandEnergyBudget.bandMass (velocity := velocity) (frequencyCube (2 * N)))
          t.1 +
        2 * nu * NavierStokesBandEnergyBudget.bandDissipation (velocity := velocity)
          (frequencyCube (2 * N)) t.1) atTop (𝓝 0) := by
  refine squeeze_zero_norm (fun N => ?_)
    (by simpa using (tendsto_frontier_defect solution t).const_mul 2)
  rw [Real.norm_eq_abs]
  exact abs_deriv_bandMass_add_dissipation_le solution t N

end Holonics.Millennium.NavierStokesFrontierVanishing
