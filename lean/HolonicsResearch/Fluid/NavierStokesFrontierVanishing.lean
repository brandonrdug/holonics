import HolonicsResearch.Fluid.NavierStokesFrontierTransfer
import HolonicsResearch.Fluid.NavierStokesTailRelevance

/-!
# The frontier defect vanishes as the band grows

The exterior `ℓ¹` velocity mass and the Jacobian tail mass are tails of summable series over
the cubes, so both tend to zero as the radius grows; the frontier product is bounded by a
constant times the Jacobian tail plus the exterior mass times a constant, so it tends to zero
too.  Hence the band energy budgets `dE_{C_{2N}}/dt + 2ν D_{C_{2N}}` converge to zero: in the
limit of the whole lattice the energy law is exact dissipation.
-/

noncomputable section

namespace Holonics.Fluid.NavierStokesFrontierVanishing

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
open Holonics.Fluid.NavierStokesFrontierTransfer
open Holonics.Fluid.NavierStokesTailRelevance

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

end Holonics.Fluid.NavierStokesFrontierVanishing
