import ElementaryHolonics.Millennium.NavierStokesFrontierTransfer
import ElementaryHolonics.Millennium.NavierStokesTailRelevance

/-!
# The frontier defect vanishes as the band grows

The exterior `ℓ¹` velocity mass and the Jacobian tail mass are tails of summable series over
the cubes, so both tend to zero as the radius grows; the frontier product is bounded by a
constant times the Jacobian tail plus the exterior mass times a constant, so it tends to zero
too.  Hence the band energy budgets `dE_{C_{2N}}/dt + 2ν D_{C_{2N}}` converge to zero: in the
limit of the whole lattice the energy law is exact dissipation.
-/

noncomputable section

namespace Soma.Holonics.Millennium.NavierStokesFrontierVanishing

open Set Filter Topology MeasureTheory Complex
open scoped Finset ComplexConjugate ContDiff
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
open Soma.Holonics.Millennium.NavierStokesTorusCubeIntegral
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open scoped ComplexConjugate
open Soma.Holonics.Millennium.NavierStokesShellStepCost
open Soma.Holonics.Millennium.NavierStokesFrontierFeed
open Soma.Holonics.Millennium.NavierStokesFourierKirchhoff
open Soma.Holonics.Millennium.NavierStokesBandEnergyBudget
open Soma.Holonics.Millennium.NavierStokesFrontierTransfer
open Soma.Holonics.Millennium.NavierStokesTailRelevance

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

end Soma.Holonics.Millennium.NavierStokesFrontierVanishing
