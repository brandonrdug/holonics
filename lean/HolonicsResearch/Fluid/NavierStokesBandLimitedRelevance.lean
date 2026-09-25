import HolonicsResearch.Fluid.NavierStokesShellBudget

/-!
# Band-limited relevance: a slice supported in the cube of radius `N` carries no transfer
current beyond the cube of radius `2N`

Every feed tooth into a receiver outside the double cube has a participant outside the cube, so
for a band-limited slice every such tooth vanishes, the advection mode vanishes there, and the
transfer current into the complement of the double cube is zero.  With the Kirchhoff law the
transfer of a band-limited slice is conserved within twice its band, and its double-cube mass
dissipates without exchange.  This is the relevance theorem in its cleanest form: nothing feeds
the far tail but the tail itself.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Finset

namespace Holonics.Fluid.NavierStokesBandLimitedRelevance

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

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
  (t : Ioo 0 T)

/-- A slice supported in the cube of radius `N`. -/
def BandLimited (N : ℕ) : Prop :=
  ∀ p, p ∉ frequencyCube N → openPeriodicVelocityFourierMode solution t p = 0

theorem jacobianMode_eq_zero_of_bandLimited {N : ℕ} (h : BandLimited solution t N)
    {q : SpatialFrequency} (hq : q ∉ frequencyCube N) :
    openPeriodicJacobianFourierMode solution t q = 0 := by
  rw [openPeriodicJacobianFourierMode_eq_fourierJacobianMode, h q hq]
  funext o c
  simp [fourierJacobianMode]

/-- **Every feed tooth into the far tail vanishes.** -/
theorem feedTerm_eq_zero_of_bandLimited {N : ℕ} (h : BandLimited solution t N)
    {k : SpatialFrequency} (hk : k ∉ frequencyCube (2 * N)) (p : SpatialFrequency)
    (output : Fin 3) : feedTerm solution t k p output = 0 := by
  unfold feedTerm
  by_cases hp : p ∈ frequencyCube N
  · rw [jacobianMode_eq_zero_of_bandLimited solution t h (transported_not_mem hk hp)]
    simp
  · rw [h p hp]
    simp

theorem advectionMode_eq_zero_of_bandLimited {N : ℕ} (h : BandLimited solution t N)
    {k : SpatialFrequency} (hk : k ∉ frequencyCube (2 * N)) (output : Fin 3) :
    openActualAdvectionMode solution t k output = 0 := by
  rw [openActualAdvectionMode_eq_tsum_feedTerm]
  simp [feedTerm_eq_zero_of_bandLimited solution t h hk]

theorem transfer_eq_zero_of_bandLimited {N : ℕ} (h : BandLimited solution t N)
    {k : SpatialFrequency} (hk : k ∉ frequencyCube (2 * N)) :
    transfer solution t k = 0 := by
  unfold transfer
  simp [advectionMode_eq_zero_of_bandLimited solution t h hk]

/-- **A band-limited slice has no current beyond twice its band.** -/
theorem tsum_compl_transfer_eq_zero {N : ℕ} (h : BandLimited solution t N) :
    ∑' k : ↑((↑(frequencyCube (2 * N)) : Set SpatialFrequency)ᶜ), transfer solution t k = 0 := by
  have hfun : (fun k : ↑((↑(frequencyCube (2 * N)) : Set SpatialFrequency)ᶜ) ↦
      transfer solution t k) = 0 := by
    funext k
    exact transfer_eq_zero_of_bandLimited solution t h fun hmem ↦ k.2 (Finset.mem_coe.mpr hmem)
  rw [hfun]
  exact tsum_zero

/-- **The transfer of a band-limited slice is conserved within twice its band.** -/
theorem sum_transfer_cube_eq_zero {N : ℕ} (h : BandLimited solution t N) :
    ∑ k ∈ frequencyCube (2 * N), transfer solution t k = 0 := by
  have := sum_transfer_add_tsum_compl solution t (frequencyCube (2 * N))
  rw [tsum_compl_transfer_eq_zero solution t h] at this
  simpa using this

/-- **The double-cube mass of a band-limited slice dissipates without exchange.** -/
theorem hasDerivAt_bandMass_of_bandLimited {N : ℕ} (h : BandLimited solution t N) :
    HasDerivAt (NavierStokesBandEnergyBudget.bandMass (velocity := velocity) (frequencyCube (2 * N)))
      (-2 * nu * bandDissipation (velocity := velocity) (frequencyCube (2 * N)) t.1) t.1 := by
  have := hasDerivAt_bandMass_kirchhoff solution t (frequencyCube (2 * N))
  rw [tsum_compl_transfer_eq_zero solution t h] at this
  simpa using this

section Audit

#print axioms feedTerm_eq_zero_of_bandLimited
#print axioms sum_transfer_cube_eq_zero
#print axioms hasDerivAt_bandMass_of_bandLimited

end Audit

end Holonics.Fluid.NavierStokesBandLimitedRelevance
