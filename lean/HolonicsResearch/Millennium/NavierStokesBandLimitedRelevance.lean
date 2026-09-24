import HolonicsResearch.Millennium.NavierStokesShellBudget

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

namespace Holonics.Millennium.NavierStokesBandLimitedRelevance

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
open Holonics.Millennium.NavierStokesH3Production
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
open Holonics.Millennium.NavierStokesFourierKirchhoff
open Holonics.Millennium.NavierStokesOpenFourierSpatialSymbols
open Holonics.Millennium.NavierStokesBandEnergyBudget
open Holonics.Millennium.NavierStokesRelevanceBudget
open Holonics.Millennium.NavierStokesShellBudget

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

end Holonics.Millennium.NavierStokesBandLimitedRelevance
