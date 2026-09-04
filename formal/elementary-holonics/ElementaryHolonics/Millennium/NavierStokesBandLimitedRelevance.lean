import ElementaryHolonics.Millennium.NavierStokesShellBudget

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

namespace Soma.Holonics.Millennium.NavierStokesBandLimitedRelevance

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
open Soma.Holonics.Millennium.NavierStokesH3Production
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
open Soma.Holonics.Millennium.NavierStokesFourierKirchhoff
open Soma.Holonics.Millennium.NavierStokesOpenFourierSpatialSymbols
open Soma.Holonics.Millennium.NavierStokesBandEnergyBudget
open Soma.Holonics.Millennium.NavierStokesRelevanceBudget
open Soma.Holonics.Millennium.NavierStokesShellBudget

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

end Soma.Holonics.Millennium.NavierStokesBandLimitedRelevance
