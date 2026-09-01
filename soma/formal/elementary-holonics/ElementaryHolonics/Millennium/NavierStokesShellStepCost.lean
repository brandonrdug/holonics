import ElementaryHolonics.Millennium.NavierStokesFrequencyReach
import ElementaryHolonics.Millennium.NavierStokesTailRelevance
import ElementaryHolonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
import ElementaryHolonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration
import ElementaryHolonics.Millennium.NavierStokesOpenFourierMildIdentity
import ElementaryHolonics.Millennium.NavierStokesH2VorticityShellDissipationBridge

/-!
# The shell-step cost: a tail mode is fed only in proportion to the tail

The advection coefficient at a frequency `k` is the complete infinite triad convolution
(`openActualAdvectionMode_eq_h3AdvectiveConvolution`).  This owner writes it as a sum of feed terms,
one per advecting frequency `p`, each pairing the velocity coefficient at `p` with the Jacobian
coefficient at `k − p`, and splits it by the reach theorem into a band-fed part (`p` inside the
cube of radius `N`) and a tail-fed part.

For a receiver outside the cube of radius `2N` every band-fed term transports a Jacobian
coefficient from outside the cube of radius `N` (`tail_fed_only_through_tail`), so

```text
‖bandFeed‖ ≤ bandMass(N) · tailJ(N),      bandMass(N) ≤ (2N+1)³ · 3·√(2·E(0)),
‖tailFeed‖ ≤ velocityTail(N) · totalJ,
```

where `tailJ(N)` is Sol's Jacobian coefficient tail mass beyond the cube, `velocityTail(N)` the
velocity coefficient tail mass, and `totalJ` the complete Jacobian coefficient mass.  Both feeds
vanish with the tail: a tail mode cannot be fed except in proportion to the tail.  The band
coefficient is an integer face count times the half-density of the initial energy; that count is
the coherent composition of the band, and replacing it by its incoherent square root is the
half-power step named in the record.

The vorticity form multiplies by the curl symbol, so the nonlinear source of the exact per-mode
vorticity equation (`openPeriodicSolutionOn_hasDerivAt_vorticityMode_stokes`) obeys the same
proportionality.  Nothing here sums over the tail or closes a differential inequality; that is the
Riccati owner this one prepares.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Finset

namespace Soma.Holonics.Millennium.NavierStokesShellStepCost

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

/-! ## The slice coefficient state and its identification -/

/-- The native `H³` coefficient state of the velocity slice at `t`. -/
abbrev sliceState :=
  smoothSliceH3State (fun x ↦ velocity x t.1)
    (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
    (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)

theorem sliceState_coeff (component : Fin 3) (p : SpatialFrequency) :
    (sliceState solution t component).1 p =
      openPeriodicVelocityFourierMode solution t p component := by
  show smoothSliceFourierL2 _ _ _ component p = _
  rw [smoothSliceFourierL2_apply]
  rfl

theorem summable_norm_velocityMode (component : Fin 3) :
    Summable fun p ↦ ‖openPeriodicVelocityFourierMode solution t p component‖ := by
  have h := periodicVectorSobolevThree_hasAbsolutelySummableComponents (sliceState solution t)
    component
  simp_rw [sliceState_coeff] at h
  exact h

theorem summable_complexVectorL1_velocityMode :
    Summable fun p ↦ complexVectorL1 (openPeriodicVelocityFourierMode solution t p) := by
  unfold complexVectorL1
  exact ((summable_norm_velocityMode solution t 0).add
    (summable_norm_velocityMode solution t 1)).add (summable_norm_velocityMode solution t 2)

theorem complexVectorL1_eq_sum (v : ComplexVector) :
    complexVectorL1 v = ∑ component : Fin 3, ‖v component‖ := by
  simp [complexVectorL1, Fin.sum_univ_three]

/-! ## Jacobian coefficient masses -/

/-- One entry of the Jacobian tail mass beyond a finite population of modes. -/
def jacobianEntryMass (modes : Finset SpatialFrequency) (output coordinate : Fin 3) : ℝ :=
  ∑' q : {q : SpatialFrequency // q ∉ modes},
    ‖openPeriodicJacobianFourierMode solution t q.1 output coordinate‖

theorem jacobianEntryMass_le_tailMass (modes : Finset SpatialFrequency)
    (output coordinate : Fin 3) :
    jacobianEntryMass solution t modes output coordinate ≤
      openPeriodicJacobianCoefficientTailMass solution t modes := by
  unfold openPeriodicJacobianCoefficientTailMass
  have h1 := norm_le_pi_norm (fun component : Fin 3 ↦ fun coordinate : Fin 3 ↦
    ∑' q : {q : SpatialFrequency // q ∉ modes},
      ‖openPeriodicJacobianFourierMode solution t q.1 component coordinate‖) output
  have h2 := norm_le_pi_norm (fun coordinate : Fin 3 ↦
    ∑' q : {q : SpatialFrequency // q ∉ modes},
      ‖openPeriodicJacobianFourierMode solution t q.1 output coordinate‖) coordinate
  refine le_trans ?_ (h2.trans h1)
  rw [Real.norm_eq_abs]
  exact le_abs_self _

theorem norm_jacobianMode_le_entryMass {modes : Finset SpatialFrequency} {q : SpatialFrequency}
    (hq : q ∉ modes) (output coordinate : Fin 3) :
    ‖openPeriodicJacobianFourierMode solution t q output coordinate‖ ≤
      jacobianEntryMass solution t modes output coordinate := by
  have hsum : Summable fun r : {q : SpatialFrequency // q ∉ modes} ↦
      ‖openPeriodicJacobianFourierMode solution t r.1 output coordinate‖ :=
    (summable_norm_openPeriodicJacobianFourierMode_entry solution t output coordinate).subtype _
  exact hsum.le_tsum ⟨q, hq⟩ (fun _ _ ↦ norm_nonneg _)

/-! ## Feed terms -/

/-- One feed term: the advecting coefficient at `p` against the transported Jacobian coefficient
at `k − p`, summed over the advecting coordinate. -/
def feedTerm (k p : SpatialFrequency) (output : Fin 3) : ℂ :=
  ∑ coordinate : Fin 3,
    openPeriodicVelocityFourierMode solution t p coordinate *
      openPeriodicJacobianFourierMode solution t (k - p) output coordinate

theorem norm_feedTerm_le {modes : Finset SpatialFrequency} {k p : SpatialFrequency}
    (hk : k - p ∉ modes) (output : Fin 3) :
    ‖feedTerm solution t k p output‖ ≤
      complexVectorL1 (openPeriodicVelocityFourierMode solution t p) *
        openPeriodicJacobianCoefficientTailMass solution t modes := by
  unfold feedTerm
  refine (norm_sum_le _ _).trans ?_
  rw [complexVectorL1_eq_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro coordinate _
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (norm_jacobianMode_le_entryMass solution t hk output coordinate).trans
    (jacobianEntryMass_le_tailMass solution t modes output coordinate)

theorem summable_feedTerm (k : SpatialFrequency) (output : Fin 3) :
    Summable fun p ↦ feedTerm solution t k p output := by
  refine Summable.of_norm_bounded
    (g := fun p ↦ complexVectorL1 (openPeriodicVelocityFourierMode solution t p) *
      openPeriodicJacobianCoefficientTailMass solution t ∅)
    ((summable_complexVectorL1_velocityMode solution t).mul_right _) ?_
  intro p
  exact norm_feedTerm_le solution t (by simp) output

/-- **The advection coefficient is the sum of its feed terms.** -/
theorem openActualAdvectionMode_eq_tsum_feedTerm (k : SpatialFrequency) (output : Fin 3) :
    openActualAdvectionMode solution t k output = ∑' p, feedTerm solution t k p output := by
  rw [openActualAdvectionMode_eq_h3AdvectiveConvolution]
  show h3AdvectiveConvolution (sliceState solution t) (sliceState solution t) output k = _
  rw [h3AdvectiveConvolution_apply
    (periodicVectorSobolevThree_hasAbsolutelySummableComponents _)]
  have hsummable : ∀ coordinate ∈ (Finset.univ : Finset (Fin 3)),
      Summable fun p ↦ openPeriodicVelocityFourierMode solution t p coordinate *
        openPeriodicJacobianFourierMode solution t (k - p) output coordinate := by
    intro coordinate _
    refine Summable.of_norm_bounded
      (g := fun p ↦ ‖openPeriodicVelocityFourierMode solution t p coordinate‖ *
        jacobianEntryMass solution t ∅ output coordinate)
      ((summable_norm_velocityMode solution t coordinate).mul_right _) ?_
    intro p
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (norm_jacobianMode_le_entryMass solution t (by simp) output coordinate) (norm_nonneg _)
  unfold feedTerm
  rw [Summable.tsum_finsetSum hsummable]
  apply Finset.sum_congr rfl
  intro coordinate _
  apply tsum_congr
  intro p
  rw [sliceState_coeff, sliceState_coeff]
  congr 1
  have h := congrFun (congrFun
    (openPeriodicJacobianFourierMode_eq_fourierJacobianMode solution t (k - p)) output) coordinate
  rw [h]
  rfl

/-! ## The split at a tail mode -/

/-- The band-fed part of the feed: advecting frequencies inside the cube. -/
def bandFeed (radius : ℕ) (k : SpatialFrequency) (output : Fin 3) : ℂ :=
  ∑ p ∈ frequencyCube radius, feedTerm solution t k p output

/-- The tail-fed part of the feed: advecting frequencies outside the cube. -/
def tailFeed (radius : ℕ) (k : SpatialFrequency) (output : Fin 3) : ℂ :=
  ∑' p : {p : SpatialFrequency // p ∉ frequencyCube radius}, feedTerm solution t k p.1 output

theorem openActualAdvectionMode_eq_bandFeed_add_tailFeed (radius : ℕ) (k : SpatialFrequency)
    (output : Fin 3) :
    openActualAdvectionMode solution t k output =
      bandFeed solution t radius k output + tailFeed solution t radius k output := by
  rw [openActualAdvectionMode_eq_tsum_feedTerm,
    ← (summable_feedTerm solution t k output).sum_add_tsum_subtype_compl (frequencyCube radius)]
  rfl

/-- The band mass: the velocity coefficient `ℓ¹` population inside the cube. -/
def bandMass (radius : ℕ) : ℝ :=
  ∑ p ∈ frequencyCube radius, complexVectorL1 (openPeriodicVelocityFourierMode solution t p)

/-- The velocity coefficient tail mass beyond the cube. -/
def velocityTailMass (radius : ℕ) : ℝ :=
  ∑' p : {p : SpatialFrequency // p ∉ frequencyCube radius},
    complexVectorL1 (openPeriodicVelocityFourierMode solution t p.1)

/-- **The band feeds a tail mode only through the tail.**  Outside the cube of radius `2N`, every
band-fed term transports a Jacobian coefficient from beyond the cube of radius `N`. -/
theorem norm_bandFeed_le {radius : ℕ} {k : SpatialFrequency}
    (hk : k ∉ frequencyCube (2 * radius)) (output : Fin 3) :
    ‖bandFeed solution t radius k output‖ ≤
      bandMass solution t radius *
        openPeriodicJacobianCoefficientTailMass solution t (frequencyCube radius) := by
  unfold bandFeed bandMass
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p hp
  have htransported : k - p ∉ frequencyCube radius := by
    intro hkp
    apply hk
    have := add_mem_frequencyCube hkp hp
    rw [sub_add_cancel, ← two_mul] at this
    exact this
  exact norm_feedTerm_le solution t htransported output

theorem norm_tailFeed_le (radius : ℕ) (k : SpatialFrequency) (output : Fin 3) :
    ‖tailFeed solution t radius k output‖ ≤
      velocityTailMass solution t radius * openPeriodicJacobianCoefficientTailMass solution t ∅ := by
  unfold tailFeed velocityTailMass
  have hsum : Summable fun p : {p : SpatialFrequency // p ∉ frequencyCube radius} ↦
      complexVectorL1 (openPeriodicVelocityFourierMode solution t p.1) :=
    (summable_complexVectorL1_velocityMode solution t).subtype _
  have hbound : ∀ p : {p : SpatialFrequency // p ∉ frequencyCube radius},
      ‖feedTerm solution t k p.1 output‖ ≤
        complexVectorL1 (openPeriodicVelocityFourierMode solution t p.1) *
          openPeriodicJacobianCoefficientTailMass solution t ∅ :=
    fun p ↦ norm_feedTerm_le solution t (by simp) output
  have hsumBound : Summable fun p : {p : SpatialFrequency // p ∉ frequencyCube radius} ↦
      complexVectorL1 (openPeriodicVelocityFourierMode solution t p.1) *
        openPeriodicJacobianCoefficientTailMass solution t ∅ :=
    hsum.mul_right _
  have hsumNorm : Summable fun p : {p : SpatialFrequency // p ∉ frequencyCube radius} ↦
      ‖feedTerm solution t k p.1 output‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hbound hsumBound
  rw [← tsum_mul_right]
  exact (norm_tsum_le_tsum_norm hsumNorm).trans (Summable.tsum_le_tsum hbound hsumNorm hsumBound)

/-- **The band mass is an integer face count times the half-density of the initial energy.** -/
theorem bandMass_le_count_mul_energy (hnu : 0 ≤ nu) (radius : ℕ) :
    bandMass solution t radius ≤
      (2 * radius + 1) ^ 3 * (3 * Real.sqrt (2 * periodicKineticEnergy velocity 0)) := by
  unfold bandMass
  have hE := openPeriodicSolutionOn_periodicKineticEnergy_le_initial solution hnu t.2
  have hsqrt : Real.sqrt (2 * periodicKineticEnergy velocity t.1) ≤
      Real.sqrt (2 * periodicKineticEnergy velocity 0) :=
    Real.sqrt_le_sqrt (by linarith)
  have hterm : ∀ p ∈ frequencyCube radius,
      complexVectorL1 (openPeriodicVelocityFourierMode solution t p) ≤
        3 * Real.sqrt (2 * periodicKineticEnergy velocity 0) := by
    intro p _
    exact (complexVectorL1_openPeriodicVelocityFourierMode_le_L2RootReceiver solution t p).trans
      ((openPeriodicVelocityL2RootReceiver_le_kineticEnergy solution t).trans
        (mul_le_mul_of_nonneg_left hsqrt (by norm_num)))
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, card_frequencyCube, nsmul_eq_mul]
  push_cast
  exact le_rfl

/-- **The shell-step cost.**  Outside the cube of radius `2N` the advection coefficient is paid
by the tail alone: the band pays through the Jacobian tail beyond `N`, the tail pays through the
velocity tail beyond `N`. -/
theorem norm_openActualAdvectionMode_le (hnu : 0 ≤ nu) {radius : ℕ} {k : SpatialFrequency}
    (hk : k ∉ frequencyCube (2 * radius)) (output : Fin 3) :
    ‖openActualAdvectionMode solution t k output‖ ≤
      (2 * radius + 1) ^ 3 * (3 * Real.sqrt (2 * periodicKineticEnergy velocity 0)) *
          openPeriodicJacobianCoefficientTailMass solution t (frequencyCube radius) +
        velocityTailMass solution t radius *
          openPeriodicJacobianCoefficientTailMass solution t ∅ := by
  rw [openActualAdvectionMode_eq_bandFeed_add_tailFeed solution t radius]
  refine (norm_add_le _ _).trans (add_le_add ?_ (norm_tailFeed_le solution t radius k output))
  refine (norm_bandFeed_le solution t hk output).trans ?_
  exact mul_le_mul_of_nonneg_right (bandMass_le_count_mul_energy solution t hnu radius)
    (norm_nonneg _)

section Audit

#print axioms openActualAdvectionMode_eq_tsum_feedTerm
#print axioms openActualAdvectionMode_eq_bandFeed_add_tailFeed
#print axioms norm_bandFeed_le
#print axioms norm_tailFeed_le
#print axioms bandMass_le_count_mul_energy
#print axioms norm_openActualAdvectionMode_le

end Audit

end Soma.Holonics.Millennium.NavierStokesShellStepCost
