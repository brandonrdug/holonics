import HolonicsResearch.Millennium.NavierStokesIncoherentClosure

/-!
# The velocity mass is paid by the kinetic energy at the start of the tail

Parseval on each component of the velocity slice identifies the velocity mass with the cube
integral of the velocity square, `V(t) = Σ_c ∫ (u_c)² ≤ 3 · 2 · E_kin(t)`, and the unforced
energy--dissipation identity on the open lifespan makes the kinetic energy nonincreasing.  So the
velocity-mass premise of `CoherenceDefectControl` is discharged by `V₀ = 3 · 2 · E_kin(s)`, and
`StatementB` follows from incoherence and interior finiteness alone.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Finset

namespace Holonics.Millennium.NavierStokesVelocityMassEnergy

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

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
  (t : Ioo 0 T)

/-! ## Parseval on the slice -/

theorem velocityMode_eq_smoothSliceFourierL2 (p : SpatialFrequency) (c : Fin 3) :
    openPeriodicVelocityFourierMode solution t p c =
      smoothSliceFourierL2 (fun x ↦ velocity x t.1)
        (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
        (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩) c p := by
  rw [← sliceState_coeff]
  rfl

theorem tsum_sq_velocityMode_eq (c : Fin 3) :
    ∑' p, ‖openPeriodicVelocityFourierMode solution t p c‖ ^ 2 =
      ∫ x in NavierStokesPeriodicFlux.unitCube, (velocity x t.1 c) ^ 2 := by
  simp_rw [velocityMode_eq_smoothSliceFourierL2]
  exact tsum_sq_smoothSliceFourierL2_eq_integral_unitCube _ _ _ c

theorem summable_sq_velocityMode (c : Fin 3) :
    Summable fun p ↦ ‖openPeriodicVelocityFourierMode solution t p c‖ ^ 2 := by
  simp_rw [velocityMode_eq_smoothSliceFourierL2]
  exact (hasSum_sq_smoothSliceFourierL2 _ _ _ c).summable

/-- **The velocity mass is at most three times twice the kinetic energy.** -/
theorem velocityMass_le_kineticEnergy :
    velocityMass solution t ≤ 3 * (2 * periodicKineticEnergy velocity t.1) := by
  unfold velocityMass velPop
  calc ∑' p, ∑ c : Fin 3, ‖openPeriodicVelocityFourierMode solution t p c‖ ^ 2
      = ∑ c : Fin 3, ∑' p, ‖openPeriodicVelocityFourierMode solution t p c‖ ^ 2 :=
        Summable.tsum_finsetSum fun c _ ↦ summable_sq_velocityMode solution t c
    _ = ∑ c : Fin 3, ∫ x in NavierStokesPeriodicFlux.unitCube, (velocity x t.1 c) ^ 2 :=
        Finset.sum_congr rfl fun c _ ↦ tsum_sq_velocityMode_eq solution t c
    _ ≤ ∑ _c : Fin 3, 2 * periodicKineticEnergy velocity t.1 :=
        Finset.sum_le_sum fun c _ ↦
          componentCubeEnergy_le_two_mul_periodicKineticEnergy solution t c
    _ = 3 * (2 * periodicKineticEnergy velocity t.1) := by simp

/-! ## The kinetic energy is nonincreasing on the open lifespan -/

include solution in
theorem periodicKineticEnergy_le_of_le (hnu : 0 ≤ nu) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbT : b < T) :
    periodicKineticEnergy velocity b ≤ periodicKineticEnergy velocity a := by
  have h := openPeriodicSolutionOn_periodicKineticEnergy_add_integral_dissipation_eq solution ha hab hbT
  have hint : 0 ≤ ∫ τ in a..b, coordinateH0Dissipation velocity τ :=
    intervalIntegral.integral_nonneg hab fun τ _ ↦ coordinateH0Dissipation_nonneg velocity τ
  nlinarith [mul_nonneg hnu hint]

/-- **The velocity mass along a terminal tail is paid by the kinetic energy at its start.** -/
theorem velocityMass_le_of_le (hnu : 0 ≤ nu) {s : ℝ} (hs : 0 < s) (σ : Ioo 0 T) (hsσ : s ≤ σ.1) :
    velocityMass solution σ ≤ 3 * (2 * periodicKineticEnergy velocity s) := by
  calc velocityMass solution σ ≤ 3 * (2 * periodicKineticEnergy velocity σ.1) :=
        velocityMass_le_kineticEnergy solution σ
    _ ≤ 3 * (2 * periodicKineticEnergy velocity s) := by
        have := periodicKineticEnergy_le_of_le solution hnu hs hsσ σ.2.2
        linarith

/-! ## The closure statement without the velocity-mass premise -/

/-- **Coherence-defect tail control.**  Along a terminal tail `[s, T)` every nonzero receiver has
coherence defect at most `κ` and the eleventh moment is finite, with a bound on every compact
`[s, τ]`, `τ < T`. -/
def CoherenceDefectTailControl : Prop :=
  ∀ {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField},
    0 < nu →
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) →
      ∃ (s κ : ℝ), 0 < s ∧ s < T ∧ 0 ≤ κ ∧
        (∀ σ (hσ : σ ∈ Ioo 0 T), s ≤ σ →
          Summable (eleventhMoment (velocity := velocity) σ) ∧
            ∀ k : SpatialFrequency, k ≠ 0 → CoherenceDefectAt solution ⟨σ, hσ⟩ κ k) ∧
        (∀ τ ∈ Ioo s T, ∃ B : ℝ, ∀ σ ∈ Icc s τ, moment (velocity := velocity) 11 σ ≤ B)

theorem coherenceDefectControl_of_tail (h : CoherenceDefectTailControl) : CoherenceDefectControl := by
  intro T nu initial velocity pressure hnu solution
  obtain ⟨s, κ, hs0, hsT, hκ, htail, hcompact⟩ := h hnu solution
  refine ⟨s, 3 * (2 * periodicKineticEnergy velocity s), κ, hs0, hsT, ?_, hκ, ?_, hcompact⟩
  · have := periodicKineticEnergy_nonneg velocity s
    positivity
  · intro σ hσ hsσ
    exact ⟨(htail σ hσ hsσ).1, velocityMass_le_of_le solution hnu.le hs0 ⟨σ, hσ⟩ hsσ,
      (htail σ hσ hsσ).2⟩

/-- **The second moment along a terminal tail on incoherent feeds, in the kinetic energy.** -/
theorem moment_two_le_kineticEnergy (hnu : 0 < nu) {s τ : ℝ} (hs : s ∈ Ioo 0 T) (hτ : τ ∈ Ioo 0 T)
    (hsτ : s ≤ τ) {κ B : ℝ} (hκ : 0 ≤ κ) (hB : 0 ≤ B)
    (hσ : ∀ σ (hσ : σ ∈ Ioo 0 T), σ ∈ Icc s τ →
      Summable (eleventhMoment (velocity := velocity) σ) ∧
        (∀ k : SpatialFrequency, k ≠ 0 → CoherenceDefectAt solution ⟨σ, hσ⟩ κ k) ∧
        moment (velocity := velocity) 11 σ ≤ B) :
    moment (velocity := velocity) 2 τ ≤ moment (velocity := velocity) 2 s *
      Real.exp (21 * defectConstant κ * (3 * (2 * periodicKineticEnergy velocity s)) /
        (nu * (2 * Real.pi) ^ 2) * (τ - s)) := by
  have hE := periodicKineticEnergy_nonneg velocity s
  have hc0 := defectConstant_nonneg hκ
  refine moment_two_le solution hnu hs hτ hsτ hκ (by positivity) hB fun σ hσT hσI ↦ ?_
  exact ⟨(hσ σ hσT hσI).1, velocityMass_le_of_le solution hnu.le hs.1 ⟨σ, hσT⟩ hσI.1,
    (hσ σ hσT hσI).2.1, (hσ σ hσT hσI).2.2⟩

/-- **Incoherent tail control returns Statement B.** -/
theorem statementB_of_coherenceDefectTail (h : CoherenceDefectTailControl) : StatementB :=
  statementB_of_coherenceDefect (coherenceDefectControl_of_tail h)

theorem officialProblem_of_coherenceDefectTail (h : CoherenceDefectTailControl) :
    TheOfficialNavierStokesProblem :=
  officialProblem_of_coherenceDefect (coherenceDefectControl_of_tail h)

section Audit

#print axioms velocityMass_le_kineticEnergy
#print axioms periodicKineticEnergy_le_of_le
#print axioms moment_two_le_kineticEnergy
#print axioms statementB_of_coherenceDefectTail

end Audit

end Holonics.Millennium.NavierStokesVelocityMassEnergy
