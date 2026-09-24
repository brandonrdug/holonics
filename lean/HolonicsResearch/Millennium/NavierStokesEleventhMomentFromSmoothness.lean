import HolonicsResearch.Millennium.NavierStokesVelocityMassEnergy
import Holonics.Millennium.NavierStokesSmoothSliceWeightedAllOrders

/-!
# The eleventh moment is finite at every time, from smoothness alone

Every slice of an open periodic solution is a smooth periodic field, so its Fourier
coefficients carry every finite Sobolev order (the all-orders owner).  The eleventh vorticity
moment `Σ_q sup(q)^{11} ‖ω̂_q‖²` is dominated by `(2π)^{−12} Σ_q λ_q^7 ‖û_q‖²` with `λ_q` the
Stokes eigenvalue, hence finite.  The summability clause of the coherence-defect tail control
is therefore derivable, and the official problem follows from the defect bound along a tail
together with the compact eleventh-moment bound alone.
-/

open Set Filter Topology MeasureTheory
open scoped Finset
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
open Holonics.Millennium.NavierStokesMomentClosure
open Holonics.Millennium.NavierStokesIncoherentSource
open Holonics.Millennium.NavierStokesIncoherentClosure
open Holonics.Millennium.NavierStokesVelocityMassEnergy
open Holonics.Millennium.NavierStokesFiniteFourierHeat
open Holonics.Millennium.NavierStokesSmoothSliceWeightedAllOrders
open Holonics.Millennium.NavierStokesModalRiccati
open Holonics.Millennium.NavierStokesHalfRadiusReach
open Holonics.Millennium.NavierStokesMomentSwap
open Holonics.Millennium.NavierStokesMomentGap

namespace Holonics.Millennium.NavierStokesEleventhMomentFromSmoothness

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
  (t : Ioo 0 T)

theorem frequencySquared_nonneg' (q : SpatialFrequency) : 0 ≤ frequencySquared q := by
  unfold frequencySquared
  positivity

theorem sup_pow_eleven_le (q : SpatialFrequency) :
    ((frequencySup q : ℕ) : ℝ) ^ 11 ≤ frequencySquared q ^ 6 := by
  have hfs := frequencySup_sq_le_frequencySquared q
  rcases Nat.eq_zero_or_pos (frequencySup q) with h0 | hpos
  · rw [h0]
    simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact pow_nonneg (frequencySquared_nonneg' q) 6
  · have h1 : (1 : ℝ) ≤ ((frequencySup q : ℕ) : ℝ) := by exact_mod_cast hpos
    calc ((frequencySup q : ℕ) : ℝ) ^ 11 ≤ ((frequencySup q : ℕ) : ℝ) ^ 12 :=
          pow_le_pow_right₀ h1 (by norm_num)
      _ = (((frequencySup q : ℕ) : ℝ) ^ 2) ^ 6 := by ring
      _ ≤ frequencySquared q ^ 6 := pow_le_pow_left₀ (by positivity) hfs 6

theorem eleventhMoment_le_stokes (q : SpatialFrequency) :
    eleventhMoment (velocity := velocity) t.1 q ≤
      (2 * Real.pi) ^ 2 / (2 * Real.pi) ^ 14 *
        (torusStokesEigenvalue q ^ 7 * velPop solution t q) := by
  unfold eleventhMoment
  rw [modalEnergy_eq_velPop solution t q, torusStokesEigenvalue]
  have h := sup_pow_eleven_le q
  have hv := velPop_nonneg solution t q
  have hfs0 := frequencySquared_nonneg' q
  have hR : (2 * Real.pi) ^ 2 / (2 * Real.pi) ^ 14 *
      (((2 * Real.pi) ^ 2 * frequencySquared q) ^ 7 * velPop solution t q) =
      (2 * Real.pi) ^ 2 * frequencySquared q ^ 7 * velPop solution t q := by
    field_simp
  rw [hR]
  calc ((frequencySup q : ℕ) : ℝ) ^ 11 * ((2 * Real.pi) ^ 2 * frequencySquared q * velPop solution t q)
      ≤ frequencySquared q ^ 6 * ((2 * Real.pi) ^ 2 * frequencySquared q * velPop solution t q) :=
        mul_le_mul_of_nonneg_right h (mul_nonneg (mul_nonneg (by positivity) hfs0) hv)
    _ = (2 * Real.pi) ^ 2 * frequencySquared q ^ 7 * velPop solution t q := by ring

/-- Every Stokes-weighted velocity population is summable, from smoothness. -/
theorem summable_stokes_pow_mul_velPop (order : ℕ) :
    Summable fun q ↦ torusStokesEigenvalue q ^ order * velPop solution t q := by
  have hsplit : (fun q ↦ torusStokesEigenvalue q ^ order * velPop solution t q) =
      fun q ↦ ∑ c : Fin 3,
        torusStokesEigenvalue q ^ order * ‖openPeriodicVelocityFourierMode solution t q c‖ ^ 2 := by
    funext q
    unfold velPop
    rw [Finset.mul_sum]
  rw [hsplit]
  apply summable_sum
  intro c _
  simp_rw [velocityMode_eq_smoothSliceFourierL2]
  exact summable_stokesPower_mul_norm_sq_smoothSliceFourierL2 _ _ _ c order

include solution in
/-- **The eleventh moment is finite at every time.** -/
theorem summable_eleventhMoment : Summable (eleventhMoment (velocity := velocity) t.1) :=
  Summable.of_nonneg_of_le
    (fun q => mul_nonneg (by positivity) (modalEnergy_nonneg q t.1))
    (eleventhMoment_le_stokes solution t)
    ((summable_stokes_pow_mul_velPop solution t 7).mul_left _)

/-! ## The tail control without its summability clause -/

/-- **Coherence-defect tail control, defect and compact bound only.**  Along a terminal tail
`[s, T)` every nonzero receiver has coherence defect at most `κ`, and the eleventh moment is
bounded on every compact `[s, τ]`, `τ < T`. -/
def CoherenceDefectTailControl' : Prop :=
  ∀ {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField},
    0 < nu →
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) →
      ∃ (s κ : ℝ), 0 < s ∧ s < T ∧ 0 ≤ κ ∧
        (∀ σ (hσ : σ ∈ Ioo 0 T), s ≤ σ →
          ∀ k : SpatialFrequency, k ≠ 0 → CoherenceDefectAt solution ⟨σ, hσ⟩ κ k) ∧
        (∀ τ ∈ Ioo s T, ∃ B : ℝ, ∀ σ ∈ Icc s τ, moment (velocity := velocity) 11 σ ≤ B)

theorem coherenceDefectTailControl_of_defect (h : CoherenceDefectTailControl') :
    CoherenceDefectTailControl := by
  intro T nu initial velocity pressure hnu solution
  obtain ⟨s, κ, hs0, hsT, hκ, hdef, hcompact⟩ := h hnu solution
  exact ⟨s, κ, hs0, hsT, hκ,
    fun σ hσ hsσ => ⟨summable_eleventhMoment solution ⟨σ, hσ⟩, hdef σ hσ hsσ⟩, hcompact⟩

/-- **The official problem from the defect bound and the compact eleventh-moment bound.** -/
theorem officialProblem_of_defect (h : CoherenceDefectTailControl') :
    TheOfficialNavierStokesProblem :=
  officialProblem_of_coherenceDefectTail (coherenceDefectTailControl_of_defect h)

end Holonics.Millennium.NavierStokesEleventhMomentFromSmoothness
