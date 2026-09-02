import ElementaryHolonics.Millennium.NavierStokesBandBarycenter
import ElementaryHolonics.Millennium.NavierStokesTailRelevance
import ElementaryHolonics.Millennium.NavierStokesVelocityMassEnergy

/-!
# The coherence defect in barycentric terms

On a finite comb of `n` teeth with barycenter `m` and spread `Σ ‖z − m‖²`,

```text
‖Σ z‖² ≤ (1 + κ) Σ ‖z‖²   ⟺   n (n − 1 − κ) ‖m‖² ≤ (1 + κ) · spread.
```

The comb power is the count times the barycentric mass, `‖Σ z‖² = n · (n ‖m‖²)`, so the defect is
the count times the barycentric fraction of the diagonal.  The cubes exhaust the lattice and the
band feeds converge to the advection mode, so the barycentric condition on every cube returns the
coherence defect at the receiver, and with it `StatementB`.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Finset

namespace Soma.Holonics.Millennium.NavierStokesCombBarycenterDefect

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

/-! ## Any finite comb -/

section General

variable {ι : Type*} [DecidableEq ι]

/-- **The comb power is the count times the barycentric mass.** -/
theorem norm_sum_sq_eq_card_sq_mul_mean_sq (s : Finset ι) (hs : s.Nonempty) (z : ι → ℂ) :
    ‖∑ p ∈ s, z p‖ ^ 2 = (s.card : ℝ) ^ 2 * ‖mean s z‖ ^ 2 := by
  have hn : ‖(s.card : ℂ)‖ = (s.card : ℝ) := by simp
  rw [sum_eq_card_mul_mean s hs, norm_mul, mul_pow, hn]

/-- **The defect of a finite comb in barycentric terms.** -/
theorem norm_sum_sq_le_iff_barycenter (s : Finset ι) (hs : s.Nonempty) (z : ι → ℂ) (κ : ℝ) :
    ‖∑ p ∈ s, z p‖ ^ 2 ≤ (1 + κ) * ∑ p ∈ s, ‖z p‖ ^ 2 ↔
      (s.card : ℝ) * ((s.card : ℝ) - 1 - κ) * ‖mean s z‖ ^ 2 ≤
        (1 + κ) * ∑ p ∈ s, ‖z p - mean s z‖ ^ 2 := by
  rw [norm_sum_sq_eq_card_sq_mul_mean_sq s hs z, sum_norm_sub_mean_sq s hs z]
  constructor <;> intro h <;> linarith

end General

/-! ## The comb at a receiver -/

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
  (t : Ioo 0 T)

theorem summable_feedTerm (hsum : Summable (eleventhMoment (velocity := velocity) t.1))
    (k : SpatialFrequency) (output : Fin 3) :
    Summable fun p ↦ feedTerm solution t k p output := by
  refine Summable.of_norm ?_
  exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun p ↦ norm_feedTerm_le_sqrt solution t k p output)
    (summable_conv (l1Pop_nonneg solution t) (rootEnergy_nonneg t) (summable_l1Pop solution t)
      (summable_rootEnergy_sq solution t hsum) k)

theorem hasSum_feedTerm (hsum : Summable (eleventhMoment (velocity := velocity) t.1))
    (k : SpatialFrequency) (output : Fin 3) :
    HasSum (fun p ↦ feedTerm solution t k p output) (openActualAdvectionMode solution t k output) := by
  rw [openActualAdvectionMode_eq_tsum_feedTerm]
  exact (summable_feedTerm solution t hsum k output).hasSum

/-- **The band feeds converge to the advection mode along the cubes.** -/
theorem tendsto_bandFeed (hsum : Summable (eleventhMoment (velocity := velocity) t.1))
    (k : SpatialFrequency) (output : Fin 3) :
    Tendsto (fun N ↦ bandFeed solution t N k output) atTop
      (𝓝 (openActualAdvectionMode solution t k output)) :=
  (hasSum_feedTerm solution t hsum k output).comp tendsto_frequencyCube_atTop

/-- **The defect passes from the cubes to the whole comb.** -/
theorem coherenceDefectAt_of_cubes (hsum : Summable (eleventhMoment (velocity := velocity) t.1))
    {κ : ℝ} (hκ : 0 ≤ κ) (k : SpatialFrequency)
    (h : ∀ (output : Fin 3) (N : ℕ), ‖bandFeed solution t N k output‖ ^ 2 ≤
      (1 + κ) * bandDiagonal solution t N k output) :
    CoherenceDefectAt solution t κ k := by
  intro output
  have hlim : Tendsto (fun N ↦ ‖bandFeed solution t N k output‖ ^ 2) atTop
      (𝓝 (‖openActualAdvectionMode solution t k output‖ ^ 2)) :=
    ((tendsto_bandFeed solution t hsum k output).norm).pow 2
  refine le_of_tendsto' hlim fun N ↦ (h output N).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  exact (summable_sq_feedTerm solution t hsum k output).sum_le_tsum _ fun p _ ↦ sq_nonneg _

/-- **The barycentric condition on every cube returns the coherence defect.** -/
theorem coherenceDefectAt_of_barycenter (hsum : Summable (eleventhMoment (velocity := velocity) t.1))
    {κ : ℝ} (hκ : 0 ≤ κ) (k : SpatialFrequency)
    (h : ∀ (output : Fin 3) (N : ℕ),
      ((2 * N + 1) ^ 3 : ℝ) * (((2 * N + 1) ^ 3 : ℝ) - 1 - κ) *
          ‖bandBarycenter solution t N k output‖ ^ 2 ≤
        (1 + κ) * bandSpread solution t N k output) :
    CoherenceDefectAt solution t κ k := by
  refine coherenceDefectAt_of_cubes solution t hsum hκ k fun output N ↦ ?_
  have key := (norm_sum_sq_le_iff_barycenter (frequencyCube N) (frequencyCube_nonempty N)
    (fun p ↦ feedTerm solution t k p output) κ).mpr ?_
  · exact key
  · rw [card_frequencyCube N]
    push_cast
    exact h output N

/-! ## The closure statement -/

/-- **Barycentric tail control.**  Along a terminal tail every nonzero receiver's feed comb has,
on every cube, barycentric mass at most the `(1 + κ)/(n (n − 1 − κ))` fraction of its spread. -/
def BarycentricTailControl : Prop :=
  ∀ {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField},
    0 < nu →
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) →
      ∃ (s κ : ℝ), 0 < s ∧ s < T ∧ 0 ≤ κ ∧
        (∀ σ (hσ : σ ∈ Ioo 0 T), s ≤ σ →
          Summable (eleventhMoment (velocity := velocity) σ) ∧
            ∀ k : SpatialFrequency, k ≠ 0 → ∀ (output : Fin 3) (N : ℕ),
              ((2 * N + 1) ^ 3 : ℝ) * (((2 * N + 1) ^ 3 : ℝ) - 1 - κ) *
                  ‖bandBarycenter solution ⟨σ, hσ⟩ N k output‖ ^ 2 ≤
                (1 + κ) * bandSpread solution ⟨σ, hσ⟩ N k output) ∧
        (∀ τ ∈ Ioo s T, ∃ B : ℝ, ∀ σ ∈ Icc s τ, moment (velocity := velocity) 11 σ ≤ B)

theorem coherenceDefectTail_of_barycentric (h : BarycentricTailControl) :
    CoherenceDefectTailControl := by
  intro T nu initial velocity pressure hnu solution
  obtain ⟨s, κ, hs0, hsT, hκ, htail, hcompact⟩ := h hnu solution
  refine ⟨s, κ, hs0, hsT, hκ, fun σ hσ hsσ ↦ ⟨(htail σ hσ hsσ).1, fun k hk ↦ ?_⟩, hcompact⟩
  exact coherenceDefectAt_of_barycenter solution ⟨σ, hσ⟩ (htail σ hσ hsσ).1 hκ k
    ((htail σ hσ hsσ).2 k hk)

/-- **Barycentric tail control returns Statement B.** -/
theorem statementB_of_barycentric (h : BarycentricTailControl) : StatementB :=
  statementB_of_coherenceDefectTail (coherenceDefectTail_of_barycentric h)

theorem officialProblem_of_barycentric (h : BarycentricTailControl) :
    TheOfficialNavierStokesProblem :=
  officialProblem_of_coherenceDefectTail (coherenceDefectTail_of_barycentric h)

section Audit

#print axioms norm_sum_sq_le_iff_barycenter
#print axioms coherenceDefectAt_of_barycenter
#print axioms statementB_of_barycentric

end Audit

end Soma.Holonics.Millennium.NavierStokesCombBarycenterDefect
