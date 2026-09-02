import ElementaryHolonics.Millennium.NavierStokesFrontierVanishing
import ElementaryHolonics.Millennium.NavierStokesHalfRadiusReach

/-!
# Moment-ladder tail relevance: the frontier defect pays a power of the radius

Outside the cube of radius `M` every frequency has sup-norm at least `M + 1`, so the exterior
`ℓ¹` velocity mass is at most the `ℓ¹` moment of order `s` divided by `(M + 1)^s`, and the
Jacobian tail mass beyond the cube of radius `N` is at most `2π` times the moment of order
`s + 1` divided by `(N + 1)^s`.  The frontier defect of the band budget therefore decays like
`(N + 1)^{-s} (2N + 1)^{-s}` times a product expansion of moments.
-/

noncomputable section

namespace Soma.Holonics.Millennium.NavierStokesMomentTailRelevance

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
open Soma.Holonics.Millennium.NavierStokesHalfRadiusReach
open Soma.Holonics.Millennium.NavierStokesFrontierVanishing

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
  (t : Ioo 0 T)

/-- The `ℓ¹` velocity moment of order `s`. -/
def l1Moment (s : ℕ) : ℝ :=
  ∑' k, ((frequencySup k : ℕ) : ℝ) ^ s * complexVectorL1 (openPeriodicVelocityFourierMode solution t k)

theorem l1MomentTerm_nonneg (s : ℕ) (k : SpatialFrequency) :
    0 ≤ ((frequencySup k : ℕ) : ℝ) ^ s * complexVectorL1 (openPeriodicVelocityFourierMode solution t k) :=
  mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (NavierStokesFrontierVanishing.complexVectorL1_nonneg _)

theorem l1Moment_nonneg (s : ℕ) : 0 ≤ l1Moment solution t s :=
  tsum_nonneg fun k => l1MomentTerm_nonneg solution t s k

theorem l1Moment_zero :
    l1Moment solution t 0 = ∑' k, complexVectorL1 (openPeriodicVelocityFourierMode solution t k) := by
  simp [l1Moment]

theorem succ_le_frequencySup_of_not_mem {M : ℕ} {k : SpatialFrequency} (hk : k ∉ frequencyCube M) :
    M + 1 ≤ frequencySup k := by
  rw [mem_frequencyCube_iff_frequencySup_le] at hk
  omega

theorem cast_succ_le_frequencySup_of_not_mem {M : ℕ} {k : SpatialFrequency}
    (hk : k ∉ frequencyCube M) : ((M : ℝ) + 1) ≤ ((frequencySup k : ℕ) : ℝ) := by
  have := succ_le_frequencySup_of_not_mem hk
  exact_mod_cast this

/-- **The exterior mass pays `(M + 1)^s` against the moment of order `s`.** -/
theorem pow_mul_exteriorMass_le (s M : ℕ)
    (hs : Summable fun k => ((frequencySup k : ℕ) : ℝ) ^ s *
      complexVectorL1 (openPeriodicVelocityFourierMode solution t k)) :
    ((M : ℝ) + 1) ^ s * exteriorMass solution t M ≤ l1Moment solution t s := by
  unfold exteriorMass l1Moment
  rw [← tsum_mul_left]
  calc ∑' k : ↑((↑(frequencyCube M) : Set SpatialFrequency)ᶜ),
        ((M : ℝ) + 1) ^ s * complexVectorL1 (openPeriodicVelocityFourierMode solution t k)
      ≤ ∑' k : ↑((↑(frequencyCube M) : Set SpatialFrequency)ᶜ),
        ((frequencySup k : ℕ) : ℝ) ^ s *
          complexVectorL1 (openPeriodicVelocityFourierMode solution t k) := by
        refine Summable.tsum_le_tsum (fun k => ?_) ?_ (hs.subtype _)
        · apply mul_le_mul_of_nonneg_right _ (NavierStokesFrontierVanishing.complexVectorL1_nonneg _)
          exact pow_le_pow_left₀ (by positivity) (cast_succ_le_frequencySup_of_not_mem k.2) s
        · exact ((summable_complexVectorL1_velocityMode solution t).mul_left _).subtype _
    _ ≤ ∑' k, ((frequencySup k : ℕ) : ℝ) ^ s *
          complexVectorL1 (openPeriodicVelocityFourierMode solution t k) :=
        Summable.tsum_subtype_le _ _ (fun k => l1MomentTerm_nonneg solution t s k) hs

theorem norm_component_le_complexVectorL1 (v : ComplexVector) (c : Fin 3) :
    ‖v c‖ ≤ complexVectorL1 v := by
  rw [complexVectorL1_eq_sum]
  exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ c)

theorem abs_coordinate_le_frequencySup (k : SpatialFrequency) (d : Fin 3) :
    |((k d : ℤ) : ℝ)| ≤ ((frequencySup k : ℕ) : ℝ) := by
  have h1 : |((k d : ℤ) : ℝ)| = (((k d).natAbs : ℕ) : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have h2 : (k d).natAbs ≤ frequencySup k :=
    Finset.le_sup (f := fun c => (k c).natAbs) (Finset.mem_univ d)
  rw [h1]
  exact_mod_cast h2

/-- **The Jacobian mode is bounded by `2π` times the sup-norm times the `ℓ¹` mass.** -/
theorem norm_jacobianMode_le_sup (k : SpatialFrequency) (c d : Fin 3) :
    ‖openPeriodicJacobianFourierMode solution t k c d‖ ≤
      2 * Real.pi * ((frequencySup k : ℕ) : ℝ) *
        complexVectorL1 (openPeriodicVelocityFourierMode solution t k) := by
  rw [openPeriodicJacobianFourierMode_eq_fourierJacobianMode]
  unfold fourierJacobianMode
  have hnorm : ‖(2 * (Real.pi : ℂ) * Complex.I * ((k d : ℤ) : ℂ))‖ =
      2 * Real.pi * |((k d : ℤ) : ℝ)| := by
    simp [Complex.norm_I, Complex.norm_real, Complex.norm_intCast,
      abs_of_pos Real.pi_pos]
  rw [norm_mul, hnorm]
  have hk := abs_coordinate_le_frequencySup k d
  have hv := norm_component_le_complexVectorL1 (openPeriodicVelocityFourierMode solution t k) c
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  calc 2 * Real.pi * |((k d : ℤ) : ℝ)| * ‖openPeriodicVelocityFourierMode solution t k c‖
      ≤ 2 * Real.pi * ((frequencySup k : ℕ) : ℝ) *
          complexVectorL1 (openPeriodicVelocityFourierMode solution t k) := by
        apply mul_le_mul _ hv (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_left hk hpi

/-- **The Jacobian tail mass pays `(N + 1)^s` against `2π` times the moment of order `s + 1`.** -/
theorem pow_mul_jacobianTailMass_le (s N : ℕ)
    (hs1 : Summable fun k => ((frequencySup k : ℕ) : ℝ) ^ (s + 1) *
      complexVectorL1 (openPeriodicVelocityFourierMode solution t k)) :
    ((N : ℝ) + 1) ^ s * openPeriodicJacobianCoefficientTailMass solution t (frequencyCube N) ≤
      2 * Real.pi * l1Moment solution t (s + 1) := by
  have hpos : (0 : ℝ) < ((N : ℝ) + 1) ^ s := by positivity
  rw [mul_comm, ← le_div_iff₀ hpos]
  have hnn : 0 ≤ 2 * Real.pi * l1Moment solution t (s + 1) / ((N : ℝ) + 1) ^ s :=
    div_nonneg (mul_nonneg (by positivity) (l1Moment_nonneg solution t _)) hpos.le
  unfold openPeriodicJacobianCoefficientTailMass
  rw [pi_norm_le_iff_of_nonneg hnn]
  intro c
  rw [pi_norm_le_iff_of_nonneg hnn]
  intro d
  rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg fun _ => norm_nonneg _), le_div_iff₀ hpos]
  calc (∑' f : {f : SpatialFrequency // f ∉ frequencyCube N},
          ‖openPeriodicJacobianFourierMode solution t f.1 c d‖) * ((N : ℝ) + 1) ^ s
      = ∑' f : {f : SpatialFrequency // f ∉ frequencyCube N},
          ‖openPeriodicJacobianFourierMode solution t f.1 c d‖ * ((N : ℝ) + 1) ^ s :=
        tsum_mul_right.symm
    _ ≤ ∑' f : {f : SpatialFrequency // f ∉ frequencyCube N},
          2 * Real.pi * (((frequencySup f.1 : ℕ) : ℝ) ^ (s + 1) *
            complexVectorL1 (openPeriodicVelocityFourierMode solution t f.1)) := by
        refine Summable.tsum_le_tsum (fun f => ?_) ?_ ?_
        · have hJ := norm_jacobianMode_le_sup solution t f.1 c d
          have hpow : ((N : ℝ) + 1) ^ s ≤ ((frequencySup f.1 : ℕ) : ℝ) ^ s :=
            pow_le_pow_left₀ (by positivity) (cast_succ_le_frequencySup_of_not_mem f.2) s
          calc ‖openPeriodicJacobianFourierMode solution t f.1 c d‖ * ((N : ℝ) + 1) ^ s
              ≤ (2 * Real.pi * ((frequencySup f.1 : ℕ) : ℝ) *
                  complexVectorL1 (openPeriodicVelocityFourierMode solution t f.1)) *
                  ((frequencySup f.1 : ℕ) : ℝ) ^ s :=
                mul_le_mul hJ hpow (by positivity)
                  (mul_nonneg (by positivity)
                    (NavierStokesFrontierVanishing.complexVectorL1_nonneg _))
            _ = 2 * Real.pi * (((frequencySup f.1 : ℕ) : ℝ) ^ (s + 1) *
                  complexVectorL1 (openPeriodicVelocityFourierMode solution t f.1)) := by
                ring
        · exact ((summable_norm_openPeriodicJacobianFourierMode_entry solution t c d).subtype
            _).mul_right _
        · exact (hs1.mul_left _).subtype _
    _ = 2 * Real.pi * ∑' f : {f : SpatialFrequency // f ∉ frequencyCube N},
          ((frequencySup f.1 : ℕ) : ℝ) ^ (s + 1) *
            complexVectorL1 (openPeriodicVelocityFourierMode solution t f.1) := tsum_mul_left
    _ ≤ 2 * Real.pi * l1Moment solution t (s + 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Summable.tsum_subtype_le _ _ (fun k => l1MomentTerm_nonneg solution t (s + 1) k) hs1

/-- **The frontier product pays `(N + 1)^s`.** -/
theorem pow_mul_frontierBound_le (s N : ℕ)
    (hs : Summable fun k => ((frequencySup k : ℕ) : ℝ) ^ s *
      complexVectorL1 (openPeriodicVelocityFourierMode solution t k))
    (hs1 : Summable fun k => ((frequencySup k : ℕ) : ℝ) ^ (s + 1) *
      complexVectorL1 (openPeriodicVelocityFourierMode solution t k)) :
    ((N : ℝ) + 1) ^ s * frontierBound solution t N ≤
      2 * Real.pi * l1Moment solution t 0 * l1Moment solution t (s + 1) +
        l1Moment solution t s * openPeriodicJacobianCoefficientTailMass solution t ∅ := by
  have hext := pow_mul_exteriorMass_le solution t s N hs
  unfold exteriorMass at hext
  have hband : (∑ p ∈ frequencyCube N, complexVectorL1 (openPeriodicVelocityFourierMode solution t p))
      ≤ l1Moment solution t 0 := by
    rw [l1Moment_zero]
    exact (summable_complexVectorL1_velocityMode solution t).sum_le_tsum _
      (fun _ _ => NavierStokesFrontierVanishing.complexVectorL1_nonneg _)
  unfold frontierBound
  rw [mul_add]
  apply add_le_add
  · calc ((N : ℝ) + 1) ^ s *
          ((∑ p ∈ frequencyCube N, complexVectorL1 (openPeriodicVelocityFourierMode solution t p)) *
            openPeriodicJacobianCoefficientTailMass solution t (frequencyCube N))
        = (∑ p ∈ frequencyCube N, complexVectorL1 (openPeriodicVelocityFourierMode solution t p)) *
            (((N : ℝ) + 1) ^ s *
              openPeriodicJacobianCoefficientTailMass solution t (frequencyCube N)) := by ring
      _ ≤ l1Moment solution t 0 * (2 * Real.pi * l1Moment solution t (s + 1)) :=
          mul_le_mul hband (pow_mul_jacobianTailMass_le solution t s N hs1)
            (mul_nonneg (by positivity) (jacobianTailMass_nonneg solution t _))
            (l1Moment_nonneg solution t 0)
      _ = 2 * Real.pi * l1Moment solution t 0 * l1Moment solution t (s + 1) := by ring
  · calc ((N : ℝ) + 1) ^ s *
          ((∑' p : ↑((↑(frequencyCube N) : Set SpatialFrequency)ᶜ),
              complexVectorL1 (openPeriodicVelocityFourierMode solution t p)) *
            openPeriodicJacobianCoefficientTailMass solution t ∅)
        = (((N : ℝ) + 1) ^ s *
            ∑' p : ↑((↑(frequencyCube N) : Set SpatialFrequency)ᶜ),
              complexVectorL1 (openPeriodicVelocityFourierMode solution t p)) *
            openPeriodicJacobianCoefficientTailMass solution t ∅ := by ring
      _ ≤ l1Moment solution t s * openPeriodicJacobianCoefficientTailMass solution t ∅ :=
          mul_le_mul_of_nonneg_right hext (jacobianTailMass_nonneg solution t _)

/-- The moment constant of the frontier defect. -/
def momentConstant (s : ℕ) : ℝ :=
  (2 * Real.pi * l1Moment solution t 0 * l1Moment solution t (s + 1) +
      l1Moment solution t s * openPeriodicJacobianCoefficientTailMass solution t ∅) *
    l1Moment solution t s

theorem momentConstant_nonneg (s : ℕ) : 0 ≤ momentConstant solution t s := by
  unfold momentConstant
  have := l1Moment_nonneg solution t 0
  have := l1Moment_nonneg solution t s
  have := l1Moment_nonneg solution t (s + 1)
  have := jacobianTailMass_nonneg solution t (∅ : Finset SpatialFrequency)
  positivity

/-- **The frontier defect pays `(N + 1)^s (2N + 1)^s` against the moment constant.** -/
theorem pow_mul_frontierDefect_le (s N : ℕ)
    (hs : Summable fun k => ((frequencySup k : ℕ) : ℝ) ^ s *
      complexVectorL1 (openPeriodicVelocityFourierMode solution t k))
    (hs1 : Summable fun k => ((frequencySup k : ℕ) : ℝ) ^ (s + 1) *
      complexVectorL1 (openPeriodicVelocityFourierMode solution t k)) :
    ((N : ℝ) + 1) ^ s * (((2 * N : ℕ) : ℝ) + 1) ^ s *
        (frontierBound solution t N * exteriorMass solution t (2 * N)) ≤
      momentConstant solution t s := by
  have h1 := pow_mul_frontierBound_le solution t s N hs hs1
  have h2 := pow_mul_exteriorMass_le solution t s (2 * N) hs
  have hb : 0 ≤ ((N : ℝ) + 1) ^ s * frontierBound solution t N := by
    have := (tendsto_frontierBound solution t)
    exact mul_nonneg (by positivity)
      (add_nonneg (mul_nonneg (Finset.sum_nonneg fun _ _ => NavierStokesFrontierVanishing.complexVectorL1_nonneg _)
        (jacobianTailMass_nonneg solution t _))
        (mul_nonneg (tsum_nonneg fun _ => NavierStokesFrontierVanishing.complexVectorL1_nonneg _)
          (jacobianTailMass_nonneg solution t _)))
  have hc : 0 ≤ 2 * Real.pi * l1Moment solution t 0 * l1Moment solution t (s + 1) +
      l1Moment solution t s * openPeriodicJacobianCoefficientTailMass solution t ∅ := by
    have := l1Moment_nonneg solution t 0
    have := l1Moment_nonneg solution t s
    have := l1Moment_nonneg solution t (s + 1)
    have := jacobianTailMass_nonneg solution t (∅ : Finset SpatialFrequency)
    positivity
  calc ((N : ℝ) + 1) ^ s * (((2 * N : ℕ) : ℝ) + 1) ^ s *
        (frontierBound solution t N * exteriorMass solution t (2 * N))
      = (((N : ℝ) + 1) ^ s * frontierBound solution t N) *
          ((((2 * N : ℕ) : ℝ) + 1) ^ s * exteriorMass solution t (2 * N)) := by ring
    _ ≤ (2 * Real.pi * l1Moment solution t 0 * l1Moment solution t (s + 1) +
          l1Moment solution t s * openPeriodicJacobianCoefficientTailMass solution t ∅) *
          l1Moment solution t s :=
        mul_le_mul h1 h2 (mul_nonneg (by positivity) (tsum_nonneg fun _ => NavierStokesFrontierVanishing.complexVectorL1_nonneg _)) hc

/-- **Moment-ladder tail relevance.** The band budget defect at radius `N` pays
`(N + 1)^s (2N + 1)^s` against twice the moment constant. -/
theorem pow_mul_abs_bandBudget_le (s N : ℕ)
    (hs : Summable fun k => ((frequencySup k : ℕ) : ℝ) ^ s *
      complexVectorL1 (openPeriodicVelocityFourierMode solution t k))
    (hs1 : Summable fun k => ((frequencySup k : ℕ) : ℝ) ^ (s + 1) *
      complexVectorL1 (openPeriodicVelocityFourierMode solution t k)) :
    ((N : ℝ) + 1) ^ s * (((2 * N : ℕ) : ℝ) + 1) ^ s *
        |deriv (NavierStokesBandEnergyBudget.bandMass (velocity := velocity)
            (frequencyCube (2 * N))) t.1 +
          2 * nu * NavierStokesBandEnergyBudget.bandDissipation (velocity := velocity)
            (frequencyCube (2 * N)) t.1| ≤
      2 * momentConstant solution t s := by
  have h := abs_deriv_bandMass_add_dissipation_le solution t N
  have h2 := pow_mul_frontierDefect_le solution t s N hs hs1
  calc ((N : ℝ) + 1) ^ s * (((2 * N : ℕ) : ℝ) + 1) ^ s *
        |deriv (NavierStokesBandEnergyBudget.bandMass (velocity := velocity)
            (frequencyCube (2 * N))) t.1 +
          2 * nu * NavierStokesBandEnergyBudget.bandDissipation (velocity := velocity)
            (frequencyCube (2 * N)) t.1|
      ≤ ((N : ℝ) + 1) ^ s * (((2 * N : ℕ) : ℝ) + 1) ^ s *
          (2 * (frontierBound solution t N * exteriorMass solution t (2 * N))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 * (((N : ℝ) + 1) ^ s * (((2 * N : ℕ) : ℝ) + 1) ^ s *
          (frontierBound solution t N * exteriorMass solution t (2 * N))) := by ring
    _ ≤ 2 * momentConstant solution t s := by linarith

end Soma.Holonics.Millennium.NavierStokesMomentTailRelevance
