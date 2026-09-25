import HolonicsResearch.Fluid.NavierStokesFourierKirchhoff

/-!
# The band energy budget

Each velocity mode's mass obeys the exact identity

```text
d/dt ‖û_k‖² = −2 ν λ_k ‖û_k‖² − 2 · transfer k,
```

the pressure gradient doing no modal work because the mode is divergence-free.  Summed over a
finite band `F` and joined with the Fourier Kirchhoff law,

```text
d/dt E_F = −2 ν D_F + 2 Σ'_{k ∉ F} transfer k :
```

the band dissipates, and what it exchanges with its complement is exactly the transfer current
into the complement.  No inequality is used; every step is an identity.
-/

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped Finset ComplexConjugate ContDiff

namespace Holonics.Fluid.NavierStokesBandEnergyBudget

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

theorem re_mul_conj_comm (z w : ℂ) : (z * conj w).re = (conj z * w).re := by
  rw [← Complex.conj_re (z * conj w), map_mul, Complex.conj_conj]

/-- The pressure-gradient pairing vanishes on a divergence-free mode. -/
theorem re_sum_gradient_pairing (k : SpatialFrequency) (P : ℂ) (v : ComplexVector)
    (hv : complexDot (complexFrequencyVector k) v = 0) :
    ∑ c : Fin 3, ((2 * (Real.pi : ℂ) * Complex.I * (k c : ℂ)) * P * conj (v c)).re = 0 := by
  rw [← Complex.re_sum]
  have : ∑ c : Fin 3, (2 * (Real.pi : ℂ) * Complex.I * (k c : ℂ)) * P * conj (v c) =
      (2 * (Real.pi : ℂ) * Complex.I * P) * conj (complexDot (complexFrequencyVector k) v) := by
    unfold complexDot dotProduct complexFrequencyVector
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [map_mul, map_intCast]
    ring
  rw [this, hv, map_zero, mul_zero, Complex.zero_re]

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)

/-- The velocity mass of a mode as a real-time curve. -/
def modeMass (k : SpatialFrequency) (τ : ℝ) : ℝ :=
  ∑ c : Fin 3, ‖velocityMode velocity k τ c‖ ^ 2

theorem modeMass_eq_velPop (t : Ioo 0 T) (k : SpatialFrequency) :
    modeMass (velocity := velocity) k t.1 = velPop solution t k := by
  unfold modeMass velPop
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [show velocityMode velocity k t.1 c = velocityModeComponent velocity k c t.1 from rfl,
    velocityModeComponent_eq_openPeriodicVelocityFourierMode solution t k c]

/-- **The pressure gradient does no modal work.** -/
theorem sum_inner_pressureGradientMode_eq_zero (t : Ioo 0 T) (k : SpatialFrequency) :
    ∑ c : Fin 3, inner ℝ (openPeriodicVelocityFourierMode solution t k c)
      (openPressureGradientMode solution t k c) = 0 := by
  have hg : openPressureGradientMode solution t k = fun c ↦
      (2 * (Real.pi : ℂ) * Complex.I * (k c : ℂ)) *
        scalarFourierMode (fun x ↦ pressure x t.1)
          (openPeriodicSolutionOn_pressureSlice_contDiff solution t.2).continuous
          (solution.pressurePeriodic t.1 ⟨t.2.1.le, t.2.2⟩) k := by
    unfold openPressureGradientMode
    exact vectorSpatialFourierCoeff_gradient_eq_frequency (fun x ↦ pressure x t.1)
      (openPeriodicSolutionOn_pressureSlice_contDiff solution t.2)
      (solution.pressurePeriodic t.1 ⟨t.2.1.le, t.2.2⟩) k
  have hdiv := openPeriodicVelocityFourierMode_divergenceFree solution t k
  simp only [Complex.inner, hg]
  exact re_sum_gradient_pairing k _ _ hdiv

/-- **The modal mass identity.** -/
theorem hasDerivAt_modeMass (t : Ioo 0 T) (k : SpatialFrequency) :
    HasDerivAt (modeMass (velocity := velocity) k)
      (-2 * nu * torusStokesEigenvalue k * modeMass (velocity := velocity) k t.1 -
        2 * transfer solution t k) t.1 := by
  have hmode := openPeriodicSolutionOn_hasDerivAt_velocityMode_unforced solution t.2 k
  set M := unforcedMomentumMode nu velocity pressure k t.1 with hM
  set v := velocityMode velocity k t.1 with hv
  set adv := openActualAdvectionMode solution t k with hadv
  set g := openPressureGradientMode solution t k with hg
  have hcomp : ∀ c : Fin 3, HasDerivAt (fun τ ↦ velocityMode velocity k τ c) (M c) t.1 :=
    fun c ↦ (hasDerivAt_pi.mp hmode) c
  have hterm : ∀ c : Fin 3, HasDerivAt
      (fun τ ↦ inner ℝ (velocityMode velocity k τ c) (velocityMode velocity k τ c))
      (2 * inner ℝ (v c) (M c)) t.1 := by
    intro c
    have h := (hcomp c).inner (𝕜 := ℝ) (hcomp c)
    refine h.congr_deriv ?_
    rw [real_inner_comm (M c)]
    ring
  have hfun : modeMass (velocity := velocity) k = fun τ ↦
      ∑ c : Fin 3, inner ℝ (velocityMode velocity k τ c) (velocityMode velocity k τ c) := by
    funext τ
    unfold modeMass
    exact Finset.sum_congr rfl fun c _ ↦ (real_inner_self_eq_norm_sq _).symm
  have hsum : HasDerivAt (modeMass (velocity := velocity) k)
      (∑ c : Fin 3, 2 * inner ℝ (v c) (M c)) t.1 := by
    rw [hfun]
    exact HasDerivAt.sum (u := Finset.univ) fun c _ ↦ hterm c
  refine hsum.congr_deriv ?_
  -- the momentum mode
  have hMeq : M = ((-(nu * torusStokesEigenvalue k) : ℝ) • v - adv) - g := by
    have h1 : pressureFreeMomentumMode solution t k = M + g := rfl
    have h2 := pressureFreeMomentumMode_eq_viscous_sub_advection solution t k
    rw [openPeriodicSolutionOn_velocityLaplacianMode_eq_stokes,
      openAdvectionMode_eq_openActualAdvectionMode, h1] at h2
    have h3 : (nu : ℂ) • (-(torusStokesEigenvalue k : ℂ) • velocityMode velocity k t.1) =
        ((-(nu * torusStokesEigenvalue k) : ℝ) • v) := by
      rw [hv, smul_smul]
      funext c
      simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul]
      push_cast
      ring
    rw [h3] at h2
    rw [hadv, hg]
    calc M = (M + openPressureGradientMode solution t k) - openPressureGradientMode solution t k := by
          abel
      _ = _ := by rw [← h2]
  have hM' : ∀ c : Fin 3, inner ℝ (v c) (M c) =
      -(nu * torusStokesEigenvalue k) * inner ℝ (v c) (v c) - inner ℝ (v c) (adv c) -
        inner ℝ (v c) (g c) := by
    intro c
    rw [hMeq]
    simp only [Pi.sub_apply, Pi.smul_apply]
    rw [inner_sub_right, inner_sub_right, real_inner_smul_right]
  have hE : ∑ c : Fin 3, inner ℝ (v c) (v c) = modeMass (velocity := velocity) k t.1 := by
    unfold modeMass
    exact Finset.sum_congr rfl fun c _ ↦ real_inner_self_eq_norm_sq _
  have hvû : ∀ c, v c = openPeriodicVelocityFourierMode solution t k c := fun c ↦ by
    rw [hv]
    exact velocityModeComponent_eq_openPeriodicVelocityFourierMode solution t k c
  have hP : ∑ c : Fin 3, inner ℝ (v c) (g c) = 0 := by
    simp only [hvû, hg]
    exact sum_inner_pressureGradientMode_eq_zero solution t k
  have hT : ∑ c : Fin 3, inner ℝ (v c) (adv c) = transfer solution t k := by
    unfold transfer
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [hvû, hadv, Complex.inner, re_mul_conj_comm]
  calc ∑ c : Fin 3, 2 * inner ℝ (v c) (M c)
      = 2 * ∑ c : Fin 3, (-(nu * torusStokesEigenvalue k) * inner ℝ (v c) (v c) -
          inner ℝ (v c) (adv c) - inner ℝ (v c) (g c)) := by
        rw [← Finset.mul_sum]
        exact congrArg _ (Finset.sum_congr rfl fun c _ ↦ hM' c)
    _ = 2 * (-(nu * torusStokesEigenvalue k) * ∑ c : Fin 3, inner ℝ (v c) (v c) -
          ∑ c : Fin 3, inner ℝ (v c) (adv c) - ∑ c : Fin 3, inner ℝ (v c) (g c)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
    _ = _ := by rw [hE, hT, hP]; ring

/-! ## The band -/

/-- The mass of a finite band. -/
def bandMass (F : Finset SpatialFrequency) (τ : ℝ) : ℝ :=
  ∑ k ∈ F, modeMass (velocity := velocity) k τ

/-- The Stokes dissipation of a finite band. -/
def bandDissipation (F : Finset SpatialFrequency) (τ : ℝ) : ℝ :=
  ∑ k ∈ F, torusStokesEigenvalue k * modeMass (velocity := velocity) k τ

theorem hasDerivAt_bandMass (t : Ioo 0 T) (F : Finset SpatialFrequency) :
    HasDerivAt (bandMass (velocity := velocity) F)
      (-2 * nu * bandDissipation (velocity := velocity) F t.1 -
        2 * ∑ k ∈ F, transfer solution t k) t.1 := by
  have hfun : bandMass (velocity := velocity) F =
      ∑ k ∈ F, fun τ ↦ modeMass (velocity := velocity) k τ := by
    funext τ
    simp [bandMass, Finset.sum_apply]
  rw [hfun]
  refine (HasDerivAt.sum (u := F) fun k _ ↦ hasDerivAt_modeMass solution t k).congr_deriv ?_
  unfold bandDissipation
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- **The band energy budget with the Kirchhoff law.** -/
theorem hasDerivAt_bandMass_kirchhoff (t : Ioo 0 T) (F : Finset SpatialFrequency) :
    HasDerivAt (bandMass (velocity := velocity) F)
      (-2 * nu * bandDissipation (velocity := velocity) F t.1 +
        2 * ∑' k : ↑((↑F : Set SpatialFrequency)ᶜ), transfer solution t k) t.1 := by
  have h := hasDerivAt_bandMass solution t F
  rw [tsum_compl_transfer_eq_neg]
  convert h using 1
  ring

section Audit

#print axioms sum_inner_pressureGradientMode_eq_zero
#print axioms hasDerivAt_modeMass
#print axioms hasDerivAt_bandMass_kirchhoff

end Audit

end Holonics.Fluid.NavierStokesBandEnergyBudget
