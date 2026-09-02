import ElementaryHolonics.Millennium.NavierStokesShellStepCost

/-!
# The modal Riccati inequality: a tail mode's energy is driven only by the tail

Sol's exact per-mode vorticity equation in diagonal Stokes form
(`openPeriodicSolutionOn_hasDerivAt_vorticityMode_stokes`) is

```text
d/dt ω̂_k = −ν λ_k ω̂_k + N_k,      λ_k = (2π)² |k|²,
```

with `N_k` the curl of the advection coefficient.  This owner differentiates the modal energy
`E_k = Σ_c |ω̂_{k,c}|²` and bounds its derivative at every interior time, for every receiver
outside the cube of radius `2N`:

```text
E_k' ≤ −2 ν λ_k E_k + 2 · ℓ¹(ω̂_k) · 3² √λ_k · B_N,      ℓ¹(ω̂_k)² ≤ 3 E_k,
```

where `B_N = (2N+1)³ · 3√(2E(0)) · tailJ(N) + velocityTail(N) · totalJ` is the shell-step cost
of the preceding owner.  Dissipation acts on `E_k` at the Stokes eigenvalue; the drive is
proportional to the tail masses beyond radius `N` and to the amplitude of the mode itself.  A
tail mode is self-limiting relative to the tail: its amplitude cannot exceed the drive divided by
`ν √λ_k` for long.

Nothing here sums over the tail.  The differential inequality is modal; the summed inequality is
the next owner.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Finset

namespace Soma.Holonics.Millennium.NavierStokesModalRiccati

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
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesH2VorticityShellDissipationBridge
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesShellStepCost

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)

/-- The vorticity mode curve of Sol's per-mode equation. -/
def vorticityModeCurve (k : SpatialFrequency) (τ : ℝ) : ComplexVector :=
  frequencyCurlMultiplier k (velocityMode velocity k τ)

/-- The modal energy `Σ_c |ω̂_{k,c}|²`, written through the real inner product of `ℂ`. -/
def modalEnergy (k : SpatialFrequency) (τ : ℝ) : ℝ :=
  ∑ component : Fin 3,
    inner ℝ (vorticityModeCurve (velocity := velocity) k τ component)
      (vorticityModeCurve (velocity := velocity) k τ component)

theorem modalEnergy_eq_sum_norm_sq (k : SpatialFrequency) (τ : ℝ) :
    modalEnergy (velocity := velocity) k τ =
      ∑ component : Fin 3, ‖vorticityModeCurve (velocity := velocity) k τ component‖ ^ 2 := by
  unfold modalEnergy
  simp [real_inner_self_eq_norm_sq]

theorem modalEnergy_nonneg (k : SpatialFrequency) (τ : ℝ) :
    0 ≤ modalEnergy (velocity := velocity) k τ := by
  rw [modalEnergy_eq_sum_norm_sq]
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- The `ℓ¹` amplitude is paid by the modal energy with the coordinate comparison `3`. -/
theorem complexVectorL1_sq_le_three_mul_modalEnergy (k : SpatialFrequency) (τ : ℝ) :
    complexVectorL1 (vorticityModeCurve (velocity := velocity) k τ) ^ 2 ≤
      3 * modalEnergy (velocity := velocity) k τ := by
  rw [modalEnergy_eq_sum_norm_sq, Fin.sum_univ_three]
  unfold complexVectorL1
  nlinarith [sq_nonneg (‖vorticityModeCurve (velocity := velocity) k τ 0‖ -
      ‖vorticityModeCurve (velocity := velocity) k τ 1‖),
    sq_nonneg (‖vorticityModeCurve (velocity := velocity) k τ 1‖ -
      ‖vorticityModeCurve (velocity := velocity) k τ 2‖),
    sq_nonneg (‖vorticityModeCurve (velocity := velocity) k τ 0‖ -
      ‖vorticityModeCurve (velocity := velocity) k τ 2‖)]

/-! ## The curl of the advection coefficient is paid by the shell-step cost -/

/-- The shell-step cost of one output component. -/
def feedBound (t : Ioo 0 T) (radius : ℕ) : ℝ :=
  (2 * radius + 1) ^ 3 * (3 * Real.sqrt (2 * periodicKineticEnergy velocity 0)) *
      openPeriodicJacobianCoefficientTailMass solution t (frequencyCube radius) +
    velocityTailMass solution t radius * openPeriodicJacobianCoefficientTailMass solution t ∅

theorem complexVectorL1_frequencyCurlMultiplier_le (k : SpatialFrequency) (v : ComplexVector) :
    complexVectorL1 (frequencyCurlMultiplier k v) ≤
      3 * Real.sqrt (torusStokesEigenvalue k) * complexVectorL1 v := by
  have hsq := complexVectorL1_frequencyCurlMultiplier_sq_le k v
  have hlam : 0 ≤ torusStokesEigenvalue k := by
    unfold torusStokesEigenvalue frequencySquared
    positivity
  have hsum : ∑ component : Fin 3, ‖v component‖ ^ 2 ≤ complexVectorL1 v ^ 2 := by
    rw [Fin.sum_univ_three]
    unfold complexVectorL1
    nlinarith [norm_nonneg (v 0), norm_nonneg (v 1), norm_nonneg (v 2)]
  have hrhs : 0 ≤ 3 * Real.sqrt (torusStokesEigenvalue k) * complexVectorL1 v :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (complexVectorL1_nonneg v)
  have hsq' : complexVectorL1 (frequencyCurlMultiplier k v) ^ 2 ≤
      (3 * Real.sqrt (torusStokesEigenvalue k) * complexVectorL1 v) ^ 2 := by
    calc complexVectorL1 (frequencyCurlMultiplier k v) ^ 2
        ≤ 9 * torusStokesEigenvalue k * (∑ component : Fin 3, ‖v component‖ ^ 2) := hsq
      _ ≤ 9 * torusStokesEigenvalue k * complexVectorL1 v ^ 2 :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (3 * Real.sqrt (torusStokesEigenvalue k) * complexVectorL1 v) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hlam]; ring
  exact (pow_le_pow_iff_left₀ (complexVectorL1_nonneg _) hrhs two_ne_zero).mp hsq'

/-- **The nonlinear source of a tail mode is paid by the shell-step cost.** -/
theorem complexVectorL1_vorticityNonlinearMode_le (hnu : 0 ≤ nu) (t : Ioo 0 T)
    {radius : ℕ} {k : SpatialFrequency} (hk : k ∉ frequencyCube (2 * radius)) :
    complexVectorL1 (vorticityNonlinearMode solution t k) ≤
      3 ^ 2 * Real.sqrt (torusStokesEigenvalue k) * feedBound solution t radius := by
  unfold vorticityNonlinearMode
  have hneg : complexVectorL1 (-frequencyCurlMultiplier k (openAdvectionMode solution t k)) =
      complexVectorL1 (frequencyCurlMultiplier k (openAdvectionMode solution t k)) := by
    simp [complexVectorL1]
  rw [hneg]
  refine (complexVectorL1_frequencyCurlMultiplier_le k _).trans ?_
  have hadv : complexVectorL1 (openAdvectionMode solution t k) ≤ 3 * feedBound solution t radius := by
    rw [openAdvectionMode_eq_openActualAdvectionMode]
    unfold complexVectorL1 feedBound
    have h0 := norm_openActualAdvectionMode_le solution t hnu hk 0
    have h1 := norm_openActualAdvectionMode_le solution t hnu hk 1
    have h2 := norm_openActualAdvectionMode_le solution t hnu hk 2
    linarith
  calc 3 * Real.sqrt (torusStokesEigenvalue k) * complexVectorL1 (openAdvectionMode solution t k)
      ≤ 3 * Real.sqrt (torusStokesEigenvalue k) * (3 * feedBound solution t radius) :=
        mul_le_mul_of_nonneg_left hadv (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    _ = 3 ^ 2 * Real.sqrt (torusStokesEigenvalue k) * feedBound solution t radius := by ring

/-! ## The modal Riccati inequality -/

/-- **The modal Riccati inequality.**  At every interior time, for every receiver outside the cube
of radius `2N`, the modal energy is differentiable and its derivative is at most the Stokes
dissipation plus the amplitude times the shell-step cost. -/
theorem modalEnergy_riccati (hnu : 0 ≤ nu) (t : Ioo 0 T) {radius : ℕ} {k : SpatialFrequency}
    (hk : k ∉ frequencyCube (2 * radius)) :
    ∃ D : ℝ, HasDerivAt (modalEnergy (velocity := velocity) k) D t.1 ∧
      D ≤ -2 * nu * torusStokesEigenvalue k * modalEnergy (velocity := velocity) k t.1 +
        2 * complexVectorL1 (vorticityModeCurve (velocity := velocity) k t.1) *
          (3 ^ 2 * Real.sqrt (torusStokesEigenvalue k) * feedBound solution t radius) := by
  have hmode := openPeriodicSolutionOn_hasDerivAt_vorticityMode_stokes solution t k
  set N := vorticityNonlinearMode solution t k with hN
  set w := vorticityModeCurve (velocity := velocity) k t.1 with hw
  have hcomp : ∀ component : Fin 3,
      HasDerivAt (fun τ ↦ vorticityModeCurve (velocity := velocity) k τ component)
        ((-(nu * torusStokesEigenvalue k)) • w component + N component) t.1 := by
    intro component
    have h := (hasDerivAt_pi.mp hmode) component
    simp only [Pi.add_apply, Pi.smul_apply] at h
    rw [smul_eq_mul, ← Complex.real_smul] at h
    rw [hw]
    exact h
  have hterm : ∀ component : Fin 3,
      HasDerivAt (fun τ ↦ inner ℝ (vorticityModeCurve (velocity := velocity) k τ component)
          (vorticityModeCurve (velocity := velocity) k τ component))
        (2 * (-(nu * torusStokesEigenvalue k) * inner ℝ (w component) (w component) +
          inner ℝ (w component) (N component))) t.1 := by
    intro component
    have h := (hcomp component).inner (𝕜 := ℝ) (hcomp component)
    refine h.congr_deriv ?_
    rw [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm (N component)]
    ring
  refine ⟨∑ component : Fin 3, 2 * (-(nu * torusStokesEigenvalue k) * inner ℝ (w component) (w component) +
      inner ℝ (w component) (N component)), ?_, ?_⟩
  · unfold modalEnergy
    exact HasDerivAt.sum (u := Finset.univ) (fun component _ ↦ hterm component)
  have hbound : ∀ component : Fin 3,
      inner ℝ (w component) (N component) ≤ ‖w component‖ * complexVectorL1 N := by
    intro component
    refine (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    unfold complexVectorL1
    fin_cases component <;> simp <;> linarith [norm_nonneg (N 0), norm_nonneg (N 1), norm_nonneg (N 2)]
  have hNle := complexVectorL1_vorticityNonlinearMode_le solution hnu t hk
  have hsum : ∑ component : Fin 3, inner ℝ (w component) (N component) ≤
      complexVectorL1 w * complexVectorL1 N := by
    rw [complexVectorL1_eq_sum w, Finset.sum_mul]
    exact Finset.sum_le_sum fun component _ ↦ hbound component
  have hE : modalEnergy (velocity := velocity) k t.1 =
      ∑ component : Fin 3, inner ℝ (w component) (w component) := rfl
  rw [hE]
  have hw_nonneg : 0 ≤ complexVectorL1 w := complexVectorL1_nonneg w
  calc ∑ component : Fin 3, 2 * (-(nu * torusStokesEigenvalue k) * inner ℝ (w component) (w component) +
          inner ℝ (w component) (N component))
      = -2 * nu * torusStokesEigenvalue k *
            (∑ component : Fin 3, inner ℝ (w component) (w component)) +
          2 * ∑ component : Fin 3, inner ℝ (w component) (N component) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro component _
        ring
    _ ≤ -2 * nu * torusStokesEigenvalue k *
            (∑ component : Fin 3, inner ℝ (w component) (w component)) +
          2 * (complexVectorL1 w * complexVectorL1 N) := by
        gcongr
    _ ≤ -2 * nu * torusStokesEigenvalue k *
            (∑ component : Fin 3, inner ℝ (w component) (w component)) +
          2 * complexVectorL1 w *
            (3 ^ 2 * Real.sqrt (torusStokesEigenvalue k) * feedBound solution t radius) := by
        have := mul_le_mul_of_nonneg_left hNle hw_nonneg
        linarith

section Audit

#print axioms complexVectorL1_sq_le_three_mul_modalEnergy
#print axioms complexVectorL1_frequencyCurlMultiplier_le
#print axioms complexVectorL1_vorticityNonlinearMode_le
#print axioms modalEnergy_riccati

end Audit

end Soma.Holonics.Millennium.NavierStokesModalRiccati
