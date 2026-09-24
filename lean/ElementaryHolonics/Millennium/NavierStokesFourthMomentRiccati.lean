import ElementaryHolonics.Millennium.NavierStokesTailGronwall
import ElementaryHolonics.Millennium.NavierStokesWeightedTailEnergy
import ElementaryHolonics.Millennium.NavierStokesIncoherentBandMass

/-!
# The fourth-moment Riccati inequality with the incoherent half-radius cost

The Riccati chain is made generic over any bound on the advection coefficient, then instantiated
with the incoherent cost: the band paid by the zero mode and its second moment of vorticity
energy through the lattice weight, no count of modes.  Summed with weights `|k|_∞⁴` over a finite
family of nonzero modes, the family's fourth moment of vorticity energy is differentiable and

```text
M₄' ≤ −ν (2π)² M₆ + (3⁵/ν) · Σ_k |k|_∞⁴ · incoherentCost(⌊(|k|_∞−1)/2⌋)².
```

Dissipation acts at weight six.  The drive is the weighted sum of squared costs; the swap lemma
of the next owner reads it in moments of the modal energy.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Finset

namespace Soma.Holonics.Millennium.NavierStokesFourthMomentRiccati

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
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesShellStepCost
open Soma.Holonics.Millennium.NavierStokesModalRiccati
open Soma.Holonics.Millennium.NavierStokesModalGronwall
open Soma.Holonics.Millennium.NavierStokesHalfRadiusReach
open Soma.Holonics.Millennium.NavierStokesTailGronwall
open Soma.Holonics.Millennium.NavierStokesIncoherentBandMass

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)

/-! ## The generic Riccati chain -/

/-- The nonlinear source is paid by any bound on the advection coefficient. -/
theorem complexVectorL1_vorticityNonlinearMode_le_of (t : Ioo 0 T) (k : SpatialFrequency)
    {B : ℝ} (hB : ∀ output : Fin 3, ‖openActualAdvectionMode solution t k output‖ ≤ B) :
    complexVectorL1 (vorticityNonlinearMode solution t k) ≤
      3 ^ 2 * Real.sqrt (torusStokesEigenvalue k) * B := by
  unfold vorticityNonlinearMode
  have hneg : complexVectorL1 (-frequencyCurlMultiplier k (openAdvectionMode solution t k)) =
      complexVectorL1 (frequencyCurlMultiplier k (openAdvectionMode solution t k)) := by
    simp [complexVectorL1]
  rw [hneg]
  refine (complexVectorL1_frequencyCurlMultiplier_le k _).trans ?_
  have hadv : complexVectorL1 (openAdvectionMode solution t k) ≤ 3 * B := by
    rw [openAdvectionMode_eq_openActualAdvectionMode]
    unfold complexVectorL1
    have h0 := hB 0
    have h1 := hB 1
    have h2 := hB 2
    linarith
  calc 3 * Real.sqrt (torusStokesEigenvalue k) * complexVectorL1 (openAdvectionMode solution t k)
      ≤ 3 * Real.sqrt (torusStokesEigenvalue k) * (3 * B) :=
        mul_le_mul_of_nonneg_left hadv (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    _ = 3 ^ 2 * Real.sqrt (torusStokesEigenvalue k) * B := by ring

theorem modalEnergy_riccati_of (t : Ioo 0 T) (k : SpatialFrequency) {B : ℝ}
    (hB : complexVectorL1 (vorticityNonlinearMode solution t k) ≤
      3 ^ 2 * Real.sqrt (torusStokesEigenvalue k) * B) :
    ∃ D : ℝ, HasDerivAt (modalEnergy (velocity := velocity) k) D t.1 ∧
      D ≤ -2 * nu * torusStokesEigenvalue k * modalEnergy (velocity := velocity) k t.1 +
        2 * complexVectorL1 (vorticityModeCurve (velocity := velocity) k t.1) *
          (3 ^ 2 * Real.sqrt (torusStokesEigenvalue k) * B) := by
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
  have hNle := hB
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
            (3 ^ 2 * Real.sqrt (torusStokesEigenvalue k) * B) := by
        have := mul_le_mul_of_nonneg_left hNle hw_nonneg
        linarith


theorem modalEnergy_riccati_amgm_of (hnu : 0 < nu) (t : Ioo 0 T) (k : SpatialFrequency) {B : ℝ}
    (hB : complexVectorL1 (vorticityNonlinearMode solution t k) ≤
      3 ^ 2 * Real.sqrt (torusStokesEigenvalue k) * B) (hpos : 0 < torusStokesEigenvalue k) :
    ∃ D : ℝ, HasDerivAt (modalEnergy (velocity := velocity) k) D t.1 ∧
      D ≤ -(nu * torusStokesEigenvalue k) * modalEnergy (velocity := velocity) k t.1 +
        3 ^ 5 / nu * B ^ 2 := by
  obtain ⟨D, hD, hle⟩ := modalEnergy_riccati_of solution t k hB
  refine ⟨D, hD, hle.trans ?_⟩
  set lam := torusStokesEigenvalue k with hlam
  set E := modalEnergy (velocity := velocity) k t.1 with hE
  set L := complexVectorL1 (vorticityModeCurve (velocity := velocity) k t.1) with hL
  have hlam0 : 0 ≤ lam := hpos.le
  have hL2 : L ^ 2 ≤ 3 * E := complexVectorL1_sq_le_three_mul_modalEnergy k t.1
  have hstep := amgm_step hnu (L * Real.sqrt lam) B
  have hsqrt : (L * Real.sqrt lam) ^ 2 = L ^ 2 * lam := by
    rw [mul_pow, Real.sq_sqrt hlam0]
  have hcross : 2 * L * (3 ^ 2 * Real.sqrt lam * B) = 2 * 3 ^ 2 * (L * Real.sqrt lam) * B := by ring
  rw [hcross]
  have hmid : nu / 3 * (L * Real.sqrt lam) ^ 2 ≤ nu * lam * E := by
    rw [hsqrt]
    have : L ^ 2 * lam ≤ 3 * E * lam := mul_le_mul_of_nonneg_right hL2 hlam0
    nlinarith
  linarith


/-! ## The incoherent half-radius cost -/

/-- The incoherent shell-step cost: the band paid by the zero mode and its second moment. -/
def incoherentCost (t : Ioo 0 T) (radius : ℕ) : ℝ :=
  (complexVectorL1 (openPeriodicVelocityFourierMode solution t 0) +
      Real.sqrt (52 * (3 / (2 * Real.pi) ^ 2)) *
        Real.sqrt (bandSecondMoment (velocity := velocity) t radius)) *
      openPeriodicJacobianCoefficientTailMass solution t (frequencyCube radius) +
    velocityTailMass solution t radius * openPeriodicJacobianCoefficientTailMass solution t ∅

theorem norm_openActualAdvectionMode_le_incoherent (t : Ioo 0 T) {radius : ℕ}
    {k : SpatialFrequency} (hk : k ∉ frequencyCube (2 * radius)) (output : Fin 3) :
    ‖openActualAdvectionMode solution t k output‖ ≤ incoherentCost solution t radius := by
  rw [openActualAdvectionMode_eq_bandFeed_add_tailFeed solution t radius]
  exact (norm_add_le _ _).trans (add_le_add (norm_bandFeed_le_secondMoment solution t hk output)
    (norm_tailFeed_le solution t radius k output))

/-- **The modal Riccati inequality with the incoherent half-radius cost.** -/
theorem modalEnergy_riccati_incoherent (hnu : 0 < nu) (t : Ioo 0 T) {k : SpatialFrequency}
    (hk : 1 ≤ frequencySup k) :
    ∃ D : ℝ, HasDerivAt (modalEnergy (velocity := velocity) k) D t.1 ∧
      D ≤ -(nu * torusStokesEigenvalue k) * modalEnergy (velocity := velocity) k t.1 +
        3 ^ 5 / nu * incoherentCost solution t (halfRadius k) ^ 2 :=
  modalEnergy_riccati_amgm_of solution hnu t k
    (complexVectorL1_vorticityNonlinearMode_le_of solution t k
      (norm_openActualAdvectionMode_le_incoherent solution t
        (not_mem_frequencyCube_two_mul_halfRadius hk)))
    (torusStokesEigenvalue_pos_of_not_mem (not_mem_frequencyCube_two_mul_halfRadius hk))

/-! ## The fourth-moment family Riccati -/

/-- The `w`-th moment of vorticity energy of a finite family. -/
def momentEnergy (w : ℕ) (family : Finset SpatialFrequency) (τ : ℝ) : ℝ :=
  ∑ k ∈ family, ((frequencySup k : ℕ) : ℝ) ^ w * modalEnergy (velocity := velocity) k τ

/-- The fourth-moment incoherent cost of a finite family. -/
def momentCost (t : Ioo 0 T) (family : Finset SpatialFrequency) : ℝ :=
  ∑ k ∈ family, ((frequencySup k : ℕ) : ℝ) ^ 4 * incoherentCost solution t (halfRadius k) ^ 2

/-- **The fourth-moment Riccati inequality.**  Dissipation at weight six against the fourth-moment
cost. -/
theorem momentEnergy_riccati (hnu : 0 < nu) (t : Ioo 0 T) {family : Finset SpatialFrequency}
    (hfamily : ∀ k ∈ family, 1 ≤ frequencySup k) :
    ∃ D : ℝ, HasDerivAt (momentEnergy (velocity := velocity) 4 family) D t.1 ∧
      D ≤ -(nu * (2 * Real.pi) ^ 2) * momentEnergy (velocity := velocity) 6 family t.1 +
          3 ^ 5 / nu * momentCost solution t family := by
  have hmode : ∀ k ∈ family, ∃ D : ℝ,
      HasDerivAt (modalEnergy (velocity := velocity) k) D t.1 ∧
        D ≤ -(nu * torusStokesEigenvalue k) * modalEnergy (velocity := velocity) k t.1 +
          3 ^ 5 / nu * incoherentCost solution t (halfRadius k) ^ 2 :=
    fun k hk ↦ modalEnergy_riccati_incoherent solution hnu t (hfamily k hk)
  choose! D hD using hmode
  refine ⟨∑ k ∈ family, ((frequencySup k : ℕ) : ℝ) ^ 4 * D k, ?_, ?_⟩
  · unfold momentEnergy
    have hfun : (fun τ ↦ ∑ k ∈ family,
        ((frequencySup k : ℕ) : ℝ) ^ 4 * modalEnergy (velocity := velocity) k τ) =
        ∑ k ∈ family, fun τ ↦ ((frequencySup k : ℕ) : ℝ) ^ 4 *
          modalEnergy (velocity := velocity) k τ := by
      funext τ
      simp [Finset.sum_apply]
    rw [hfun]
    exact HasDerivAt.sum fun k hk ↦ (hD k hk).1.const_mul _
  · unfold momentEnergy momentCost
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro k hk
    have hw : (0 : ℝ) ≤ ((frequencySup k : ℕ) : ℝ) ^ 4 := by positivity
    have hE := modalEnergy_nonneg (velocity := velocity) k t.1
    have hlam : (2 * Real.pi) ^ 2 * ((frequencySup k : ℕ) : ℝ) ^ 2 ≤ torusStokesEigenvalue k :=
      torusStokesEigenvalue_ge k
    have h1 := mul_le_mul_of_nonneg_left (hD k hk).2 hw
    have h2 : ((frequencySup k : ℕ) : ℝ) ^ 4 * (-(nu * torusStokesEigenvalue k) *
        modalEnergy (velocity := velocity) k t.1) ≤
        -(nu * (2 * Real.pi) ^ 2) * (((frequencySup k : ℕ) : ℝ) ^ 6 *
          modalEnergy (velocity := velocity) k t.1) := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlam hnu.le)
        (mul_nonneg hw hE)
      nlinarith [this]
    nlinarith [h1, h2]

section Audit

#print axioms modalEnergy_riccati_of
#print axioms modalEnergy_riccati_incoherent
#print axioms momentEnergy_riccati

end Audit

end Soma.Holonics.Millennium.NavierStokesFourthMomentRiccati
