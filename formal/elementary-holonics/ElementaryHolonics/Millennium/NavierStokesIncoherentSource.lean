import ElementaryHolonics.Millennium.NavierStokesMomentClosure

/-!
# The incoherent source: feeds that do not interfere constructively

The family Riccati at a generic weight `w`:

```text
M_w(F)' ≤ −2 ν (2π)² M_{w+2}(F) + 2 √(3 M_w(F)) · √(Σ_F |k|^w ℓ¹(N_k)²),
|k|^w ℓ¹(N_k)² ≤ 3³ (2π)² |k|^{w+2} Σ_o ‖adv_k(o)‖².
```

**Incoherence at a receiver** `k`: the advection mode is at most the diagonal of its feeds,
`‖adv_k(o)‖² ≤ Σ'_p ‖feed_{k,p}(o)‖²` (the cross term of the feed comb is nonpositive).  Each feed
is paid by the velocity mass of the sender and the modal energy of the carrier,
`Σ_o ‖feed_{k,p}(o)‖² ≤ 3 · V(p) · E_{k−p}`, so on incoherent receivers the weight-four source of
the advection is paid by products of moments only:

```text
Σ_F |k|⁴ Σ_o ‖adv_k(o)‖² ≤ 3 · 2³ · ( V · W₄ + W₀ · W₂ / (2π)² ),      V = Σ'_p V(p).
```

Every constant is a product expansion.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Finset

namespace Soma.Holonics.Millennium.NavierStokesIncoherentSource

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

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
  (t : Ioo 0 T)

/-! ## The generic-weight family Riccati -/

/-- The weighted source squared at weight `w` is paid by the advection at weight `w + 2`. -/
theorem sup_pow_l1_nonlinear_sq_le (w : ℕ) (k : SpatialFrequency) :
    ((frequencySup k : ℕ) : ℝ) ^ w * complexVectorL1 (vorticityNonlinearMode solution t k) ^ 2 ≤
      3 ^ 3 * (2 * Real.pi) ^ 2 * ((frequencySup k : ℕ) : ℝ) ^ (w + 2) *
        ∑ output : Fin 3, ‖openActualAdvectionMode solution t k output‖ ^ 2 := by
  unfold vorticityNonlinearMode
  have hneg : complexVectorL1 (-frequencyCurlMultiplier k (openAdvectionMode solution t k)) =
      complexVectorL1 (frequencyCurlMultiplier k (openAdvectionMode solution t k)) := by
    simp [complexVectorL1]
  rw [hneg]
  have hcurl := complexVectorL1_frequencyCurlMultiplier_sq_le k (openAdvectionMode solution t k)
  have hlam : torusStokesEigenvalue k ≤ (2 * Real.pi) ^ 2 * (3 * ((frequencySup k : ℕ) : ℝ) ^ 2) := by
    unfold torusStokesEigenvalue
    exact mul_le_mul_of_nonneg_left (frequencySquared_le_three_sup_sq k) (by positivity)
  rw [openAdvectionMode_eq_openActualAdvectionMode] at hcurl ⊢
  have hS : 0 ≤ ∑ component : Fin 3, ‖openActualAdvectionMode solution t k component‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hw : (0 : ℝ) ≤ ((frequencySup k : ℕ) : ℝ) ^ w := by positivity
  calc ((frequencySup k : ℕ) : ℝ) ^ w *
        complexVectorL1 (frequencyCurlMultiplier k (openActualAdvectionMode solution t k)) ^ 2
      ≤ ((frequencySup k : ℕ) : ℝ) ^ w * (9 * torusStokesEigenvalue k *
          ∑ component : Fin 3, ‖openActualAdvectionMode solution t k component‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hcurl hw
    _ ≤ ((frequencySup k : ℕ) : ℝ) ^ w * (9 * ((2 * Real.pi) ^ 2 * (3 * ((frequencySup k : ℕ) : ℝ) ^ 2)) *
          ∑ component : Fin 3, ‖openActualAdvectionMode solution t k component‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hw
        apply mul_le_mul_of_nonneg_right _ hS
        exact mul_le_mul_of_nonneg_left hlam (by norm_num)
    _ = 3 ^ 3 * (2 * Real.pi) ^ 2 * ((frequencySup k : ℕ) : ℝ) ^ (w + 2) *
          ∑ output : Fin 3, ‖openActualAdvectionMode solution t k output‖ ^ 2 := by
        rw [pow_add]; ring

/-- **The family Riccati at weight `w`.** -/
theorem momentEnergy_riccati_gen (w : ℕ) (hnu : 0 < nu) {F : Finset SpatialFrequency}
    (hF : ∀ k ∈ F, 1 ≤ frequencySup k) :
    ∃ D : ℝ, HasDerivAt (momentEnergy (velocity := velocity) w F) D t.1 ∧
      D ≤ -2 * nu * (2 * Real.pi) ^ 2 * momentEnergy (velocity := velocity) (w + 2) F t.1 +
        2 * Real.sqrt (3 * momentEnergy (velocity := velocity) w F t.1) *
          Real.sqrt (∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ w *
            complexVectorL1 (vorticityNonlinearMode solution t k) ^ 2) := by
  have hmode : ∀ k ∈ F, ∃ D : ℝ,
      HasDerivAt (modalEnergy (velocity := velocity) k) D t.1 ∧
        D ≤ -2 * nu * torusStokesEigenvalue k * modalEnergy (velocity := velocity) k t.1 +
          2 * complexVectorL1 (vorticityModeCurve (velocity := velocity) k t.1) *
            complexVectorL1 (vorticityNonlinearMode solution t k) :=
    fun k hk ↦ modalEnergy_riccati_raw solution t (hF k hk)
  choose! D hD using hmode
  refine ⟨∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ w * D k, ?_, ?_⟩
  · unfold momentEnergy
    have hfun : (fun τ ↦ ∑ k ∈ F,
        ((frequencySup k : ℕ) : ℝ) ^ w * modalEnergy (velocity := velocity) k τ) =
        ∑ k ∈ F, fun τ ↦ ((frequencySup k : ℕ) : ℝ) ^ w *
          modalEnergy (velocity := velocity) k τ := by
      funext τ
      simp [Finset.sum_apply]
    rw [hfun]
    exact HasDerivAt.sum fun k hk ↦ (hD k hk).1.const_mul _
  · set a : SpatialFrequency → ℝ := fun k ↦ Real.sqrt (((frequencySup k : ℕ) : ℝ) ^ w) *
      complexVectorL1 (vorticityModeCurve (velocity := velocity) k t.1) with ha
    set b : SpatialFrequency → ℝ := fun k ↦ Real.sqrt (((frequencySup k : ℕ) : ℝ) ^ w) *
      complexVectorL1 (vorticityNonlinearMode solution t k) with hb
    have hsqrt : ∀ k, Real.sqrt (((frequencySup k : ℕ) : ℝ) ^ w) *
        Real.sqrt (((frequencySup k : ℕ) : ℝ) ^ w) = ((frequencySup k : ℕ) : ℝ) ^ w :=
      fun k ↦ Real.mul_self_sqrt (by positivity)
    have hterm : ∀ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ w * D k ≤
        -2 * nu * (2 * Real.pi) ^ 2 *
          (((frequencySup k : ℕ) : ℝ) ^ (w + 2) * modalEnergy (velocity := velocity) k t.1) +
          2 * a k * b k := by
      intro k hk
      have hw : (0 : ℝ) ≤ ((frequencySup k : ℕ) : ℝ) ^ w := by positivity
      have h1 := mul_le_mul_of_nonneg_left (hD k hk).2 hw
      have hlam : (2 * Real.pi) ^ 2 * ((frequencySup k : ℕ) : ℝ) ^ 2 ≤ torusStokesEigenvalue k :=
        torusStokesEigenvalue_ge k
      have hE := modalEnergy_nonneg (velocity := velocity) k t.1
      have h2 : ((frequencySup k : ℕ) : ℝ) ^ w * (-2 * nu * torusStokesEigenvalue k *
          modalEnergy (velocity := velocity) k t.1) ≤
          -2 * nu * (2 * Real.pi) ^ 2 *
            (((frequencySup k : ℕ) : ℝ) ^ (w + 2) * modalEnergy (velocity := velocity) k t.1) := by
        rw [pow_add]
        have := mul_le_mul_of_nonneg_left hlam
          (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hnu.le) (mul_nonneg hw hE))
        nlinarith [this]
      have h3 : ((frequencySup k : ℕ) : ℝ) ^ w *
          (2 * complexVectorL1 (vorticityModeCurve (velocity := velocity) k t.1) *
            complexVectorL1 (vorticityNonlinearMode solution t k)) = 2 * a k * b k := by
        rw [ha, hb]
        dsimp only
        have h := hsqrt k
        calc ((frequencySup k : ℕ) : ℝ) ^ w *
              (2 * complexVectorL1 (vorticityModeCurve (velocity := velocity) k t.1) *
                complexVectorL1 (vorticityNonlinearMode solution t k))
            = (Real.sqrt (((frequencySup k : ℕ) : ℝ) ^ w) * Real.sqrt (((frequencySup k : ℕ) : ℝ) ^ w)) *
              (2 * complexVectorL1 (vorticityModeCurve (velocity := velocity) k t.1) *
                complexVectorL1 (vorticityNonlinearMode solution t k)) := by rw [h]
          _ = _ := by ring
      calc ((frequencySup k : ℕ) : ℝ) ^ w * D k
          ≤ ((frequencySup k : ℕ) : ℝ) ^ w * (-2 * nu * torusStokesEigenvalue k *
              modalEnergy (velocity := velocity) k t.1) +
            ((frequencySup k : ℕ) : ℝ) ^ w *
              (2 * complexVectorL1 (vorticityModeCurve (velocity := velocity) k t.1) *
                complexVectorL1 (vorticityNonlinearMode solution t k)) := by
            rw [← mul_add]; exact h1
        _ ≤ _ := by rw [h3]; exact add_le_add h2 le_rfl
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq F a b
    have hleft : ∑ k ∈ F, a k ^ 2 ≤ 3 * momentEnergy (velocity := velocity) w F t.1 := by
      unfold momentEnergy
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k _
      have := complexVectorL1_sq_le_three_mul_modalEnergy (velocity := velocity) k t.1
      have hw : (0 : ℝ) ≤ ((frequencySup k : ℕ) : ℝ) ^ w := by positivity
      calc a k ^ 2 = ((frequencySup k : ℕ) : ℝ) ^ w *
            complexVectorL1 (vorticityModeCurve (velocity := velocity) k t.1) ^ 2 := by
            rw [ha]; dsimp only; rw [mul_pow, Real.sq_sqrt hw]
        _ ≤ ((frequencySup k : ℕ) : ℝ) ^ w * (3 * modalEnergy (velocity := velocity) k t.1) :=
            mul_le_mul_of_nonneg_left this hw
        _ = 3 * (((frequencySup k : ℕ) : ℝ) ^ w * modalEnergy (velocity := velocity) k t.1) := by ring
    have hright : ∑ k ∈ F, b k ^ 2 = ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ w *
        complexVectorL1 (vorticityNonlinearMode solution t k) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hb]; dsimp only; rw [mul_pow, Real.sq_sqrt (by positivity)]
    have hab0 : 0 ≤ ∑ k ∈ F, a k * b k :=
      Finset.sum_nonneg fun k _ ↦ mul_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (complexVectorL1_nonneg _))
        (mul_nonneg (Real.sqrt_nonneg _) (complexVectorL1_nonneg _))
    have hM0 : 0 ≤ 3 * momentEnergy (velocity := velocity) w F t.1 :=
      mul_nonneg (by norm_num) (momentEnergy_nonneg w F t.1)
    have hS0 : 0 ≤ ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ w *
        complexVectorL1 (vorticityNonlinearMode solution t k) ^ 2 :=
      Finset.sum_nonneg fun k _ ↦ mul_nonneg (by positivity) (sq_nonneg _)
    have hsq : (∑ k ∈ F, a k * b k) ^ 2 ≤ (3 * momentEnergy (velocity := velocity) w F t.1) *
        ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ w *
          complexVectorL1 (vorticityNonlinearMode solution t k) ^ 2 := by
      rw [← hright]
      exact hcs.trans (mul_le_mul hleft le_rfl (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) hM0)
    have hle := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq hab0, Real.sqrt_mul hM0] at hle
    have hcross : ∑ k ∈ F, 2 * a k * b k ≤
        2 * Real.sqrt (3 * momentEnergy (velocity := velocity) w F t.1) *
          Real.sqrt (∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ w *
            complexVectorL1 (vorticityNonlinearMode solution t k) ^ 2) := by
      calc ∑ k ∈ F, 2 * a k * b k = 2 * ∑ k ∈ F, a k * b k := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ ↦ by ring
        _ ≤ 2 * (Real.sqrt (3 * momentEnergy (velocity := velocity) w F t.1) *
              Real.sqrt (∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ w *
                complexVectorL1 (vorticityNonlinearMode solution t k) ^ 2)) :=
            mul_le_mul_of_nonneg_left hle (by norm_num)
        _ = _ := by ring
    have hdiss : ∑ k ∈ F, -2 * nu * (2 * Real.pi) ^ 2 *
        (((frequencySup k : ℕ) : ℝ) ^ (w + 2) * modalEnergy (velocity := velocity) k t.1) =
        -2 * nu * (2 * Real.pi) ^ 2 * momentEnergy (velocity := velocity) (w + 2) F t.1 := by
      unfold momentEnergy
      rw [Finset.mul_sum]
    rw [hdiss]
    linarith [hcross]

/-! ## Velocity mass and the feed diagonal -/

/-- The velocity mass of a mode. -/
def velPop (p : SpatialFrequency) : ℝ :=
  ∑ c : Fin 3, ‖openPeriodicVelocityFourierMode solution t p c‖ ^ 2

theorem velPop_nonneg (p : SpatialFrequency) : 0 ≤ velPop solution t p :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem velPop_le_l1Pop_sq (p : SpatialFrequency) :
    velPop solution t p ≤ l1Pop solution t p ^ 2 := by
  unfold velPop l1Pop complexVectorL1
  rw [Fin.sum_univ_three]
  have h0 := norm_nonneg (openPeriodicVelocityFourierMode solution t p 0)
  have h1 := norm_nonneg (openPeriodicVelocityFourierMode solution t p 1)
  have h2 := norm_nonneg (openPeriodicVelocityFourierMode solution t p 2)
  nlinarith [mul_nonneg h0 h1, mul_nonneg h0 h2, mul_nonneg h1 h2]

theorem summable_velPop : Summable (velPop solution t) := by
  have hL := summable_l1Pop solution t
  refine Summable.of_nonneg_of_le (velPop_nonneg solution t)
    (fun p ↦ (velPop_le_l1Pop_sq solution t p).trans ?_) (hL.mul_right (∑' q, l1Pop solution t q))
  have hp : l1Pop solution t p ≤ ∑' q, l1Pop solution t q :=
    hL.le_tsum p fun q _ ↦ l1Pop_nonneg solution t q
  calc l1Pop solution t p ^ 2 = l1Pop solution t p * l1Pop solution t p := by ring
    _ ≤ l1Pop solution t p * ∑' q, l1Pop solution t q :=
        mul_le_mul_of_nonneg_left hp (l1Pop_nonneg solution t p)

/-- The velocity mass: the Fourier energy at the slice. -/
def velocityMass : ℝ := ∑' p, velPop solution t p

theorem velocityMass_nonneg : 0 ≤ velocityMass solution t :=
  tsum_nonneg fun p ↦ velPop_nonneg solution t p

theorem velPop_le_velocityMass (p : SpatialFrequency) :
    velPop solution t p ≤ velocityMass solution t :=
  (summable_velPop solution t).le_tsum p fun q _ ↦ velPop_nonneg solution t q

/-- The modal energy is the velocity mass weighted by the Stokes eigenvalue. -/
theorem modalEnergy_eq_velPop (q : SpatialFrequency) :
    modalEnergy (velocity := velocity) q t.1 =
      (2 * Real.pi) ^ 2 * frequencySquared q * velPop solution t q := by
  have h1 := modalEnergy_eq_sum_norm_sq_curl (solution := solution) t q
  have h2 := sum_norm_sq_frequencyCurlMultiplier q (openPeriodicVelocityFourierMode solution t q)
    (openPeriodicVelocityFourierMode_divergenceFree solution t q)
  rw [h1, h2]
  rfl

theorem sup_pow_four_velPop_le (q : SpatialFrequency) :
    ((frequencySup q : ℕ) : ℝ) ^ 4 * velPop solution t q ≤
      momentPop (velocity := velocity) 2 t.1 q / (2 * Real.pi) ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  unfold momentPop
  rw [modalEnergy_eq_velPop solution t q]
  have hfs := frequencySup_sq_le_frequencySquared q
  have hv := velPop_nonneg solution t q
  have hc : (0 : ℝ) ≤ (2 * Real.pi) ^ 2 * velPop solution t q * ((frequencySup q : ℕ) : ℝ) ^ 2 :=
    mul_nonneg (mul_nonneg (by positivity) hv) (by positivity)
  have key := mul_le_mul_of_nonneg_left hfs hc
  calc ((frequencySup q : ℕ) : ℝ) ^ 4 * velPop solution t q * (2 * Real.pi) ^ 2
      = (2 * Real.pi) ^ 2 * velPop solution t q * ((frequencySup q : ℕ) : ℝ) ^ 2 *
          ((frequencySup q : ℕ) : ℝ) ^ 2 := by ring
    _ ≤ (2 * Real.pi) ^ 2 * velPop solution t q * ((frequencySup q : ℕ) : ℝ) ^ 2 *
          frequencySquared q := key
    _ = _ := by ring

theorem momentPop_zero_weight (q : SpatialFrequency) (τ : ℝ) :
    momentPop (velocity := velocity) 0 τ q = modalEnergy (velocity := velocity) q τ := by
  unfold momentPop; simp

include solution in
theorem summable_momentPop_zero (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) :
    Summable (momentPop (velocity := velocity) 0 t.1) := by
  refine Summable.of_nonneg_of_le (momentPop_nonneg 0 t.1) (fun q ↦ ?_)
    (summable_momentPop (w := 1) (by norm_num) (by norm_num) t.1 hsum)
  rw [momentPop_zero_weight]
  exact modalEnergy_le_momentPop_one solution t q

include solution in
theorem modalEnergy_le_moment_one (hsum : Summable (eleventhMoment (velocity := velocity) t.1))
    (q : SpatialFrequency) :
    modalEnergy (velocity := velocity) q t.1 ≤ moment (velocity := velocity) 1 t.1 :=
  (modalEnergy_le_momentPop_one solution t q).trans
    ((summable_momentPop (by norm_num) (by norm_num) t.1 hsum).le_tsum q
      fun j _ ↦ momentPop_nonneg 1 t.1 j)

/-- **Each feed is paid by the sender's velocity mass and the carrier's modal energy.** -/
theorem sum_sq_feedTerm_le (k p : SpatialFrequency) :
    ∑ output : Fin 3, ‖feedTerm solution t k p output‖ ^ 2 ≤
      3 * velPop solution t p * modalEnergy (velocity := velocity) (k - p) t.1 := by
  have hJ : ∀ c : Fin 3, ∑ o : Fin 3, ‖openPeriodicJacobianFourierMode solution t (k - p) o c‖ ^ 2 ≤
      modalEnergy (velocity := velocity) (k - p) t.1 := by
    intro c
    rw [← sum_norm_sq_jacobianMode_eq solution t (k - p)]
    exact Finset.sum_le_sum fun o _ ↦ Finset.single_le_sum
      (f := fun c' ↦ ‖openPeriodicJacobianFourierMode solution t (k - p) o c'‖ ^ 2)
      (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ c)
  have hterm : ∀ o : Fin 3, ‖feedTerm solution t k p o‖ ^ 2 ≤
      3 * ∑ c : Fin 3, ‖openPeriodicVelocityFourierMode solution t p c‖ ^ 2 *
        ‖openPeriodicJacobianFourierMode solution t (k - p) o c‖ ^ 2 := by
    intro o
    have h1 : ‖feedTerm solution t k p o‖ ≤ ∑ c : Fin 3,
        ‖openPeriodicVelocityFourierMode solution t p c‖ *
          ‖openPeriodicJacobianFourierMode solution t (k - p) o c‖ := by
      unfold feedTerm
      refine (norm_sum_le _ _).trans ?_
      exact Finset.sum_le_sum fun c _ ↦ by rw [norm_mul]
    have h2 : (∑ c : Fin 3, ‖openPeriodicVelocityFourierMode solution t p c‖ *
        ‖openPeriodicJacobianFourierMode solution t (k - p) o c‖) ^ 2 ≤
        3 * ∑ c : Fin 3, (‖openPeriodicVelocityFourierMode solution t p c‖ *
          ‖openPeriodicJacobianFourierMode solution t (k - p) o c‖) ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 3)))
        (f := fun c ↦ ‖openPeriodicVelocityFourierMode solution t p c‖ *
          ‖openPeriodicJacobianFourierMode solution t (k - p) o c‖)
      simpa using this
    calc ‖feedTerm solution t k p o‖ ^ 2
        ≤ (∑ c : Fin 3, ‖openPeriodicVelocityFourierMode solution t p c‖ *
            ‖openPeriodicJacobianFourierMode solution t (k - p) o c‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
      _ = _ := by simp only [mul_pow]
  calc ∑ output : Fin 3, ‖feedTerm solution t k p output‖ ^ 2
      ≤ ∑ o : Fin 3, 3 * ∑ c : Fin 3, ‖openPeriodicVelocityFourierMode solution t p c‖ ^ 2 *
          ‖openPeriodicJacobianFourierMode solution t (k - p) o c‖ ^ 2 :=
        Finset.sum_le_sum fun o _ ↦ hterm o
    _ = 3 * ∑ c : Fin 3, ‖openPeriodicVelocityFourierMode solution t p c‖ ^ 2 *
          ∑ o : Fin 3, ‖openPeriodicJacobianFourierMode solution t (k - p) o c‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        exact Finset.sum_congr rfl fun c _ ↦ (Finset.mul_sum _ _ _).symm
    _ ≤ 3 * ∑ c : Fin 3, ‖openPeriodicVelocityFourierMode solution t p c‖ ^ 2 *
          modalEnergy (velocity := velocity) (k - p) t.1 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ ↦
          mul_le_mul_of_nonneg_left (hJ c) (sq_nonneg _)) (by norm_num)
    _ = _ := by unfold velPop; rw [← Finset.sum_mul]; ring

theorem summable_velPop_mul_energy (hsum : Summable (eleventhMoment (velocity := velocity) t.1))
    (k : SpatialFrequency) :
    Summable fun p ↦ velPop solution t p * modalEnergy (velocity := velocity) (k - p) t.1 :=
  Summable.of_nonneg_of_le
    (fun p ↦ mul_nonneg (velPop_nonneg solution t p) (modalEnergy_nonneg _ _))
    (fun p ↦ mul_le_mul_of_nonneg_left (modalEnergy_le_moment_one solution t hsum (k - p))
      (velPop_nonneg solution t p))
    ((summable_velPop solution t).mul_right _)

theorem summable_sq_feedTerm (hsum : Summable (eleventhMoment (velocity := velocity) t.1))
    (k : SpatialFrequency) (output : Fin 3) :
    Summable fun p ↦ ‖feedTerm solution t k p output‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun _ ↦ sq_nonneg _)
    (fun p ↦ (Finset.single_le_sum (f := fun o ↦ ‖feedTerm solution t k p o‖ ^ 2)
      (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ output)).trans
      (by simpa [mul_assoc] using sum_sq_feedTerm_le solution t k p))
    ((summable_velPop_mul_energy solution t hsum k).mul_left 3)

/-! ## Incoherence and the coherence defect -/

/-- **The coherence defect at a receiver**: the advection mode exceeds the diagonal of its feed
comb by the factor `1 + κ` at most. -/
def CoherenceDefectAt (κ : ℝ) (k : SpatialFrequency) : Prop :=
  ∀ output : Fin 3, ‖openActualAdvectionMode solution t k output‖ ^ 2 ≤
    (1 + κ) * ∑' p, ‖feedTerm solution t k p output‖ ^ 2

/-- **Incoherence at a receiver**: defect zero, the advection mode is at most the diagonal of its
feed comb. -/
abbrev IncoherentAt (k : SpatialFrequency) : Prop := CoherenceDefectAt solution t 0 k

theorem sum_tsum_sq_feedTerm_le (hsum : Summable (eleventhMoment (velocity := velocity) t.1))
    (k : SpatialFrequency) :
    ∑ output : Fin 3, ∑' p, ‖feedTerm solution t k p output‖ ^ 2 ≤
      3 * ∑' p, velPop solution t p * modalEnergy (velocity := velocity) (k - p) t.1 := by
  have hs : ∀ o ∈ (Finset.univ : Finset (Fin 3)), Summable fun p ↦ ‖feedTerm solution t k p o‖ ^ 2 :=
    fun o _ ↦ summable_sq_feedTerm solution t hsum k o
  calc ∑ output : Fin 3, ∑' p, ‖feedTerm solution t k p output‖ ^ 2
      = ∑' p, ∑ output : Fin 3, ‖feedTerm solution t k p output‖ ^ 2 :=
        (Summable.tsum_finsetSum hs).symm
    _ ≤ ∑' p, 3 * (velPop solution t p * modalEnergy (velocity := velocity) (k - p) t.1) :=
        Summable.tsum_le_tsum (fun p ↦ by rw [← mul_assoc]; exact sum_sq_feedTerm_le solution t k p)
          (summable_sum hs) ((summable_velPop_mul_energy solution t hsum k).mul_left 3)
    _ = _ := tsum_mul_left

theorem sum_sq_adv_le_of_defect (hsum : Summable (eleventhMoment (velocity := velocity) t.1))
    {κ : ℝ} (hκ : 0 ≤ κ) {k : SpatialFrequency} (hk : CoherenceDefectAt solution t κ k) :
    ∑ output : Fin 3, ‖openActualAdvectionMode solution t k output‖ ^ 2 ≤
      (1 + κ) * (3 * ∑' p, velPop solution t p * modalEnergy (velocity := velocity) (k - p) t.1) := by
  calc ∑ output : Fin 3, ‖openActualAdvectionMode solution t k output‖ ^ 2
      ≤ ∑ output : Fin 3, (1 + κ) * ∑' p, ‖feedTerm solution t k p output‖ ^ 2 :=
        Finset.sum_le_sum fun o _ ↦ hk o
    _ = (1 + κ) * ∑ output : Fin 3, ∑' p, ‖feedTerm solution t k p output‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_tsum_sq_feedTerm_le solution t hsum k) (by linarith)

/-! ## The weight-four incoherent source -/

theorem frequencySup_pow_four_le (k p : SpatialFrequency) :
    ((frequencySup k : ℕ) : ℝ) ^ 4 ≤
      2 ^ 3 * (((frequencySup (k - p) : ℕ) : ℝ) ^ 4 + ((frequencySup p : ℕ) : ℝ) ^ 4) := by
  have h := frequencySup_sub_le k p
  have hcast : ((frequencySup k : ℕ) : ℝ) ≤
      ((frequencySup (k - p) : ℕ) : ℝ) + ((frequencySup p : ℕ) : ℝ) := by exact_mod_cast h
  have h2 : ∀ u v : ℝ, (u + v) ^ 2 ≤ 2 * (u ^ 2 + v ^ 2) := fun u v ↦ by nlinarith [sq_nonneg (u - v)]
  set a : ℝ := ((frequencySup (k - p) : ℕ) : ℝ)
  set b : ℝ := ((frequencySup p : ℕ) : ℝ)
  calc ((frequencySup k : ℕ) : ℝ) ^ 4 ≤ (a + b) ^ 4 := pow_le_pow_left₀ (by positivity) hcast 4
    _ = ((a + b) ^ 2) ^ 2 := by ring
    _ ≤ (2 * (a ^ 2 + b ^ 2)) ^ 2 := pow_le_pow_left₀ (by positivity) (h2 a b) 2
    _ = 4 * (a ^ 2 + b ^ 2) ^ 2 := by ring
    _ ≤ 4 * (2 * ((a ^ 2) ^ 2 + (b ^ 2) ^ 2)) := mul_le_mul_of_nonneg_left (h2 _ _) (by norm_num)
    _ = 2 ^ 3 * (a ^ 4 + b ^ 4) := by ring

/-- A finite family of shifted moment populations is at most the moment. -/
theorem sum_shift_le_moment {w : ℕ} (hsummable : Summable (momentPop (velocity := velocity) w t.1))
    (F : Finset SpatialFrequency) (p : SpatialFrequency) :
    ∑ k ∈ F, momentPop (velocity := velocity) w t.1 (k - p) ≤ moment (velocity := velocity) w t.1 := by
  have hinj : ∀ x ∈ F, ∀ y ∈ F, x - p = y - p → x = y := fun x _ y _ h ↦ sub_left_injective h
  calc ∑ k ∈ F, momentPop (velocity := velocity) w t.1 (k - p)
      = ∑ q ∈ F.image (fun k ↦ k - p), momentPop (velocity := velocity) w t.1 q :=
        (Finset.sum_image (f := momentPop (velocity := velocity) w t.1) (g := fun k ↦ k - p) hinj).symm
    _ ≤ _ := hsummable.sum_le_tsum _ fun q _ ↦ momentPop_nonneg w t.1 q

/-- **The weight-four source of the advection on incoherent receivers is paid by moments.** -/
theorem sum_pow_four_adv_sq_le_of_defect (F : Finset SpatialFrequency)
    (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) {κ : ℝ} (hκ : 0 ≤ κ)
    (hinc : ∀ k ∈ F, CoherenceDefectAt solution t κ k) :
    ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 *
        ∑ output : Fin 3, ‖openActualAdvectionMode solution t k output‖ ^ 2 ≤
      (1 + κ) * (3 * 2 ^ 3 * (velocityMass solution t * moment (velocity := velocity) 4 t.1 +
        moment (velocity := velocity) 0 t.1 * moment (velocity := velocity) 2 t.1 / (2 * Real.pi) ^ 2)) := by
  have hsum4 := summable_momentPop (velocity := velocity) (by norm_num : 1 ≤ 4) (by norm_num) t.1 hsum
  have hsum2 := summable_momentPop (velocity := velocity) (by norm_num : 1 ≤ 2) (by norm_num) t.1 hsum
  have hsum0 := summable_momentPop_zero solution t hsum
  have hV := summable_velPop solution t
  -- the two legs
  have hA : ∀ k ∈ F, Summable fun p ↦ momentPop (velocity := velocity) 4 t.1 (k - p) * velPop solution t p :=
    fun k _ ↦ Summable.of_nonneg_of_le
      (fun p ↦ mul_nonneg (momentPop_nonneg _ _ _) (velPop_nonneg solution t p))
      (fun p ↦ mul_le_mul_of_nonneg_right
        (hsum4.le_tsum (k - p) fun j _ ↦ momentPop_nonneg 4 t.1 j) (velPop_nonneg solution t p))
      (hV.mul_left _)
  have hB : ∀ k ∈ F, Summable fun p ↦ ((frequencySup p : ℕ) : ℝ) ^ 4 * velPop solution t p *
      modalEnergy (velocity := velocity) (k - p) t.1 :=
    fun k _ ↦ Summable.of_nonneg_of_le
      (fun p ↦ mul_nonneg (mul_nonneg (by positivity) (velPop_nonneg solution t p)) (modalEnergy_nonneg _ _))
      (fun p ↦ mul_le_mul (sup_pow_four_velPop_le solution t p)
        (modalEnergy_le_moment_one solution t hsum (k - p)) (modalEnergy_nonneg _ _)
        (by have := momentPop_nonneg (velocity := velocity) 2 t.1 p; positivity))
      ((hsum2.div_const _).mul_right _)
  have hcore : ∀ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 *
      (3 * ∑' p, velPop solution t p * modalEnergy (velocity := velocity) (k - p) t.1) ≤
      3 * 2 ^ 3 * ((∑' p, momentPop (velocity := velocity) 4 t.1 (k - p) * velPop solution t p) +
        ∑' p, ((frequencySup p : ℕ) : ℝ) ^ 4 * velPop solution t p *
          modalEnergy (velocity := velocity) (k - p) t.1) := by
    intro k hkF
    have hw : (0 : ℝ) ≤ ((frequencySup k : ℕ) : ℝ) ^ 4 := by positivity
    have hs1 : Summable fun p ↦ ((frequencySup k : ℕ) : ℝ) ^ 4 *
        (velPop solution t p * modalEnergy (velocity := velocity) (k - p) t.1) :=
      (summable_velPop_mul_energy solution t hsum k).mul_left _
    have hs2 : Summable fun p ↦ 2 ^ 3 * (((frequencySup (k - p) : ℕ) : ℝ) ^ 4 + ((frequencySup p : ℕ) : ℝ) ^ 4) *
        (velPop solution t p * modalEnergy (velocity := velocity) (k - p) t.1) :=
      (((hA k hkF).add (hB k hkF)).mul_left (2 ^ 3)).congr fun p ↦ by unfold momentPop; ring
    calc ((frequencySup k : ℕ) : ℝ) ^ 4 *
          (3 * ∑' p, velPop solution t p * modalEnergy (velocity := velocity) (k - p) t.1)
        = 3 * ∑' p, ((frequencySup k : ℕ) : ℝ) ^ 4 *
          (velPop solution t p * modalEnergy (velocity := velocity) (k - p) t.1) := by
          rw [mul_left_comm, ← tsum_mul_left]
      _ ≤ 3 * ∑' p, 2 ^ 3 * (((frequencySup (k - p) : ℕ) : ℝ) ^ 4 + ((frequencySup p : ℕ) : ℝ) ^ 4) *
          (velPop solution t p * modalEnergy (velocity := velocity) (k - p) t.1) := by
          refine mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum (fun p ↦ ?_) hs1 hs2) (by norm_num)
          exact mul_le_mul_of_nonneg_right (frequencySup_pow_four_le k p)
            (mul_nonneg (velPop_nonneg solution t p) (modalEnergy_nonneg _ _))
      _ = 3 * 2 ^ 3 * ∑' p, (momentPop (velocity := velocity) 4 t.1 (k - p) * velPop solution t p +
          ((frequencySup p : ℕ) : ℝ) ^ 4 * velPop solution t p *
            modalEnergy (velocity := velocity) (k - p) t.1) := by
          conv_rhs => rw [mul_assoc, ← tsum_mul_left]
          congr 1
          exact tsum_congr fun p ↦ by unfold momentPop; ring
      _ = _ := by rw [(hA k hkF).tsum_add (hB k hkF)]
  have hk : ∀ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 *
      ∑ output : Fin 3, ‖openActualAdvectionMode solution t k output‖ ^ 2 ≤
      (1 + κ) * (3 * 2 ^ 3 * ((∑' p, momentPop (velocity := velocity) 4 t.1 (k - p) * velPop solution t p) +
        ∑' p, ((frequencySup p : ℕ) : ℝ) ^ 4 * velPop solution t p *
          modalEnergy (velocity := velocity) (k - p) t.1)) := by
    intro k hkF
    have hw : (0 : ℝ) ≤ ((frequencySup k : ℕ) : ℝ) ^ 4 := by positivity
    calc ((frequencySup k : ℕ) : ℝ) ^ 4 *
          ∑ output : Fin 3, ‖openActualAdvectionMode solution t k output‖ ^ 2
        ≤ ((frequencySup k : ℕ) : ℝ) ^ 4 * ((1 + κ) *
          (3 * ∑' p, velPop solution t p * modalEnergy (velocity := velocity) (k - p) t.1)) :=
          mul_le_mul_of_nonneg_left (sum_sq_adv_le_of_defect solution t hsum hκ (hinc k hkF)) hw
      _ = (1 + κ) * (((frequencySup k : ℕ) : ℝ) ^ 4 *
          (3 * ∑' p, velPop solution t p * modalEnergy (velocity := velocity) (k - p) t.1)) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcore k hkF) (by linarith)
  refine (Finset.sum_le_sum hk).trans ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib]
  -- leg A
  have hlegA : ∑ k ∈ F, ∑' p, momentPop (velocity := velocity) 4 t.1 (k - p) * velPop solution t p ≤
      velocityMass solution t * moment (velocity := velocity) 4 t.1 := by
    rw [← Summable.tsum_finsetSum hA]
    have hsL : Summable fun p ↦ ∑ k ∈ F, momentPop (velocity := velocity) 4 t.1 (k - p) * velPop solution t p :=
      summable_sum hA
    calc ∑' p, ∑ k ∈ F, momentPop (velocity := velocity) 4 t.1 (k - p) * velPop solution t p
        ≤ ∑' p, velPop solution t p * moment (velocity := velocity) 4 t.1 := by
          refine Summable.tsum_le_tsum (fun p ↦ ?_) hsL (hV.mul_right _)
          rw [← Finset.sum_mul, mul_comm]
          exact mul_le_mul_of_nonneg_left (sum_shift_le_moment t hsum4 F p) (velPop_nonneg solution t p)
      _ = _ := tsum_mul_right
  -- leg B
  have hlegB : ∑ k ∈ F, ∑' p, ((frequencySup p : ℕ) : ℝ) ^ 4 * velPop solution t p *
      modalEnergy (velocity := velocity) (k - p) t.1 ≤
      moment (velocity := velocity) 0 t.1 * moment (velocity := velocity) 2 t.1 / (2 * Real.pi) ^ 2 := by
    rw [← Summable.tsum_finsetSum hB]
    have hsL : Summable fun p ↦ ∑ k ∈ F, ((frequencySup p : ℕ) : ℝ) ^ 4 * velPop solution t p *
        modalEnergy (velocity := velocity) (k - p) t.1 := summable_sum hB
    have hsR : Summable fun p ↦ momentPop (velocity := velocity) 2 t.1 p / (2 * Real.pi) ^ 2 *
        moment (velocity := velocity) 0 t.1 := (hsum2.div_const _).mul_right _
    calc ∑' p, ∑ k ∈ F, ((frequencySup p : ℕ) : ℝ) ^ 4 * velPop solution t p *
          modalEnergy (velocity := velocity) (k - p) t.1
        ≤ ∑' p, momentPop (velocity := velocity) 2 t.1 p / (2 * Real.pi) ^ 2 *
          moment (velocity := velocity) 0 t.1 := by
          refine Summable.tsum_le_tsum (fun p ↦ ?_) hsL hsR
          rw [← Finset.mul_sum]
          have hE : ∑ k ∈ F, modalEnergy (velocity := velocity) (k - p) t.1 ≤
              moment (velocity := velocity) 0 t.1 := by
            have := sum_shift_le_moment t hsum0 F p
            simpa only [momentPop_zero_weight] using this
          exact mul_le_mul (sup_pow_four_velPop_le solution t p) hE
            (Finset.sum_nonneg fun _ _ ↦ modalEnergy_nonneg _ _)
            (by have := momentPop_nonneg (velocity := velocity) 2 t.1 p; positivity)
      _ = (∑' p, momentPop (velocity := velocity) 2 t.1 p) / (2 * Real.pi) ^ 2 *
          moment (velocity := velocity) 0 t.1 := by
          rw [tsum_mul_right, tsum_div_const]
      _ = _ := by unfold moment; ring
  have h0 : (0 : ℝ) ≤ 3 * 2 ^ 3 := by norm_num
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add hlegA hlegB) h0)
    (by linarith)

section Audit

#print axioms momentEnergy_riccati_gen
#print axioms sum_pow_four_adv_sq_le_of_defect

end Audit

end Soma.Holonics.Millennium.NavierStokesIncoherentSource
