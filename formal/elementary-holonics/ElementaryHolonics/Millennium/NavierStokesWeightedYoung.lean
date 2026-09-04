import ElementaryHolonics.Millennium.NavierStokesYoungTsum

/-!
# The weighted Young on the whole advection coefficient

The advection coefficient at a receiver `k` is the complete convolution of the velocity `ℓ¹`
population with the Jacobian population.  Each term is at most `ℓ¹(û(p)) · √E_{k−p}`, and the
receiver's weight is shared between the legs by the sup-norm triangle inequality,
`|k|_∞² ≤ 2 (|p|_∞² + |k−p|_∞²)`.  Young twice returns, for every finite family of receivers,

```text
Σ_{k∈F} |k|_∞⁴ ‖adv_k‖² ≤ 2³ (Σ'_p |p|_∞² ℓ¹(û(p)))² · W₀ + 2³ (Σ'_p ℓ¹(û(p)))² · W₄,
```

with `W₀` the enstrophy and `W₄` the fourth moment of vorticity energy.  This is the product
estimate: the receiver's fourth moment is paid by the advecting population's second moment
against the enstrophy, plus the advecting mass against the fourth moment.  No split, no count.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Finset

namespace Soma.Holonics.Millennium.NavierStokesWeightedYoung

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

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
  (t : Ioo 0 T)

/-- The velocity `ℓ¹` population. -/
def l1Pop (p : SpatialFrequency) : ℝ := complexVectorL1 (openPeriodicVelocityFourierMode solution t p)

/-- The second-moment velocity `ℓ¹` population. -/
def l1SecondPop (p : SpatialFrequency) : ℝ := ((frequencySup p : ℕ) : ℝ) ^ 2 * l1Pop solution t p

/-- The root modal energy population. -/
def rootEnergy (q : SpatialFrequency) : ℝ := Real.sqrt (modalEnergy (velocity := velocity) q t.1)

/-- The second-moment root energy population. -/
def rootSecond (q : SpatialFrequency) : ℝ := ((frequencySup q : ℕ) : ℝ) ^ 2 * rootEnergy (velocity := velocity) t q

theorem l1Pop_nonneg (p : SpatialFrequency) : 0 ≤ l1Pop solution t p := complexVectorL1_nonneg _
theorem l1SecondPop_nonneg (p : SpatialFrequency) : 0 ≤ l1SecondPop solution t p :=
  mul_nonneg (by positivity) (l1Pop_nonneg solution t p)
theorem rootEnergy_nonneg (q : SpatialFrequency) : 0 ≤ rootEnergy (velocity := velocity) t q :=
  Real.sqrt_nonneg _
theorem rootSecond_nonneg (q : SpatialFrequency) : 0 ≤ rootSecond (velocity := velocity) t q :=
  mul_nonneg (by positivity) (rootEnergy_nonneg t q)

theorem rootEnergy_sq (q : SpatialFrequency) :
    rootEnergy (velocity := velocity) t q ^ 2 = modalEnergy (velocity := velocity) q t.1 := by
  unfold rootEnergy
  exact Real.sq_sqrt (modalEnergy_nonneg q t.1)

theorem rootSecond_sq (q : SpatialFrequency) :
    rootSecond (velocity := velocity) t q ^ 2 = momentPop (velocity := velocity) 4 t.1 q := by
  unfold rootSecond momentPop
  rw [mul_pow, rootEnergy_sq]
  ring

theorem summable_l1Pop : Summable (l1Pop solution t) :=
  summable_complexVectorL1_velocityMode solution t

include solution in
theorem modalEnergy_le_momentPop_one (q : SpatialFrequency) :
    modalEnergy (velocity := velocity) q t.1 ≤ momentPop (velocity := velocity) 1 t.1 q := by
  unfold momentPop
  rcases Nat.eq_zero_or_pos (frequencySup q) with h0 | hpos
  · -- the zero mode has zero energy
    have hq : q = 0 := by
      by_contra hne
      have := one_le_frequencySup_of_ne_zero hne
      omega
    subst hq
    rw [h0]
    have hcfv : complexFrequencyVector 0 = 0 := by
      funext j
      simp [complexFrequencyVector]
    have hE0 : modalEnergy (velocity := velocity) 0 t.1 = 0 := by
      rw [modalEnergy_eq_sum_norm_sq_curl solution t 0]
      simp [frequencyCurlMultiplier, complexCross, hcfv]
    rw [hE0]
    simp
  · have h1 : (1 : ℝ) ≤ ((frequencySup q : ℕ) : ℝ) := by exact_mod_cast hpos
    have := modalEnergy_nonneg (velocity := velocity) q t.1
    nlinarith

include solution in
theorem summable_rootEnergy_sq (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) :
    Summable fun q ↦ rootEnergy (velocity := velocity) t q ^ 2 := by
  simp_rw [rootEnergy_sq]
  exact Summable.of_nonneg_of_le (fun q ↦ modalEnergy_nonneg q t.1)
    (fun q ↦ modalEnergy_le_momentPop_one solution t q)
    (summable_momentPop (w := 1) (by norm_num) (by norm_num) t.1 hsum)

theorem summable_rootSecond_sq (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) :
    Summable fun q ↦ rootSecond (velocity := velocity) t q ^ 2 := by
  simp_rw [rootSecond_sq]
  exact summable_momentPop (w := 4) (by norm_num) (by norm_num) t.1 hsum

/-! ## The advection coefficient under the complete convolution bound -/

theorem norm_openActualAdvectionMode_le_conv (k : SpatialFrequency) (output : Fin 3)
    (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) :
    ‖openActualAdvectionMode solution t k output‖ ≤
      ∑' p, l1Pop solution t p * rootEnergy (velocity := velocity) t (k - p) := by
  rw [openActualAdvectionMode_eq_tsum_feedTerm]
  have hbound : ∀ p, ‖feedTerm solution t k p output‖ ≤
      l1Pop solution t p * rootEnergy (velocity := velocity) t (k - p) :=
    fun p ↦ norm_feedTerm_le_sqrt solution t k p output
  have hsumb : Summable fun p ↦ l1Pop solution t p * rootEnergy (velocity := velocity) t (k - p) :=
    summable_conv (l1Pop_nonneg solution t) (rootEnergy_nonneg t) (summable_l1Pop solution t)
      (summable_rootEnergy_sq solution t hsum) k
  have hsumn : Summable fun p ↦ ‖feedTerm solution t k p output‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hbound hsumb
  exact (norm_tsum_le_tsum_norm hsumn).trans (Summable.tsum_le_tsum hbound hsumn hsumb)

/-- The sup-norm square is shared between the legs. -/
theorem frequencySup_sq_le (k p : SpatialFrequency) :
    ((frequencySup k : ℕ) : ℝ) ^ 2 ≤
      2 * (((frequencySup p : ℕ) : ℝ) ^ 2 + ((frequencySup (k - p) : ℕ) : ℝ) ^ 2) := by
  have h := frequencySup_sub_le k p
  have hc : ((frequencySup k : ℕ) : ℝ) ≤ ((frequencySup (k - p) : ℕ) : ℝ) + ((frequencySup p : ℕ) : ℝ) := by
    exact_mod_cast h
  have h0 : (0 : ℝ) ≤ ((frequencySup k : ℕ) : ℝ) := by positivity
  nlinarith [sq_nonneg (((frequencySup p : ℕ) : ℝ) - ((frequencySup (k - p) : ℕ) : ℝ))]

/-- **The weighted convolution bound at one receiver.** -/
theorem sup_sq_mul_norm_le (k : SpatialFrequency) (output : Fin 3)
    (hsum : Summable (eleventhMoment (velocity := velocity) t.1))
    (hA : Summable (l1SecondPop solution t)) :
    ((frequencySup k : ℕ) : ℝ) ^ 2 * ‖openActualAdvectionMode solution t k output‖ ≤
      2 * ∑' p, l1SecondPop solution t p * rootEnergy (velocity := velocity) t (k - p) +
        2 * ∑' p, l1Pop solution t p * rootSecond (velocity := velocity) t (k - p) := by
  have h1 := mul_le_mul_of_nonneg_left (norm_openActualAdvectionMode_le_conv solution t k output hsum)
    (by positivity : (0 : ℝ) ≤ ((frequencySup k : ℕ) : ℝ) ^ 2)
  refine h1.trans ?_
  have hs1 : Summable fun p ↦ l1SecondPop solution t p * rootEnergy (velocity := velocity) t (k - p) :=
    summable_conv (l1SecondPop_nonneg solution t) (rootEnergy_nonneg t) hA (summable_rootEnergy_sq solution t hsum) k
  have hs2 : Summable fun p ↦ l1Pop solution t p * rootSecond (velocity := velocity) t (k - p) :=
    summable_conv (l1Pop_nonneg solution t) (rootSecond_nonneg t) (summable_l1Pop solution t)
      (summable_rootSecond_sq t hsum) k
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add (hs1.mul_left 2) (hs2.mul_left 2)]
  refine Summable.tsum_le_tsum (fun p ↦ ?_) ?_ ((hs1.mul_left 2).add (hs2.mul_left 2))
  · have hw := frequencySup_sq_le k p
    have hab : 0 ≤ l1Pop solution t p * rootEnergy (velocity := velocity) t (k - p) :=
      mul_nonneg (l1Pop_nonneg solution t p) (rootEnergy_nonneg t _)
    calc ((frequencySup k : ℕ) : ℝ) ^ 2 * (l1Pop solution t p * rootEnergy (velocity := velocity) t (k - p))
        ≤ 2 * (((frequencySup p : ℕ) : ℝ) ^ 2 + ((frequencySup (k - p) : ℕ) : ℝ) ^ 2) *
            (l1Pop solution t p * rootEnergy (velocity := velocity) t (k - p)) :=
          mul_le_mul_of_nonneg_right hw hab
      _ = 2 * (l1SecondPop solution t p * rootEnergy (velocity := velocity) t (k - p)) +
          2 * (l1Pop solution t p * rootSecond (velocity := velocity) t (k - p)) := by
          unfold l1SecondPop rootSecond
          ring
  · exact (summable_conv (l1Pop_nonneg solution t) (rootEnergy_nonneg t) (summable_l1Pop solution t)
      (summable_rootEnergy_sq solution t hsum) k).mul_left _

/-- **The weighted Young on the whole advection coefficient.** -/
theorem sum_pow_four_norm_adv_sq_le (F : Finset SpatialFrequency) (output : Fin 3)
    (hsum : Summable (eleventhMoment (velocity := velocity) t.1))
    (hA : Summable (l1SecondPop solution t)) :
    ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 * ‖openActualAdvectionMode solution t k output‖ ^ 2 ≤
      2 ^ 3 * (∑' p, l1SecondPop solution t p) ^ 2 * moment (velocity := velocity) 0 t.1 +
        2 ^ 3 * (∑' p, l1Pop solution t p) ^ 2 * moment (velocity := velocity) 4 t.1 := by
  set X : SpatialFrequency → ℝ := fun k ↦
    ∑' p, l1SecondPop solution t p * rootEnergy (velocity := velocity) t (k - p) with hX
  set Y : SpatialFrequency → ℝ := fun k ↦
    ∑' p, l1Pop solution t p * rootSecond (velocity := velocity) t (k - p) with hY
  have hX0 : ∀ k, 0 ≤ X k := fun k ↦ tsum_nonneg fun p ↦
    mul_nonneg (l1SecondPop_nonneg solution t p) (rootEnergy_nonneg t _)
  have hY0 : ∀ k, 0 ≤ Y k := fun k ↦ tsum_nonneg fun p ↦
    mul_nonneg (l1Pop_nonneg solution t p) (rootSecond_nonneg t _)
  have hterm : ∀ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 * ‖openActualAdvectionMode solution t k output‖ ^ 2 ≤
      2 ^ 3 * X k ^ 2 + 2 ^ 3 * Y k ^ 2 := by
    intro k _
    have h := sup_sq_mul_norm_le solution t k output hsum hA
    have h0 : 0 ≤ ((frequencySup k : ℕ) : ℝ) ^ 2 * ‖openActualAdvectionMode solution t k output‖ :=
      mul_nonneg (by positivity) (norm_nonneg _)
    have hsq := pow_le_pow_left₀ h0 h 2
    have hrw : (((frequencySup k : ℕ) : ℝ) ^ 2 * ‖openActualAdvectionMode solution t k output‖) ^ 2 =
        ((frequencySup k : ℕ) : ℝ) ^ 4 * ‖openActualAdvectionMode solution t k output‖ ^ 2 := by ring
    rw [hrw] at hsq
    refine hsq.trans ?_
    nlinarith [sq_nonneg (X k - Y k), hX0 k, hY0 k]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hYoungX := young_l1_l2 (l1SecondPop_nonneg solution t) (rootEnergy_nonneg t) hA
    (summable_rootEnergy_sq solution t hsum) F
  have hYoungY := young_l1_l2 (l1Pop_nonneg solution t) (rootSecond_nonneg t) (summable_l1Pop solution t)
    (summable_rootSecond_sq t hsum) F
  have hW0 : ∑' q, rootEnergy (velocity := velocity) t q ^ 2 = moment (velocity := velocity) 0 t.1 := by
    unfold moment momentPop
    simp_rw [rootEnergy_sq, pow_zero, one_mul]
  have hW4 : ∑' q, rootSecond (velocity := velocity) t q ^ 2 = moment (velocity := velocity) 4 t.1 := by
    unfold moment
    simp_rw [rootSecond_sq]
  rw [hW0] at hYoungX
  rw [hW4] at hYoungY
  calc 2 ^ 3 * ∑ k ∈ F, X k ^ 2 + 2 ^ 3 * ∑ k ∈ F, Y k ^ 2
      ≤ 2 ^ 3 * ((∑' p, l1SecondPop solution t p) ^ 2 * moment (velocity := velocity) 0 t.1) +
        2 ^ 3 * ((∑' p, l1Pop solution t p) ^ 2 * moment (velocity := velocity) 4 t.1) :=
        add_le_add (mul_le_mul_of_nonneg_left hYoungX (by norm_num))
          (mul_le_mul_of_nonneg_left hYoungY (by norm_num))
    _ = _ := by ring

section Audit

#print axioms norm_openActualAdvectionMode_le_conv
#print axioms sup_sq_mul_norm_le
#print axioms sum_pow_four_norm_adv_sq_le

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedYoung
