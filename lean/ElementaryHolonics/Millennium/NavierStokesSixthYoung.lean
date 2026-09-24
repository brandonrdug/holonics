import ElementaryHolonics.Millennium.NavierStokesMomentInterpolation

/-!
# The weight-six Young on the advection: the source of the modal equation, paid in moments

The curl symbol of the modal equation multiplies the advection coefficient by one power of the
frequency, so the source's fourth moment is the advection's sixth.  The cube weight shares
`|k|_∞³` between the legs, and the two Youngs place the weight where it is paid:

```text
Σ_{k∈F} |k|_∞⁶ ‖adv_k‖² ≤ 2⁵ · (3/(2π)²) · 52 · W₄² + 2⁵ · (Σ'_p ℓ¹(û(p)))² · W₆.
```

The first term is the weighted velocity leg, paid by `W₄` through Lagrange, against the mass of
`√E`, paid by `√(52 W₄)` through the lattice weight.  The second is the velocity mass against
the sixth moment.  No higher moment than six enters, and `W₄²` is paid by `W₂ W₆` through the
interpolation.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Finset

namespace Soma.Holonics.Millennium.NavierStokesSixthYoung

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
open Soma.Holonics.Millennium.NavierStokesWeightedTailEnergy
open Soma.Holonics.Millennium.NavierStokesIncoherentBandMass
open Soma.Holonics.Millennium.NavierStokesMomentSwap
open Soma.Holonics.Millennium.NavierStokesMomentGap
open Soma.Holonics.Millennium.NavierStokesYoungFeed
open Soma.Holonics.Millennium.NavierStokesYoungTsum
open Soma.Holonics.Millennium.NavierStokesWeightedYoung
open Soma.Holonics.Millennium.NavierStokesMomentInterpolation
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
  (t : Ioo 0 T)

/-! ## The populations and what pays them -/

/-- The cube-weighted velocity `ℓ¹` population. -/
def l1CubePop (p : SpatialFrequency) : ℝ := ((frequencySup p : ℕ) : ℝ) ^ 3 * l1Pop solution t p

/-- The cube-weighted root energy population. -/
def rootCube (q : SpatialFrequency) : ℝ := ((frequencySup q : ℕ) : ℝ) ^ 3 * rootEnergy (velocity := velocity) t q

theorem l1CubePop_nonneg (p : SpatialFrequency) : 0 ≤ l1CubePop solution t p :=
  mul_nonneg (by positivity) (l1Pop_nonneg solution t p)

theorem rootCube_nonneg (q : SpatialFrequency) : 0 ≤ rootCube (velocity := velocity) t q :=
  mul_nonneg (by positivity) (rootEnergy_nonneg t q)

/-- The squared cube-weighted velocity population is paid by the fourth moment, through Lagrange. -/
theorem l1CubePop_sq_le (p : SpatialFrequency) :
    l1CubePop solution t p ^ 2 ≤ 3 / (2 * Real.pi) ^ 2 * momentPop (velocity := velocity) 4 t.1 p := by
  unfold l1CubePop l1Pop momentPop
  have h := fourthMoment_tooth_le solution t p
  have hs : (0 : ℝ) ≤ ((frequencySup p : ℕ) : ℝ) ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left h hs
  calc (((frequencySup p : ℕ) : ℝ) ^ 3 * complexVectorL1 (openPeriodicVelocityFourierMode solution t p)) ^ 2
      = ((frequencySup p : ℕ) : ℝ) ^ 2 * (((frequencySup p : ℕ) : ℝ) ^ 4 *
          complexVectorL1 (openPeriodicVelocityFourierMode solution t p) ^ 2) := by ring
    _ ≤ ((frequencySup p : ℕ) : ℝ) ^ 2 * (3 / (2 * Real.pi) ^ 2 *
          (((frequencySup p : ℕ) : ℝ) ^ 2 * modalEnergy (velocity := velocity) p t.1)) := this
    _ = 3 / (2 * Real.pi) ^ 2 * (((frequencySup p : ℕ) : ℝ) ^ 4 * modalEnergy (velocity := velocity) p t.1) := by
        ring

theorem summable_l1CubePop_sq (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) :
    Summable fun p ↦ l1CubePop solution t p ^ 2 :=
  Summable.of_nonneg_of_le (fun p ↦ sq_nonneg _) (fun p ↦ l1CubePop_sq_le solution t p)
    ((summable_momentPop (w := 4) (by norm_num) (by norm_num) t.1 hsum).mul_left _)

theorem tsum_l1CubePop_sq_le (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) :
    ∑' p, l1CubePop solution t p ^ 2 ≤ 3 / (2 * Real.pi) ^ 2 * moment (velocity := velocity) 4 t.1 := by
  unfold moment
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun p ↦ l1CubePop_sq_le solution t p) (summable_l1CubePop_sq solution t hsum)
    ((summable_momentPop (w := 4) (by norm_num) (by norm_num) t.1 hsum).mul_left _)

theorem rootCube_sq (q : SpatialFrequency) :
    rootCube (velocity := velocity) t q ^ 2 = momentPop (velocity := velocity) 6 t.1 q := by
  unfold rootCube momentPop
  rw [mul_pow, rootEnergy_sq]
  ring

theorem summable_rootCube_sq (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) :
    Summable fun q ↦ rootCube (velocity := velocity) t q ^ 2 := by
  simp_rw [rootCube_sq]
  exact summable_momentPop (w := 6) (by norm_num) (by norm_num) t.1 hsum

include solution in
/-- The zero mode has zero root energy. -/
theorem rootEnergy_zero : rootEnergy (velocity := velocity) t 0 = 0 := by
  unfold rootEnergy
  have h := modalEnergy_le_momentPop_one solution t 0
  have h0 : momentPop (velocity := velocity) 1 t.1 0 = 0 := by
    unfold momentPop
    have : frequencySup (0 : SpatialFrequency) = 0 := by
      unfold frequencySup
      simp
    rw [this]
    simp
  rw [h0] at h
  have := modalEnergy_nonneg (velocity := velocity) 0 t.1
  rw [show modalEnergy (velocity := velocity) 0 t.1 = 0 by linarith]
  exact Real.sqrt_zero

include solution in
/-- **The mass of the root energies is paid by the fourth moment**, through the lattice weight. -/
theorem sum_rootEnergy_le (F : Finset SpatialFrequency) :
    ∑ q ∈ F, rootEnergy (velocity := velocity) t q ≤
      Real.sqrt 52 * Real.sqrt (∑ q ∈ F, momentPop (velocity := velocity) 4 t.1 q) := by
  have h0mem : ∑ q ∈ F, rootEnergy (velocity := velocity) t q =
      ∑ q ∈ F.erase 0, rootEnergy (velocity := velocity) t q := by
    by_cases h : (0 : SpatialFrequency) ∈ F
    · rw [← Finset.add_sum_erase F _ h, rootEnergy_zero solution t, zero_add]
    · rw [Finset.erase_eq_of_notMem h]
  rw [h0mem]
  set G := F.erase 0 with hG
  have hG1 : ∀ q ∈ G, 1 ≤ frequencySup q :=
    fun q hq ↦ one_le_frequencySup_of_ne_zero (Finset.ne_of_mem_erase hq)
  set a : SpatialFrequency → ℝ := fun q ↦ 1 / ((frequencySup q : ℕ) : ℝ) ^ 2 with ha
  set b : SpatialFrequency → ℝ := fun q ↦ ((frequencySup q : ℕ) : ℝ) ^ 2 * rootEnergy (velocity := velocity) t q
    with hb
  have hprod : ∀ q ∈ G, rootEnergy (velocity := velocity) t q = a q * b q := by
    intro q hq
    have hq0 : (0 : ℝ) < ((frequencySup q : ℕ) : ℝ) := by exact_mod_cast hG1 q hq
    simp only [ha, hb]
    field_simp
  rw [Finset.sum_congr rfl hprod]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq G a b
  have hA : ∑ q ∈ G, a q ^ 2 ≤ 52 := by
    have : ∀ q ∈ G, a q ^ 2 = 1 / ((frequencySup q : ℕ) : ℝ) ^ 4 := by
      intro q _
      simp only [ha]
      field_simp
    rw [Finset.sum_congr rfl this]
    exact sum_inv_pow_four_le G hG1
  have hB : ∑ q ∈ G, b q ^ 2 ≤ ∑ q ∈ F, momentPop (velocity := velocity) 4 t.1 q := by
    have heq : ∀ q ∈ G, b q ^ 2 = momentPop (velocity := velocity) 4 t.1 q := by
      intro q _
      simp only [hb, momentPop]
      rw [mul_pow, rootEnergy_sq]
      ring
    rw [Finset.sum_congr rfl heq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset 0 F)
      (fun q _ _ ↦ momentPop_nonneg 4 t.1 q)
  have hsum_nonneg : 0 ≤ ∑ q ∈ G, a q * b q :=
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (by positivity) (mul_nonneg (by positivity) (rootEnergy_nonneg t q))
  have hB0 : 0 ≤ ∑ q ∈ G, b q ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hsq : (∑ q ∈ G, a q * b q) ^ 2 ≤ 52 * ∑ q ∈ F, momentPop (velocity := velocity) 4 t.1 q :=
    hcs.trans (mul_le_mul hA hB hB0 (by norm_num))
  rw [← Real.sqrt_sq hsum_nonneg, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 52)]
  exact Real.sqrt_le_sqrt hsq

include solution in
theorem summable_rootEnergy (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) :
    Summable (rootEnergy (velocity := velocity) t) := by
  refine summable_of_sum_le (fun q ↦ rootEnergy_nonneg t q) (c := Real.sqrt 52 *
    Real.sqrt (moment (velocity := velocity) 4 t.1)) ?_
  intro F
  refine (sum_rootEnergy_le solution t F).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Real.sqrt_le_sqrt
  exact (summable_momentPop (w := 4) (by norm_num) (by norm_num) t.1 hsum).sum_le_tsum F
    (fun q _ ↦ momentPop_nonneg 4 t.1 q)

include solution in
theorem tsum_rootEnergy_le (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) :
    ∑' q, rootEnergy (velocity := velocity) t q ≤
      Real.sqrt 52 * Real.sqrt (moment (velocity := velocity) 4 t.1) := by
  refine Real.tsum_le_of_sum_le (fun q ↦ rootEnergy_nonneg t q) ?_
  intro F
  refine (sum_rootEnergy_le solution t F).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Real.sqrt_le_sqrt
  exact (summable_momentPop (w := 4) (by norm_num) (by norm_num) t.1 hsum).sum_le_tsum F
    (fun q _ ↦ momentPop_nonneg 4 t.1 q)

/-! ## The weight-six bound at one receiver -/

theorem sup_cube_mul_norm_le (k : SpatialFrequency) (output : Fin 3)
    (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) :
    ((frequencySup k : ℕ) : ℝ) ^ 3 * ‖openActualAdvectionMode solution t k output‖ ≤
      2 ^ 2 * ∑' p, l1CubePop solution t p * rootEnergy (velocity := velocity) t (k - p) +
        2 ^ 2 * ∑' p, l1Pop solution t p * rootCube (velocity := velocity) t (k - p) := by
  have h1 := mul_le_mul_of_nonneg_left (norm_openActualAdvectionMode_le_conv solution t k output hsum)
    (by positivity : (0 : ℝ) ≤ ((frequencySup k : ℕ) : ℝ) ^ 3)
  refine h1.trans ?_
  have hs1 : Summable fun p ↦ l1CubePop solution t p * rootEnergy (velocity := velocity) t (k - p) := by
    have hmaj : Summable fun p ↦ (l1CubePop solution t p ^ 2 + rootEnergy (velocity := velocity) t (k - p) ^ 2) / 2 :=
      ((summable_l1CubePop_sq solution t hsum).add
        (summable_shift_neg (summable_rootEnergy_sq solution t hsum) k)).div_const 2
    refine Summable.of_nonneg_of_le (fun p ↦ mul_nonneg (l1CubePop_nonneg solution t p) (rootEnergy_nonneg t _))
      (fun p ↦ ?_) hmaj
    nlinarith [sq_nonneg (l1CubePop solution t p - rootEnergy (velocity := velocity) t (k - p))]
  have hs2 : Summable fun p ↦ l1Pop solution t p * rootCube (velocity := velocity) t (k - p) :=
    summable_conv (l1Pop_nonneg solution t) (rootCube_nonneg t) (summable_l1Pop solution t)
      (summable_rootCube_sq t hsum) k
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left,
    ← Summable.tsum_add (hs1.mul_left _) (hs2.mul_left _)]
  refine Summable.tsum_le_tsum (fun p ↦ ?_) ?_ ((hs1.mul_left _).add (hs2.mul_left _))
  · have hw := frequencySup_cube_le k p
    have hab : 0 ≤ l1Pop solution t p * rootEnergy (velocity := velocity) t (k - p) :=
      mul_nonneg (l1Pop_nonneg solution t p) (rootEnergy_nonneg t _)
    calc ((frequencySup k : ℕ) : ℝ) ^ 3 * (l1Pop solution t p * rootEnergy (velocity := velocity) t (k - p))
        ≤ 2 ^ 2 * (((frequencySup p : ℕ) : ℝ) ^ 3 + ((frequencySup (k - p) : ℕ) : ℝ) ^ 3) *
            (l1Pop solution t p * rootEnergy (velocity := velocity) t (k - p)) :=
          mul_le_mul_of_nonneg_right hw hab
      _ = 2 ^ 2 * (l1CubePop solution t p * rootEnergy (velocity := velocity) t (k - p)) +
          2 ^ 2 * (l1Pop solution t p * rootCube (velocity := velocity) t (k - p)) := by
          unfold l1CubePop rootCube
          ring
  · exact (summable_conv (l1Pop_nonneg solution t) (rootEnergy_nonneg t) (summable_l1Pop solution t)
      (summable_rootEnergy_sq solution t hsum) k).mul_left _

/-- **The weight-six Young on the advection.** -/
theorem sum_pow_six_norm_adv_sq_le (F : Finset SpatialFrequency) (output : Fin 3)
    (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) :
    ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 6 * ‖openActualAdvectionMode solution t k output‖ ^ 2 ≤
      2 ^ 5 * (3 / (2 * Real.pi) ^ 2) * 52 * moment (velocity := velocity) 4 t.1 ^ 2 +
        2 ^ 5 * (∑' p, l1Pop solution t p) ^ 2 * moment (velocity := velocity) 6 t.1 := by
  set X : SpatialFrequency → ℝ := fun k ↦
    ∑' p, l1CubePop solution t p * rootEnergy (velocity := velocity) t (k - p) with hX
  set Y : SpatialFrequency → ℝ := fun k ↦
    ∑' p, l1Pop solution t p * rootCube (velocity := velocity) t (k - p) with hY
  have hX0 : ∀ k, 0 ≤ X k := fun k ↦ tsum_nonneg fun p ↦
    mul_nonneg (l1CubePop_nonneg solution t p) (rootEnergy_nonneg t _)
  have hY0 : ∀ k, 0 ≤ Y k := fun k ↦ tsum_nonneg fun p ↦
    mul_nonneg (l1Pop_nonneg solution t p) (rootCube_nonneg t _)
  have hterm : ∀ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 6 * ‖openActualAdvectionMode solution t k output‖ ^ 2 ≤
      2 ^ 5 * X k ^ 2 + 2 ^ 5 * Y k ^ 2 := by
    intro k _
    have h := sup_cube_mul_norm_le solution t k output hsum
    have h0 : 0 ≤ ((frequencySup k : ℕ) : ℝ) ^ 3 * ‖openActualAdvectionMode solution t k output‖ :=
      mul_nonneg (by positivity) (norm_nonneg _)
    have hsq := pow_le_pow_left₀ h0 h 2
    have hrw : (((frequencySup k : ℕ) : ℝ) ^ 3 * ‖openActualAdvectionMode solution t k output‖) ^ 2 =
        ((frequencySup k : ℕ) : ℝ) ^ 6 * ‖openActualAdvectionMode solution t k output‖ ^ 2 := by ring
    rw [hrw] at hsq
    refine hsq.trans ?_
    nlinarith [sq_nonneg (X k - Y k), hX0 k, hY0 k]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hYoungX := young_l2_l1 (l1CubePop_nonneg solution t) (rootEnergy_nonneg t)
    (summable_l1CubePop_sq solution t hsum) (summable_rootEnergy solution t hsum) F
  have hYoungY := young_l1_l2 (l1Pop_nonneg solution t) (rootCube_nonneg t) (summable_l1Pop solution t)
    (summable_rootCube_sq t hsum) F
  have hW6 : ∑' q, rootCube (velocity := velocity) t q ^ 2 = moment (velocity := velocity) 6 t.1 := by
    unfold moment
    simp_rw [rootCube_sq]
  rw [hW6] at hYoungY
  have hXbound : (∑' p, l1CubePop solution t p ^ 2) * (∑' q, rootEnergy (velocity := velocity) t q) ^ 2 ≤
      (3 / (2 * Real.pi) ^ 2 * moment (velocity := velocity) 4 t.1) *
        (52 * moment (velocity := velocity) 4 t.1) := by
    have hr := tsum_rootEnergy_le solution t hsum
    have hr0 : 0 ≤ ∑' q, rootEnergy (velocity := velocity) t q := tsum_nonneg fun q ↦ rootEnergy_nonneg t q
    have hr2 : (∑' q, rootEnergy (velocity := velocity) t q) ^ 2 ≤ 52 * moment (velocity := velocity) 4 t.1 := by
      have := pow_le_pow_left₀ hr0 hr 2
      rwa [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (moment_nonneg 4 t.1)] at this
    exact mul_le_mul (tsum_l1CubePop_sq_le solution t hsum) hr2 (sq_nonneg _)
      (mul_nonneg (by positivity) (moment_nonneg 4 t.1))
  calc 2 ^ 5 * ∑ k ∈ F, X k ^ 2 + 2 ^ 5 * ∑ k ∈ F, Y k ^ 2
      ≤ 2 ^ 5 * ((3 / (2 * Real.pi) ^ 2 * moment (velocity := velocity) 4 t.1) *
            (52 * moment (velocity := velocity) 4 t.1)) +
          2 ^ 5 * ((∑' p, l1Pop solution t p) ^ 2 * moment (velocity := velocity) 6 t.1) :=
        add_le_add (mul_le_mul_of_nonneg_left (hYoungX.trans hXbound) (by norm_num))
          (mul_le_mul_of_nonneg_left hYoungY (by norm_num))
    _ = _ := by ring

section Audit

#print axioms sum_rootEnergy_le
#print axioms sup_cube_mul_norm_le
#print axioms sum_pow_six_norm_adv_sq_le

end Audit

end Soma.Holonics.Millennium.NavierStokesSixthYoung
