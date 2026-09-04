import ElementaryHolonics.Millennium.NavierStokesWeightedYoung

/-!
# Moment interpolation, the second Young, and the cube weight

Three exact facts that let the fourth-moment drive close without a higher moment.

* **Interpolation.**  `W₄² ≤ W₂ · W₆`: Cauchy--Schwarz between the second and sixth moments, so
  a term quadratic in `W₄` is paid by `W₂` against the dissipating moment.
* **The second Young.**  `ℓ² * ℓ¹ → ℓ²` on the frequency lattice: the weight can be placed on the
  square-summable leg while the other leg carries only its mass.
* **The cube weight.**  `|k|_∞³ ≤ 2² (|p|_∞³ + |k − p|_∞³)`: the weight of the curl symbol times the
  receiver's fourth moment is shared between the legs with the doubling `2²`.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Finset

namespace Soma.Holonics.Millennium.NavierStokesMomentInterpolation

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
open Soma.Holonics.Millennium.NavierStokesMomentSwap
open Soma.Holonics.Millennium.NavierStokesMomentGap
open Soma.Holonics.Millennium.NavierStokesYoungFeed
open Soma.Holonics.Millennium.NavierStokesYoungTsum

/-! ## Interpolation between moments -/

variable {velocity : VelocityField}

/-- **Interpolation on a finite family.**  `(Σ |k|⁴ E)² ≤ (Σ |k|² E)(Σ |k|⁶ E)`. -/
theorem sum_momentPop_four_sq_le (τ : ℝ) (F : Finset SpatialFrequency) :
    (∑ k ∈ F, momentPop (velocity := velocity) 4 τ k) ^ 2 ≤
      (∑ k ∈ F, momentPop (velocity := velocity) 2 τ k) *
        ∑ k ∈ F, momentPop (velocity := velocity) 6 τ k := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq F
    (fun k ↦ ((frequencySup k : ℕ) : ℝ) * Real.sqrt (modalEnergy (velocity := velocity) k τ))
    (fun k ↦ ((frequencySup k : ℕ) : ℝ) ^ 3 * Real.sqrt (modalEnergy (velocity := velocity) k τ))
  have h1 : ∀ k ∈ F, ((frequencySup k : ℕ) : ℝ) * Real.sqrt (modalEnergy (velocity := velocity) k τ) *
      (((frequencySup k : ℕ) : ℝ) ^ 3 * Real.sqrt (modalEnergy (velocity := velocity) k τ)) =
      momentPop (velocity := velocity) 4 τ k := by
    intro k _
    unfold momentPop
    have := Real.mul_self_sqrt (modalEnergy_nonneg (velocity := velocity) k τ)
    linear_combination ((frequencySup k : ℕ) : ℝ) ^ 4 * this
  have h2 : ∀ k ∈ F, (((frequencySup k : ℕ) : ℝ) * Real.sqrt (modalEnergy (velocity := velocity) k τ)) ^ 2 =
      momentPop (velocity := velocity) 2 τ k := by
    intro k _
    unfold momentPop
    rw [mul_pow, Real.sq_sqrt (modalEnergy_nonneg k τ)]
  have h3 : ∀ k ∈ F, (((frequencySup k : ℕ) : ℝ) ^ 3 * Real.sqrt (modalEnergy (velocity := velocity) k τ)) ^ 2 =
      momentPop (velocity := velocity) 6 τ k := by
    intro k _
    unfold momentPop
    rw [mul_pow, Real.sq_sqrt (modalEnergy_nonneg k τ)]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_congr rfl h3] at hcs
  exact hcs

/-- **Interpolation on the complete populations.**  `W₄² ≤ W₂ · W₆`. -/
theorem moment_four_sq_le (τ : ℝ) (hsum : Summable (eleventhMoment (velocity := velocity) τ)) :
    moment (velocity := velocity) 4 τ ^ 2 ≤
      moment (velocity := velocity) 2 τ * moment (velocity := velocity) 6 τ := by
  have hW2 := moment_nonneg (velocity := velocity) 2 τ
  have hW6 := moment_nonneg (velocity := velocity) 6 τ
  have hW4 := moment_nonneg (velocity := velocity) 4 τ
  have hle : moment (velocity := velocity) 4 τ ≤
      Real.sqrt (moment (velocity := velocity) 2 τ * moment (velocity := velocity) 6 τ) := by
    unfold moment
    refine Real.tsum_le_of_sum_le (fun k ↦ momentPop_nonneg 4 τ k) ?_
    intro F
    have hF0 : 0 ≤ ∑ k ∈ F, momentPop (velocity := velocity) 4 τ k :=
      Finset.sum_nonneg fun k _ ↦ momentPop_nonneg 4 τ k
    rw [← Real.sqrt_sq hF0]
    apply Real.sqrt_le_sqrt
    refine (sum_momentPop_four_sq_le τ F).trans ?_
    exact mul_le_mul ((summable_momentPop (w := 2) (by norm_num) (by norm_num) τ hsum).sum_le_tsum F
        (fun k _ ↦ momentPop_nonneg 2 τ k))
      ((summable_momentPop (w := 6) (by norm_num) (by norm_num) τ hsum).sum_le_tsum F
        (fun k _ ↦ momentPop_nonneg 6 τ k))
      (Finset.sum_nonneg fun k _ ↦ momentPop_nonneg 6 τ k) hW2
  have := pow_le_pow_left₀ hW4 hle 2
  rwa [Real.sq_sqrt (mul_nonneg hW2 hW6)] at this

/-! ## The second Young: `ℓ² * ℓ¹ → ℓ²` -/

theorem le_tsum_of_nonneg {b : SpatialFrequency → ℝ} (hb0 : ∀ q, 0 ≤ b q) (hb : Summable b)
    (q : SpatialFrequency) : b q ≤ ∑' q, b q :=
  hb.le_tsum q fun _ _ ↦ hb0 _

theorem summable_sq_mul_shift {A b : SpatialFrequency → ℝ} (hb0 : ∀ q, 0 ≤ b q)
    (hA2 : Summable fun p ↦ A p ^ 2) (hb : Summable b) (k : SpatialFrequency) :
    Summable fun p ↦ A p ^ 2 * b (k - p) := by
  refine Summable.of_nonneg_of_le (fun p ↦ mul_nonneg (sq_nonneg _) (hb0 _)) (fun p ↦ ?_)
    (hA2.mul_right (∑' q, b q))
  exact mul_le_mul_of_nonneg_left (le_tsum_of_nonneg hb0 hb (k - p)) (sq_nonneg _)

theorem summable_shift {b : SpatialFrequency → ℝ} (hb : Summable b) (p : SpatialFrequency) :
    Summable fun k ↦ b (k - p) :=
  hb.comp_injective (fun x y (h : x - p = y - p) ↦ by simpa using h)

theorem summable_shift_neg {b : SpatialFrequency → ℝ} (hb : Summable b) (k : SpatialFrequency) :
    Summable fun p ↦ b (k - p) :=
  hb.comp_injective (fun x y (h : k - x = k - y) ↦ by simpa using h)

/-- **Cauchy--Schwarz weighted by the mass leg.** -/
theorem conv_sq_le' {A b : SpatialFrequency → ℝ} (hA0 : ∀ p, 0 ≤ A p) (hb0 : ∀ q, 0 ≤ b q)
    (hA2 : Summable fun p ↦ A p ^ 2) (hb : Summable b) (k : SpatialFrequency) :
    (∑' p, A p * b (k - p)) ^ 2 ≤ (∑' q, b q) * ∑' p, A p ^ 2 * b (k - p) := by
  have hB0 : 0 ≤ ∑' q, b q := tsum_nonneg hb0
  have hS0 : 0 ≤ ∑' p, A p ^ 2 * b (k - p) :=
    tsum_nonneg fun p ↦ mul_nonneg (sq_nonneg _) (hb0 _)
  have hsumAb : Summable fun p ↦ A p * b (k - p) := by
    have hbound : ∀ p, A p * b (k - p) ≤ (A p ^ 2 * b (k - p) + b (k - p)) / 2 := by
      intro p
      have hbp := hb0 (k - p)
      nlinarith [mul_nonneg (sq_nonneg (A p - 1)) hbp]
    have hmaj : Summable fun p ↦ (A p ^ 2 * b (k - p) + b (k - p)) / 2 :=
      ((summable_sq_mul_shift hb0 hA2 hb k).add (summable_shift_neg hb k)).div_const 2
    exact Summable.of_nonneg_of_le (fun p ↦ mul_nonneg (hA0 p) (hb0 _)) hbound hmaj
  have hconv0 : 0 ≤ ∑' p, A p * b (k - p) := tsum_nonneg fun p ↦ mul_nonneg (hA0 p) (hb0 _)
  have hle : ∑' p, A p * b (k - p) ≤ Real.sqrt ((∑' q, b q) * ∑' p, A p ^ 2 * b (k - p)) := by
    refine Real.tsum_le_of_sum_le (fun p ↦ mul_nonneg (hA0 p) (hb0 _)) ?_
    intro G
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq G (fun p ↦ Real.sqrt (b (k - p)))
      (fun p ↦ A p * Real.sqrt (b (k - p)))
    have hrw : ∀ p ∈ G, Real.sqrt (b (k - p)) * (A p * Real.sqrt (b (k - p))) = A p * b (k - p) := by
      intro p _
      have := Real.mul_self_sqrt (hb0 (k - p))
      linear_combination A p * this
    have h1 : ∑ p ∈ G, Real.sqrt (b (k - p)) ^ 2 = ∑ p ∈ G, b (k - p) :=
      Finset.sum_congr rfl fun p _ ↦ Real.sq_sqrt (hb0 _)
    have h2 : ∑ p ∈ G, (A p * Real.sqrt (b (k - p))) ^ 2 = ∑ p ∈ G, A p ^ 2 * b (k - p) :=
      Finset.sum_congr rfl fun p _ ↦ by rw [mul_pow, Real.sq_sqrt (hb0 _)]
    rw [Finset.sum_congr rfl hrw, h1, h2] at hcs
    have hG1 : ∑ p ∈ G, b (k - p) ≤ ∑' q, b q := by
      have hinj : Set.InjOn (fun p : SpatialFrequency ↦ k - p) G := fun x _ y _ h ↦ by simpa using h
      calc ∑ p ∈ G, b (k - p) = ∑ q ∈ G.image (fun p ↦ k - p), b q :=
            (Finset.sum_image (f := b) hinj).symm
        _ ≤ ∑' q, b q := hb.sum_le_tsum _ fun q _ ↦ hb0 q
    have hG2 : ∑ p ∈ G, A p ^ 2 * b (k - p) ≤ ∑' p, A p ^ 2 * b (k - p) :=
      (summable_sq_mul_shift hb0 hA2 hb k).sum_le_tsum G fun p _ ↦ mul_nonneg (sq_nonneg _) (hb0 _)
    have hG0 : 0 ≤ ∑ p ∈ G, A p * b (k - p) :=
      Finset.sum_nonneg fun p _ ↦ mul_nonneg (hA0 p) (hb0 _)
    have hB0' : 0 ≤ ∑ p ∈ G, A p ^ 2 * b (k - p) :=
      Finset.sum_nonneg fun p _ ↦ mul_nonneg (sq_nonneg _) (hb0 _)
    rw [← Real.sqrt_sq hG0]
    apply Real.sqrt_le_sqrt
    calc (∑ p ∈ G, A p * b (k - p)) ^ 2 ≤ (∑ p ∈ G, b (k - p)) * ∑ p ∈ G, A p ^ 2 * b (k - p) := hcs
      _ ≤ (∑' q, b q) * ∑' p, A p ^ 2 * b (k - p) := mul_le_mul hG1 hG2 hB0' hB0
  have := pow_le_pow_left₀ hconv0 hle 2
  rwa [Real.sq_sqrt (mul_nonneg hB0 hS0)] at this

/-- **Young `ℓ² * ℓ¹ → ℓ²` on any finite family of receivers.** -/
theorem young_l2_l1 {A b : SpatialFrequency → ℝ} (hA0 : ∀ p, 0 ≤ A p) (hb0 : ∀ q, 0 ≤ b q)
    (hA2 : Summable fun p ↦ A p ^ 2) (hb : Summable b) (F : Finset SpatialFrequency) :
    ∑ k ∈ F, (∑' p, A p * b (k - p)) ^ 2 ≤ (∑' p, A p ^ 2) * (∑' q, b q) ^ 2 := by
  have hB0 : 0 ≤ ∑' q, b q := tsum_nonneg hb0
  calc ∑ k ∈ F, (∑' p, A p * b (k - p)) ^ 2
      ≤ ∑ k ∈ F, (∑' q, b q) * ∑' p, A p ^ 2 * b (k - p) :=
        Finset.sum_le_sum fun k _ ↦ conv_sq_le' hA0 hb0 hA2 hb k
    _ = (∑' q, b q) * ∑' p, A p ^ 2 * ∑ k ∈ F, b (k - p) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [← Summable.tsum_finsetSum (fun k _ ↦ summable_sq_mul_shift hb0 hA2 hb k)]
        apply tsum_congr
        intro p
        rw [Finset.mul_sum]
    _ ≤ (∑' q, b q) * ∑' p, A p ^ 2 * ∑' q, b q := by
        apply mul_le_mul_of_nonneg_left _ hB0
        have hsum1 : Summable fun p ↦ A p ^ 2 * ∑ k ∈ F, b (k - p) :=
          summable_sum (fun k _ ↦ summable_sq_mul_shift hb0 hA2 hb k) |>.congr
            (fun p ↦ by rw [Finset.mul_sum])
        refine Summable.tsum_le_tsum (fun p ↦ ?_) hsum1 (hA2.mul_right _)
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        have hinj : Set.InjOn (fun k : SpatialFrequency ↦ k - p) F := fun x _ y _ h ↦ by simpa using h
        calc ∑ k ∈ F, b (k - p) = ∑ q ∈ F.image (fun k ↦ k - p), b q :=
              (Finset.sum_image (f := b) hinj).symm
          _ ≤ ∑' q, b q := hb.sum_le_tsum _ fun q _ ↦ hb0 q
    _ = (∑' p, A p ^ 2) * (∑' q, b q) ^ 2 := by
        rw [tsum_mul_right]
        ring

/-! ## The cube weight -/

theorem frequencySup_cube_le (k p : SpatialFrequency) :
    ((frequencySup k : ℕ) : ℝ) ^ 3 ≤
      2 ^ 2 * (((frequencySup p : ℕ) : ℝ) ^ 3 + ((frequencySup (k - p) : ℕ) : ℝ) ^ 3) := by
  have h := frequencySup_sub_le k p
  have hc : ((frequencySup k : ℕ) : ℝ) ≤ ((frequencySup (k - p) : ℕ) : ℝ) + ((frequencySup p : ℕ) : ℝ) := by
    exact_mod_cast h
  set x : ℝ := ((frequencySup p : ℕ) : ℝ) with hx
  set y : ℝ := ((frequencySup (k - p) : ℕ) : ℝ) with hy
  have hx0 : 0 ≤ x := by positivity
  have hy0 : 0 ≤ y := by positivity
  have hk0 : (0 : ℝ) ≤ ((frequencySup k : ℕ) : ℝ) := by positivity
  have hsum : ((frequencySup k : ℕ) : ℝ) ^ 3 ≤ (y + x) ^ 3 := pow_le_pow_left₀ hk0 hc 3
  have hcube : (y + x) ^ 3 ≤ 4 * (x ^ 3 + y ^ 3) := by
    nlinarith [mul_nonneg hx0 hy0, mul_nonneg (mul_nonneg hx0 hy0) (sq_nonneg (x - y)),
      sq_nonneg (x - y), mul_nonneg hx0 (sq_nonneg (x - y)), mul_nonneg hy0 (sq_nonneg (x - y))]
  linarith

section Audit

#print axioms moment_four_sq_le
#print axioms young_l2_l1
#print axioms frequencySup_cube_le

end Audit

end Soma.Holonics.Millennium.NavierStokesMomentInterpolation
