import ElementaryHolonics.Millennium.NavierStokesMomentGap

/-!
# Young on the feed: the weighted feed energy is paid without a count of receivers

The coherent swap paid each receiver the whole tail mass beyond its half radius and then counted
the receivers.  Young's inequality `ℓ¹ * ℓ² → ℓ²` on the feed convolution pays all receivers at
once.  For a band of radius `N` and receivers outside the cube of radius `2N`,

```text
Σ_k |k|_∞^w ‖bandFeed_k‖² ≤ 2^w · bandMass(N)² · Σ'_{q ∉ cube N} |q|_∞^w E_q,
```

for every weight `w`.  Two facts carry it: each feed term is at most `ℓ¹(û(p)) · √E_{k−p}` by
Lagrange, and `|k|_∞ ≤ 2 |k − p|_∞` when `p` is in the band and `k` beyond twice it, so the
receiver's weight is paid by the transported mode's weight with the factor `2^w`.  Cauchy--Schwarz
on the band and a reindexing `q = k − p` finish it.  No count of receivers, no lattice weight.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Finset

namespace Soma.Holonics.Millennium.NavierStokesYoungFeed

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
open Soma.Holonics.Millennium.NavierStokesModeLagrange
open Soma.Holonics.Millennium.NavierStokesHalfRadiusReach
open Soma.Holonics.Millennium.NavierStokesShellStepCost
open Soma.Holonics.Millennium.NavierStokesWeightedTailEnergy
open Soma.Holonics.Millennium.NavierStokesIncoherentBandMass
open Soma.Holonics.Millennium.NavierStokesMomentSwap
open Soma.Holonics.Millennium.NavierStokesMomentGap
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
  (t : Ioo 0 T)

/-! ## The sup-norm triangle inequality and the doubling -/

theorem frequencySup_sub_le (k p : SpatialFrequency) :
    frequencySup k ≤ frequencySup (k - p) + frequencySup p := by
  unfold frequencySup
  rw [Finset.sup_le_iff]
  intro c _
  have h1 : (k c - p c).natAbs ≤ Finset.univ.sup fun c ↦ (k c - p c).natAbs :=
    Finset.le_sup (f := fun c ↦ (k c - p c).natAbs) (Finset.mem_univ c)
  have h2 : (p c).natAbs ≤ Finset.univ.sup fun c ↦ (p c).natAbs :=
    Finset.le_sup (f := fun c ↦ (p c).natAbs) (Finset.mem_univ c)
  have h3 : (k c).natAbs ≤ (k c - p c).natAbs + (p c).natAbs := by
    have := Int.natAbs_add_le (k c - p c) (p c)
    rwa [sub_add_cancel] at this
  have hgoal : (k c).natAbs ≤ (Finset.univ.sup fun c ↦ (k c - p c).natAbs) +
      (Finset.univ.sup fun c ↦ (p c).natAbs) := by omega
  simpa [Pi.sub_apply] using hgoal

/-- Beyond twice the band, the receiver's sup-norm is at most twice the transported mode's. -/
theorem frequencySup_le_two_mul {radius : ℕ} {k p : SpatialFrequency}
    (hk : k ∉ frequencyCube (2 * radius)) (hp : p ∈ frequencyCube radius) :
    frequencySup k ≤ 2 * frequencySup (k - p) := by
  rw [mem_frequencyCube_iff_frequencySup_le] at hk hp
  have := frequencySup_sub_le k p
  omega

theorem transported_not_mem {radius : ℕ} {k p : SpatialFrequency}
    (hk : k ∉ frequencyCube (2 * radius)) (hp : p ∈ frequencyCube radius) :
    k - p ∉ frequencyCube radius := by
  rw [mem_frequencyCube_iff_frequencySup_le] at hk hp ⊢
  have := frequencySup_sub_le k p
  omega

/-! ## Each feed term is paid by the band tooth and the transported modal energy -/

/-- The Frobenius norm squared of the Jacobian mode is the modal energy. -/
theorem sum_norm_sq_jacobianMode_eq (q : SpatialFrequency) :
    ∑ i : Fin 3, ∑ j : Fin 3, ‖openPeriodicJacobianFourierMode solution t q i j‖ ^ 2 =
      modalEnergy (velocity := velocity) q t.1 := by
  rw [openPeriodicJacobianFourierMode_eq_fourierJacobianMode, sum_norm_sq_fourierJacobianMode,
    modalEnergy_eq_sum_norm_sq_curl solution t q,
    sum_norm_sq_frequencyCurlMultiplier q _ (openPeriodicVelocityFourierMode_divergenceFree solution t q)]

theorem norm_jacobianMode_le_sqrt_modalEnergy (q : SpatialFrequency) (i j : Fin 3) :
    ‖openPeriodicJacobianFourierMode solution t q i j‖ ≤
      Real.sqrt (modalEnergy (velocity := velocity) q t.1) := by
  rw [← Real.sqrt_sq (norm_nonneg _)]
  exact Real.sqrt_le_sqrt (norm_jacobianMode_sq_le_modalEnergy solution t q i j)

theorem norm_feedTerm_le_sqrt (k p : SpatialFrequency) (output : Fin 3) :
    ‖feedTerm solution t k p output‖ ≤
      complexVectorL1 (openPeriodicVelocityFourierMode solution t p) *
        Real.sqrt (modalEnergy (velocity := velocity) (k - p) t.1) := by
  unfold feedTerm
  refine (norm_sum_le _ _).trans ?_
  rw [complexVectorL1_eq_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro c _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_jacobianMode_le_sqrt_modalEnergy solution t (k - p) output c)
    (norm_nonneg _)

/-! ## Young on the band feed -/

/-- The `w`-th moment tail population beyond the cube of radius `N`. -/
def tailPop (velocity : VelocityField) (t : Ioo 0 T) (w radius : ℕ) (q : SpatialFrequency) : ℝ :=
  if q ∈ frequencyCube radius then 0 else momentPop (velocity := velocity) w t.1 q

theorem tailPop_nonneg (w radius : ℕ) (q : SpatialFrequency) :
    0 ≤ tailPop velocity t w radius q := by
  unfold tailPop; split_ifs
  · exact le_rfl
  · exact momentPop_nonneg w t.1 q

theorem tailPop_le (w radius : ℕ) (q : SpatialFrequency) :
    tailPop velocity t w radius q ≤ momentPop (velocity := velocity) w t.1 q := by
  unfold tailPop; split_ifs
  · exact momentPop_nonneg w t.1 q
  · exact le_rfl

theorem summable_tailPop {w : ℕ} (hw : 1 ≤ w) (hw11 : w ≤ 11) (radius : ℕ)
    (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) :
    Summable (tailPop velocity t w radius) :=
  Summable.of_nonneg_of_le (tailPop_nonneg t w radius) (tailPop_le t w radius)
    (summable_momentPop hw hw11 t.1 hsum)

/-- The transported weighted energies of one band tooth, over a finite family of receivers beyond
twice the band, are paid by the `w`-th moment tail. -/
theorem sum_transported_le {w radius : ℕ} (hw : 1 ≤ w) (hw11 : w ≤ 11)
    (hsum : Summable (eleventhMoment (velocity := velocity) t.1))
    (F : Finset SpatialFrequency) (hF : ∀ k ∈ F, k ∉ frequencyCube (2 * radius))
    {p : SpatialFrequency} (hp : p ∈ frequencyCube radius) :
    ∑ k ∈ F, ((frequencySup (k - p) : ℕ) : ℝ) ^ w * modalEnergy (velocity := velocity) (k - p) t.1 ≤
      ∑' q, tailPop velocity t w radius q := by
  have hinj : Set.InjOn (fun k : SpatialFrequency ↦ k - p) F := fun a _ b _ h ↦ by
    simpa using h
  have heq : ∑ k ∈ F, ((frequencySup (k - p) : ℕ) : ℝ) ^ w *
      modalEnergy (velocity := velocity) (k - p) t.1 =
      ∑ q ∈ F.image (fun k ↦ k - p), tailPop velocity t w radius q := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro k hk
    unfold tailPop
    rw [if_neg (transported_not_mem (hF k hk) hp)]
    rfl
  rw [heq]
  exact (summable_tailPop t hw hw11 radius hsum).sum_le_tsum _ (fun q _ ↦ tailPop_nonneg t w radius q)

/-- **Young on the band feed.**  The `w`-th moment of the squared band feed over any finite family
of receivers beyond twice the band is paid by `2^w` times the squared band mass times the
`w`-th moment tail. -/
theorem sum_pow_bandFeed_sq_le {w radius : ℕ} (hw : 1 ≤ w) (hw11 : w ≤ 11)
    (hsum : Summable (eleventhMoment (velocity := velocity) t.1))
    (F : Finset SpatialFrequency) (hF : ∀ k ∈ F, k ∉ frequencyCube (2 * radius)) (output : Fin 3) :
    ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ w * ‖bandFeed solution t radius k output‖ ^ 2 ≤
      2 ^ w * bandMass solution t radius ^ 2 * ∑' q, tailPop velocity t w radius q := by
  set a : SpatialFrequency → ℝ := fun p ↦ complexVectorL1 (openPeriodicVelocityFourierMode solution t p)
    with ha
  have ha0 : ∀ p, 0 ≤ a p := fun p ↦ complexVectorL1_nonneg _
  set B := frequencyCube radius with hB
  -- Cauchy--Schwarz on the band for each receiver
  have hcs : ∀ k ∈ F, ‖bandFeed solution t radius k output‖ ^ 2 ≤
      bandMass solution t radius * ∑ p ∈ B, a p * modalEnergy (velocity := velocity) (k - p) t.1 := by
    intro k _
    have h1 : ‖bandFeed solution t radius k output‖ ≤
        ∑ p ∈ B, a p * Real.sqrt (modalEnergy (velocity := velocity) (k - p) t.1) := by
      unfold bandFeed
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ ↦ ?_)
      exact norm_feedTerm_le_sqrt solution t k p output
    have h2 : (∑ p ∈ B, a p * Real.sqrt (modalEnergy (velocity := velocity) (k - p) t.1)) ^ 2 ≤
        (∑ p ∈ B, Real.sqrt (a p) ^ 2) *
          ∑ p ∈ B, (Real.sqrt (a p) * Real.sqrt (modalEnergy (velocity := velocity) (k - p) t.1)) ^ 2 := by
      have := Finset.sum_mul_sq_le_sq_mul_sq B (fun p ↦ Real.sqrt (a p))
        (fun p ↦ Real.sqrt (a p) * Real.sqrt (modalEnergy (velocity := velocity) (k - p) t.1))
      have hrw : ∀ p ∈ B, Real.sqrt (a p) * (Real.sqrt (a p) *
          Real.sqrt (modalEnergy (velocity := velocity) (k - p) t.1)) =
          a p * Real.sqrt (modalEnergy (velocity := velocity) (k - p) t.1) := by
        intro p _
        rw [← mul_assoc, Real.mul_self_sqrt (ha0 p)]
      rw [Finset.sum_congr rfl hrw] at this
      exact this
    have h3 : ∑ p ∈ B, Real.sqrt (a p) ^ 2 = bandMass solution t radius := by
      unfold bandMass
      exact Finset.sum_congr rfl fun p _ ↦ Real.sq_sqrt (ha0 p)
    have h4 : ∑ p ∈ B, (Real.sqrt (a p) * Real.sqrt (modalEnergy (velocity := velocity) (k - p) t.1)) ^ 2 =
        ∑ p ∈ B, a p * modalEnergy (velocity := velocity) (k - p) t.1 := by
      apply Finset.sum_congr rfl
      intro p _
      rw [mul_pow, Real.sq_sqrt (ha0 p), Real.sq_sqrt (modalEnergy_nonneg _ _)]
    have h0 : 0 ≤ ∑ p ∈ B, a p * Real.sqrt (modalEnergy (velocity := velocity) (k - p) t.1) :=
      Finset.sum_nonneg fun p _ ↦ mul_nonneg (ha0 p) (Real.sqrt_nonneg _)
    calc ‖bandFeed solution t radius k output‖ ^ 2
        ≤ (∑ p ∈ B, a p * Real.sqrt (modalEnergy (velocity := velocity) (k - p) t.1)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
      _ = bandMass solution t radius * ∑ p ∈ B, a p * modalEnergy (velocity := velocity) (k - p) t.1 := by
          rw [h3, h4]
  -- the receiver's weight is paid by the transported mode's weight
  have hweight : ∀ k ∈ F, ∀ p ∈ B, ((frequencySup k : ℕ) : ℝ) ^ w ≤
      2 ^ w * ((frequencySup (k - p) : ℕ) : ℝ) ^ w := by
    intro k hk p hp
    have := frequencySup_le_two_mul (hF k hk) hp
    have hcast : ((frequencySup k : ℕ) : ℝ) ≤ 2 * ((frequencySup (k - p) : ℕ) : ℝ) := by
      exact_mod_cast this
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hcast w
  have hM0 : 0 ≤ bandMass solution t radius := Finset.sum_nonneg fun p _ ↦ ha0 p
  calc ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ w * ‖bandFeed solution t radius k output‖ ^ 2
      ≤ ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ w *
          (bandMass solution t radius * ∑ p ∈ B, a p * modalEnergy (velocity := velocity) (k - p) t.1) :=
        Finset.sum_le_sum fun k hk ↦ mul_le_mul_of_nonneg_left (hcs k hk) (by positivity)
    _ = bandMass solution t radius * ∑ p ∈ B, a p *
          ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ w * modalEnergy (velocity := velocity) (k - p) t.1 := by
        have hl : ∀ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ w *
            (bandMass solution t radius * ∑ p ∈ B, a p * modalEnergy (velocity := velocity) (k - p) t.1) =
            ∑ p ∈ B, bandMass solution t radius *
              (a p * (((frequencySup k : ℕ) : ℝ) ^ w * modalEnergy (velocity := velocity) (k - p) t.1)) := by
          intro k _
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _
          ring
        rw [Finset.sum_congr rfl hl, Finset.sum_comm]
        simp only [Finset.mul_sum]
    _ ≤ bandMass solution t radius * ∑ p ∈ B, a p *
          (2 ^ w * ∑' q, tailPop velocity t w radius q) := by
        apply mul_le_mul_of_nonneg_left _ hM0
        apply Finset.sum_le_sum
        intro p hp
        apply mul_le_mul_of_nonneg_left _ (ha0 p)
        calc ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ w * modalEnergy (velocity := velocity) (k - p) t.1
            ≤ ∑ k ∈ F, 2 ^ w * (((frequencySup (k - p) : ℕ) : ℝ) ^ w *
                modalEnergy (velocity := velocity) (k - p) t.1) := by
              apply Finset.sum_le_sum
              intro k hk
              have hstep : ((frequencySup k : ℕ) : ℝ) ^ w * modalEnergy (velocity := velocity) (k - p) t.1 ≤
                  2 ^ w * ((frequencySup (k - p) : ℕ) : ℝ) ^ w *
                    modalEnergy (velocity := velocity) (k - p) t.1 :=
                mul_le_mul_of_nonneg_right (hweight k hk p hp)
                  (modalEnergy_nonneg (velocity := velocity) (k - p) t.1)
              rw [← mul_assoc]
              exact hstep
          _ = 2 ^ w * ∑ k ∈ F, ((frequencySup (k - p) : ℕ) : ℝ) ^ w *
                modalEnergy (velocity := velocity) (k - p) t.1 := by rw [Finset.mul_sum]
          _ ≤ 2 ^ w * ∑' q, tailPop velocity t w radius q :=
              mul_le_mul_of_nonneg_left (sum_transported_le t hw hw11 hsum F hF hp) (by positivity)
    _ = 2 ^ w * bandMass solution t radius ^ 2 * ∑' q, tailPop velocity t w radius q := by
        rw [← Finset.sum_mul]
        unfold bandMass
        ring

section Audit

#print axioms frequencySup_le_two_mul
#print axioms norm_feedTerm_le_sqrt
#print axioms sum_pow_bandFeed_sq_le

end Audit

end Soma.Holonics.Millennium.NavierStokesYoungFeed
