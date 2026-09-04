import ElementaryHolonics.Millennium.NavierStokesBandCoherence

/-!
# The cross term collapses into barycentric geometry

The teeth of the band feed are points of the plane `ℂ`.  Their barycenter `z̄` and their spread
about it, `Σ_p ‖z_p − z̄‖²`, carry the whole comb expansion:

```text
bandFeed      = n · z̄,
bandDiagonal  = spread + n ‖z̄‖²,
bandCrossTerm = n (n − 1) ‖z̄‖² − spread,          n = (2N+1)³.
```

So the cross term is nonpositive, and the half power holds, exactly when the pair count times
the squared barycenter is at most the spread: the teeth surround the origin more than they cluster
away from it.  The origin is the pin.  Coherent composition is a barycenter far from the pin
relative to the spread; a brush is a barycenter at the pin.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Finset

namespace Soma.Holonics.Millennium.NavierStokesBandBarycenter

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
open Soma.Holonics.Millennium.NavierStokesShellStepCost
open Soma.Holonics.Millennium.NavierStokesBandCoherence

/-! ## The barycentric identities on any finite family -/

section General

variable {ι : Type*} [DecidableEq ι]

/-- The barycenter of a finite family of complex numbers. -/
def mean (s : Finset ι) (z : ι → ℂ) : ℂ := ((s.card : ℂ))⁻¹ * ∑ p ∈ s, z p

theorem sum_eq_card_mul_mean (s : Finset ι) (hs : s.Nonempty) (z : ι → ℂ) :
    ∑ p ∈ s, z p = (s.card : ℂ) * mean s z := by
  unfold mean
  have hcard : (s.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hs).ne'
  rw [mul_inv_cancel_left₀ hcard]

/-- The natural-number multiple of a complex number is its real scalar multiple. -/
theorem natCast_mul_eq_smul (n : ℕ) (w : ℂ) : (n : ℂ) * w = ((n : ℕ) : ℝ) • w := by
  rw [Complex.real_smul, Complex.ofReal_natCast]

/-- **The variance identity.**  The spread about the barycenter is the diagonal minus the count
times the squared barycenter. -/
theorem sum_norm_sub_mean_sq (s : Finset ι) (hs : s.Nonempty) (z : ι → ℂ) :
    ∑ p ∈ s, ‖z p - mean s z‖ ^ 2 =
      ∑ p ∈ s, ‖z p‖ ^ 2 - (s.card : ℝ) * ‖mean s z‖ ^ 2 := by
  have hexpand : ∀ p ∈ s, ‖z p - mean s z‖ ^ 2 =
      ‖z p‖ ^ 2 - 2 * inner ℝ (z p) (mean s z) + ‖mean s z‖ ^ 2 :=
    fun p _ ↦ norm_sub_sq_real (z p) (mean s z)
  rw [Finset.sum_congr rfl hexpand, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← sum_inner, sum_eq_card_mul_mean s hs z, natCast_mul_eq_smul,
    real_inner_smul_left, real_inner_self_eq_norm_sq, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **The comb expansion in barycentric form.**  The cross term is the pair count times the
squared barycenter minus the spread. -/
theorem cross_eq_pairs_mul_mean_sq_sub_spread (s : Finset ι) (hs : s.Nonempty) (z : ι → ℂ) :
    ∑ p ∈ s, ∑ q ∈ s.erase p, inner ℝ (z p) (z q) =
      (s.card : ℝ) * ((s.card : ℝ) - 1) * ‖mean s z‖ ^ 2 -
        ∑ p ∈ s, ‖z p - mean s z‖ ^ 2 := by
  have hcomb := norm_sum_sq_eq_diagonal_add_cross s z
  have hsum : ‖∑ p ∈ s, z p‖ ^ 2 = (s.card : ℝ) ^ 2 * ‖mean s z‖ ^ 2 := by
    rw [sum_eq_card_mul_mean s hs z, norm_mul, mul_pow, Complex.norm_natCast]
  have hvar := sum_norm_sub_mean_sq s hs z
  rw [hvar]
  linarith [hcomb, hsum]

end General

/-! ## On the band feed -/

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
  (t : Ioo 0 T)

/-- The barycenter of the band's teeth at a receiver. -/
def bandBarycenter (radius : ℕ) (k : SpatialFrequency) (output : Fin 3) : ℂ :=
  mean (frequencyCube radius) (fun p ↦ feedTerm solution t k p output)

/-- The spread of the band's teeth about their barycenter. -/
def bandSpread (radius : ℕ) (k : SpatialFrequency) (output : Fin 3) : ℝ :=
  ∑ p ∈ frequencyCube radius,
    ‖feedTerm solution t k p output - bandBarycenter solution t radius k output‖ ^ 2

theorem frequencyCube_nonempty (radius : ℕ) : (frequencyCube radius).Nonempty :=
  ⟨0, by rw [mem_frequencyCube_iff]; intro c; simp⟩

/-- **The band feed is the count times the barycenter.** -/
theorem bandFeed_eq_count_mul_barycenter (radius : ℕ) (k : SpatialFrequency) (output : Fin 3) :
    bandFeed solution t radius k output =
      ((2 * radius + 1) ^ 3 : ℂ) * bandBarycenter solution t radius k output := by
  unfold bandFeed bandBarycenter
  rw [sum_eq_card_mul_mean _ (frequencyCube_nonempty radius), card_frequencyCube]
  push_cast
  ring

/-- **The cross term in barycentric form.** -/
theorem bandCrossTerm_eq (radius : ℕ) (k : SpatialFrequency) (output : Fin 3) :
    bandCrossTerm solution t radius k output =
      ((2 * radius + 1) ^ 3 : ℝ) * (((2 * radius + 1) ^ 3 : ℝ) - 1) *
          ‖bandBarycenter solution t radius k output‖ ^ 2 -
        bandSpread solution t radius k output := by
  unfold bandCrossTerm bandSpread bandBarycenter
  rw [cross_eq_pairs_mul_mean_sq_sub_spread _ (frequencyCube_nonempty radius), card_frequencyCube]
  push_cast
  ring

/-- **The half power holds exactly when the teeth surround the pin.** -/
theorem bandCrossTerm_nonpos_iff (radius : ℕ) (k : SpatialFrequency) (output : Fin 3) :
    bandCrossTerm solution t radius k output ≤ 0 ↔
      ((2 * radius + 1) ^ 3 : ℝ) * (((2 * radius + 1) ^ 3 : ℝ) - 1) *
          ‖bandBarycenter solution t radius k output‖ ^ 2 ≤
        bandSpread solution t radius k output := by
  rw [bandCrossTerm_eq]
  constructor <;> intro h <;> linarith

section Audit

#print axioms sum_norm_sub_mean_sq
#print axioms cross_eq_pairs_mul_mean_sq_sub_spread
#print axioms bandFeed_eq_count_mul_barycenter
#print axioms bandCrossTerm_nonpos_iff

end Audit

end Soma.Holonics.Millennium.NavierStokesBandBarycenter
