import ElementaryHolonics.RH.FoldedKernel
import ElementaryHolonics.RH.FoldedSourceBounds

/-!
# The folded integer population reconstructs the actual standard xi flow

The complete theta symmetry is retained before passage to the positive-index population.
The half-line integrals then have an integrable majorant at every real heat time.
-/

noncomputable section

namespace Soma.Holonics.RH.FoldedSource

open Real Set Filter Topology MeasureTheory Complex
open Soma.Holonics.RH.HeatKernelPhi
open Soma.Holonics.RH.CriticalChart
open Soma.Holonics.RH.FoldedKernel
open Soma.Holonics.RH.FoldedSourceBounds

/-- Removing a zero centre and pairing the two exact integer orientations halves an even sum. -/
theorem hasSum_positive_of_even
    {f : ℤ → ℝ} {a : ℝ} (hs : HasSum f a)
    (hzero : f 0 = 0) (heven : ∀ n, f (-n) = f n) :
    HasSum (fun n : ℕ ↦ f ((n : ℤ) + 1)) (a / 2) := by
  have hn : Summable (fun n : ℕ ↦ f (n : ℤ)) :=
    hs.summable.comp_injective Int.ofNat_injective
  let b : ℝ := ∑' n : ℕ, f (n : ℤ)
  have hp : HasSum (fun n : ℕ ↦ f ((n : ℤ) + 1)) b := by
    have h := (hasSum_nat_add_iff' (f := fun n : ℕ ↦ f (n : ℤ)) 1).2 hn.hasSum
    simpa [b, Finset.sum_range_one, hzero] using h
  have hneg : HasSum (fun n : ℕ ↦ f (-((n : ℤ) + 1))) b := by
    simpa only [heven] using hp
  have hz : HasSum f (b + b) := hn.hasSum.of_nat_of_neg_add_one hneg
  have hb : b = a / 2 := by linarith [hz.unique hs]
  rwa [hb] at hp

/-- One positive integer event is the corresponding theta derivative term in the standard chart. -/
theorem foldedPhiTerm_eq_thetaTerm (n : ℕ) (u : ℝ) :
    foldedPhiTerm n u = Real.exp u * Ψterm ((n : ℤ) + 1) (Real.exp (4 * u)) := by
  have h9 : Real.exp (9 * u) = Real.exp u * Real.exp (4 * u) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have h5 : Real.exp (5 * u) = Real.exp u * Real.exp (4 * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold foldedPhiTerm Ψterm
  push_cast
  rw [h9, h5]
  ring

/-- The positive-index folded population sums to the actual standard theta kernel. -/
theorem hasSum_foldedPhiTerm (u : ℝ) :
    HasSum (fun n : ℕ ↦ foldedPhiTerm n u) (Φstd u) := by
  have h := (hasSum_Ψ (Real.exp_pos (4 * u))).mul_left (Real.exp u)
  have hp := hasSum_positive_of_even h (by simp [Ψterm]) (by
    intro n
    simp [Ψterm]
    ring)
  have hv : Real.exp u * Ψ (Real.exp (4 * u)) / 2 = Φstd u := by
    unfold Φstd Φ
    rw [show 2 * u / 2 = u by ring, show 2 * (2 * u) = 4 * u by ring]
  rw [hv] at hp
  exact hp.congr_fun (fun n ↦ foldedPhiTerm_eq_thetaTerm n u)

/-- Pointwise assembly of the flowed cosine population preserves the same actual kernel. -/
theorem hasSum_foldedSourceTerm (t : ℝ) (z : ℂ) (u : ℝ) :
    HasSum (fun n : ℕ ↦ foldedSourceTerm t z n u) (cosineIntegrand t z u) := by
  have h : HasSum (fun n : ℕ ↦ (foldedPhiTerm n u : ℂ)) (Φstd u : ℂ) :=
    by simpa [HasSum] using (hasSum_foldedPhiTerm u).ofReal
  have hm := (h.mul_left (Real.exp (t * u ^ 2) : ℂ)).mul_right (Complex.cos (z * u))
  simpa [foldedSourceTerm, cosineIntegrand, foldedWeight] using hm

def sourceCoefficient (n : ℕ) : ℝ :=
  2 * π ^ 2 * (n + 1 : ℝ) ^ 4 * Real.exp (-π * (n + 1 : ℝ) ^ 2 / 2)

def sourceMajorant (T R u : ℝ) : ℝ :=
  Real.exp (T * u ^ 2 + (R + 9) * u - π * Real.exp (4 * u) / 2)

theorem continuous_foldedSourceTerm (t : ℝ) (z : ℂ) (n : ℕ) :
    Continuous (foldedSourceTerm t z n) := by
  unfold foldedSourceTerm foldedPhiTerm
  fun_prop

theorem summable_sourceCoefficient : Summable sourceCoefficient :=
  summable_foldedPhiCoefficient

theorem integrableOn_sourceMajorant {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    IntegrableOn (sourceMajorant T R) (Ioi 0) :=
  integrableOn_foldedSourceMajorant hT hR

/-- Every folded event is absolutely integrable at every real time. -/
theorem integrableOn_foldedSourceTerm (t : ℝ) (z : ℂ) (n : ℕ) :
    IntegrableOn (foldedSourceTerm t z n) (Ioi 0) := by
  have hm := (integrableOn_sourceMajorant (abs_nonneg t) (abs_nonneg z.im)).const_mul
    (sourceCoefficient n)
  apply hm.mono' (continuous_foldedSourceTerm t z n).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact norm_foldedSourceTerm_le (abs_nonneg t) (abs_nonneg z.im) hu.le le_rfl le_rfl

/-- The whole source-to-flow return, justified by an integrable majorant and the exact theta sum. -/
theorem hasSum_integral_foldedSourceTerm (t : ℝ) (z : ℂ) :
    HasSum (fun n : ℕ ↦ ∫ u in Ioi (0 : ℝ), foldedSourceTerm t z n u) (Hstd t z) := by
  rw [Hstd_eq_integral_positiveHalfLine]
  let bound : ℕ → ℝ → ℝ := fun n u ↦
    sourceCoefficient n * sourceMajorant |t| |z.im| u
  apply hasSum_integral_of_dominated_convergence bound
  · intro n
    exact (continuous_foldedSourceTerm t z n).aestronglyMeasurable
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact norm_foldedSourceTerm_le (abs_nonneg t) (abs_nonneg z.im) hu.le le_rfl le_rfl
  · exact Filter.Eventually.of_forall fun u ↦
      summable_sourceCoefficient.mul_right (sourceMajorant |t| |z.im| u)
  · have hm := (integrableOn_sourceMajorant (abs_nonneg t) (abs_nonneg z.im)).const_mul
      (∑' n : ℕ, sourceCoefficient n)
    simpa only [bound, tsum_mul_right] using hm
  · exact Filter.Eventually.of_forall fun u ↦ hasSum_foldedSourceTerm t z u

/-- A uniform bound on the integrated event over each declared compact time/height aperture. -/
theorem norm_integral_foldedSourceTerm_le
    {T R t : ℝ} {z : ℂ} (n : ℕ) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (ht : |t| ≤ T) (hz : |z.im| ≤ R) :
    ‖∫ u in Ioi (0 : ℝ), foldedSourceTerm t z n u‖ ≤
      sourceCoefficient n * ∫ u in Ioi (0 : ℝ), sourceMajorant T R u := by
  calc
    ‖∫ u in Ioi (0 : ℝ), foldedSourceTerm t z n u‖ ≤
        ∫ u in Ioi (0 : ℝ), ‖foldedSourceTerm t z n u‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ u in Ioi (0 : ℝ), sourceCoefficient n * sourceMajorant T R u := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun u ↦ norm_nonneg _)
        ((integrableOn_sourceMajorant hT hR).const_mul (sourceCoefficient n))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact norm_foldedSourceTerm_le hT hR hu.le ht hz
    _ = sourceCoefficient n * ∫ u in Ioi (0 : ℝ), sourceMajorant T R u := integral_const_mul _ _

#print axioms hasSum_positive_of_even
#print axioms hasSum_foldedPhiTerm
#print axioms hasSum_foldedSourceTerm
#print axioms integrableOn_foldedSourceTerm
#print axioms hasSum_integral_foldedSourceTerm
#print axioms norm_integral_foldedSourceTerm_le

end Soma.Holonics.RH.FoldedSource
