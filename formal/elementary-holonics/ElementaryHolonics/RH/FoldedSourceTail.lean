import ElementaryHolonics.RH.FoldedSource

/-!
# A compact-uniform remainder for the folded xi source

The partial population includes positive integers `1,...,N`. The complete omitted population is
retained as a shifted series, and its norm is bounded by an explicit Gaussian cutoff factor times
one finite aperture constant. The bound is uniform in real time and imaginary height on their
declared apertures, without a cutoff on the real part of the spectral variable.
-/

noncomputable section

namespace Soma.Holonics.RH.FoldedSourceTail

open Real Set Filter Topology MeasureTheory Complex
open Soma.Holonics.RH.CriticalChart
open Soma.Holonics.RH.FoldedSourceBounds
open Soma.Holonics.RH.FoldedSource

def partialSource (N : ℕ) (t : ℝ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, ∫ u in Ioi (0 : ℝ), foldedSourceTerm t z n u

def majorantIntegral (T R : ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), sourceMajorant T R u

def remainderConstant (T R : ℝ) : ℝ := foldedQuarterConstant * majorantIntegral T R

def remainderBound (T R : ℝ) (N : ℕ) : ℝ :=
  remainderConstant T R * Real.exp (-π * (N + 1 : ℝ) ^ 2 / 4)

theorem majorantIntegral_nonneg (T R : ℝ) : 0 ≤ majorantIntegral T R := by
  exact integral_nonneg fun u ↦ (Real.exp_pos _).le

theorem remainderConstant_nonneg (T R : ℝ) : 0 ≤ remainderConstant T R :=
  mul_nonneg foldedQuarterConstant_nonneg (majorantIntegral_nonneg T R)

theorem sourceCoefficient_tail_le (N : ℕ) :
    (∑' j : ℕ, sourceCoefficient (j + N)) ≤
      foldedQuarterConstant * Real.exp (-π * (N + 1 : ℝ) ^ 2 / 4) := by
  simpa [sourceCoefficient, Nat.cast_add] using foldedPhiCoefficient_tail_le N

/-- The omitted source population bounds the error against the actual standard flow. -/
theorem norm_Hstd_sub_partialSource_le
    {T R t : ℝ} {z : ℂ} (N : ℕ) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (ht : |t| ≤ T) (hz : |z.im| ≤ R) :
    ‖Hstd t z - partialSource N t z‖ ≤ remainderBound T R N := by
  let F : ℕ → ℂ := fun n ↦ ∫ u in Ioi (0 : ℝ), foldedSourceTerm t z n u
  have hsum : HasSum F (Hstd t z) := hasSum_integral_foldedSourceTerm t z
  have htail : HasSum (fun j : ℕ ↦ F (j + N)) (Hstd t z - partialSource N t z) :=
    (hasSum_nat_add_iff' N).2 hsum
  have hbound : ∀ j : ℕ, ‖F (j + N)‖ ≤
      sourceCoefficient (j + N) * majorantIntegral T R :=
    fun j ↦ norm_integral_foldedSourceTerm_le (j + N) hT hR ht hz
  have hcoeff : Summable (fun j : ℕ ↦ sourceCoefficient (j + N) * majorantIntegral T R) :=
    ((summable_nat_add_iff N).2 summable_sourceCoefficient).mul_right (majorantIntegral T R)
  have hnorm : Summable (fun j : ℕ ↦ ‖F (j + N)‖) :=
    hcoeff.of_nonneg_of_le (fun j ↦ norm_nonneg _) hbound
  rw [← htail.tsum_eq]
  calc
    ‖∑' j : ℕ, F (j + N)‖ ≤ ∑' j : ℕ, ‖F (j + N)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' j : ℕ, sourceCoefficient (j + N) * majorantIntegral T R :=
      Summable.tsum_le_tsum hbound hnorm hcoeff
    _ = (∑' j : ℕ, sourceCoefficient (j + N)) * majorantIntegral T R := tsum_mul_right
    _ ≤ (foldedQuarterConstant * Real.exp (-π * (N + 1 : ℝ) ^ 2 / 4)) *
        majorantIntegral T R :=
      mul_le_mul_of_nonneg_right (sourceCoefficient_tail_le N) (majorantIntegral_nonneg T R)
    _ = remainderBound T R N := by unfold remainderBound remainderConstant; ring

theorem cutoffFactor_tendsto_zero :
    Tendsto (fun N : ℕ ↦ Real.exp (-π * (N + 1 : ℝ) ^ 2 / 4)) atTop (𝓝 0) := by
  have hn : Tendsto (fun N : ℕ ↦ (N + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun N : ℕ ↦ by simp) tendsto_natCast_atTop_atTop
  have hs : Tendsto (fun N : ℕ ↦ (N + 1 : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hn
  have hp := hs.const_mul_atTop (by positivity : 0 < π / 4)
  convert Real.tendsto_exp_neg_atTop_nhds_zero.comp hp using 1
  funext N
  congr 1
  ring

theorem remainderBound_tendsto_zero (T R : ℝ) :
    Tendsto (remainderBound T R) atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ ↦
    remainderConstant T R * Real.exp (-π * (N + 1 : ℝ) ^ 2 / 4)) atTop (𝓝 0)
  simpa only [mul_zero] using cutoffFactor_tendsto_zero.const_mul (remainderConstant T R)

def parameterAperture (T R : ℝ) : Set (ℝ × ℂ) :=
  {p | |p.1| ≤ T ∧ |p.2.im| ≤ R}

/-- Uniform convergence on every declared time/height aperture, in particular on compact sets. -/
theorem tendstoUniformlyOn_partialSource
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    TendstoUniformlyOn (fun N p ↦ partialSource N p.1 p.2)
      (fun p ↦ Hstd p.1 p.2) atTop (parameterAperture T R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(remainderBound_tendsto_zero T R).eventually (Iio_mem_nhds hε)]
    with N hN p hp
  calc
    dist (Hstd p.1 p.2) (partialSource N p.1 p.2) =
        ‖Hstd p.1 p.2 - partialSource N p.1 p.2‖ := dist_eq_norm _ _
    _ ≤ remainderBound T R N := norm_Hstd_sub_partialSource_le N hT hR hp.1 hp.2
    _ < ε := hN

/-- Every fixed-time source series converges locally uniformly on the entire complex plane. -/
theorem tendstoLocallyUniformly_partialSource (t : ℝ) :
    TendstoLocallyUniformly (fun N z ↦ partialSource N t z) (Hstd t) atTop := by
  rw [← tendstoLocallyUniformlyOn_univ]
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).2
  intro K _hK hcompact
  obtain ⟨R, hR⟩ := hcompact.exists_bound_of_continuousOn
    (f := fun z : ℂ ↦ z) continuous_id.continuousOn
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(remainderBound_tendsto_zero |t| (max R 0)).eventually
    (Iio_mem_nhds hε)] with N hN z hz
  rw [dist_eq_norm]
  exact (norm_Hstd_sub_partialSource_le N (abs_nonneg t) (le_max_right R 0) le_rfl
    ((Complex.abs_im_le_norm z).trans ((hR z hz).trans (le_max_left R 0)))).trans_lt hN

#print axioms norm_Hstd_sub_partialSource_le
#print axioms remainderBound_tendsto_zero
#print axioms tendstoUniformlyOn_partialSource
#print axioms tendstoLocallyUniformly_partialSource

end Soma.Holonics.RH.FoldedSourceTail
