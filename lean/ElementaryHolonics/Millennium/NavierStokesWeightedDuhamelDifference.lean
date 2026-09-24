import ElementaryHolonics.Millennium.NavierStokesWeightedDuhamelBound

/-!
# Two-path control for the weighted Duhamel passage

**[proved-derived]** The quadratic Leray source is bilinear before the two inputs are identified.
Keeping that incidence visible gives the polarization identity

`B(u,u) - B(v,v) = B(u-v,u) + B(v,u-v)`.

This owner transports that exact difference through the positive-time heat passage.  The result is
the two-path majorant needed by the actual restart contraction: the separation of two Duhamel
returns is controlled by the sum of their radii, their pointwise separation, and the same
integrable heat kernel used by the one-path estimate.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Interval

namespace Soma.Holonics.Millennium.NavierStokesWeightedDuhamelDifference

open Soma.Holonics.Millennium.NavierStokesDuhamelKernelIntegral
open Soma.Holonics.Millennium.NavierStokesH2ToH3HeatSmoothing
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelBound
open Soma.Holonics.Millennium.NavierStokesWeightedHeatSemigroup
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## Polarization of the caused quadratic source -/

/-- The exact quadratic difference retains the two bilinear incidences which produced it. -/
theorem weightedLerayQuadratic_sub
    (u v : PeriodicVectorWeightedSobolev 3) :
    weightedLerayQuadratic u - weightedLerayQuadratic v =
      weightedLerayDivergenceConvolution (u - v) u +
        weightedLerayDivergenceConvolution v (u - v) := by
  change weightedLerayDivergenceConvolutionContinuous u u -
      weightedLerayDivergenceConvolutionContinuous v v =
    weightedLerayDivergenceConvolutionContinuous (u - v) u +
      weightedLerayDivergenceConvolutionContinuous v (u - v)
  rw [map_sub, map_sub]
  rw [ContinuousLinearMap.sub_apply]
  abel

/-- Quantitative local Lipschitz control of the native quadratic source. -/
theorem norm_weightedLerayQuadratic_sub_le
    (u v : PeriodicVectorWeightedSobolev 3) :
    ‖weightedLerayQuadratic u - weightedLerayQuadratic v‖ ≤
      (23328 * periodicH3EmbeddingConstant) * (‖u‖ + ‖v‖) * ‖u - v‖ := by
  rw [weightedLerayQuadratic_sub]
  calc
    ‖weightedLerayDivergenceConvolution (u - v) u +
        weightedLerayDivergenceConvolution v (u - v)‖ ≤
      ‖weightedLerayDivergenceConvolution (u - v) u‖ +
        ‖weightedLerayDivergenceConvolution v (u - v)‖ := norm_add_le _ _
    _ ≤ (23328 * periodicH3EmbeddingConstant) * ‖u - v‖ * ‖u‖ +
        (23328 * periodicH3EmbeddingConstant) * ‖v‖ * ‖u - v‖ :=
      add_le_add
        (norm_weightedLerayDivergenceConvolution_le (u - v) u)
        (norm_weightedLerayDivergenceConvolution_le v (u - v))
    _ = (23328 * periodicH3EmbeddingConstant) * (‖u‖ + ‖v‖) * ‖u - v‖ := by
      ring

/-! ## Heat transport of a two-path difference -/

/-- Componentwise heat smoothing obeys the scalar one-derivative operator bound. -/
private theorem norm_vectorHeatTwoToThree_le
    (nu tau : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (tau : ℝ))
    (state : PeriodicVectorWeightedSobolev 2) :
    ‖periodicVectorWeightedHeatTwoToThree nu tau hviscous state‖ ≤
      Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (tau : ℝ)) * ‖state‖ := by
  have hconstant : 0 ≤
      Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (tau : ℝ)) * ‖state‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  rw [pi_norm_le_iff_of_nonneg hconstant]
  intro component
  calc
    ‖periodicWeightedHeatTwoToThree nu tau hviscous (state component)‖ ≤
        Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (tau : ℝ)) *
          ‖state component‖ :=
      norm_periodicWeightedHeatTwoToThree_le nu tau hviscous (state component)
    _ ≤ Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (tau : ℝ)) * ‖state‖ :=
      mul_le_mul_of_nonneg_left (norm_le_pi_norm state component) (Real.sqrt_nonneg _)

/-- Before imposing a path ball, the actual endpoint-totalized Duhamel integrands have the exact
two-path heat-kernel bound. -/
theorem norm_weightedDuhamelIntegrand_sub_le
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (u v : ℝ → PeriodicVectorWeightedSobolev 3) (s : ℝ) :
    ‖weightedDuhamelIntegrand nu hnu t u s -
        weightedDuhamelIntegrand nu hnu t v s‖ ≤
      duhamelHeatKernelMajorant (nu : ℝ) (t - s) *
        ((23328 * periodicH3EmbeddingConstant) *
          (‖u s‖ + ‖v s‖) * ‖u s - v s‖) := by
  by_cases hs : s < t
  · rw [weightedDuhamelIntegrand_of_lt nu hnu t u hs,
      weightedDuhamelIntegrand_of_lt nu hnu t v hs, ← map_sub]
    calc
      ‖periodicVectorWeightedHeatTwoToThree nu (positiveElapsed t s hs)
          (mul_pos hnu (sub_pos.mpr hs))
          (weightedLerayQuadratic (u s) - weightedLerayQuadratic (v s))‖ ≤
        Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (t - s)) *
          ‖weightedLerayQuadratic (u s) - weightedLerayQuadratic (v s)‖ := by
        simpa only [coe_positiveElapsed] using
          norm_vectorHeatTwoToThree_le nu (positiveElapsed t s hs)
            (mul_pos hnu (sub_pos.mpr hs))
            (weightedLerayQuadratic (u s) - weightedLerayQuadratic (v s))
      _ ≤ Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (t - s)) *
          ((23328 * periodicH3EmbeddingConstant) *
            (‖u s‖ + ‖v s‖) * ‖u s - v s‖) := by
        apply mul_le_mul_of_nonneg_left
          (norm_weightedLerayQuadratic_sub_le (u s) (v s))
          (Real.sqrt_nonneg _)
      _ = duhamelHeatKernelMajorant (nu : ℝ) (t - s) *
          ((23328 * periodicH3EmbeddingConstant) *
            (‖u s‖ + ‖v s‖) * ‖u s - v s‖) := rfl
  · simp [weightedDuhamelIntegrand_of_not_lt nu hnu t u hs,
      weightedDuhamelIntegrand_of_not_lt nu hnu t v hs]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) periodicH3EmbeddingConstant_nonneg)
          (add_nonneg (norm_nonneg _) (norm_nonneg _)))
        (norm_nonneg _))

/-- On a common radius ball and with a uniform pointwise separation, the two-path integrand is
dominated by the reflected integrable heat kernel. -/
theorem norm_weightedDuhamelIntegrand_sub_le_of_norm_le
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t R D : ℝ)
    (u v : ℝ → PeriodicVectorWeightedSobolev 3) (s : ℝ)
    (hR : 0 ≤ R)
    (hu : ‖u s‖ ≤ R) (hv : ‖v s‖ ≤ R) (huv : ‖u s - v s‖ ≤ D) :
    ‖weightedDuhamelIntegrand nu hnu t u s -
        weightedDuhamelIntegrand nu hnu t v s‖ ≤
      (23328 * periodicH3EmbeddingConstant) * (2 * R) * D *
        duhamelHeatKernelMajorant (nu : ℝ) (t - s) := by
  have hkernel : 0 ≤ duhamelHeatKernelMajorant (nu : ℝ) (t - s) :=
    Real.sqrt_nonneg _
  have hconstant : 0 ≤ 23328 * periodicH3EmbeddingConstant :=
    mul_nonneg (by norm_num) periodicH3EmbeddingConstant_nonneg
  calc
    ‖weightedDuhamelIntegrand nu hnu t u s -
        weightedDuhamelIntegrand nu hnu t v s‖ ≤
      duhamelHeatKernelMajorant (nu : ℝ) (t - s) *
        ((23328 * periodicH3EmbeddingConstant) *
          (‖u s‖ + ‖v s‖) * ‖u s - v s‖) :=
      norm_weightedDuhamelIntegrand_sub_le nu hnu t u v s
    _ ≤ duhamelHeatKernelMajorant (nu : ℝ) (t - s) *
        ((23328 * periodicH3EmbeddingConstant) * (2 * R) * D) := by
      gcongr
      linarith
    _ = (23328 * periodicH3EmbeddingConstant) * (2 * R) * D *
        duhamelHeatKernelMajorant (nu : ℝ) (t - s) := by ring

/-! ## Integrated separation return -/

/-- The actual Bochner integral of the two-path integrand difference has the uniform Volterra
Lipschitz bound.  As for the one-path norm estimate, totality of the Bochner integral means the
inequality itself needs only the integrable scalar majorant; separate integrability is required
later when identifying this integral with the difference of the two Duhamel returns. -/
theorem norm_intervalIntegral_weightedDuhamelIntegrand_sub_le
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {t : ℝ} (ht : 0 < t) (R D : ℝ)
    (u v : ℝ → PeriodicVectorWeightedSobolev 3)
    (hu : ∀ s ∈ Icc (0 : ℝ) t, ‖u s‖ ≤ R)
    (hv : ∀ s ∈ Icc (0 : ℝ) t, ‖v s‖ ≤ R)
    (huv : ∀ s ∈ Icc (0 : ℝ) t, ‖u s - v s‖ ≤ D) :
    ‖∫ s in (0 : ℝ)..t,
        (weightedDuhamelIntegrand nu hnu t u s -
          weightedDuhamelIntegrand nu hnu t v s)‖ ≤
      (23328 * periodicH3EmbeddingConstant) * (2 * R) * D *
        (t + 2 * Real.sqrt (t / (2 * (nu : ℝ)))) := by
  have hR : 0 ≤ R :=
    (norm_nonneg (u 0)).trans (hu 0 ⟨le_rfl, ht.le⟩)
  have hD : 0 ≤ D :=
    (norm_nonneg (u 0 - v 0)).trans (huv 0 ⟨le_rfl, ht.le⟩)
  let K : ℝ := (23328 * periodicH3EmbeddingConstant) * (2 * R) * D
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) periodicH3EmbeddingConstant_nonneg)
        (mul_nonneg (by norm_num) hR)) hD
  have hmajorant : IntervalIntegrable
      (fun s : ℝ ↦ K * duhamelHeatKernelMajorant (nu : ℝ) (t - s))
      volume 0 t :=
    (intervalIntegrable_reflectedDuhamelHeatKernelMajorant nu hnu ht).const_mul K
  have hnorm :
      ‖∫ s in (0 : ℝ)..t,
          (weightedDuhamelIntegrand nu hnu t u s -
            weightedDuhamelIntegrand nu hnu t v s)‖ ≤
        ∫ s in (0 : ℝ)..t,
          K * duhamelHeatKernelMajorant (nu : ℝ) (t - s) := by
    apply intervalIntegral.norm_integral_le_of_norm_le ht.le
    · filter_upwards with s
      intro hs
      exact norm_weightedDuhamelIntegrand_sub_le_of_norm_le
        nu hnu t R D u v s hR
          (hu s ⟨hs.1.le, hs.2⟩) (hv s ⟨hs.1.le, hs.2⟩)
          (huv s ⟨hs.1.le, hs.2⟩)
    · exact hmajorant
  calc
    ‖∫ s in (0 : ℝ)..t,
        (weightedDuhamelIntegrand nu hnu t u s -
          weightedDuhamelIntegrand nu hnu t v s)‖ ≤
      ∫ s in (0 : ℝ)..t,
        K * duhamelHeatKernelMajorant (nu : ℝ) (t - s) := hnorm
    _ = K * ∫ s in (0 : ℝ)..t,
        duhamelHeatKernelMajorant (nu : ℝ) (t - s) := by
      rw [intervalIntegral.integral_const_mul]
    _ = K * ∫ tau in (0 : ℝ)..t,
        duhamelHeatKernelMajorant (nu : ℝ) tau := by
      rw [intervalIntegral_reflectedDuhamelHeatKernelMajorant]
    _ ≤ K * (t + 2 * Real.sqrt (t / (2 * (nu : ℝ)))) :=
      mul_le_mul_of_nonneg_left
        (intervalIntegral_duhamelHeatKernelMajorant_le hnu ht) hK
    _ = (23328 * periodicH3EmbeddingConstant) * (2 * R) * D *
        (t + 2 * Real.sqrt (t / (2 * (nu : ℝ)))) := rfl

section Audit

#print axioms weightedLerayQuadratic_sub
#print axioms norm_weightedLerayQuadratic_sub_le
#print axioms norm_weightedDuhamelIntegrand_sub_le
#print axioms norm_weightedDuhamelIntegrand_sub_le_of_norm_le
#print axioms norm_intervalIntegral_weightedDuhamelIntegrand_sub_le

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedDuhamelDifference
