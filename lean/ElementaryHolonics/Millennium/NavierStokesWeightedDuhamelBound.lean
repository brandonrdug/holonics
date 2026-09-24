import ElementaryHolonics.Millennium.NavierStokesWeightedHeatSemigroup
import ElementaryHolonics.Millennium.NavierStokesWeightedLerayBilinear
import ElementaryHolonics.Millennium.NavierStokesDuhamelKernelIntegral

/-!
# The positive-time weighted Duhamel passage

This owner composes the complete native passages already returned by the weighted Fourier line:

* the continuous bilinear map `H³ × H³ → H²` given by Leray-projected divergence;
* the positive-time heat map `H² → H³`; and
* the integrable endpoint majorant `sqrt (1 + (2 * ν * τ)⁻¹)`.

For a terminal time `t`, the integrand at `s < t` is the heat return at elapsed time `t - s`
of the exact quadratic Leray population.  Its value at `s = t` (and outside the positive-time
branch) is totalized to zero.  This changes no interval integral.

The norm of the actual Bochner interval integral is bounded without assuming integrability of the
integrand: Mathlib's Bochner integral is total, and `norm_integral_le_of_norm_le` only needs the
integrable scalar majorant.  A separate theorem returns interval integrability from the precise
remaining port, almost-everywhere strong measurability of the parameter-dependent heat passage.
Continuity of the quadratic source path is proved here; joint strong measurability of
`(τ, f) ↦ exp (ν τ Δ) f : H² → H³` is not asserted by the imported heat owner, whose
continuous-linear-map structure is only pointwise in positive `τ`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal Interval

namespace Soma.Holonics.Millennium.NavierStokesWeightedDuhamelBound

open Soma.Holonics.Millennium.NavierStokesDuhamelKernelIntegral
open Soma.Holonics.Millennium.NavierStokesH2ToH3HeatSmoothing
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesWeightedHeatSemigroup
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## The caused source and positive elapsed-time return -/

/-- The native quadratic Leray-divergence source at one `H³` state. -/
def weightedLerayQuadratic
    (state : PeriodicVectorWeightedSobolev 3) :
    PeriodicVectorWeightedSobolev 2 :=
  weightedLerayDivergenceConvolutionContinuous state state

@[simp]
theorem weightedLerayQuadratic_apply
    (state : PeriodicVectorWeightedSobolev 3) :
    weightedLerayQuadratic state =
      weightedLerayDivergenceConvolution state state :=
  rfl

/-- The exact native quadratic source is a continuous function of its `H³` state. -/
theorem continuous_weightedLerayQuadratic :
    Continuous weightedLerayQuadratic := by
  exact weightedLerayDivergenceConvolutionContinuous.continuous.clm_apply continuous_id

/-- Hence a continuous `H³` path has a continuous `H²` quadratic-source path. -/
theorem Continuous.comp_weightedLerayQuadratic
    {u : ℝ → PeriodicVectorWeightedSobolev 3} (hu : Continuous u) :
    Continuous (fun s ↦ weightedLerayQuadratic (u s)) :=
  continuous_weightedLerayQuadratic.comp hu

/-- The positive elapsed time as a nonnegative-real heat parameter. -/
def positiveElapsed (t s : ℝ) (hs : s < t) : ℝ≥0 :=
  ⟨t - s, sub_nonneg.mpr hs.le⟩

@[simp]
theorem coe_positiveElapsed (t s : ℝ) (hs : s < t) :
    ((positiveElapsed t s hs : ℝ≥0) : ℝ) = t - s :=
  rfl

/-- The actual native `H³` Duhamel integrand.  Only strictly positive elapsed heat time is sent
through the one-derivative heat passage; the terminal endpoint is represented by zero. -/
def weightedDuhamelIntegrand
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (u : ℝ → PeriodicVectorWeightedSobolev 3) (s : ℝ) :
    PeriodicVectorWeightedSobolev 3 :=
  if hs : s < t then
    periodicVectorWeightedHeatTwoToThree nu (positiveElapsed t s hs)
      (mul_pos hnu (sub_pos.mpr hs)) (weightedLerayQuadratic (u s))
  else
    0

theorem weightedDuhamelIntegrand_of_lt
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (u : ℝ → PeriodicVectorWeightedSobolev 3) {s : ℝ} (hs : s < t) :
    weightedDuhamelIntegrand nu hnu t u s =
      periodicVectorWeightedHeatTwoToThree nu (positiveElapsed t s hs)
        (mul_pos hnu (sub_pos.mpr hs)) (weightedLerayQuadratic (u s)) := by
  rw [weightedDuhamelIntegrand, dif_pos hs]

@[simp]
theorem weightedDuhamelIntegrand_of_not_lt
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (u : ℝ → PeriodicVectorWeightedSobolev 3) {s : ℝ} (hs : ¬ s < t) :
    weightedDuhamelIntegrand nu hnu t u s = 0 := by
  simp [weightedDuhamelIntegrand, hs]

/-! ## Pointwise transport through the singular heat face -/

/-- The componentwise vector smoothing map inherits the scalar one-derivative norm bound. -/
private theorem norm_periodicVectorWeightedHeatTwoToThree_le
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
    _ ≤ Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (tau : ℝ)) *
          ‖state‖ :=
      mul_le_mul_of_nonneg_left (norm_le_pi_norm state component) (Real.sqrt_nonneg _)

/-- Exact pointwise norm control before imposing a path ball. -/
theorem norm_weightedDuhamelIntegrand_le
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (u : ℝ → PeriodicVectorWeightedSobolev 3) (s : ℝ) :
    ‖weightedDuhamelIntegrand nu hnu t u s‖ ≤
      duhamelHeatKernelMajorant (nu : ℝ) (t - s) *
        ((23328 * periodicH3EmbeddingConstant) * ‖u s‖ * ‖u s‖) := by
  by_cases hs : s < t
  · rw [weightedDuhamelIntegrand_of_lt nu hnu t u hs]
    calc
      ‖periodicVectorWeightedHeatTwoToThree nu (positiveElapsed t s hs)
          (mul_pos hnu (sub_pos.mpr hs)) (weightedLerayQuadratic (u s))‖ ≤
          Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (t - s)) *
            ‖weightedLerayQuadratic (u s)‖ := by
        simpa only [coe_positiveElapsed] using
          norm_periodicVectorWeightedHeatTwoToThree_le
            nu (positiveElapsed t s hs) (mul_pos hnu (sub_pos.mpr hs))
              (weightedLerayQuadratic (u s))
      _ ≤ Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (t - s)) *
          ((23328 * periodicH3EmbeddingConstant) * ‖u s‖ * ‖u s‖) := by
        apply mul_le_mul_of_nonneg_left
          (norm_weightedLerayDivergenceConvolution_le (u s) (u s))
          (Real.sqrt_nonneg _)
      _ = duhamelHeatKernelMajorant (nu : ℝ) (t - s) *
          ((23328 * periodicH3EmbeddingConstant) * ‖u s‖ * ‖u s‖) := by
        rfl
  · rw [weightedDuhamelIntegrand_of_not_lt nu hnu t u hs, norm_zero]
    have hconstant : 0 ≤ 23328 * periodicH3EmbeddingConstant :=
      mul_nonneg (by norm_num) periodicH3EmbeddingConstant_nonneg
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (mul_nonneg hconstant (norm_nonneg _)) (norm_nonneg _))

/-- Uniform path-ball control by the reflected integrable heat kernel. -/
theorem norm_weightedDuhamelIntegrand_le_of_norm_le
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t R : ℝ)
    (u : ℝ → PeriodicVectorWeightedSobolev 3) (s : ℝ)
    (hR : 0 ≤ R) (hu : ‖u s‖ ≤ R) :
    ‖weightedDuhamelIntegrand nu hnu t u s‖ ≤
      (23328 * periodicH3EmbeddingConstant) * R ^ 2 *
        duhamelHeatKernelMajorant (nu : ℝ) (t - s) := by
  have hkernel : 0 ≤ duhamelHeatKernelMajorant (nu : ℝ) (t - s) :=
    Real.sqrt_nonneg _
  have hconstant : 0 ≤ 23328 * periodicH3EmbeddingConstant :=
    mul_nonneg (by norm_num) periodicH3EmbeddingConstant_nonneg
  calc
    ‖weightedDuhamelIntegrand nu hnu t u s‖ ≤
        duhamelHeatKernelMajorant (nu : ℝ) (t - s) *
          ((23328 * periodicH3EmbeddingConstant) * ‖u s‖ * ‖u s‖) :=
      norm_weightedDuhamelIntegrand_le nu hnu t u s
    _ ≤ duhamelHeatKernelMajorant (nu : ℝ) (t - s) *
          ((23328 * periodicH3EmbeddingConstant) * R * R) := by
      gcongr
    _ = (23328 * periodicH3EmbeddingConstant) * R ^ 2 *
          duhamelHeatKernelMajorant (nu : ℝ) (t - s) := by ring

/-! ## Scalar majorant and Bochner return -/

/-- The reflected scalar heat budget is interval-integrable on the Duhamel interval. -/
theorem intervalIntegrable_reflectedDuhamelHeatKernelMajorant
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {t : ℝ} (ht : 0 < t) :
    IntervalIntegrable
      (fun s : ℝ ↦ duhamelHeatKernelMajorant (nu : ℝ) (t - s)) volume 0 t := by
  have hbase := intervalIntegrable_duhamelHeatKernelMajorant hnu ht
  have hreflected := (hbase.comp_sub_left t).symm
  simpa only [sub_zero, sub_self] using hreflected

/-- Its reflected interval integral is the original positive-time kernel integral. -/
theorem intervalIntegral_reflectedDuhamelHeatKernelMajorant
    (nu : ℝ≥0) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, duhamelHeatKernelMajorant (nu : ℝ) (t - s)) =
      ∫ tau in (0 : ℝ)..t, duhamelHeatKernelMajorant (nu : ℝ) tau := by
  simpa only [sub_self, sub_zero] using
    (intervalIntegral.integral_comp_sub_left
      (fun tau : ℝ ↦ duhamelHeatKernelMajorant (nu : ℝ) tau) t
      (a := (0 : ℝ)) (b := t))

/-- The full scalar path-ball majorant is interval-integrable. -/
theorem intervalIntegrable_weightedDuhamelMajorant
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {t : ℝ} (ht : 0 < t) (R : ℝ) :
    IntervalIntegrable
      (fun s : ℝ ↦ (23328 * periodicH3EmbeddingConstant) * R ^ 2 *
        duhamelHeatKernelMajorant (nu : ℝ) (t - s)) volume 0 t :=
  (intervalIntegrable_reflectedDuhamelHeatKernelMajorant nu hnu ht).const_mul
    ((23328 * periodicH3EmbeddingConstant) * R ^ 2)

/-- If the parameter-dependent heat composition is almost everywhere strongly measurable, the
pointwise scalar domination returns honest interval integrability.  This premise names the exact
joint-time port absent from the pointwise heat-semigroup owner; it is not an integrability premise. -/
theorem intervalIntegrable_weightedDuhamelIntegrand
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {t : ℝ} (ht : 0 < t) (R : ℝ)
    (u : ℝ → PeriodicVectorWeightedSobolev 3)
    (hu : ∀ s ∈ Icc (0 : ℝ) t, ‖u s‖ ≤ R)
    (hmeas : AEStronglyMeasurable (weightedDuhamelIntegrand nu hnu t u)
      (volume.restrict (Ioc (0 : ℝ) t))) :
    IntervalIntegrable (weightedDuhamelIntegrand nu hnu t u) volume 0 t := by
  have hR : 0 ≤ R := by
    exact (norm_nonneg (u 0)).trans (hu 0 ⟨le_rfl, ht.le⟩)
  have hmeas' : AEStronglyMeasurable (weightedDuhamelIntegrand nu hnu t u)
      (volume.restrict (Ι (0 : ℝ) t)) := by
    simpa only [uIoc_of_le ht.le] using hmeas
  apply (intervalIntegrable_weightedDuhamelMajorant nu hnu ht R).mono_fun'
    hmeas'
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
  rw [uIoc_of_le ht.le] at hs
  exact norm_weightedDuhamelIntegrand_le_of_norm_le nu hnu t R u s hR
    (hu s ⟨hs.1.le, hs.2⟩)

/-- The actual Bochner Duhamel return obeys the explicit critical ball estimate.

No measurability hypothesis is needed for this inequality: the total Bochner integral is bounded
by any integrable almost-everywhere norm majorant.  The preceding theorem separately records when
the integrand itself is an honest interval-integrable passage. -/
theorem norm_intervalIntegral_weightedDuhamelIntegrand_le
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {t : ℝ} (ht : 0 < t) (R : ℝ)
    (u : ℝ → PeriodicVectorWeightedSobolev 3)
    (hu : ∀ s ∈ Icc (0 : ℝ) t, ‖u s‖ ≤ R) :
    ‖∫ s in (0 : ℝ)..t, weightedDuhamelIntegrand nu hnu t u s‖ ≤
      (23328 * periodicH3EmbeddingConstant) * R ^ 2 *
        (t + 2 * Real.sqrt (t / (2 * (nu : ℝ)))) := by
  have hR : 0 ≤ R := by
    exact (norm_nonneg (u 0)).trans (hu 0 ⟨le_rfl, ht.le⟩)
  let K : ℝ := (23328 * periodicH3EmbeddingConstant) * R ^ 2
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg (by norm_num) periodicH3EmbeddingConstant_nonneg) (sq_nonneg R)
  have hmajorant := intervalIntegrable_weightedDuhamelMajorant nu hnu ht R
  have hnorm :
      ‖∫ s in (0 : ℝ)..t, weightedDuhamelIntegrand nu hnu t u s‖ ≤
        ∫ s in (0 : ℝ)..t,
          K * duhamelHeatKernelMajorant (nu : ℝ) (t - s) := by
    apply intervalIntegral.norm_integral_le_of_norm_le ht.le
    · filter_upwards with s
      intro hs
      exact norm_weightedDuhamelIntegrand_le_of_norm_le nu hnu t R u s hR
        (hu s ⟨hs.1.le, hs.2⟩)
    · simpa only [K] using hmajorant
  calc
    ‖∫ s in (0 : ℝ)..t, weightedDuhamelIntegrand nu hnu t u s‖ ≤
        ∫ s in (0 : ℝ)..t,
          K * duhamelHeatKernelMajorant (nu : ℝ) (t - s) := hnorm
    _ = K * ∫ s in (0 : ℝ)..t,
          duhamelHeatKernelMajorant (nu : ℝ) (t - s) := by
      rw [intervalIntegral.integral_const_mul]
    _ = K * ∫ tau in (0 : ℝ)..t,
          duhamelHeatKernelMajorant (nu : ℝ) tau := by
      rw [intervalIntegral_reflectedDuhamelHeatKernelMajorant]
    _ ≤ K * (t + 2 * Real.sqrt (t / (2 * (nu : ℝ)))) := by
      exact mul_le_mul_of_nonneg_left
        (intervalIntegral_duhamelHeatKernelMajorant_le hnu ht) hK
    _ = (23328 * periodicH3EmbeddingConstant) * R ^ 2 *
          (t + 2 * Real.sqrt (t / (2 * (nu : ℝ)))) := by
      rfl

section Audit

#print axioms continuous_weightedLerayQuadratic
#print axioms norm_weightedDuhamelIntegrand_le
#print axioms intervalIntegrable_reflectedDuhamelHeatKernelMajorant
#print axioms intervalIntegrable_weightedDuhamelIntegrand
#print axioms norm_intervalIntegral_weightedDuhamelIntegrand_le

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedDuhamelBound
