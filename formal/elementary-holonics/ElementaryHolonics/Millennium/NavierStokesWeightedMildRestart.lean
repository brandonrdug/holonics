import ElementaryHolonics.Millennium.NavierStokesWeightedDuhamelReturnContinuity
import ElementaryHolonics.Millennium.NavierStokesWeightedRestartAperture

/-!
# The actual unforced weighted mild restart

**[proved-derived]** The continuous weighted heat and Duhamel paths are composed into the
unforced mild map

`Phi(u) = exp(nu t Delta) u₀ - Duhamel(u)`.

The exact one-path quadratic remainder and two-path Lipschitz remainder retain the native
weighted Leray coefficient and the explicit viscous aperture budget.  At the common time selected
from a uniform native norm cap, these estimates discharge the complete quadratic-contraction
interface and return an actual fixed path.  Its zero-time face is definitionally inherited from
the linear heat orbit because the nonlinear return vanishes there.
-/

noncomputable section

open Function MeasureTheory Set
open scoped ENNReal NNReal Interval

namespace Soma.Holonics.Millennium.NavierStokesWeightedMildRestart

open Soma.Holonics.Millennium.NavierStokesDuhamelKernelIntegral
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelBound
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelDifference
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelMeasurability
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelReturnContinuity
open Soma.Holonics.Millennium.NavierStokesWeightedLinearPath
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedRestartAperture
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## The actual mild map -/

/-- The unforced mild map on the complete native weighted `H³` path carrier. -/
def weightedMildMap
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev 3) :
    WeightedH3Path T → WeightedH3Path T :=
  fun path ↦
    weightedLinearHeatPath nu hT initial -
      weightedDuhamelPath nu hnu hT path

/-- The actual mild map has exactly the prescribed initial face for every input path. -/
@[simp]
theorem weightedMildMap_zero
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev 3) (path : WeightedH3Path T) :
    weightedMildMap nu hnu hT initial path ⟨0, ⟨le_rfl, hT⟩⟩ = initial := by
  simp [weightedMildMap]

/-! ## Exact Duhamel separation before the fixed-point return -/

/-- The two actual variable-terminal returns retain the sum of the two path norms, rather than
replacing it by the coarser twice-a-common-radius estimate. -/
theorem norm_weightedDuhamelReturn_sub_le_sum
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (u v : WeightedH3Path T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖weightedDuhamelReturn nu hnu hT u t -
        weightedDuhamelReturn nu hnu hT v t‖ ≤
      weightedDuhamelCoefficient (nu : ℝ) t * (‖u‖ + ‖v‖) * ‖u - v‖ := by
  rcases ht.1.eq_or_lt with hzero | htpos
  · subst t
    simp [weightedDuhamelCoefficient]
  · have huIntegrable :=
      intervalIntegrable_weightedDuhamelIntegrand_path nu hnu hT u ht
    have hvIntegrable :=
      intervalIntegrable_weightedDuhamelIntegrand_path nu hnu hT v ht
    rw [weightedDuhamelReturn, weightedDuhamelReturn,
      ← intervalIntegral.integral_sub huIntegrable hvIntegrable]
    let K : ℝ := weightedLerayCoefficient * (‖u‖ + ‖v‖) * ‖u - v‖
    have hK : 0 ≤ K := by
      dsimp [K]
      exact mul_nonneg
        (mul_nonneg weightedLerayCoefficient_nonneg
          (add_nonneg (norm_nonneg u) (norm_nonneg v)))
        (norm_nonneg (u - v))
    have hmajorant : IntervalIntegrable
        (fun s : ℝ ↦ K * duhamelHeatKernelMajorant (nu : ℝ) (t - s))
        volume 0 t :=
      (intervalIntegrable_reflectedDuhamelHeatKernelMajorant nu hnu htpos).const_mul K
    have hnorm :
        ‖∫ s in (0 : ℝ)..t,
            (weightedDuhamelIntegrand nu hnu t (weightedPathExtension hT u) s -
              weightedDuhamelIntegrand nu hnu t (weightedPathExtension hT v) s)‖ ≤
          ∫ s in (0 : ℝ)..t,
            K * duhamelHeatKernelMajorant (nu : ℝ) (t - s) := by
      apply intervalIntegral.norm_integral_le_of_norm_le htpos.le
      · filter_upwards with s
        intro _hs
        have hkernel :
            0 ≤ duhamelHeatKernelMajorant (nu : ℝ) (t - s) :=
          Real.sqrt_nonneg _
        have hinside :
            (23328 * periodicH3EmbeddingConstant) *
                (‖weightedPathExtension hT u s‖ + ‖weightedPathExtension hT v s‖) *
                ‖weightedPathExtension hT u s - weightedPathExtension hT v s‖ ≤
              weightedLerayCoefficient * (‖u‖ + ‖v‖) * ‖u - v‖ := by
          have hcoefficient : 0 ≤ 23328 * periodicH3EmbeddingConstant :=
            mul_nonneg (by norm_num) periodicH3EmbeddingConstant_nonneg
          have hsum :
              ‖weightedPathExtension hT u s‖ + ‖weightedPathExtension hT v s‖ ≤
                ‖u‖ + ‖v‖ :=
            add_le_add (norm_weightedPathExtension_le hT u s)
              (norm_weightedPathExtension_le hT v s)
          have hdiff :
              ‖weightedPathExtension hT u s - weightedPathExtension hT v s‖ ≤
                ‖u - v‖ :=
            norm_weightedPathExtension_sub_le hT u v s
          unfold weightedLerayCoefficient
          calc
            (23328 * periodicH3EmbeddingConstant) *
                  (‖weightedPathExtension hT u s‖ + ‖weightedPathExtension hT v s‖) *
                  ‖weightedPathExtension hT u s - weightedPathExtension hT v s‖ ≤
                (23328 * periodicH3EmbeddingConstant) * (‖u‖ + ‖v‖) *
                  ‖weightedPathExtension hT u s - weightedPathExtension hT v s‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hsum hcoefficient) (norm_nonneg _)
            _ ≤ (23328 * periodicH3EmbeddingConstant) * (‖u‖ + ‖v‖) * ‖u - v‖ :=
              mul_le_mul_of_nonneg_left hdiff
                (mul_nonneg hcoefficient
                  (add_nonneg (norm_nonneg u) (norm_nonneg v)))
        calc
          ‖weightedDuhamelIntegrand nu hnu t (weightedPathExtension hT u) s -
              weightedDuhamelIntegrand nu hnu t (weightedPathExtension hT v) s‖ ≤
              duhamelHeatKernelMajorant (nu : ℝ) (t - s) *
                ((23328 * periodicH3EmbeddingConstant) *
                  (‖weightedPathExtension hT u s‖ + ‖weightedPathExtension hT v s‖) *
                  ‖weightedPathExtension hT u s - weightedPathExtension hT v s‖) :=
            norm_weightedDuhamelIntegrand_sub_le nu hnu t
              (weightedPathExtension hT u) (weightedPathExtension hT v) s
          _ ≤ duhamelHeatKernelMajorant (nu : ℝ) (t - s) * K :=
            mul_le_mul_of_nonneg_left hinside hkernel
          _ = K * duhamelHeatKernelMajorant (nu : ℝ) (t - s) := by ring
      · exact hmajorant
    calc
      ‖∫ s in (0 : ℝ)..t,
          (weightedDuhamelIntegrand nu hnu t (weightedPathExtension hT u) s -
            weightedDuhamelIntegrand nu hnu t (weightedPathExtension hT v) s)‖ ≤
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
          (intervalIntegral_duhamelHeatKernelMajorant_le hnu htpos) hK
      _ = weightedDuhamelCoefficient (nu : ℝ) t * (‖u‖ + ‖v‖) * ‖u - v‖ := by
        unfold K weightedDuhamelCoefficient
        ring

/-- Supremum-norm separation of the actual nonlinear path return with the exact sum-of-norms
factor required by the quadratic contraction interface. -/
theorem norm_weightedDuhamelPath_sub_le_sum
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (u v : WeightedH3Path T) :
    ‖weightedDuhamelPath nu hnu hT u - weightedDuhamelPath nu hnu hT v‖ ≤
      weightedDuhamelCoefficient (nu : ℝ) T * (‖u‖ + ‖v‖) * ‖u - v‖ := by
  have hbound :
      0 ≤ weightedDuhamelCoefficient (nu : ℝ) T * (‖u‖ + ‖v‖) * ‖u - v‖ :=
    mul_nonneg
      (mul_nonneg (weightedDuhamelCoefficient_nonneg hT)
        (add_nonneg (norm_nonneg u) (norm_nonneg v)))
      (norm_nonneg (u - v))
  apply (ContinuousMap.norm_le
    (weightedDuhamelPath nu hnu hT u - weightedDuhamelPath nu hnu hT v) hbound).2
  intro t
  change ‖weightedDuhamelReturn nu hnu hT u t.1 -
      weightedDuhamelReturn nu hnu hT v t.1‖ ≤
    weightedDuhamelCoefficient (nu : ℝ) T * (‖u‖ + ‖v‖) * ‖u - v‖
  have hpoint := norm_weightedDuhamelReturn_sub_le_sum nu hnu hT u v t.2
  have hcoefficient :
      weightedDuhamelCoefficient (nu : ℝ) t.1 ≤
        weightedDuhamelCoefficient (nu : ℝ) T := by
    have hbudget := duhamelApertureBudget_mono nu hnu t.2.2
    exact mul_le_mul_of_nonneg_left hbudget weightedLerayCoefficient_nonneg
  exact hpoint.trans (by
    gcongr)

/-! ## Exact mild-map remainders -/

/-- The one-path mild remainder is exactly the negative nonlinear return and carries the native
quadratic coefficient. -/
theorem norm_weightedMildMap_sub_linear_le
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev 3) (u : WeightedH3Path T) :
    ‖weightedMildMap nu hnu hT initial u - weightedLinearHeatPath nu hT initial‖ ≤
      weightedDuhamelCoefficient (nu : ℝ) T * ‖u‖ ^ 2 := by
  have hduhamel := norm_weightedDuhamelPath_le nu hnu hT u
  simp only [weightedMildMap]
  rw [show
    (weightedLinearHeatPath nu hT initial - weightedDuhamelPath nu hnu hT u) -
        weightedLinearHeatPath nu hT initial =
      -weightedDuhamelPath nu hnu hT u by abel, norm_neg]
  calc
    ‖weightedDuhamelPath nu hnu hT u‖ ≤
        (23328 * periodicH3EmbeddingConstant) * ‖u‖ ^ 2 *
          duhamelApertureBudget nu T := hduhamel
    _ = weightedDuhamelCoefficient (nu : ℝ) T * ‖u‖ ^ 2 := by
      unfold weightedDuhamelCoefficient weightedLerayCoefficient duhamelApertureBudget
      ring

/-- The difference of two mild remainders carries the exact sum-of-path-norms factor. -/
theorem norm_weightedMildMap_remainder_sub_le
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev 3) (u v : WeightedH3Path T) :
    ‖(weightedMildMap nu hnu hT initial u - weightedLinearHeatPath nu hT initial) -
        (weightedMildMap nu hnu hT initial v - weightedLinearHeatPath nu hT initial)‖ ≤
      weightedDuhamelCoefficient (nu : ℝ) T * (‖u‖ + ‖v‖) * ‖u - v‖ := by
  simp only [weightedMildMap]
  rw [show
    ((weightedLinearHeatPath nu hT initial - weightedDuhamelPath nu hnu hT u) -
        weightedLinearHeatPath nu hT initial) -
      ((weightedLinearHeatPath nu hT initial - weightedDuhamelPath nu hnu hT v) -
        weightedLinearHeatPath nu hT initial) =
      -(weightedDuhamelPath nu hnu hT u - weightedDuhamelPath nu hnu hT v) by abel,
    norm_neg]
  exact norm_weightedDuhamelPath_sub_le_sum nu hnu hT u v

/-! ## The cap-selected real-viscosity restart -/

/-- A positive real viscosity remains positive after passage to the native nonnegative-real heat
parameter. -/
theorem real_toNNReal_pos {nu : ℝ} (hnu : 0 < nu) :
    0 < (Real.toNNReal nu : ℝ) := by
  rwa [Real.coe_toNNReal _ hnu.le]

/-- The actual mild map at the common aperture selected from a real viscosity and native cap. -/
def weightedMildRestartMap
    (nu cap : ℝ) (hnu : 0 < nu) (hcap : 0 ≤ cap)
    (initial : PeriodicVectorWeightedSobolev 3) :
    WeightedH3Path (weightedRestartTimeFromCap nu cap) →
      WeightedH3Path (weightedRestartTimeFromCap nu cap) :=
  weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu)
    (weightedRestartTimeFromCap_pos hnu hcap).le initial

/-- **Actual fixed-point return.**  Every initial occurrence below the declared cap returns one
fixed native path at the common viscous aperture, together with its path-ball receipt and exact
initial face. -/
theorem exists_weightedMildRestart_fixedPoint
    {nu cap : ℝ} (hnu : 0 < nu) (hcap : 0 ≤ cap)
    (initial : PeriodicVectorWeightedSobolev 3) (hinitial : ‖initial‖ ≤ cap) :
    ∃ u : WeightedH3Path (weightedRestartTimeFromCap nu cap),
      ‖u‖ ≤ weightedRestartRadiusFromCap cap ∧
        IsFixedPt (weightedMildRestartMap nu cap hnu hcap initial) u ∧
          u ⟨0, ⟨le_rfl, (weightedRestartTimeFromCap_pos hnu hcap).le⟩⟩ = initial := by
  let hT : 0 ≤ weightedRestartTimeFromCap nu cap :=
    (weightedRestartTimeFromCap_pos hnu hcap).le
  let linear : WeightedH3Path (weightedRestartTimeFromCap nu cap) :=
    weightedLinearHeatPath (Real.toNNReal nu) hT initial
  have hlinear : ‖linear‖ ≤ cap :=
    (norm_weightedLinearHeatPath_le (Real.toNNReal nu) hT initial).trans hinitial
  have hremainder : ∀ u : WeightedH3Path (weightedRestartTimeFromCap nu cap),
      ‖weightedMildRestartMap nu cap hnu hcap initial u - linear‖ ≤
        weightedDuhamelCoefficient nu (weightedRestartTimeFromCap nu cap) * ‖u‖ ^ 2 := by
    intro u
    simpa only [weightedMildRestartMap, linear, Real.coe_toNNReal _ hnu.le] using
      norm_weightedMildMap_sub_linear_le
        (Real.toNNReal nu) (real_toNNReal_pos hnu) hT initial u
  have hdifference : ∀ u v : WeightedH3Path (weightedRestartTimeFromCap nu cap),
      ‖(weightedMildRestartMap nu cap hnu hcap initial u - linear) -
          (weightedMildRestartMap nu cap hnu hcap initial v - linear)‖ ≤
        weightedDuhamelCoefficient nu (weightedRestartTimeFromCap nu cap) *
          (‖u‖ + ‖v‖) * ‖u - v‖ := by
    intro u v
    simpa only [weightedMildRestartMap, linear, Real.coe_toNNReal _ hnu.le] using
      norm_weightedMildMap_remainder_sub_le
        (Real.toNNReal nu) (real_toNNReal_pos hnu) hT initial u v
  obtain ⟨u, hu, hfixed⟩ :=
    exists_fixedPoint_of_weightedRestartCap_estimates
      (X := WeightedH3Path (weightedRestartTimeFromCap nu cap))
      hnu hcap (weightedMildRestartMap nu cap hnu hcap initial) linear
      hlinear hremainder hdifference
  refine ⟨u, hu, hfixed, ?_⟩
  have hface := congrArg
    (fun path : WeightedH3Path (weightedRestartTimeFromCap nu cap) ↦
      path ⟨0, ⟨le_rfl, (weightedRestartTimeFromCap_pos hnu hcap).le⟩⟩)
    hfixed
  simpa only [weightedMildRestartMap, weightedMildMap_zero] using hface.symm

section Audit

#print axioms weightedMildMap_zero
#print axioms norm_weightedDuhamelReturn_sub_le_sum
#print axioms norm_weightedDuhamelPath_sub_le_sum
#print axioms norm_weightedMildMap_sub_linear_le
#print axioms norm_weightedMildMap_remainder_sub_le
#print axioms exists_weightedMildRestart_fixedPoint

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
