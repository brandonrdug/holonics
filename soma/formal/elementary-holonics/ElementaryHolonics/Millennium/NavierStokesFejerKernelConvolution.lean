import ElementaryHolonics.Millennium.NavierStokesFejerMultiplier

/-!
# The normalized positive tensor Fejer kernel and its convolution bound

**[proved-derived]** This owner takes the literal finite average behind the Fejer construction.
The positive-frequency cube in `Z^3` supplies a rectangular Dirichlet population.  Its normalized
complex norm-square is pointwise real and nonnegative.  Genuine torus Haar orthogonality proves
that the square has integral equal to the population size, so the normalized kernel has physical
`L1` mass exactly one at every radius.  Convolution by this kernel is consequently an
exact pointwise uniform contraction estimate with constant one, uniformly in the radius.

The square is an explicit averaged finite Fourier multiplier: expanding it gives the normalized
population of ordered frequency differences.  **[open]** This file does not identify that
difference-fibre cardinality with the closed coordinate formula in `tensorHatWeight`; therefore
the pointwise equality `averagedTensorFejerKernel = tensorHatKernel` remains the exact finite
combinatorial bridge to the preceding owner.  The uniform physical-space theorem below concerns
the averaged square itself and does not silently transfer across that open equality.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Soma.Holonics.Millennium.NavierStokesFejerKernelConvolution

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFejerMultiplier

/- Keep the same probability-Haar chart as every torus Fourier owner in this line. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## The positive-frequency population and its normalized square -/

/-- The finite positive-frequency cube used by the rectangular Dirichlet average. -/
def positiveFrequencyCube (radius : ℕ) : Finset SpatialFrequency :=
  Finset.Icc
    (fun _ : Fin 3 ↦ (0 : ℤ))
    (fun _ : Fin 3 ↦ (radius : ℤ))

/-- The positive cube has exactly `(radius + 1)^3` members. -/
theorem card_positiveFrequencyCube (radius : ℕ) :
    (positiveFrequencyCube radius).card = (radius + 1) ^ 3 := by
  simp [positiveFrequencyCube, Pi.card_Icc]

/-- In particular the averaging population is never empty. -/
theorem card_positiveFrequencyCube_pos (radius : ℕ) :
    0 < (positiveFrequencyCube radius).card := by
  rw [card_positiveFrequencyCube]
  positivity

/-- The genuine-torus rectangular Dirichlet population over the positive cube. -/
def rectangularDirichletSum (radius : ℕ) : C(SpatialTorus, ℂ) :=
  ∑ frequency ∈ positiveFrequencyCube radius, UnitAddTorus.mFourier frequency

/-- The physical tensor Fejer kernel: the normalized norm-square of the rectangular Dirichlet
population. -/
def averagedTensorFejerKernel (radius : ℕ) : C(SpatialTorus, ℂ) where
  toFun q :=
    (((positiveFrequencyCube radius).card : ℝ)⁻¹ *
      Complex.normSq (rectangularDirichletSum radius q) : ℝ)
  continuous_toFun := by fun_prop

theorem averagedTensorFejerKernel_apply (radius : ℕ) (q : SpatialTorus) :
    averagedTensorFejerKernel radius q =
      (((positiveFrequencyCube radius).card : ℝ)⁻¹ *
        Complex.normSq (rectangularDirichletSum radius q) : ℝ) := rfl

/-- The physical kernel is real-valued. -/
@[simp]
theorem averagedTensorFejerKernel_im (radius : ℕ) (q : SpatialTorus) :
    (averagedTensorFejerKernel radius q).im = 0 := by
  simp [averagedTensorFejerKernel]

/-- The physical kernel is pointwise nonnegative. -/
theorem averagedTensorFejerKernel_re_nonneg (radius : ℕ) (q : SpatialTorus) :
    0 ≤ (averagedTensorFejerKernel radius q).re := by
  simp only [averagedTensorFejerKernel, ContinuousMap.coe_mk, Complex.ofReal_re]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Complex.normSq_nonneg _)

/-- Its complex norm is exactly the underlying nonnegative real square. -/
theorem norm_averagedTensorFejerKernel (radius : ℕ) (q : SpatialTorus) :
    ‖averagedTensorFejerKernel radius q‖ =
      ((positiveFrequencyCube radius).card : ℝ)⁻¹ *
        Complex.normSq (rectangularDirichletSum radius q) := by
  rw [averagedTensorFejerKernel_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Complex.normSq_nonneg _)

/-! ## Orthogonality normalizes the square -/

/-- The unnormalized rectangular Dirichlet square has Haar mass equal to the exact number of
characters in its population. -/
theorem integral_normSq_rectangularDirichletSum (radius : ℕ) :
    ∫ q : SpatialTorus, Complex.normSq (rectangularDirichletSum radius q) =
      ((positiveFrequencyCube radius).card : ℝ) := by
  rw [← Complex.ofReal_inj, ← integral_complex_ofReal]
  have hexpand : ∀ q : SpatialTorus,
      ((Complex.normSq (rectangularDirichletSum radius q) : ℝ) : ℂ) =
        ∑ first ∈ positiveFrequencyCube radius,
          ∑ second ∈ positiveFrequencyCube radius,
            UnitAddTorus.mFourier (-first) q *
              UnitAddTorus.mFourier second q := by
    intro q
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [rectangularDirichletSum, ContinuousMap.sum_apply, map_sum,
      UnitAddTorus.mFourier_neg, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [integral_congr_ae (Filter.Eventually.of_forall hexpand)]
  have hintegrable : ∀ first ∈ positiveFrequencyCube radius,
      Integrable (fun q : SpatialTorus ↦
        ∑ second ∈ positiveFrequencyCube radius,
          UnitAddTorus.mFourier (-first) q *
            UnitAddTorus.mFourier second q) := by
    intro first _hfirst
    exact continuousMap_integrable_on_compact
      { toFun := fun q : SpatialTorus ↦
          ∑ second ∈ positiveFrequencyCube radius,
            UnitAddTorus.mFourier (-first) q *
              UnitAddTorus.mFourier second q
        continuous_toFun := by fun_prop }
  rw [integral_finset_sum (positiveFrequencyCube radius) hintegrable]
  calc
    ∑ first ∈ positiveFrequencyCube radius,
        ∫ q : SpatialTorus,
          ∑ second ∈ positiveFrequencyCube radius,
            UnitAddTorus.mFourier (-first) q *
              UnitAddTorus.mFourier second q =
        ∑ first ∈ positiveFrequencyCube radius,
          ∑ second ∈ positiveFrequencyCube radius,
            ∫ q : SpatialTorus,
              UnitAddTorus.mFourier (-first) q *
                UnitAddTorus.mFourier second q := by
      apply Finset.sum_congr rfl
      intro first hfirst
      rw [integral_finset_sum]
      intro second _hsecond
      exact continuousMap_integrable_on_compact
        { toFun := fun q : SpatialTorus ↦
            UnitAddTorus.mFourier (-first) q *
              UnitAddTorus.mFourier second q
          continuous_toFun := by fun_prop }
    _ = ((positiveFrequencyCube radius).card : ℂ) := by
      simp [integral_mFourier_neg_mul_mFourier]

/-- **Exact physical `L1` normalization.**  The averaged tensor Fejer kernel has norm integral
one for every radius. -/
theorem integral_norm_averagedTensorFejerKernel (radius : ℕ) :
    ∫ q : SpatialTorus, ‖averagedTensorFejerKernel radius q‖ = 1 := by
  simp_rw [norm_averagedTensorFejerKernel]
  rw [integral_const_mul, integral_normSq_rectangularDirichletSum]
  have hcard : ((positiveFrequencyCube radius).card : ℝ) ≠ 0 := by
    exact_mod_cast (card_positiveFrequencyCube_pos radius).ne'
  exact inv_mul_cancel₀ hcard

/-! ## The scale-uniform convolution return -/

/-- The single physical convolution owner for a continuous complex kernel on the spatial torus. -/
def torusKernelConvolution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (kernel : C(SpatialTorus, ℂ)) (field : C(SpatialTorus, E))
    (q : SpatialTorus) : E :=
  ∫ y : SpatialTorus, kernel y • field (q - y)

/-- Every continuous torus kernel has the elementary pointwise convolution bound by its physical
`L1` norm and the uniform norm of the field. -/
theorem norm_torusKernelConvolution_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (kernel : C(SpatialTorus, ℂ)) (field : C(SpatialTorus, E))
    (q : SpatialTorus) :
    ‖torusKernelConvolution kernel field q‖ ≤
      (∫ y : SpatialTorus, ‖kernel y‖) * ‖field‖ := by
  have hmajorant : Integrable
      (fun y : SpatialTorus ↦ ‖kernel y‖ * ‖field‖) :=
    continuousMap_integrable_on_compact
      { toFun := fun y : SpatialTorus ↦ ‖kernel y‖ * ‖field‖
        continuous_toFun := by fun_prop }
  calc
    ‖torusKernelConvolution kernel field q‖ ≤
        ∫ y : SpatialTorus, ‖kernel y‖ * ‖field‖ := by
      apply norm_integral_le_of_norm_le hmajorant
      filter_upwards [] with y
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left
        (field.norm_coe_le_norm (q - y)) (norm_nonneg _)
    _ = (∫ y : SpatialTorus, ‖kernel y‖) * ‖field‖ := by
      rw [integral_mul_const]

/-- Physical-space convolution by the normalized averaged tensor Fejer kernel. -/
def averagedTensorFejerConvolution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (radius : ℕ) (field : C(SpatialTorus, E)) (q : SpatialTorus) : E :=
  torusKernelConvolution (averagedTensorFejerKernel radius) field q

/-- **Scale-uniform physical-space contraction.**  Convolution by the averaged tensor Fejer
kernel does not enlarge the uniform norm, with radius-independent upper-bound constant one. -/
theorem norm_averagedTensorFejerConvolution_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (radius : ℕ) (field : C(SpatialTorus, E)) (q : SpatialTorus) :
    ‖averagedTensorFejerConvolution radius field q‖ ≤ ‖field‖ := by
  refine (norm_torusKernelConvolution_le
    (averagedTensorFejerKernel radius) field q).trans_eq ?_
  rw [integral_norm_averagedTensorFejerKernel, one_mul]

section Audit

#print axioms integral_normSq_rectangularDirichletSum
#print axioms integral_norm_averagedTensorFejerKernel
#print axioms norm_torusKernelConvolution_le
#print axioms norm_averagedTensorFejerConvolution_le

end Audit

end Soma.Holonics.Millennium.NavierStokesFejerKernelConvolution
